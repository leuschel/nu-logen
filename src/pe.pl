% (c) 2012-2013 Lehrstuhl fuer Softwaretechnik und Programmiersprachen,
% Heinrich Heine Universitaet Duesseldorf
% This software is licenced under EPL 1.0 (http://www.eclipse.org/org/documents/epl-v10.html)

:- module(pe, [pe/2,
               partially_evaluate/2, % partially evaluate a call marked as unfold
               partially_evaluate_and_load/2,
               fast_partially_evaluate_and_load/3, fast_partially_evaluate_and_load/4,
               partially_evaluate_fail_detect/2, partially_evaluate_fail_detect/3,
               specialized_predicate/2,
               generalize_call/3,
               clear_specialized_code/0,
               warnings_occured/0,
               % annotations:
                unfold/1, unfold/2,
                execute/1, execute/2,
                memo/3,
                forward_block/1 % declare that a call to a predicate may precede its first usage
              ]).

% written by Michael Leuschel
% started 15/12/2012


% a partial evaluator implemented using term expansion
% the original program is copied unmodified, interspersed with discontiguous directives
% and unfolder clauses in the style of Logen (see Theory and Practice of Logic Programming 4(1):pp. 139-191.)

% A difference with Logen is that the term expander works directly on the source program:
%  the goal is to only selectively annotate certain points of the source program.

% Annotations are:
%  - mark predicates to be unfolded with
%     :- unfold p(_,...).
%  - mark predicates to be fully executed with
%     :- execute p(_,...).
%  - mark predicates to be fully executed upon a condition with:
%     :- execute(p(_,...),Condition).

% Commands:
%  - clear specialized code with clear_specialized_code
%  - specialize a predicate with partially_evaluate(Pred,R)
%      (R is the residual call to be used to call the specialized code)
% TO DO:
%  - proper module treatment [partially done]
%  - asserting and calling specialized clauses [partially done]
%  - generate memoization points to avoid backpropagation and clause duplication
%  - introduce memo annotation and treatment if necessary


:- use_module(builtin_tools).
%:- use_module(probsrc(tools),[print_message/1]).
print_message(X) :- print_message(informational,X).

:- multifile user:term_expansion/6.

:- use_module(library(lists)).
:- use_module(library(timeout)).


:- op(1150, fx, unfold).

%:- meta_predicate unfold(0).
% unfold annotation
unfold(MCall,Condition) :-
   get_module_context(MCall,Module,Call),
   %print(unfold(Module:Call)),nl,
   check_nonvar_args(Call),
   assert(is_unfolded(Module,Call,Condition)),
   (not_unfolded_or_memoized(Module,Call)
     ->  nl, print('*** WARNING: UNFOLD DECLARATION OCCURS AFTER FIRST CLAUSE '),nl,
             print('*** PREDICATE: '), print(Module:Call),nl,nl
     ;   true).
:- dynamic is_unfolded/3.
unfold(MCall) :- unfold(MCall,true).

check_nonvar_args(Call) :- Call =.. [_F|Args],
   member(X,Args), nonvar(X),!,
   print_warning('non-variable argument in annotation:',Call,X).
check_nonvar_args(_).

:- dynamic is_memoized/4.
memo(MCall,Condition,Filter) :-
   get_module_context(MCall,Module,Call),
   print(unfold(Module:Call)),nl,
   assert(is_memoized(Module,Call,Condition,Filter)),
   (not_unfolded_or_memoized(Module,Call)
     ->  nl, print('*** WARNING: MEMO DECLARATION OCCURS AFTER FIRST CLAUSE '),nl,
             print('*** PREDICATE: '), print(Module:Call),nl,nl
     ;   true).

:- dynamic not_unfolded_or_memoized/2.
check_is_unfolded_or_memoized(V) :- var(V),!,
    print_warning('illegal call:',check_is_unfolded_or_memoized(V)),fail.
check_is_unfolded_or_memoized(M:C) :- !, check_is_unfolded_or_memoized(M,C).
check_is_unfolded_or_memoized(C) :- prolog_load_context(module,M),
    check_is_unfolded_or_memoized(M,C).

check_is_unfolded_or_memoized(M,C) :- (is_unfolded(M,C,_) ; is_memoized(M,C,_,_)),!.
check_is_unfolded_or_memoized(M,C) :-
   \+ not_unfolded_or_memoized(M,C),
   assert(not_unfolded_or_memoized(M,C)),
   fail.

% check if this call is unfolded in this or some other module (which could be imported)
is_unfolded_somewhere(MCall,AdaptedCall,Condition) :-
   get_module_context(MCall,Module,Call),
   (is_unfolded(Module,Call,Condition) -> AdaptedCall=Module:Call
    ; is_unfolded(OtherModule,Call,Condition),
      AdaptedCall = OtherModule:Call,
      print('*** assuming '), print(OtherModule:Call), print(' imported in '),print(Module),nl
       % TO DO: keep track of imports and check that this is indeed the case !!
    ).
% check if this call is memoized in this or some other module (which could be imported)
is_memoized_somewhere(MCall,AdaptedCall,Condition,GenAdaptedCall) :-
   get_module_context(MCall,Module,Call),
   (is_memoized(Module,Call,Condition,GenCall)
    -> AdaptedCall=Module:Call, GenAdaptedCall=Module:GenCall
    ;  is_memoized(OtherModule,Call,Condition,GenCall),
       AdaptedCall=OtherModule:Call, GenAdaptedCall=OtherModule:GenCall,
       print('*** assuming '), print(OtherModule:Call), print(' imported in '),print(Module),nl
       % TO DO: keep track of imports and check that this is indeed the case !!
    ).


:- op(1150, fx, execute).
% register conditions under which some predicates should be executed directly
:- dynamic execute_predicate/3.
execute(MCall) :-
   get_module_context(MCall,Module,Call),
   print(execute(Module,Call)),nl,
   assert(execute_predicate(Module,Call,true)).
execute(MCall,Condition) :-
   get_module_context(MCall,Module,Call),
   print(execute(Module,Call,Condition)),nl,
   assert(execute_predicate(Module,Call,Condition)).

execute_predicate_in_load_context(Call,Cond) :- prolog_load_context(module,M),
   execute_predicate_in_context(M,Call,Cond).
execute_predicate_in_context(_,M:Call,Cond) :- execute_predicate(M,Call,Cond).
execute_predicate_in_context(Module,Call,Cond) :- execute_predicate(Module,Call,Cond).

add_module_qualifier(M:C,R) :- !, R=M:C. % already qualified
add_module_qualifier(C,M:C) :- prolog_load_context(module,M).

get_module_context(M:C,RM,RC) :- !,  % already qualified
    get_inner_module_context(C,M,RM,RC).  % strip out further module qualifiers; user the innermost module as the real module
get_module_context(Call,M,Call) :- prolog_load_context(module,M).

get_inner_module_context(Var,M,RM,RC) :- var(Var),!, RM=M, RC=Var.
get_inner_module_context(M:C,_,RM,RC) :- !, get_inner_module_context(C,M,RM,RC).
get_inner_module_context(C,M,M,C).


:- dynamic block_declaration/4.
% TO DO: extract predicate and use as index --> block_declaration/2
% ?? Do we need a meta_predicate annotation ??
add_block_declaration(A) :- prolog_load_context(module,M),
   %print(block_declaration(A,M,TP)),nl,
   (flatten_block(A,Pred,N,BlockList)
      -> functor(Call,Pred,N),
         assert(block_declaration(Call,M,BlockList,A))
         %,print(block_declaration(Call,M,BlockList,A)),nl
      ;  prolog_load_context(term_position,TP), % TP=$stream_position(?,?,LineNumberBefore,?)
         print_warning('could not parse block declaration: ',(TP:A))
    ),
    (no_block_unfold(Call,M)
      -> Call=..[F|Args],
         print_warning('declaration needed for:',F),
         maplist(qmark,Args,QArgs), QCall =.. [F|QArgs],
         print_warning(' :-',forward_block(QCall),'.')
      ; true).
get_block_declaration(M:Call,BlockList,A) :-
   block_declaration(Call,M,BlockList,A).
qmark(_,'?').

:- dynamic nr_warnings/1.
nr_warnings(0).
inc_nr_warnings :- retract(nr_warnings(N)),
   N1 is N+1, assert(nr_warnings(N1)).
:- public print_warning/1.
print_warning(Msg) :-
    format(user_error,'~n! ### WARNING : ~w~n~n',[Msg]),inc_nr_warnings.
print_warning(Msg1,Msg2) :-
    format(user_error,'~n! ### WARNING : ~w ~w~n~n',[Msg1,Msg2]), inc_nr_warnings.
print_warning(Msg1,Msg2,Msg3) :-
    format(user_error,'~n! ### WARNING : ~w ~w ~w~n~n',[Msg1,Msg2,Msg3]), inc_nr_warnings.
warnings_occured :-
    nr_warnings(X), X>0,
    format(user_error,'~n! WARNINGS have occured !~n! Number of WARNINGS : ~w~n~n',[X]).

:- dynamic no_block_unfold/2.
% register that we unfold a call assuming no block declaration
assert_no_block_unfold(M:Call) :- !,
   (\+ no_block_unfold(Call,M) -> functor(Call,F,N), functor(CC,F,N),assert(no_block_unfold(CC,M))
      ; true).
assert_no_block_unfold(Call) :- % should not happen
   assert_no_block_unfold(unknown:Call).

:- dynamic forward_block_declaration/2.
has_block_declaration(M:Call) :-
   (block_declaration(Call,M,_BlockList,_A) ;
    forward_block_declaration(Call,M)).

% declare that a call to a predicate may precede its first usage
forward_block(MCall) :-
   get_module_context(MCall,Module,Call),
   functor(Call,F,N), functor(VCall,F,N), % get rid of any terms inside
   assert(forward_block_declaration(VCall,Module)).

% transform a block declaration into a list of argument pattern lists
flatten_block((A,B),Pred,N,X) :- !, flatten_block(A,Pred,N,XA),
   flatten_block(B,Pred,N,XB),
   append(XA,XB,X).
flatten_block(Call,Pred,N,X) :- Call =.. [Pred|Args], length(Args,N),
   maplist(get_block_pattern,Args,BPat),
   X = [ BPat ].
% - is kept, everything else is translated to variable matching anything
get_block_pattern(X,Pat) :- (X = '-' -> Pat = '-' ; Pat = _).

% check if a call is blocked:
call_is_blocked(Call,AbsInfo) :- get_block_declaration(Call,BlockList,_A),
   call_is_blocked(Call,BlockList,AbsInfo).
call_is_blocked(_M:Call,BlockList,AbsInfo) :- !, call_is_blocked(Call,BlockList,AbsInfo).
call_is_blocked(Call,BlockList,AbsInfo) :-
   %print(checking_block(Call,BlockList)),nl,
   Call =.. [_Pred|Args],
   maplist(get_arg_pattern(AbsInfo),Args,Pat),
   (member(Pat,BlockList)
    -> true %print('% '), print(blocking(Call,Pat)),nl
     ; %print(non_blocking(Pat)),nl,
       fail
   ).

get_arg_pattern(AbsInfo,X,Pat) :-
   (check_nonvar(AbsInfo,X) -> Pat = nonvar
                             ; Pat = '-').


% NOTE: block declarations can also be extracted using predicate_property
% | ?- predicate_property(test_pe:myapp(A,B,C),P).
% P = (block myapp(-,?,-)) ?

% turn discontiguous_warnings off as SICStus currently erroneously generates them
:- set_prolog_flag(discontiguous_warnings, off).
% does not really help

% now: generate unfolder predicates for those predicates marked as unfoldable
user:term_expansion(':-'(block(A)), Lay1, Tokens1,
                    ':-'(block(A)), Lay1, [partial_evaluator | Tokens1]) :-
    nonmember(partial_evaluator, Tokens1), % do not expand if already expanded
    !,
    add_block_declaration(A).
user:term_expansion(H1, Lay1, Tokens1,
     [(:- discontiguous(P1/A1)),H1, % a copy of the original fact
      (:- discontiguous(P2/A2)),H2],  % the corresponding unfolder clause
      Lay1, [partial_evaluator | Tokens1]) :-
    %print(check(H1,Tokens1)),nl,
    nonmember(partial_evaluator, Tokens1), % do not expand if already expanded
    check_is_unfolded_or_memoized(H1),!, % fact
    get_predicate_arity(H1,_,P1,A1),
    generate_unfolder_call(H1,true,_AbsInfo,H2),
    %print('  unfold fact: '), print(H2),nl, %%
    get_predicate_arity(H2,_,P2,A2).
user:term_expansion(':-'(H1,B1), Lay1, Tokens1,
     [(:- discontiguous(P1/A1)),':-'(H1,B1), % a copy of the original clause
      (:- discontiguous(P2/A2)),':-'(H2,PP_B2)],  % the corresponding unfolder clause
      Lay1, [partial_evaluator | Tokens1]) :-
    nonmember(partial_evaluator, Tokens1), % do not expand if already expanded
    check_is_unfolded_or_memoized(H1),!, % rule
    get_predicate_arity(H1,_,P1,A1),
    generate_unfolder_call(H1,Code,AbsInfo,H2),
    annotate_cut_in_body(B1,AB1), % detect ! and replace by '$CUT' if possible
    compile_body(AB1,B2,Code,AbsInfo),
    post_process(B2,PP_B2),
    % print(' ***  unfold rule: '),nl, portray_clause((H2:-PP_B2)), %%
    %portray_clause((H1 :- B1)),
    get_predicate_arity(H2,_,P2,A2).

get_predicate_arity(X,M,P,A) :- var(X),!,
   print_warning('get_predicate_arity of variable: ',get_predicate_arity(X,M,P,A)),fail.
get_predicate_arity(':'(Module,Call),Module,Pred,Arity) :- !,
   functor(Call,Pred,Arity).
get_predicate_arity(Call,Module,Pred,Arity) :-
   prolog_load_context(module,Module),
   functor(Call,Pred,Arity).

% generate an unfolding call
generate_unfolder_call(Module:Call,CodeArg,AbsInfoArg,Module:NewUnfoldingCall) :- !,
    generate_unfolder2(Call,CodeArg,AbsInfoArg,NewUnfoldingCall).
generate_unfolder_call(Call,CodeArg,AbsInfoArg,Module:NewUnfoldingCall) :- !,
    prolog_load_context(module,Module),
    generate_unfolder2(Call,CodeArg,AbsInfoArg,NewUnfoldingCall).
generate_unfolder2(Call,CodeArg,AbsInfoArg,NewUnfoldingCall) :-
    Call =.. [F|Args],
    append(Args,[CodeArg,AbsInfoArg],NewArgs),
    atom_concat(F,'$unfold',NewF),
    NewUnfoldingCall =.. [NewF|NewArgs].

% specialize the call built-in
:- public specialize_call/4.
specialize_call(Module,Call,Code,_AbsInfo) :- var(Call),!, Code=call(Module:Call).
specialize_call(Module,Call,Code,AbsInfo) :- get_inner_module_context(Call,Module,RealModule,RealCall),
    nl,print(specialize(RealModule,RealCall)),nl,
    specialize_call_aux(RealModule,RealCall,Code,AbsInfo).
specialize_call_aux(Module,Call,Code,_AbsInfo) :- var(Call),!, Code=call(Module:Call).
specialize_call_aux(Module,Call,Code,AbsInfo) :- !,
     compile_body(Module:Call,Spec,Code,AbsInfo), %print(spec(Spec,Code)),nl,
     call(Spec).
/*
specialize_call_aux(_Module,Call,Code) :-
    executable_builtin(Call),!,call(Call), Code=true.
specialize_call_aux(_Module,Call,Code) :-
    is_builtin(Call),!, Code=Call.
specialize_call_aux(Module,Call,Code) :- %print(try_exec(Module,Call,Code)),nl,
    execute_predicate_in_context(Module,Call,Condition), % print(cond(Condition)),nl,
    call(Condition),!, % we can execute the predicate
    %print(executing(Call)),nl,
    call(Module:Call),Code=true.
% TO DO: register unfolder predicates and look if we can unfold the call
specialize_call_aux(Module,Call,Module:Call).
*/

% find top-level cuts and compute atoms to the left and right
find_cut_in_body(V,_,_) :- var(V),!,fail.
find_cut_in_body(!,true,Rest) :- !,Rest=true.
find_cut_in_body((A,B),ACut,Rest) :- find_cut_in_body(A,ACut,ARest),!,
   (ARest=true -> Rest=B ; Rest=(ARest,B)).
find_cut_in_body((A,B),(A,BCut),Rest) :- find_cut_in_body(B,BCut,BRest),!, Rest=BRest.

annotate_cut_in_body(A,Res) :- find_cut_in_body(A,ACut,Rest),!,
    annotate_cut_in_body(Rest,ARest),
    (ARest==true -> Res = '$CUT'(ACut) ; Res=('$CUT'(ACut),ARest)).
annotate_cut_in_body(A,A).

conjoin(A,B,AB) :-
  (  A==true -> AB=B
   ; B==true -> AB=A
   ; A==fail -> AB=fail
   ; AB = (A,B)).

% compile the body of a clause; translating calls to unfoldable predicates
compile_body(B1,B2,Code,AbsInfo) :- var(B1),!, prolog_load_context(module,M),
    B2=pe:specialize_call(M,B1,Code,AbsInfo).
compile_body(true,B2,Code,_AbsInfo) :- !, B2=true, Code=true.
compile_body(call(A),B2,Code,AbsInfo) :- !, compile_body(A,B2,Code,AbsInfo).
compile_body((A1,B1),Spec,Code,AbsInfo) :- !, % specialize the conjunction
    compile_body(A1,A2,C1,AbsInfo),
    compile_body(B1,B2,C2,AbsInfo),
    conjoin(A2,B2,Spec),
    conjoin(C1,C2,Code).
compile_body(B1,Spec,Code,AbsInfo) :- is_memoized_somewhere(B1,_MB1,_,_),!,
    protected_compile_body(B1,Spec,Code,AbsInfo).
compile_body(B1,Spec,Code,AbsInfo) :- is_unfolded_somewhere(B1,MB1,Condition),!,
    %VB2=if(Spec,true,(print(unfold_failed(MB1)),nl,fail)),  %%
    (has_block_declaration(MB1)
      ->   generate_unfolder_call(MB1,UnfCode,AbsInfo,UnfSpec),
           Spec = (call(Condition) ->
                    (pe:call_is_blocked(MB1,AbsInfo)
                     -> %Code=MB1 % just residualize; maybe do this if all args are variables or unfold condition is false
                      partially_evaluate_fail_detect(MB1,Code,AbsInfo)
                     ; Code=UnfCode, UnfSpec)
                   ; Code=MB1)
      ;  (Condition = true) -> generate_unfolder_call(MB1,Code,AbsInfo,Spec),
                               assert_no_block_unfold(MB1)
      ;  otherwise ->          generate_unfolder_call(MB1,UnfCode,AbsInfo,UnfSpec),
                               Spec = (call(Condition) -> Code=UnfCode, UnfSpec ; Code=MB1),
                               assert_no_block_unfold(MB1)
    ).
compile_body(B1,B2,Code,_AbsInfo) :- execute_predicate_in_load_context(B1,true),!,
    add_module_qualifier(B1,MB1),
    B2=MB1,
    %B2=if(MB1,true,(print(exec_failed(MB1)),nl,fail)),  %% comment in if you want to see failed execute calls
    Code=true.
compile_body(B1,B2,Code,_AbsInfo) :- execute_predicate_in_load_context(B1,Condition),!,
    add_module_qualifier(B1,MB1),
    B2=(call(Condition) -> call(MB1),Code=true ; Code=MB1).
compile_body(B1,B2,Code,AbsInfo) :- is_builtin(B1), !,
     B2 = builtin_tools:specialize_builtin(B1,Code,AbsInfo).
compile_body((Tst->Thn;Els),B2,Code,AbsInfo) :- !,
     protected_compile_body(Tst,Tst2,C0,AbsInfo),
     protected_compile_body(Thn,T2,C1,AbsInfo),
     protected_compile_body(Els,E2,C2,AbsInfo),
     compile_body(Thn,UPT2,UPC1,AbsInfo), /* unprotected version for static if */
     compile_body(Els,UPE2,UPC2,AbsInfo),
     (\+ could_be_decided(C0)
       -> %nl,nl,print(undecidable(C0,Tst,Tst2)),nl,nl,
          B2 = (Tst2, T2,E2),   Code=(C0->C1;C2)  % always dynamic if
       ;  B2 = (Tst2, pe:post_process(C0,PPC0),
                     ( PPC0==fail  -> UPE2,Code=UPC2 % static if; we can use an improved unprotected compile
                      ; PPC0==true -> UPT2,Code=UPC1 % ditto
                      ; T2,E2, Code=(PPC0->C1;C2)))  % dynamic if
      ).
compile_body(if(Tst,Thn,Els),B2,Code,AbsInfo) :- !,
     protected_compile_body(Tst,Tst2,C0,AbsInfo),
     protected_compile_body(Thn,T2,C1,AbsInfo),
     protected_compile_body(Els,E2,C2,AbsInfo),
     compile_body(Thn,UPT2,UPC1,AbsInfo), /* unprotected version for static if */
     compile_body(Els,UPE2,UPC2,AbsInfo),
     (\+ could_be_decided(C0)
       -> B2 = (Tst2, T2,E2),   Code=if(C0,C1,C2)
       ;  B2 = (Tst2, pe:post_process(C0,PPC0),
                      (PPC0==fail   -> UPE2,Code=UPC2  /* static if; we can use unprotected compile */
                       ; PPC0==true -> UPT2,Code=UPC1  /* ditto */
                       ; T2,E2, Code=if(PPC0,C1,C2)))
     ).
compile_body((A;B),B2,Code,AbsInfo) :- !,
     protected_compile_body(A,T2,C1,AbsInfo),
     protected_compile_body(B,E2,C2,AbsInfo),
     B2 = (T2,E2), Code = (C1 ; C2).
compile_body((A->B),B2,Code,AbsInfo) :- !,
     protected_compile_body(A,T2,C1,AbsInfo),
     protected_compile_body(B,E2,C2,AbsInfo),
     compile_body(B,UPE2,UPC2,AbsInfo), % in case A simplifies to true
     B2 = (T2, pe:post_process(C1,PPC1),
           (PPC1==true -> UPE2, Code=UPC2 ; PPC1\==false, E2, Code = (PPC1 -> C2))).
compile_body(when(Cond,A),Spec,Code,AbsInfo) :- !,
     protected_compile_body(A,PASpec,PACode,AbsInfo),
     compile_body(A,ASpec,ACode,AbsInfo),
     Spec = (pe:simplify_when_condition(Cond,SCond,AbsInfo), %print(when(Cond,SCond,AbsInfo)),nl,
             (SCond=true -> ASpec,Code = ACode % when no longer needed
              ; PASpec,Code = when(SCond,PACode))).
compile_body(on_exception(E,A,B),S1,Code,_AbsInfo) :- !,
     protected_compile_body(A,AS,AC,AbsInfo),
     protected_compile_body(B,BS,BC,AbsInfo),
     S1 = (on_exception(E,AS,AC=throw(E)),BS),
     Code = on_exception(E,AC,BC).
compile_body(time_out(A,TO,TRes),B2,Code,AbsInfo) :- !,
% to do: ensure that big single clauses not copied into here
     protected_compile_body(A,B2,C1,AbsInfo), Code = time_out(C1,TO,TRes).
%compile_body(!,B2,Code) :- !, B2=true, Code=!. % dynamic cut; does not work like this
compile_body(!,B2,Code,_AbsInfo) :- !, B2=!, Code=(print(static_cut),nl). % static cut
compile_body('$CUT'(Left),Spec,Code,AbsInfo) :- !,
     compile_body(Left,LSpec,LCode,AbsInfo),
     (LCode==true % definitely no code to the left of the cut remains
       -> Spec = (LSpec, ! ), Code = true
       ;  Spec = (LSpec, pe:post_process(LCode,PPLCode),
             (PPLCode=true ->  % static cut, the code to the left succeeds
                 !, Code = PPLCode
               ; PPLCode \= fail,
                 pe:print_warning(code_to_the_left_of_cut(Left,PPLCode)),
                    %!, Code = (PPLCode,print(unsafe_cut),nl) % static cut
                 % TO DO: check if we are at the top-level of a clause; then ok
                     Code = (PPLCode,!) % dynamic cut
            ) )
     ).
% to do: X^P, call_cleanup, try, call_residue_vars, iterators
compile_body(M:B1,B2,Code,_AbsInfo) :- !,B2=true, Code=M:B1.
compile_body(B1,B2,Code,_AbsInfo) :- prolog_load_context(module,M),
     % add module qualifier if missing as residual clauses reside in pe module
     B2=true, Code=M:B1.

% check if a piece of code could be decided to be true or fail at compile time
could_be_decided(X) :- var(X),!.
could_be_decided(true). could_be_decided(fail).
could_be_decided((A,_)) :- could_be_decided(A).
could_be_decided((_;_)).

:- use_module(library(terms),[term_variables_bag/2, variant/2]).
:- if(current_prolog_flag(dialect,sicstus)).
:- if((current_prolog_flag(version_data,sicstus(4,X,_,_,_)),X<3)).
:- use_module(library(terms),[term_variables/2]). % is built-in in SICSTUS 4.3
:- endif.
:- endif.

% compile a body in such a way that we the specializer does not instantiate nor fails
protected_compile_body(B1,B2,Code,AbsInfo) :- var(B1),!, prolog_load_context(module,M),
    B2=pe:specialize_call(M,B1,Code,AbsInfo).
protected_compile_body(true,B2,Code,_AbsInfo) :- !, B2=true, Code=true.
protected_compile_body((A1,B1),(A2,B2),(C1,C2),AbsInfo) :- !,
   protected_compile_body(A1,A2,C1,AbsInfo),
   protected_compile_body(B1,B2,C2,AbsInfo).
protected_compile_body(call(A),B2,Code,AbsInfo) :- !,
   protected_compile_body(A,B2,Code,AbsInfo).
protected_compile_body(B1,Spec,Code,AbsInfo) :-
    is_memoized_somewhere(B1,MB1,Condition,GenMB1),!,
    Spec = (call(Condition) -> %print(memo(MB1)),nl,
                         partially_evaluate_fail_detect(GenMB1,Code,AbsInfo),  % memoize; return residual call as Code
                         MB1=GenMB1 % unify call with generalized call to instantiate Call in Code
                       ; %print(residualize(MB1)),nl,
                         Code=MB1).
protected_compile_body(B1,Spec,Code,AbsInfo) :- is_unfolded_somewhere(B1,MB1,Condition),!,
    %print(protected_unfold(MB1,Condition)),nl,
    Spec = (call(Condition) -> %print(memo(MB1)),nl,
                         partially_evaluate_fail_detect(MB1,Code,AbsInfo)  % memoize; return residual call as Code
                       ; %print(residualize(MB1)),nl,
                         Code=MB1).
protected_compile_body(B1,B2,Code,_AbsInfo) :- execute_predicate_in_load_context(B1,Condition),!,
    add_module_qualifier(B1,MB1),
    B2=((ground(B1),call(Condition))  /* we can execute and no bindings can be generated */
    % Sometimes it is also safe to do this even if B1 is not ground, namely if the variables are all free; e.g., the call  bmachine:b_machine_temp_predicate(Q)
        -> (call(MB1) -> Code=true ; Code=fail)
         ; (call(Condition), \+ pe:is_builtin(B1)) % it is an executable user-built-in
            ->  terms:term_variables(MB1,Vars), copy_term((MB1,Vars),(CMB1,CVars)),
                (call(CMB1)
                   ->  Code = (Vars=CVars) % we could seperated out into a conjunction of =
                   ; Code=fail)
        ; Code=MB1).
protected_compile_body((Tst->Thn;Els),B2,Code,AbsInfo) :- !,
     protected_compile_body(Tst,Tst2,C0,AbsInfo),
     protected_compile_body(Thn,T2,C1,AbsInfo),
     protected_compile_body(Els,E2,C2,AbsInfo),
     (\+ could_be_decided(C0)
       -> %nl,nl,print(undecidable(C0,Tst,Tst2)),nl,nl,
          B2 = (Tst2, T2,E2),   Code=(C0->C1;C2)  % always dynamic if
       ;  B2 = (Tst2, pe:post_process(C0,PPC0),
                     ( PPC0==fail  -> E2,Code=C2 % static if
                      ; PPC0==true -> T2,Code=C1 % ditto
                      ; T2,E2, Code=(PPC0->C1;C2)))  % dynamic if
      ).
protected_compile_body(if(Tst,Thn,Els),B2,Code,AbsInfo) :- !,
     protected_compile_body(Tst,Tst2,C0,AbsInfo),
     protected_compile_body(Thn,T2,C1,AbsInfo),
     protected_compile_body(Els,E2,C2,AbsInfo),
     (\+ could_be_decided(C0)
       -> B2 = (Tst2, T2,E2),   Code=if(C0,C1,C2)
       ;  B2 = (Tst2, pe:post_process(C0,PPC0),
                      (PPC0==fail   -> E2,Code=C2  /* static if */
                       ; PPC0==true -> T2,Code=C1  /* ditto */
                       ; T2,E2, Code=if(PPC0,C1,C2)))
     ).
protected_compile_body((A->B),B2,Code,AbsInfo) :- !,
     protected_compile_body(A,T2,C1,AbsInfo),
     protected_compile_body(B,E2,C2,AbsInfo),
     B2 = (T2, pe:post_process(C1,PPC1),
           (PPC1==true -> E2, Code=C2
             ; PPC1==false -> Code=false
             ; E2, Code = (PPC1 -> C2))).
protected_compile_body(when(Cond,A),Spec,Code,AbsInfo) :- !,
     protected_compile_body(A,ASpec,ACode,AbsInfo),
     Spec = (ASpec, pe:simplify_when_condition(Cond,SCond,AbsInfo),
             (SCond=true -> Code = ACode ; Code = when(SCond,ACode))).
protected_compile_body(Body,Spec,Code,AbsInfo) :- \+ can_instantiate_or_fail(Body),!,
   %print(is_safe(Body)),nl,
   compile_body(Body,Spec,Code,AbsInfo).
protected_compile_body(Body,Spec,Code,AbsInfo) :- is_builtin(Body),!,
   Spec =(builtin_tools:is_decidable_builtin(Body,AbsInfo)
           -> (Body -> Code=true ; Code=fail)
           ; Code=Body).
protected_compile_body(Body,PSpec,PCode,AbsInfo) :-
   compile_body(Body,BSpec,BCode,AbsInfo),
   % better: create a memoisation point
   PSpec = (terms:term_variables(Body,VB),findall((VB:-BCode),BSpec,Clauses)),
   PCode = (member((VB:-C),Clauses),call(C)).

% simplify the condition of a when
simplify_when_condition(V,R,_AbsInfo) :- var(V),!, R=V.
simplify_when_condition(ground(X),R,AbsInfo) :- !,
  (check_ground(AbsInfo,X) -> R=true ;
    nonvar(X) -> term_variables(X,TV),exclude(check_ground(AbsInfo),TV,FTV),
                 (FTV=[VAR] -> R=ground(VAR) ; R=ground(FTV))
    ; otherwise -> R = ground(X)).
simplify_when_condition(nonvar(X),R,AbsInfo) :- !,
  (check_nonvar(AbsInfo,X) -> R=true ; R = nonvar(X)).
simplify_when_condition((A,B),R,AbsInfo) :- !,
   simplify_when_condition(A,RA,AbsInfo),
   simplify_when_condition(B,RB,AbsInfo),
   (RA=true -> R=RB
    ; RB=true -> R=RA
    ; R=(RA,RB)).
simplify_when_condition((A;B),R,AbsInfo) :- !,
   simplify_when_condition(A,RA,AbsInfo),
   simplify_when_condition(B,RB,AbsInfo),
   (RA=true -> R=true
    ; RB=true -> R=true
    ; R=(RA;RB)).
simplify_when_condition(A,A,_AbsInfo).

% check when compile_body could instantiate the goal or fail during specialization time
can_instantiate_or_fail(V) :- var(V),!,fail.
can_instantiate_or_fail(true) :- !,fail.
can_instantiate_or_fail(otherwise) :- !,fail.
can_instantiate_or_fail(B) :- is_builtin(B).
can_instantiate_or_fail(B) :- is_unfolded_somewhere(B,_,_).
can_instantiate_or_fail(B) :- execute_predicate_in_load_context(B,_).
% below cannot instantiante; or can they ??
%can_instantiate_or_fail((A;B)) :- can_instantiate_or_fail(A) ; can_instantiate_or_fail(B).
%can_instantiate_or_fail((A->B)) :- can_instantiate_or_fail(A) ; can_instantiate_or_fail(B).
%can_instantiate_or_fail(\+(_)).


% remove useless true literals; remove everything after a fail
post_process(X,Y) :- var(X),!,Y=X.
post_process((A,B),Res) :- !,post_process(A,PA),
   (PA==true -> post_process(B,Res)
    ; PA==fail -> Res = fail
    ; post_process(B,PB),
       (PB==true -> Res=PA
        ; (PA==!, PB=(!,_)) -> Res = PB % remove two cuts that follow each other
        ; Res = (PA,PB))
   ).
post_process((A->B;C),Res) :- !,post_process(A,PA),
   (PA==fail -> post_process(C,Res)
    ; PA==true -> post_process(B,Res)
    ; post_process(B,PB),post_process(C,PC),
      Res = (PA->PB;PC)
   ).
post_process((A;B),Res) :- !,post_process(A,PA),
   (PA==fail -> post_process(B,Res)
    ; post_process(B,PB),
       (PB==fail -> Res=PA ; Res = (PA;PB))
   ).
post_process((A->B),Res) :- !,post_process(A,PA),
   (PA==fail -> Res=fail
    % ; PA==true -> post_process(B,Res) %% correct ???
    ; post_process(B,PB),
      Res = (PA->PB)
   ).
post_process(M:W,Res) :- nonvar(W),W=when(A,B),!,
   Res=M:R,post_process(when(A,B),R). % also do this for other constructs ??
post_process(when(A,B),Res) :- !,
   simplify_when_condition(A,PA,[]), % TO DO: use AbsInfo !?
   post_process(B,PB),
   (PA==true -> Res=PB
    ; PA==fail -> print_warning('unsatisfiable when:',when(A,B)),
                  Res = when(A,PB)
    ; Res = when(PA,PB)
   ).
post_process(member(_,L),Res) :- L==[],!, Res = fail. % appears in protected_compile
post_process(BI,S) :- post_process_builtin(BI,SBI),!, S=SBI.
post_process(call(X),S) :- nonvar(X),!, post_process(X,S).
post_process(time_out(X,TO,TRes),Res) :- !,  % to do: check if library(timeout) loaded
    post_process(X,PX),
    Res = time_out(PX,TO,TRes).
post_process(X,X).


:- meta_predicate pe(0,*).
unfold_call(Call,AbstractInfos,PPCode) :- %print(unfolding(Call)),nl,
   generate_unfolder_call(Call,Code,AbstractInfos,NC),!,
   call(NC),
   post_process(Code,PPCode).
unfold_call(Call,_AbstractInfos,Code) :-
    print_warning('trying to unfold unregistered call :',Call),
    Code=true, call(Call).

pe(C,Clauses) :-
   findall((C :- Code), unfold_call(C,[],Code), Clauses).

:- dynamic specialized_predicate/2.
:- meta_predicate partially_evaluate(0,*).
:- meta_predicate partially_evaluate(0,*,*,*).
:- meta_predicate fast_partially_evaluate_and_load(0,*,0).
:- meta_predicate fast_partially_evaluate_and_load(0,*,0,*).
:- meta_predicate partially_evaluate_and_load(0,*).
% partially_evaluate(Call, ResidualCallToCallSpecializedCode)

partially_evaluate_and_load(Call,Res) :- partially_evaluate(Call,Res,Reused,[]),
   %print(residual_call(Res,Reused)),nl,
   (Reused=true -> true ; load_partially_evaluated_code).

% a version which assumes Call is alreayd sufficiently insantiated to find correct specialized predicate
% MemoCode is only executed if no version found
fast_partially_evaluate_and_load(Call,Res,MemoCode) :-
   fast_partially_evaluate_and_load(Call,Res,MemoCode,[]).
fast_partially_evaluate_and_load(Call,Res,_MemoCode,_AbstractInfos) :-
   % performs no variant check !!
   specialized_predicate(Call,Entry),
   !,
   Res = pe:Entry.
fast_partially_evaluate_and_load(Call,Res,MemoCode,AbstractInfos) :-
   call(MemoCode),
   partially_evaluate(Call,Res,Reused,AbstractInfos),
   %print(residual_call(Res,Reused)),nl,
   (Reused=true -> true ; load_partially_evaluated_code).

:- public try_reuse_specialized_predicate/2.
try_reuse_specialized_predicate(Call,pe:Entry) :-
   % performs no variant check !!
   specialized_predicate(Call,Entry).

partially_evaluate(Call,Res) :- partially_evaluate(Call,Res,_Reused,[]).
partially_evaluate(Call,Res,Reused,_AbstractInfos) :-
   %copy_term(Call,Copy),numbervars(Copy,0,_), % no longer used; expensive for large terms
   term_variables_bag(Call,Vars1),
   specialized_predicate(Call,Entry),
   % Check that call has not been instantiated; i.e., is an instance of call already specialized
   term_variables_bag(Call,Vars2), Vars1==Vars2,
   %\+ \+ (Call = Copy),
   !,
   Res=pe:Entry, Reused=true.
partially_evaluate(Call,pe:Entry,false,AbstractInfos) :-
   generate_entry(Call,Entry),
   assert(specialized_predicate(Call,Entry)),
   %print(partially_evaluating(Call,Entry)),nl,
   print_specialized_clause_declaration(Call,Entry),
   start_specialization(Entry,AbstractInfos),
   ((get_block_declaration(Call,BlockList,BlockDecl),
     call_is_blocked(Call,BlockList,AbstractInfos))
     -> instantiated_block_pattern(Call,OrigCallPat),
        %print(generating_block_declaration(Call,OrigCallPat,Entry,BlockDecl)),nl,
        adapt_block_declaration(BlockDecl,OrigCallPat,Entry,AbstractInfos,NewBlockDecl),
        my_portray_clause(':-'(block(NewBlockDecl))),
        (NewBlockDecl=fail
           -> % block optimized away; should not happen if call_is_blocked succeeds ??
              print_warning('call can never block',Call)
           ; add_specialized_block_declaration(NewBlockDecl)
        )
     ;  true),
   pe_aux(Call,Entry,AbstractInfos).
pe_aux(Call,Entry,AbstractInfos) :-
   unfold_call(Call,AbstractInfos,Code),
   assert_specialized_clause(Entry,Code,AbstractInfos),
   fail.
pe_aux(_Call,Entry,_AbstractInfos) :- stop_specializing(Entry).
  %print(finished_partially_evaluating(_Call,_Entry)),nl.

% generalize a call according to a binding-type description
generalize_call(dynamic,_,_) :- !.
generalize_call(ground_dynamic,X,_V) :-
  ground(X),!. % TO DO: add info to _V that ground
generalize_call(static,X,GX) :- !, GX=X.
generalize_call(atomic,X,GX) :- atomic(X),!, GX=X.
generalize_call(ground,X,GX) :- ground(X),!, GX=X.
generalize_call(list(BT),L,GL) :- !,list_gen_call(L,BT,GL).
generalize_call(nonvar,X,GX) :- !, functor(X,F,N), functor(GX,F,N).
generalize_call(term(F,BT),X,GX) :-  X =.. [F|XArgs], !,
   l_generalize_call(BT,XArgs,GXArgs),
   GX =.. [F|GXArgs].
generalize_call(BT,X,GX) :-
    print_warning('Nonmatching binding type:',BT,value(X)),
    GX=X.

l_generalize_call([],[],GX) :- !, GX=[].
l_generalize_call([BType|BT],[X|TX],[GX|TGX]) :-
     generalize_call(BType,X,GX),
     l_generalize_call(BT,TX,TGX).

list_gen_call([],_,GL) :- !, GL=[].
list_gen_call([H|T],BType,[GH|GT]) :- !, generalize_call(BType,H,GH), list_gen_call(T,BType,GT).
list_gen_call(L,T,GL) :-
    print_warning('nonmatching list binding-type:',list_gen_call(L,T,GL)),
    GL=L.

:- public my_free_of_var/2.
:- use_module(library(terms),[free_of_var/2,cyclic_term/1]).
my_free_of_var(V,T) :-
  (cyclic_term(T) -> print(cyclic_for_var(V)),nl,fail ; free_of_var(V,T)).

% first version of a specific optimizer to remove redundant calls;
% TO DO : generalize based on assertions :- redundant(p(X), free_var(X)).
post_process_specialized_clause_check(Body,Before,After,AbstractInfos,Res,OutInfos) :-
   (post_process_specialized_clause(Body,Before,After,AbstractInfos,Res,OutInfos) -> true
     ; print(post_processing_failed(Body)),nl,
       Res=Body).

%post_process_specialized_clause(A,_,_,_,R) :- !, R=A. % comment back in to disable post_processing
post_process_specialized_clause(X,_,_,Abs,Y,Abs) :- var(X),!,Y=X.
post_process_specialized_clause((A,B),Before,After,AbstractInfos,Res,OutAbsInfo) :- !,
    post_process_specialized_clause_check(A,Before,(B,After),AbstractInfos,PA,AbsInfo1),
    %(cyclic_term(PA) -> print('### CYCLIC L !'),nl,trace, print(PA),nl ; true),
    post_process_specialized_clause_check(B,(PA,Before),After,AbsInfo1,PB,OutAbsInfo),
    %(cyclic_term(PB) -> print('### CYCLIC R !'),nl,trace, print(PB),nl ; true),
    (PA==true -> Res = PB
     ; PB==true -> Res = PA
     ; Res = (PA,PB)).
post_process_specialized_clause(Call,_,_,AbstractInfos,Code,OutAbsInfo) :-
    b_is_operator(Call,Val,Expr),
    check_ground(AbstractInfos,Expr),!,
    Code = 'is'(Val,Expr),
    add_ground_info(AbstractInfos,Val,OutAbsInfo).
post_process_specialized_clause(kernel_mappings:determined(V1, V2, V3, Det),_,_,AbstractInfos,Code,OutInfos) :-
    (check_ground(AbstractInfos,V1)
     -> (check_ground(AbstractInfos,V2) ; check_ground(AbstractInfos,V3))
     ;  check_ground(AbstractInfos,V2) , check_ground(AbstractInfos,V3)
     ), % two of three values known
     !,
     Code = (Det=determined),
    add_ground_info(AbstractInfos,Det,OutInfos).
post_process_specialized_clause(Body,Before,After,AbstractInfos,Res,OutInfos) :-
     OutInfos = AbstractInfos,
     post_process_specialized_clause(Body,Before,After,AbstractInfos,Res).


% version of post_process which does not modify abstract infos
post_process_specialized_clause(Var,_,_,_,R) :- var(Var),!,R=Var.
post_process_specialized_clause(_:get_wait_flag(_, _, _, LWF),Before,After,_AbstractInfos, true) :-
    (nonvar(LWF) ;  var(LWF), free_of_var(LWF,After), free_of_var(LWF,Before)).
post_process_specialized_clause(_:ground_wait_flags(W),Before,After,_AbstractInfos,true) :-
    nonvar(W), W=wfx(A,B,C,_),
    % suboptimal implementation; remove ground_wait_flags if arg fresh variable
    var(A),var(B),var(C),
    free_of_var(A,Before), free_of_var(B,Before), free_of_var(C,Before),
    free_of_var(A,After), free_of_var(B,After), free_of_var(C,After),
    !.
:- if(true).
% preliminary unsafe optimisations: will later check whether args are guaranteed to be ground
%:- nl,nl,print('UNSAFE OPTIMISATIONS ENABLED'),nl,nl,nl.
post_process_specialized_clause(b_interpreter:combine_updates(N, E, H),_,_,_AbstractInfos,Code) :- E==[],!,
   Code = (H=N).
post_process_specialized_clause(Call,_,_,AbstractInfos,Code) :-
    b_comparison(Call,Comp),
    check_ground(AbstractInfos,Comp),!,
    Code = Comp.
post_process_specialized_clause(Call,_,_,AbstractInfos,Code) :-
    b_is_operator(Call,Val,Expr),
    check_ground(AbstractInfos,Expr),!,
    Code = 'is'(Val,Expr).
:- endif.
post_process_specialized_clause(A,_,_,_AbsInfo,A). %  :- print(pp(A,_AbsInfo)),nl.

:- public b_comparison/2.
% check if we can translate a B comparison call to a Prolog comparison:
b_comparison(kernel_objects:less_than(int(X),int(Y)), '<'(X,Y)).
b_comparison(kernel_objects:less_than_equal(int(X),int(Y)), '=<'(X,Y)).
b_comparison(clpfd_interface:clpfd_leq_expr(X, Y), '=<'(X,Y)).
b_comparison(kernel_mappings:not_eq_wf(XX, YY, _, _,_), '\\='(X,Y)) :- nonvar(XX),XX=int(X),YY=int(Y).
b_comparison(_:clpfd_neq_expr(X,Y), '\\='(X,Y)).

% check if we can translate a B interpreter call to a Prolog is/2 construct:
b_is_operator(kernel_mappings:call_determined_integer_function2(int_plus,int(V1),int(V2),int(Val),_,_,_WF,_Span),Val,V1+V2).
b_is_operator(kernel_mappings:call_determined_integer_function2(int_minus,int(V1),int(V2),int(Val),_,_,_WF,_Span),Val,V1+V2).
b_is_operator(kernel_objects:square(int(V1),int(Val),_WF),Val,V1*V1).
b_is_operator(kernel_objects:times(int(V1),int(V2),int(Val)),Val,V1*V2).
b_is_operator(kernel_objects:int_plus(int(V1),int(V2),int(Val)),Val,V1+V2).
b_is_operator(kernel_objects:int_minus(int(V1),int(V2),int(Val)),Val,V1-V2).

% ----------------------------------------------------------------------
:- load_files(library(system), [when(compile_time), imports([environ/2])]).
:- dynamic currently_specializing/1.
is_currently_specializing(pe:X) :- !, currently_specializing(X).
is_currently_specializing(ResCall) :- currently_specializing(ResCall).

% ----------------------------------------------------------------------
:- if(\+ environ(partially_evaluate_compile, true)).
% ASSERT MODE: SPECIALIZED CLAUSES ASSERTED DYNAMICALLY
start_specialization(Entry,_AbstractInfos) :-
    %print_message(start_specialization(Entry)),
    assert(currently_specializing(Entry)),
    assert( ( Entry :- fail ) ), % make an entry for the predicate; in case no clauses generated by unfolding
    retract( ( Entry :- fail) ).
stop_specializing(Entry) :- %print_message(stop_specializing(Entry)),
   (retract(currently_specializing(Entry)) -> true
     ; print_warning('specialization already stopped:',Entry)).
assert_specialized_clause(Head,Body,AbstractInfos) :-
   % print('POST-PROCESSING: '), nl, portray_clause( (Head :- Body )), %trace,
   post_process(Body,Body1),
   post_process_specialized_clause_check(Body1,Head,true,AbstractInfos,NewBody,_),
   assert( (Head :- NewBody ) ),
   my_portray_clause( (Head :- absinfos(AbstractInfos),NewBody ) ).
add_specialized_block_declaration(NewBlockDecl) :-
  prolog:'$block'(pe:NewBlockDecl,compiled).  % SICSTUS hook to add block declarations at runtime; see SPRM 12990
clear_specialized_clauses :-
   (retract(currently_specializing(S)) -> print('*** WARNING: still specializing: '), print(S),nl
     ; true),
   retract(specialized_predicate(_Call,Entry)),
   %print_message(clearing(Call,Entry)),
   retract((Entry :- _Body)),fail.
clear_specialized_clauses.
load_partially_evaluated_code. % already asserted

% check if residual call is failing
failed_residual_call(ResCall) :-
   \+ is_currently_specializing(ResCall), % we have finished specializing
   \+ (clause(ResCall,B), B\=fail) % no non-failing clause exists
   , nl,print(failing(ResCall)),nl.

% check if residual call is defined by a single clause
single_clause(ResCall,Head,Body) :- \+ is_currently_specializing(ResCall),
   copy_term(ResCall,Head),
   clause(Head,Body,Ref),
   \+ (clause(ResCall,_,OtherRef), OtherRef \= Ref). % no other clause exists.
% ----------------------------------------------------------------------
:- else.
% COMPILE MODE: SPECIALIZED CLAUSES WRITTEN TO FILE AND THEN COMPILED
:- dynamic clause_generated/3, multiple_clauses_generated/1.
start_specialization(Entry,AbstractInfos) :-
    print_message(start_specialization(Entry,AbstractInfos)),
    assert(currently_specializing(Entry)).
stop_specializing(Entry) :- %print_message(stop_specializing(Entry)),
   (retract(currently_specializing(Entry)) ->
     (clause_generated(Entry,_,_) -> true
      ; assert_specialized_clause(Entry,fail,[]))
     ; print_warning('specialization already stopped:',Entry)).
assert_specialized_clause(Head,Body,AbstractInfos) :-
   post_process(Body,Body1),
   post_process_specialized_clause_check(Body1,Head,true,AbstractInfos,NewBody,_),
   (clause_generated(Head,_,_) ->
      (multiple_clauses_generated(Head) -> true
         ;  functor(Head,F,N), functor(CH,F,N),
            assert(multiple_clauses_generated(CH)))
      ; functor(Head,F,N), functor(CH,F,N), assert(clause_generated(CH,Head,NewBody))),
   open('pe_cache.pl',append,S),
   portray_clause(S, (Head :- NewBody ) ),
   close(S).
add_specialized_block_declaration(NewBlockDecl) :-
   open('pe_cache.pl',append,S),
   portray_clause(S,':-'(block(NewBlockDecl))),
   close(S).
clear_specialized_clauses :- retractall(specialized_predicate(_Call,_Entry)),
   retractall(clause_generated(_,_,_)),
   retractall(multiple_clauses_generated(_)),
   (retract(currently_specializing(S)) -> print('*** WARNING: still specializing: '), print(S),nl
     ; true),
   print('% Clearing specialized code'),nl,
   open('pe_cache.pl',write,S),
   format(S,'/* PE CACHE FILE */~n',[]), close(S).
load_partially_evaluated_code :- print('% LOADING : pe_cache.pl'),nl,
   compile('pe_cache.pl'),
   %consult('pe_cache.pl'),
   print('% Compiled'),nl.

failed_residual_call(pe:ResCall) :- !, failed_residual_call(ResCall).
failed_residual_call(ResCall) :- \+ is_currently_specializing(ResCall),
   \+ clause_generated(ResCall,_,_), nl,print(failing(ResCall)),nl.

single_clause(pe:ResCall,Head,Body) :- !, single_clause(ResCall,Head,Body).
single_clause(ResCall,Head,Body) :- \+ multiple_clauses_generated(ResCall),
  % TO DO: take pattern into account !
   % note: no need to do copy_term of ResCall
   clause_generated(ResCall,Head,Body).
% ----------------------------------------------------------------------
:- endif.

:- meta_predicate partially_evaluate_fail_detect(0,*).
:- meta_predicate partially_evaluate_fail_detect(0,*,*).
partially_evaluate_fail_detect(Call,Result) :-
   partially_evaluate_fail_detect(Call,Result,[]).
partially_evaluate_fail_detect(Call,Result,AbsInfo) :-
   partially_evaluate(Call,PResCall,_,AbsInfo),
   (PResCall=pe:ResCall -> true ; ResCall=PResCall),
   (failed_residual_call(ResCall)
      -> Result=fail %, print(unfold_fail_detect(ResCall))
     ; (single_clause(ResCall,Head,Body),
        %nl,print(single_clause(ResCall,Head)),nl,
        variant(ResCall,Head), % no instantiation
        \+ call_is_blocked(Call,AbsInfo),
        Body\=(_,_), Body\=if(_,_,_), Body \= (_ -> _ ; _), Body \= (_ -> _)
         )
        % Note: the clause should not contain the cut !
         -> ResCall=Head, Result=Body
     % TO DO : extract binding if not a variant and insert it ?? or even extract MSG from clauses ?
     ; Result = ResCall).
clear_specialized_code :- clear_specialized_clauses,
   reset_pe_pred_count.


:- dynamic pe_pred_count/1.
% count number of specialized predicates generated
pe_pred_count(0).
reset_pe_pred_count :- retractall(pe_pred_count(_)), assert(pe_pred_count(0)).
get_new_pred(P,NP) :- retract(pe_pred_count(C)),
   C1 is C+1, assert(pe_pred_count(C1)),
   number_codes(C,NC), atom_codes(A,NC),
   atom_concat(P,A,NP).

% generate an unfolding call
generate_entry(_Module:Call,NewSpecializedCall) :- !,
    generate_entry(Call,NewSpecializedCall).
generate_entry(Call,NewSpecializedCall) :-
    Call =.. [F|Args],
    term_variables_bag(Args,Vars), % sometimes this seems to generate the variables *not* in order; annoying for indexing
    atom_concat(F,'$spec_',FS),
    get_new_pred(FS,NewF),
    %print(generated_new_entry(Call,Vars,NewF)),nl,
    NewSpecializedCall =.. [NewF|Vars].


:- use_module(library(plunit)).
:- begin_tests(block_pe).
test(pat1) :- instantiated_block_pattern(p(f(_X,_Y),a,Z),R), R==p('?','?',Z).
test(pat2) :- instantiated_block_pattern(p(V,f(X,X),a,V),R), R==p(V,'?','?',V).
:- end_tests(block_pe).

% replace nonvar args by '?'
instantiated_block_pattern(_:Call,Pattern) :- !, instantiated_block_pattern(Call,Pattern).
instantiated_block_pattern(Call,Pattern) :-
    Call =.. [Pred|Args],
    maplist(inst_block_pat_aux,Args,PatArgs),
    Pattern =.. [Pred|PatArgs].
inst_block_pat_aux(Arg,Pat) :- (nonvar(Arg) -> Pat = '?' ; Pat=Arg).

adapt_block_declaration((B1,B2),OrigPat,ResidualCall,AbstractInfos,Result) :- !,
    adapt_block_declaration(B1,OrigPat,ResidualCall,AbstractInfos,RB1),
    adapt_block_declaration(B2,OrigPat,ResidualCall,AbstractInfos,RB2),
    (RB1 = false -> Result = RB2 ; RB2 = false -> Result = RB1
      ; Result = (RB1,RB2)).
adapt_block_declaration(Block,OrigPat,ResidualCall,_AbstractInfos,Result) :-
    copy_term((OrigPat,ResidualCall),(O,R)),
    %print(check(Block,O,R)),nl,
    % TO DO: use ,AbstractInfos
    (Block=O % will instantiate some variables of R by '-'
       -> %print(match(O,R)),nl,
          R =.. [Pred|RArgs],
          maplist(inst_var('?'),RArgs,BRArgs), % replace remaining vars by '?'
          Result =.. [Pred|BRArgs]
        ; Result = false
     ).
inst_var(Val,H,Res) :- (var(H) -> Res=Val ; Res=H).


%% debugging information

:- if(true).
% silent
print_specialized_clause_declaration(_Call,_Entry).
my_portray_clause(_).

:- else.
print_specialized_clause_declaration(Call,Entry) :-
   copy_term((Call,Entry),(C,E)), numbervars((C,E),0,_),
   format('%% ~w :- ~w. %%~n',[C,E]).

my_portray_clause(C) :- portray_clause(C).
:- endif.
