:- module(builtin_tools, 
        [is_builtin/1,
         executable_builtin/1, 
         is_decidable_builtin/2,
         specialize_builtin/3,
         post_process_builtin/2,
         
         check_ground/2,
         check_nonvar/2,
         add_ground_info/3]).



:- dynamic executable_builtin/1.

executable_builtin(is(_,Expr)) :- 
     ground(Expr).
executable_builtin(arg(Nr,T,_)) :- 
     number(Nr), nonvar(T).
executable_builtin(functor(T,F,N)) :- 
     (nonvar(T) ; atomic(F), number(N)).
executable_builtin('='(_X,_Y)).
%executable_builtin('C'(_X,_Y,_Z)). % old-style DCGs
executable_builtin(true).
executable_builtin(fail).
executable_builtin(false).
executable_builtin(otherwise).
executable_builtin(repeat).
executable_builtin('=..'(X,Y)) :-
	(nonvar(X)) ; (list_ok_for_eqdotdot(Y)).
executable_builtin('<'(X,Y)) :-
	arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin('=<'(X,Y)) :-
	arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin('>'(X,Y)) :-
	arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin('>='(X,Y)) :-
	arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin('@<'(X,Y)) :- '?='(X,Y). % is this sufficient ??
executable_builtin('@=<'(X,Y)) :-'?='(X,Y). % is this sufficient ??
executable_builtin('@>'(X,Y)) :-'?='(X,Y). % is this sufficient ??
executable_builtin('@>='(X,Y)) :-'?='(X,Y). % is this sufficient ??
executable_builtin(nonvar(X)) :-
	nonvar(X).
executable_builtin(var(X)) :-
	nonvar(X).
executable_builtin(ground(X)) :-
	ground(X).
executable_builtin(number(X)) :-
	nonvar(X).
executable_builtin(float(X)) :-
	nonvar(X).
executable_builtin(integer(X)) :-
	nonvar(X).
executable_builtin(atomic(X)) :-
	nonvar(X).
executable_builtin(atom(X)) :-
	nonvar(X).
executable_builtin(call(X)) :-
	nonvar(X),
	executable_builtin(X).
executable_builtin(   dif(X,Y)) :- '?='(X,Y). 
executable_builtin('\\=='(X,Y)) :- '?='(X,Y).
executable_builtin(  '=='(X,Y)) :- '?='(X,Y). 
executable_builtin( '\\='(X,Y)) :- '?='(X,Y). 
executable_builtin('=:='(X,Y)) :-
    arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin('=\\='(X,Y)) :-
    arithmetic_expression(X),arithmetic_expression(Y).
executable_builtin(append(X,_,Y)) :-
    (is_list_skeleton(X) ; is_list_skeleton(Y)).
executable_builtin(sort(X,_)) :-
    ground(X).
executable_builtin(member(_,Y)) :-
    is_list_skeleton(Y).
executable_builtin(nonmember(X,Y)) :- ground(X), ground(Y).
executable_builtin(length(Y)) :-
    is_list_skeleton(Y).
executable_builtin(atom_concat(X,Y,_)) :-
	atom(X), atom(Y).
executable_builtin(atom_codes(A,_)) :- atom(A).
executable_builtin(number_codes(A,_)) :- number(A).
executable_builtin(atom_chars(A,_)) :- atom(A).
executable_builtin(number_chars(A,_)) :- number(A).
executable_builtin(atom_length(A,_)) :- atom(A).


:- if(current_prolog_flag(dialect,sicstus)).
:- if((current_prolog_flag(version_data,sicstus(4,X,_,_,_)),X<3)).
:- use_module(library(terms),[term_variables/2]). % is built-in in SICSTUS 4.3
:- endif.
:- endif.
specialize_builtin(ground(X),Code,AbsInfo) :- !,
    (check_ground(AbsInfo,X) -> Code=true
     ; term_variables(X,V), Code=ground(V)).
specialize_builtin(nonvar(X),Code,AbsInfo) :- !,
    (check_nonvar(AbsInfo,X) -> Code=true
     ; Code=nonvar(X)).
specialize_builtin(var(X),Code,AbsInfo) :- !,
    (check_nonvar(AbsInfo,X) -> Code=fail
     ; Code=var(X)).
specialize_builtin(X,Code,_AbsInfo) :- executable_builtin(X),!,call(X), Code=true.
specialize_builtin(X,X,_AbsInfo). % we cannot specialize; just return call as residual code


post_process_builtin(otherwise,C) :- !, C=true.
post_process_builtin(ground(X),Code) :- !,
  term_variables(X,V), Code=ground(V).
post_process_builtin('=..'(X,Y),Code) :- nonvar(X),!,
   X =.. YY, Code = '='(Y,YY).
post_process_builtin('=..'(X,Y),Code) :- list_ok_for_eqdotdot(Y),!,
   XX =.. Y, Code = '='(X,XX).

% ---------------------------


arithmetic_expression(X) :- ground(X).
 /* will cause error to appear at specialization time
    if not really an arithmetic expression !
    TO DO : improve ; or add try-catch around executing builtin's */

list_ok_for_eqdotdot(L) :-
	nonvar(L),L = [H|T],
	atomic(H),
	is_list_skeleton(T).

is_list_skeleton(X) :- nonvar(X),is_list_skeleton_aux(X).
is_list_skeleton_aux([]).
is_list_skeleton_aux([_H|T]) :- is_list_skeleton(T).

% ----------------------------

% update using  builtin_tools:update.
%
:- public update/0.
update :- clause(executable_builtin(H),_), portray_clause(is_builtin(H)),fail.
update.
is_builtin(number(_)).
is_builtin(_ is _).
is_builtin(arg(_,_,_)).
is_builtin(functor(_,_,_)).
is_builtin(_=_).
is_builtin(true).
is_builtin(fail).
is_builtin(false).
is_builtin(otherwise).
is_builtin(repeat).
is_builtin(_=.._).
is_builtin(_<_).
is_builtin(_=<_).
is_builtin(_>_).
is_builtin(_>=_).
is_builtin(_@<_).
is_builtin(_@=<_).
is_builtin(_@>_).
is_builtin(_@>=_).
is_builtin(nonvar(_)).
is_builtin(var(_)).
is_builtin(ground(_)).
is_builtin(float(_)).
is_builtin(integer(_)).
is_builtin(atomic(_)).
is_builtin(atom(_)).
is_builtin(call(_)).
is_builtin(dif(_,_)).
is_builtin(_\==_).
is_builtin(_==_).
is_builtin(_\=_).
is_builtin(_=:=_).
is_builtin(_=\=_).
is_builtin(append(_,_,_)).
is_builtin(sort(_,_)).
is_builtin(member(_,_)).
is_builtin(nonmember(_,_)).
is_builtin(length(_)).
is_builtin(atom_concat(_,_,_)).
is_builtin(atom_codes(_,_)).
is_builtin(number_codes(_,_)).
is_builtin(atom_chars(_,_)).
is_builtin(number_chars(_,_)).
is_builtin(atom_length(_,_)).

% return true when a built-in can be decided to be true or false, with on other options
% i.e., when is it safe to execute an if-then-else with it as condition


is_decidable_builtin(member(X,L),AbsInfo) :-
   (check_ground(AbsInfo,X),check_ground(AbsInfo,L)  ; is_list_skeleton(L),\+ member(X,L)).
is_decidable_builtin(nonmember(X,L),AbsInfo) :- check_ground(AbsInfo,X), check_ground(AbsInfo,L).
is_decidable_builtin('<'(X,Y),AbsInfo) :- check_ground(AbsInfo,X),check_ground(AbsInfo,Y).
is_decidable_builtin('=<'(X,Y),AbsInfo) :- check_ground(AbsInfo,X),check_ground(AbsInfo,Y).
is_decidable_builtin('>'(X,Y),AbsInfo) :- check_ground(AbsInfo,X),check_ground(AbsInfo,Y).
is_decidable_builtin('>='(X,Y),AbsInfo) :- check_ground(AbsInfo,X),check_ground(AbsInfo,Y).
is_decidable_builtin(ground(X),AbsInfo) :- check_ground(AbsInfo,X).
is_decidable_builtin(var(X),AbsInfo) :- check_nonvar(AbsInfo,X).
is_decidable_builtin(nonvar(X),AbsInfo) :- check_nonvar(AbsInfo,X).
is_decidable_builtin(number(X),AbsInfo) :- check_nonvar(AbsInfo,X).
is_decidable_builtin(atom(X),AbsInfo) :- check_nonvar(AbsInfo,X).
is_decidable_builtin(atomic(X),AbsInfo) :- check_nonvar(AbsInfo,X).
is_decidable_builtin(X,_) :- is_decidable_builtin(X).


is_decidable_builtin(true).
is_decidable_builtin(fail).
is_decidable_builtin(false).
is_decidable_builtin(otherwise).
is_decidable_builtin(repeat).
is_decidable_builtin('='(X,Y)) :- '?='(X,Y).
is_decidable_builtin('=='(X,Y)) :- '?='(X,Y).
is_decidable_builtin('\\='(X,Y)) :- '?='(X,Y).
is_decidable_builtin('\\=='(X,Y)) :- '?='(X,Y).
is_decidable_builtin(dif(X,Y)) :- '?='(X,Y).
is_decidable_builtin('@<'(X,Y)) :- '?='(X,Y).
is_decidable_builtin('@=<'(X,Y)) :- '?='(X,Y).
is_decidable_builtin('@>'(X,Y)) :- '?='(X,Y).
is_decidable_builtin('@>='(X,Y)) :- '?='(X,Y).


% ABSTRACT INFO UTILITIES
% -----------------------
:- use_module(library(lists),[maplist/2]).
:- use_module(library(terms),[contains_var/2]). % term_variables/2 is built-in in SICSTUS 4.3
%check_ground(AbstractInfos,X) :- ground(X),!.
check_ground(AbstractInfos,X) :- var(X),!,
   safe_member(ground/Term,AbstractInfos),
   contains_var(X,Term),!.
check_ground(AbstractInfos,X) :- term_variables(X,TV), maplist(check_ground(AbstractInfos),TV).

safe_member(X,List) :- var(List),!, print('*** not a list arg: '), print(safe_member(X,List)),nl,fail.
safe_member(_X,[]) :- !, fail.
safe_member(X,[H|T]) :- !, (X=H ; safe_member(X,T)).
safe_member(X,List) :-  print('*** not a list arg: '), print(safe_member(X,List)),nl,fail.

check_nonvar(_AbstractInfos,X) :- nonvar(X),!.
check_nonvar(AbstractInfos,X) :- var(X),!,
   safe_member(ground/Term,AbstractInfos),
   contains_var(X,Term),!.
   
% add information that a variable is now ground to Abstract Infos:
add_ground_info(AbsInfo,Var,OutAbsInfo) :-
    (check_ground(AbsInfo,Var) -> OutAbsInfo=AbsInfo
      ; %print(now_ground(Var)),nl,
        OutAbsInfo = [ground/Var|AbsInfo]).
% -----------------------

