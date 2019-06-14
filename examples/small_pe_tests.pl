:- module(small_pe_tests,[mymem/2, test/2, test3/2]).

:- use_module('../src/pe').

:- unfold mymem(_,_). % important to move this before the protect clause !
:- unfold protect(_,_).
protect(X,R) :- (mymem(Y,X) -> print(mem(Y,X)),R=mem(Y) ; print(not_mem(_,X)),R=not_mem), nl.
mymem(X,[X|_]).
mymem(X,[_|T]) :- mymem(X,T).


:- unfold tom(_,_).
:- use_module(library(timeout),[time_out/3]).
tom(X,R) :- time_out(mymem(X,R),10,TRes),
               (TRes==time_out -> print(time_out),nl ; true).
test3(X,R) :- nl,nl,
   clear_specialized_code,
   partially_evaluate_and_load(tom(X,R),C), call(C).

:- unfold bmem(_,_).
:- unfold btest(_,_).
:- forward_block(bmem(_,_)).
btest(X,L) :- bmem(X,L).
:- block bmem(?,-), bmem(-,?).
bmem(X,[X|_]).
bmem(X,[_|T]) :- bmem(X,T).

:- unfold(revacc(A,_),nonvar(A)).
:- memo(rev3(A,_,_),nonvar(A),rev3(A,_,_)).
revacc(X,Y) :- rev3(X,[],Y).
rev3([],A,A).
rev3([H|T],A,R) :- rev3(T,[H|A],R).

:- unfold(revw(A,_,_),nonvar(A)).
revw([],A,A).
revw([H|T],A,R) :- when(nonvar(T),revw(T,[H|A],R)).

:- unfold(p(X,_),nonvar(X)).
p(X,R) :- number(X),X>0,!,R=pos.
p(X,R) :- number(X),X<0,!,R=neg.
p(X,R) :- atomic(X),!,R=at.
p(f(X),R) :- atomic(X),!,R=fat.
p(f(_X),R) :- !,R=fvar.
p(s(X,Y),r(R,S)) :- p(X,R), p(Y,S).
 
:- use_module(library(plunit)).
:- begin_tests(pe).

test(simple_mymem1) :- R=[a,b,c],
   partially_evaluate_and_load(mymem(X,R),C),
   call(C),X==c.
test(simple_mymem2,[all(X==[a,b,c,a,d,e,f])]) :- R=[a,b,c,a,d,e,f],
   partially_evaluate_and_load(mymem(X,R),C),
   call(C).
test(simple_mymem4,[fail]) :- R=[a,b,c,a,d,e,f], 
   partially_evaluate_and_load(mymem(X,R),C), X=g,
   call(C).
test(simple_mymem5,[fail]) :- R=[a,b,c,a,d,e,f],  X=g,
   partially_evaluate_and_load(mymem(X,R),C),
   call(C).
test(simple_mymem6,[fail]) :- R=[], 
   partially_evaluate_and_load(mymem(_X,R),C),
   call(C).

test(protect1) :-
   clear_specialized_code,
   partially_evaluate_and_load(protect([a,b,c],R),C), 
   call(C),R=mem(a).
test(protect_fail,[fail]) :-
   partially_evaluate_and_load(protect([a,b,c],R),C), 
   call(C),R=mem(b).
   
test(block_member1) :-  R=[a,b,c],
   partially_evaluate_and_load(btest(b,R),C),
   call(C).
test(block_member2) :-  R=[a|T],
   partially_evaluate_and_load(btest(b,R),C),
   T = [b,c],
   call(C).
test(block_member3) :-  R=[a|T],
   partially_evaluate_and_load(btest(b,R),C),
   call(C), var(T), % check that block declaration active
   T = [b,c].
test(block_member4,[true(var(T4))]) :-  R=[a|T],
   partially_evaluate_and_load(btest(b,R),C),
   call(C), var(T), % check that block declaration active
   T = [c,c|T2], var(T2), % check that block declaration active
   T2 = [d,e|T3], var(T3), % check that block declaration active
   T3 = [b|T4].
test(block_member5,[fail]) :-  R=[a|T],
   partially_evaluate_and_load(btest(b,R),C),
   call(C), var(T), % check that block declaration active
   T = [c,d].
test(revacc1) :- partially_evaluate_and_load(revacc([a,b,c|T],R),C),
   T=[d,e], call(C), R=[e,d,c,b,a].
test(revaccw1) :- partially_evaluate_and_load(revw([a,b,c|T],[],R),C),
   T=[d,e], call(C), R=[e,d,c,b,a].

test(cut1) :- partially_evaluate_and_load(p(s(1,s(-1,s(c,R))),Res),C),
   R=22, call(C), Res=r(pos,r(neg,r(at,pos))).
test(cut2) :- partially_evaluate_and_load(p(s(f(1),f(_)),Res),C),
   call(C), Res=r(fat,fvar).
   
test(warnings,[fail]) :- warnings_occured.
:- end_tests(pe).

%:- run_tests.
