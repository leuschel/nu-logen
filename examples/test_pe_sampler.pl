:- module(test_pe_sampler,[q/1, p/2, test/1]).
%:- ensure_loaded(pe).
:- use_module('../src/pe').

% ------------ test

:- unfold p(_,_).
:- unfold t(_).

q(X) :- p(X,X).
p(a,X) :- s(X).
p(b,X) :- t(X).
p(X,Y) :- number(X), Y is X*X. 
p(c,c).
p(d,e).
s(a). s(b).
t(c).

test(X) :- nl,pe(p(X,X),R), print(p_code(R)), member((test_pe:p(X,X):-B),R),call(B).

:- test(1).
:- \+ test(2).
:- test(X), X==a.
:- test(X), X==c.
:- p(X,X), X==c.
:- p(A,B), A==d, B==e.


:- use_module(library(lists)).

:- unfold ap(_,_).
ap(XX,YY) :- append(X,Y,[1,3,2]), sort(X,XX), sort(Y,YY).

test_ap(X,Y) :- nl,pe(ap(X,Y),R), print(ap_code(R)),nl, member((test_pe:ap(X,Y):-B),R),call(B).

:- test_ap(X,Y), X==[1,2], Y==[3].

:- unfold ex(_,_).
:- execute(ex2(A,_),ground(A)).
ex(A,B) :- A=..[_|AA], length(AA,L), ex2(L,B).
ex2(0,R) :- !,R=null.
ex2(N,N).


test_ex(X,Y) :- nl,pe(ex(_,_),R), print_code(R),nl, member((test_pe:ex(X,Y):-B),R),call(B).

print_code([]).
print_code([H|T]) :- portray_clause(H), print_code(T).

:- test_ex(f(a,b),R), R==2.
:- test_ex(f,R), R==null.

:- unfold ift(_,_).
ift(A,B) :- (A==B -> print(eq(A,B)) ; print(neq(A,B))),nl,
            if(member(A,[a,b,c]), print(mem1(A)) , print(not_mem1(A))),nl,
            (A==B -> print(eq(A,B)) ; print(neq(A,B))),nl,
            (member(A,[a,b,c]) -> print(mem2(A)) ; print(not_mem2(A))),nl.

test_if(X,Y) :- nl,nl,
   pe(ift(X,Y),R), print_code(R), member((test_pe:ift(X,Y):-B),R),call(B).

:- test_if(b,c).
:- test_if(B,c),B==b.
:- ift(B,c),B==b.

:- block bl(-,?), bl(?,-).
bl(X,Y) :- (X=Y -> print(eq_bl(X,Y)),nl,fail ; print(neq_bl(X,Y))),nl.
:- unfold tbl(_,_).
tbl(X,Y) :- if(bl(X,Y),print(neq_tbl(X,Y)),print(eq_tbl(X,Y))),nl.

test_bl(X) :- nl,nl,
   pe(tbl(_XX,b),R), print_code(R), member((test_pe:tbl(X,b):-B),R),call(B).

:- test_bl(a).
:- test_bl(b).
:- test_bl(X), X=a.

:- unfold mymem(_,_). % important to move this before the protect clause !
:- unfold protect(_,_).
protect(X,R) :- (mymem(Y,X) -> print(mem(Y,X)),R=mem(Y) ; print(not_mem(_,X)),R=not_mem), nl.
mymem(X,[X|_]).
mymem(X,[_|T]) :- mymem(X,T).
test_protect(X,R) :- nl,nl,
   partially_evaluate_and_load(protect(X,R),C), call(C), clear_specialized_code.

:- test_protect([a,b,c],R),R==mem(a).
:- test_protect([],R), R==not_mem.

:- unfold myapp(_,_,_).
:- block myapp(-,?,-).
myapp([],X,X).
myapp([H|X],Y,[H|Z]) :- myapp(X,Y,Z).

:- unfold twomyapp(_).
twomyapp(X) :-  (myapp(X,[a],R1) -> myapp(X,[a],R2) ; R1=[],R2=[]),
                  print(res(R1,R2)),nl.
test_memo(X) :- nl,nl,
   partially_evaluate_and_load(twomyapp(X),C), call(C), clear_specialized_code.

:- test_memo([e,f,g]).


:- unfold call_other_module(_).
:- use_module(library(avl)).
call_other_module(X) :- empty_avl(E), avl_store(a,E,1,X).

:- partially_evaluate_and_load(call_other_module(_),C), call(C), clear_specialized_code.

:- unfold test_univ_call(_,_).
:- unfold myop(_).
:- unfold mypred(_,_).
:- execute mypred3(_,_).
test_univ_call(Arg,Y) :- myop(F), X=..[F,Arg,Y], call(X).
myop(mypred).
myop(mypred2).
myop(mypred3).
:- public mypred/2, mypred2/2, mypred3/2.
mypred(0,100).
mypred(1,110).
mypred2(2,120).
mypred3(3,130).
:- partially_evaluate_and_load(test_univ_call(Y,X),C), Y=1,call(C),X==110, 
   partially_evaluate_and_load(test_univ_call(YY,XX),CC), YY=2, call(CC), XX==120,
   partially_evaluate_and_load(test_univ_call(YYY,XXX),CCC), YYY=3, call(CCC), XXX==130,
   clear_specialized_code.

