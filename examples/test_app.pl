:- module(test_app,[test/1]).

:- use_module('../src/pe').

:- unfold(myapp(A,_,_),nonvar(A)).
%:- block myapp(-,?,-).
myapp([],X,X).
myapp([H|X],Y,[H|Z]) :- myapp(X,Y,Z).

test(C) :- partially_evaluate_and_load(myapp([a,b,c],_,_),C),
  print(C),nl.
  
  
:- unfold(rev(A,_,_),nonvar(A)).
:- memo(rev(A,B,C),var(B),rev(A,B,C)).
rev([],A,A).
rev([H|T],A,R) :- rev(T,[H|A],R).

:- unfold(body(_,_),true).
body(N,N1) :- N1 is N-1.

:- unfold(while(A,B,_),(nonvar(A),nonvar(B))).
:- memo(while(_,B,C),var(B),while(_,B,C)).
while(N,N,finished).
while(N,M,s(R)) :- N>M, body(N,N1),while(N1,M,R).
