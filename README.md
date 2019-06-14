# nu-logen
New version of the logen partial evaluation system for Prolog

A partial evaluator implemented using term expansion
- the original program is copied unmodified, interspersed with discontiguous directives
- and unfolder clauses in the style of Logen (see Theory and Practice of Logic Programming 4(1):pp. 139-191.)

A difference with Logen is that the term expander works directly on the source program:
-  the goal is to only selectively annotate certain points of the source program.

Annotations are:
  - mark predicates to be unfolded with
     :- unfold p(_,...).
  - mark predicates to be fully executed with
     :- execute p(_,...).
  - mark predicates to be fully executed upon a condition with:
     :- execute(p(_,...),Condition).

Commands:
  - clear specialized code with clear_specialized_code
  - specialize a predicate with partially_evaluate(Pred,R)
      (R is the residual call to be used to call the specialized code)

TO DO:
  - proper module treatment [partially done]
  - asserting and calling specialized clauses [partially done]
  - generate memoization points to avoid backpropagation and clause duplication
  - introduce memo annotation and treatment if necessary