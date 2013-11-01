% p, q, r, s, t.
p.
q.
r.
s.
t.

verify(InputFileName) :- 
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,
  valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
  valid_proof(Prems, Goal, Proof, []).

valid_proof(_, _, [], _).
valid_proof(Prems, Goals, [H|T], Previously) :-
  isValid(H),
  valid_proof(Prems, Goals, T, [H|Previously]).

isValid([_, _, premise]).
isValid([_, _, assumption]).
isValid([_, _, X]) :- isValidProof(X).

neg(X) :-
  not(X).

imp(fail, fail) :- !.
imp(_, true) :- true.
imp(true, Y) :- Y.

and(A, B) :- A, B.

or(A, _) :- A.
or(_, B) :- B.

