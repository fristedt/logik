% Verify.
verify(InputFileName) :- 
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,
  valid_proof(Prems, Goal, Proof).

% Check if proof is valid.
valid_proof(Prems, Goal, Proof) :-
  valid_proof(Prems, Goal, Proof, []).

% Check if proof is valid.
valid_proof(_, _, [], _) :- !.
valid_proof(Prems, Goals, [H|T], Previously) :-
  valid_line(H, Prems), !,
  valid_proof(Prems, Goals, T, [H|Previously]).

% Check if line is valid.
valid_line([_, P, premise], Prems) :- 
  valid_premise(P, Prems).
valid_line([_, _, assumption], _).
valid_line([_, _, X], _) :- valid_proofilicous(X).

% Check if premise is valid.
valid_premise(_, []) :- fail.
valid_premise(Prems, [Prems|T]).
valid_premise(Prems, [_|T]) :-
  valid_premise(Prems, T).

lookup_line(Index, []) :- fail.
lookup_line(Index, [[Index, Line, _]|T]) :- Line.
lookup_line(Index, [_|T]) :- lookup_line(Index, T).

% Return !X.
neg(X) :-
  not(X).

% Check if an implication holds.
imp(fail, fail) :- !.
imp(_, true) :- true.
imp(true, Y) :- Y.

% Logical and.
and(A, B) :- A, B.

% Logical or.
or(A, _) :- A.
or(_, B) :- B.

