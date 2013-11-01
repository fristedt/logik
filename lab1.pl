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
% Premise.
valid_proof(Prems, Goal, [[L, Predicate, premise]|T], Previously) :-
  is_premise(Previously),
  valid_premise(Predicate, Prems), !,
  valid_proof(Prems, Goal, T, [[L, Predicate, premise]|Previously]).
% Copy.
valid_proof(Prems, Goal, [[L, Y, copy(X)]|T], Previously) :-
  lookup_line(X, Previously, Y), !,
  valid_proof(Prems, Goal, T, [[L, Y, copy(X)]|Previously]).
% And introduction.
valid_proof(Prems, Goal, [[L, and(A, B), andint(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, A),
  lookup_line(Y, Previously, B), !,
  valid_proof(Prems, Goal, T, [[L, and(A, B), andint(X, Y)]|Previously]).
% And elimination 1.
valid_proof(Prems, Goal, [[L, Y, andel1(X)]|T], Previously) :-
  lookup_line(X, Previously, and(Y, _)), !,
  valid_proof(Prems, Goal, T, [[L, Y, andel1(X)]|Previously]).
% And elimination 2.
valid_proof(Prems, Goal, [[L, Y, andel2(X)]|T], Previously) :-
  lookup_line(X, Previously, and(_, Y)), !,
  valid_proof(Prems, Goal, T, [[L, Y, andel2(X)]|Previously]).
% Or introduction 1.
valid_proof(Prems, Goal, [[L, or(Y, Z), orint1(X)]|T], Previously) :-
  lookup_line(X, Previously, Y), !,
  valid_proof(Prems, Goal, T, [[L, or(Y, Z), orint1(X)]|Previously]).
% Or introduction 2.
valid_proof(Prems, Goal, [[L, or(Z, Y), orint2(X)]|T], Previously) :-
  lookup_line(X, Previously, Y), !,
  valid_proof(Prems, Goal, T, [[L, or(Z, Y), orint2(X)]|Previously]).
% Double negation elimination.
valid_proof(Prems, Goal, [[L, neg(neg(Y)), negnegel(X)]|T], Previously) :-
  lookup_line(X, Previously, Y), !,
  valid_proof(Prems, Goal, T, [[L, neg(neg(Y)), negnegel(X)]|Previously]).
% MT
valid_proof(Prems, Goal, [[L, neg(B), mt(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, imp(B, A)),
  lookup_line(Y, Previously, neg(A)),
  valid_proof(Prems, Goal, T, [[L, neg(B), mt(X, Y)]|Previously]).
% LEM
valid_proof(Prems, Goal, [[L, or(A, neg(A)), lem]|T], Previously) :-
  !,
  valid_proof(Prems, Goal, T, [[L, or(A, neg(A)), lem]|Previously]).

% 2. p -> neg(p) A
% 3. p           Z
% 4. neg(p)      B
% Implication elimination.
valid_proof(Prems, Goal, [[L, B, impel(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, Z),
  lookup_line(Y, Previously, imp(Z, B)), !,
  valid_proof(Prems, Goal, T, [[L, B, impel(X, Y)]|Previously]).

% valid_proof(Prems, Goal, [[L, Predicate, assumption]|T], Previously) :-
%   valid_proof(Prems, Goal, T, [[L, Predicate, assumption]|Previously]).

% Check if line is valid.
valid_line([_, P, premise], Prems) :- 
  valid_premise(P, Prems).
valid_line([_, _, assumption], _).
valid_line([_, _, X], _) :- valid_proofilicous(X).

% Make sure that the premise isn't in the middle of our proof or anything crazy.
is_premise([]).
is_premise([[_, _, premise]|T]) :- is_premise(T).

% Check if premise is valid.
valid_premise(_, []) :- fail.
valid_premise(Prem, [Prem|_]).
valid_premise(Prem, [_|T]) :-
  valid_premise(Prem, T).

lookup_line(_, [], _) :- fail.
lookup_line(Index, [[Index, Line, _]|_], Line).
lookup_line(Index, [_|T], Match) :- lookup_line(Index, T, Match).

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

