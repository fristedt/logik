% Verify.
verify(InputFileName) :- 
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,
  valid_proof(Prems, Goal, Proof).

% Proofs can't be empty.
valid_proof(_, _, []) :- !, fail.
% Check if proof is valid.
valid_proof(Prems, Goal, Proof) :-
  last_in_box(Proof, [_, Goal, _]), % Proofs should end with the conclusion.
  valid_proof(Prems, Goal, Proof, []).

% Check if proof is valid.
valid_proof(_, _, [], _) :- !.
% Premise.
valid_proof(Prems, Goal, [[L, Predicate, premise]|T], Previously) :-
  valid_premise(Predicate, Prems), !,
  valid_proof(Prems, Goal, T, [[L, Predicate, premise]|Previously]).
% Assumption.
% You can't end a proof with an assumption.
valid_proof(_, _, [[[_, _, assumption]|[]]|[]], _) :- !, fail.
% Parse box.
valid_proof(Prems, Goal, [[[L, Predicate, assumption]|T1]|T2], Previously) :-
  valid_proof(Prems, Goal, T1, [[L, Predicate, assumption]|Previously]), !,
  valid_proof(Prems, Goal, T2, [[[L, Predicate, assumption]|T1]|Previously]).
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
% Or elimination. 
valid_proof(Prems, Goal, [[L, C, orel(X, Y, U, V, W)]|T], Previously) :-
  lookup_line(X, Previously, or(A, B)),
  first_in_box(Box1, A),
  first_in_box(Box2, B),
  last_in_box(Box1, C),
  last_in_box(Box2, C), !,
  valid_proof(Prems, Goal, T, [[L, C, orel(X, Y, U, V, W)]|Previously]).
% Implication introduction. 
valid_proof(Prems, Goal, [[L, imp(A, B), impint(X, Y)]|T], Previously) :-
  box_is_in_box(Previously, Box), % Make sure that Box isn't in a closed box.
  first_in_box(Box, [_, A, _]), 
  last_in_box(Box, [_, B, _]),
  lookup_line(X, Box, A),
  lookup_line(Y, Box, B), !,
  valid_proof(Prems, Goal, T, [[L, imp(A, B), impint(X, Y)]|Previously]).
% Implication elimination.
valid_proof(Prems, Goal, [[L, B, impel(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, A),
  lookup_line(Y, Previously, imp(A, B)), !,
  valid_proof(Prems, Goal, T, [[L, B, impel(X, Y)]|Previously]).
% Negation introduction.
valid_proof(Prems, Goal, [[L, neg(A), negint(X, Y)]|T], Previously) :-
  first_in_box(Previously, Box),
  lookup_line(X, Box, A),
  lookup_line(Y, Box, cont), !, 
  valid_proof(Prems, Goal, T, [[L, neg(A), negint(X, Y)]|Previously]).
% Negation elimination.
valid_proof(Prems, Goal, [[L, cont, negel(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, A),
  lookup_line(Y, Previously, neg(A)), !,
  valid_proof(Prems, Goal, T, [[L, cont, negel(X, Y)]|Previously]).
% Contradiction elimination.
valid_proof(Prems, Goal, [[L, A, contel(X)]|T], Previously) :-
  lookup_line(X, Previously, cont), !,
  valid_proof(Prems, Goal, T, [[L, A, contel(X)]|Previously]).
% Double negation introduction. 
valid_proof(Prems, Goal, [[L, neg(neg(A)), negnegint(X)]|T], Previously) :-
  lookup_line(X, Previously, A), !,
  valid_proof(Prems, Goal, T, [[L, A, cont]|Previously]).
% Double negation elimination.
valid_proof(Prems, Goal, [[L, Y, negnegel(X)]|T], Previously) :-
  lookup_line(X, Previously, neg(neg(Y))), !,
  valid_proof(Prems, Goal, T, [[L, Y, negnegel(X)]|Previously]).
% MT
valid_proof(Prems, Goal, [[L, neg(B), mt(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, imp(B, A)),
  lookup_line(Y, Previously, neg(A)),
  valid_proof(Prems, Goal, T, [[L, neg(B), mt(X, Y)]|Previously]).
% Proof by contradiction.
valid_proof(Prems, Goal, [[L, A, pbc(X, Y)]|T], Previously) :-
  first_in_box(Previously, Box),
  lookup_line(X, Box, neg(A)),
  lookup_line(Y, Box, cont), !, 
  valid_proof(Prems, Goal, T, [[L, neg(A), negint(X, Y)]|Previously]).
% LEM
valid_proof(Prems, Goal, [[L, or(A, neg(A)), lem]|T], Previously) :-
  !,
  valid_proof(Prems, Goal, T, [[L, or(A, neg(A)), lem]|Previously]).

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

first_in_box([H|_], H).

last_in_box([H|[]], H) :- !.
last_in_box([_|T], H) :- last_in_box(T, H).

box_is_in_box([], _) :- !, fail.
box_is_in_box([Box|_], Box).
box_is_in_box([_|T], Box) :- box_is_in_box(T, Box).

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

