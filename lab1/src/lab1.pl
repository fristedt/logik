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
% Previously is a list storing previous lines, used to check which lines are 
% allowed to make a reference to. 
valid_proof(Prems, Goal, [[L, Predicate, premise]|T], Previously) :-
  valid_premise(Predicate, Prems), !,
  valid_proof(Prems, Goal, T, [[L, Predicate, premise]|Previously]).
% Assumption.
% You can't end a proof with an assumption.
valid_proof(_, _, [[[_, _, assumption]|[]]|[]], _) :- !, fail.
% Parse box.
% Box (T1) in a box (T2). 
% Add lines from T1 to Previously until box closes, T1 is allowed to use all
% previous lines. When T1 closes it is added to Previously as a box, which
% makes T2 and the rest of the program unable to access the lines in it
% without the use of the predicates first_in_box and last_in_box.
valid_proof(Prems, Goal, [[[L, Predicate, assumption]|T1]|T2], Previously) :-
  valid_proof(Prems, Goal, T1, [[L, Predicate, assumption]|Previously]), !,
  valid_proof(Prems, Goal, T2, [[[L, Predicate, assumption]|T1]|Previously]).
% Copy.
valid_proof(Prems, Goal, [[L, Y, copy(X)]|T], Previously) :-
  lookup_line(X, Previously, Y), !,
  valid_proof(Prems, Goal, T, [[L, Y, copy(X)]|Previously]).
% And introduction.
% If and introduction is used, look up the lines that are referenced to
% and see if an and-operation is allowed.
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
% X is an or statement.
% Y is line number of first statement in first box.
% U is line number of last statement in first box.
% V is line number of first statement in second box.
% W is line number of last statement in second box.
valid_proof(Prems, Goal, [[L, C, orel(X, Y, U, V, W)]|T], Previously) :-
  lookup_line(X, Previously, or(A, B)),
  first_in_box(Box1, [Y, A, _]),
  first_in_box(Box2, [V, B, _]),
  last_in_box(Box1, [U, C, _]),
  last_in_box(Box2, [W, C, _]), !,
  valid_proof(Prems, Goal, T, [[L, C, orel(X, Y, U, V, W)]|Previously]).
% Implication introduction. 
% Checks if the box that is being referenced to is in the scope of the current
% box. Checks if A is the first predicate in a box and if B is the last
% predicate in the same box. Checks if the line numbers of A and B matches 
% X and Y.
valid_proof(Prems, Goal, [[L, imp(A, B), impint(X, Y)]|T], Previously) :-
  box_is_in_box(Previously, Box), % Make sure that Box isn't in a closed box.
  first_in_box(Box, [X, A, _]), 
  last_in_box(Box, [Y, B, _]), !,
  valid_proof(Prems, Goal, T, [[L, imp(A, B), impint(X, Y)]|Previously]).
% Implication elimination.
% Look up the lines being referenced to and check if the predicate on line X
% implies the predicate on line Y. It is assumed that the predicate on line X is true since it
% is in Previously, which can only happen if it is true.
valid_proof(Prems, Goal, [[L, B, impel(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, A),
  lookup_line(Y, Previously, imp(A, B)), !,
  valid_proof(Prems, Goal, T, [[L, B, impel(X, Y)]|Previously]).
% Negation introduction.
% Assumes the predicate on line X and arrives at arbitrary contradiction.
% Returns the negation of the assumption.
valid_proof(Prems, Goal, [[L, neg(A), negint(X, Y)]|T], Previously) :-
  first_in_box(Previously, Box),
  lookup_line(X, Box, A),
  lookup_line(Y, Box, cont), !, 
  valid_proof(Prems, Goal, T, [[L, neg(A), negint(X, Y)]|Previously]).
% Negation elimination.
% Assumes something on line X is true and arrives at a contradiction on line Y.
% Returns contradiction.
valid_proof(Prems, Goal, [[L, cont, negel(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, A),
  lookup_line(Y, Previously, neg(A)), !,
  valid_proof(Prems, Goal, T, [[L, cont, negel(X, Y)]|Previously]).
% Contradiction elimination.
% Checks if the predicate on line X is a contradiction.
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
% Ensures that B implies A and negation of A is present.
valid_proof(Prems, Goal, [[L, neg(B), mt(X, Y)]|T], Previously) :-
  lookup_line(X, Previously, imp(B, A)),
  lookup_line(Y, Previously, neg(A)),
  valid_proof(Prems, Goal, T, [[L, neg(B), mt(X, Y)]|Previously]).
% Proof by contradiction.
% Assume negation of A and arrive at a contradiction. Returns A.
valid_proof(Prems, Goal, [[L, A, pbc(X, Y)]|T], Previously) :-
  first_in_box(Previously, Box),
  lookup_line(X, Box, neg(A)),
  lookup_line(Y, Box, cont), !, 
  valid_proof(Prems, Goal, T, [[L, neg(A), negint(X, Y)]|Previously]).
% LEM
valid_proof(Prems, Goal, [[L, or(A, neg(A)), lem]|T], Previously) :-
  !,
  valid_proof(Prems, Goal, T, [[L, or(A, neg(A)), lem]|Previously]).

% Check if premise is valid.
valid_premise(_, []) :- fail.
valid_premise(Prem, [Prem|_]).
valid_premise(Prem, [_|T]) :-
  valid_premise(Prem, T).

% Get the content of the line with the given Index in the given list.
%   lookup_line(1, [[1, 2, _]], Line). => Line = 2
lookup_line(_, [], _) :- fail.
lookup_line(Index, [[Index, Line, _]|_], Line).
lookup_line(Index, [_|T], Match) :- lookup_line(Index, T, Match).

% Get the first element in the given list.
%   first_in_box([1, 2, 3], H). => H = 1
first_in_box([H|_], H).

% Get the last element in the given list.
%   last_in_box([1, 2, 3], L). => L = 3
last_in_box([H|[]], H) :- !.
last_in_box([_|T], H) :- last_in_box(T, H).

% Determine if the given Box in in the list.
%   box_is_in_box([1, 2, 3], 2). => true
box_is_in_box([], _) :- !, fail.
box_is_in_box([Box|_], Box).
box_is_in_box([_|T], Box) :- box_is_in_box(T, Box).

% Return !X.
neg(X) :- not(X).

% Check if an implication holds.
imp(fail, fail) :- !.
imp(_, true) :- true.
imp(true, Y) :- Y.

% Logical and.
and(A, B) :- A, B.

% Logical or.
or(A, _) :- A.
or(_, B) :- B.
