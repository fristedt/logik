% Load model, initial state and formula from file.
verify(Input) :-
  see(Input), read(T), read(L), read(S), read(F), seen,
  check(T, L, S, [], F).

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
% (T,L), S |- F
%           U

% To execute: consult(’your_file.pl’). verify(’input.txt’).

% Literals
check(_, L, S, [], X) :- 
  getList(L, S, L1),
  isIn(L1, X), !.
check(_, L, S, [], neg(X)) :- 
  \+ check(_, L, S, [], X), !.

% And
check(T, L, S, [], and(F,G)) :-
  check(T, L, S, [], F),
  check(T, L, S, [], G).

% Or
check(T, L, S, [], or(F,_)) :-
  check(T, L, S, [], F), !.
check(T, L, S, [], or(_,G)) :-
  check(T, L, S, [], G), !.

% AX
check(T, L, S, [], ax(F)) :-
  getList(T, S, T1),
  checkAllNext(T1, L, S, F), !.

% EX
check(T, L, S, [], ex(F)) :-
  getList(T, S, T1),
  checkExistsNext(T1, L, S, F), !.

% AG
% Base case, loop found because state S is in list of visited states
% U.
check(_, _, S, U, _) :-
  memberchk(S, U), !. 
check(T, L, S, U, ag(F)) :- 
  % Make sure that F holds in S.
  check(T, L, S, [], F),
  % Get all states reachable from S.
  getList(T, S, States),
  % For all states s ∈ T1 from state S, check that F holds in s.
  checkAllGlobal(T, States, L, [S|U], ag(F)).

% EG
% EF
% AF

% TODO: Substitute all uses of this with memberchk.
isIn([X|_], X) :- !.
isIn([_|T], X) :- isIn(T, X).

% Find all paths/labeling from given state (S) in AllPathsFromState.
% getList([s0, [s1, s2]], s0, [s1, s2])
getList([[S|[L|_]]|_], S, L) :- !.
getList([_|T], S, L) :- getList(T, S, L).

checkAllNext([], _, _, _).
checkAllNext([H|T], L, S, X) :-
  check([], L, H, [], X),
  checkAllNext(T, L, S, X).

checkExistsNext([H|_], L, _, X) :-
  check([], L, H, [], X), !.
checkExistsNext([_|T], L, S, X) :-
  checkExistsNext(T, L, S, X).

checkAllGlobal(_, [], _, _, _) :- !.
checkAllGlobal(Transitions, [H|T], L, U, F) :-
  check(Transitions, L, H, U, F),
  checkAllGlobal(Transitions, T, L, [H|U], F).
 
