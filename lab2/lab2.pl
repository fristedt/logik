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
  memberchk(X, L1), !.
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
check(_, _, S, U, _) :-
  memberchk(S, U), !. 
check(T, L, S, U, eg(F)) :- 
  % Make sure that F holds in S.
  check(T, L, S, [], F),
  % Ensure that X is reachable from S.
  % getList(T, S, T1),
  % memberchk(X, T1),
  check(T, L, _, [S|U], eg(F)).

% EF
check(T, L, S, U, ef(F)) :- 
  % \+ memberchk(S, U),
  check(T, L, S, [], F).
check(T, L, S, U, ef(F)) :- 
  % \+ memberchk(S, U),
  check(T, L, _, [S|U], ef(F)).

% AF
check(T, L, S, U, af(F)) :- 
  % \+ memberchk(S, U),
  check(T, L, S, [], F).
check(T, L, S, U, af(F)) :- 
  % Make sure that F holds in S.
  check(T, L, S, [], F),
  % Get all states reachable from S.
  getList(T, S, States),
  % For all states s ∈ T1 from state S, check that F holds in s.
  checkAllFuture(T, States, L, [S|U], af(F)).

% Find all paths/labeling from given state (S) in AllPathsFromState.
% getList([s0, [s1, s2]], s0, [s1, s2])
getList([[S|[L|_]]|_], S, L) :- !.
getList([_|T], S, L) :- getList(T, S, L).

done([]) :- !.
done([_|T]) :- done(T).

filterList(_, _, [], _, T) :- 
  done(T), !.
filterList(T, L, [S|Tail], F, [S|T1]) :-
  % getList(L, S, L1),
  % memberchk(F, L1),
  check(T, L, S, [], F),
  filterList(T, L, Tail, F, [S|T1]), !.
filterList(T, L, [_|Tail], F, T1) :-
  filterList(T, L, Tail, F, T1), !.

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
 
% checkExistsGlobal(_, [H|[]], _, U, _) :- 
%   memberchk(H, U), !, fail. 
% checkExistsGlobal(_, [H|H], _, _, _).
% checkExistsGlobal(Transitions, [H|T], L, U, F) :-
%   check(Transitions, L, H, U, F),
%   checkAllGlobal(Transitions, T, L, [H|U], F).

% filterList([[s0, [s0]], [s1, [s0]]], [[s0, [q]], [s1, [p, r]]], [s0], neg(p), X).
