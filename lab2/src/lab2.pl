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
check(T, L, S, U, ax(X)) :-
  getList(T, S, T1),
	checkAllNext(T,L,T1,U,X).

% EX
check(T, L, S, U, ex(F)) :-
  getList(T, S, States),
  member(State, States),
  check(T, L, State, U, F).

% AG
% Base case, loop found because state S is in list of visited states
% U.
check(_, _, S, U, ag(_)) :-
  member(S, U). 
check(T, L, S, U, ag(F)) :- 
  check(T, L, S, [], F),
  check(T, L, S, [S|U], ax(ag(F))).

% EG
check(_, _, S, U, eg(_)) :-
  memberchk(S, U), !. 
check(T, L, S, U, eg(F)) :- 
  check(T, L, S, [], F),
  check(T, L, S, [S|U], ex(eg(F))).

% EF
check(T, L, S, U, ef(F)) :- 
  \+ memberchk(S, U),
  check(T, L, S, [], F).
check(T, L, S, U, ef(F)) :- 
  \+ memberchk(S, U),
  check(T, L, S, [S|U], ex(ef(F))).

% AF
check(T, L, S, U, af(F)) :- 
  % TODO: Ensure that S is not in U.
  \+ member(S, U),
  check(T, L, S, [], F).
check(T, L, S, U, af(F)) :- 
  \+ member(S, U),
  check(T, L, S, [S|U], ax(af(F))).
 
 % Literals
check(_, L, S, [], neg(X)) :- 
  % \+ check(_, L, S, [], X), !.
  getList(L, S, L1),
  \+ member(X, L1).
check(_, L, S, [], X) :- 
  getList(L, S, L1),
  member(X, L1).

% Find all paths/labeling from given state (S) in AllPathsFromState.
% getList([s0, [s1, s2]], s0, [s1, s2])
getList([[S,L]|_], S, L) :- !.
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

checkAllNext(_, _, [], _, _).
checkAllNext(T, L, [State|States], U, F) :-
  check(T, L, State, U, F), !,
  checkAllNext(T, L, States, U, F).
% checkAXhelp(_,_,[],_,_).
% checkAXhelp(T, L, [F|Rest], U, X) :-
% 	check(T,L,F,U,X), !,
% 	checkAXhelp(T,L,Rest,U,X).

checkAllGlobal(_, _, [], _, _) :- !.
checkAllGlobal(Transitions, Labels, [State|Rest], U, F) :-
  check(Transitions, Labels, State, U, F),
  checkAllGlobal(Transitions, Labels, Rest, [State|U], F).

checkAllFuture(_, _, [], _, _).
checkAllFuture(Transitions, Labels, [State|States], U, af(F)) :-
  check(Transitions, Labels, State, U, af(F)),
  checkAllFuture(Transitions, Labels, States, U, af(F)).

% checkExistsGlobal(_, [H|[]], _, U, _) :- 
%   memberchk(H, U), !, fail. 
% checkExistsGlobal(_, [H|H], _, _, _).
% checkExistsGlobal(Transitions, [H|T], L, U, F) :-
%   check(Transitions, L, H, U, F),
%   checkAllGlobal(Transitions, T, L, [H|U], F).

% filterList([[s0, [s0]], [s1, [s0]]], [[s0, [q]], [s1, [p, r]]], [s0], neg(p), X).
