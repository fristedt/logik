% Load model, initial state and formula from file.
verify(Input) :-
  see(Input), read(T), read(L), read(S), read(F), seen,
  check(T, L, S, [], F).

% and
check(Transitions, Labels, State, [], and(F1, F2)) :-
  check(Transitions, Labels, State, [], F1),
  check(Transitions, Labels, State, [], F2).

% or
check(Transitions, Labels, State, [], or(F, _)) :-
  check(Transitions, Labels, State, [], F), !.
check(Transitions, Labels, State, [], or(_, F)) :-
  check(Transitions, Labels, State, [], F), !.

% ax
check(Transitions, Labels, State, U, ax(F)) :-
  getList(Transitions, State, Paths),
	checkAllNext(Transitions, Labels, Paths, U, F).

% ex
check(Transitions, Labels, State, U, ex(F)) :-
  % Get all available paths from the given State.
  getList(Transitions, State, States),
  % Find a next state (S1) in the list of states (States) where F holds.
  % Since member S1 is unbound at this point Prolog will iterate over the given
  % list of states (States) until the next predicate is true which then implies
  % that F holds in found next state.
  member(S1, States),
  check(Transitions, Labels, S1, U, F).

% ag
check(_, _, State, U, ag(_)) :-
  % Stop if the current state has been visited before.
  member(State, U).
check(Transitions, Labels, State, U, ag(F)) :-
  % Ensure F hold in the current state (State).
  check(Transitions, Labels, State, [], F),
  % Use the fact that ax(ag(F)) will traverse all next paths and
  % ensure that ag(F) holds in all those paths.
  check(Transitions, Labels, State, [State|U], ax(ag(F))).

% eg
check(_, _, State, U, eg(_)) :-
  % Stop if the current state has been visited before.
  member(State, U), !.
check(Transitions, Labels, State, U, eg(F)) :-
  % Ensure the formula holds in the current state.
  check(Transitions, Labels, State, [], F),
  % Get all paths from the current state.
  getList(Transitions, State, Paths),
  % See ex/5 for further comments.
  member(S1, Paths),
  check(Transitions, Labels, S1, [State|U], eg(F)).

% ef
check(Transitions, Labels, State, U, ef(F)) :-
  % Ensure the current state has not been visited before.
  \+ member(State, U),
  % Ensure the formula holds in the current state.
  check(Transitions, Labels, State, [], F).
check(Transitions, Labels, State, U, ef(F)) :-
  % Ensure the current state has not been visited before.
  \+ member(State, U),
  % Traverse all paths from the current state in order to find a
  % state where F holds.
  check(Transitions, Labels, State, [State|U], ex(ef(F))).

% af
check(Transitions, Labels, State, U, af(F)) :-
  % Ensure the current state has not been visited before.
  \+ member(State, U),
  % Ensure the formula holds in the current state.
  check(Transitions, Labels, State, [], F).
check(Transitions, Labels, State, U, af(F)) :-
  % See ef/5 for furher comments.
  \+ member(State, U),
  check(Transitions, Labels, State, [State|U], ax(af(F))).
 
% neg
check(_, Labels, State, [], neg(F)) :-
  getList(Labels, State, Formulas),
  % Ensure the given formula is not present in the list of formulas that holds
  % in the current state.
  \+ member(F, Formulas).

% arbitrary formula
check(_, Labels, State, [], F) :-
  % Get all formulas that holds in the current state.
  getList(Labels, State, Formulas),
  % Ensure that the given formula is present in the list of formulas that
  % holds in the current state.
  member(F, Formulas).

% Iterate over all given states and ensure the given formula holds in all states.
checkAllNext(_, _, [], _, _).
checkAllNext(T, L, [State|States], U, F) :-
  check(T, L, State, U, F), !,
  checkAllNext(T, L, States, U, F).

% Get the associated list for the given state.
%
% Examples:
%
%   getList([s0, [s1]], s0, P).
%   P = [s1]
%
%   getList([s0, [r]], s0, F).
%   F = [r]
getList([[State, Paths]|_], State, Paths) :- !.
getList([_|T], State, Paths) :- getList(T, State, Paths).
