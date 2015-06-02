% Piotr Daszkiewicz 219411

user:runtime_entry(start):-
	grammar(ex1, Grammar),
	debug_grammar(Grammar).

debug_grammar(Grammar) :-
	format("Grammar: ~p\n", [Grammar]),
	print_results_2X(normalized, Grammar),
	print_results_2X(start, Grammar),
	print_results_2X(terminals, Grammar),
	print_results_2X(is_terminal, Grammar),
	print_results_2X(nonterminals, Grammar),
	print_results_2X(nonterminals_wrapped, Grammar),
	print_results_2X(results, Grammar),
	print_results_2X(first_map_keys, Grammar),
	print_results_2X(first_map, Grammar),
	print_results_2X(first, Grammar),
	print_results_2X(cycle_map, Grammar),
	print_results_1X(cycle_exists, Gramar),
	print_results_2X(test_firsts, Grammar),
	print_results_2X(follow, Grammar),
	print_results_2X(select, Grammar).


print_result(Predicate, Result) :-
	write(Predicate), write(' : '), write(Result), write('\n').

print_results_1X(Predicate, FirstParam) :-
	( call(Predicate, FirstParam) ->
		print_result(Predicate, 'SUCCESS')
		% print_more(Predicate, FirstParam)
	;
		print_result(Predicate, 'FAIL')
	).

print_results_2X(Predicate, FirstParam) :-
	( call(Predicate, FirstParam, X) ->
		print_more_2X(Predicate, FirstParam)
	;
		print_result(Predicate, 'FAIL')
	).

print_more_2X(Predicate, FirstParam) :-
	call(Predicate, FirstParam, X),
	print_result(Predicate, X),
	fail ; true.

% grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).
% grammar(ex1, [prod('A', [[a, nt('R')]]), prod('R', [[nt('B')], [nt('C')]]), prod('B', [[b]]), prod('C', [[c]])]).
grammar(ex1, [prod('S', [[nt('A'), a, nt('A'), b], [nt('B'), b, nt('B'), a]]), prod('A', [[]]), prod('B', [[]])]).
% grammar(ex1, [prod('A', [[nt('X'), nt('B'), nt('Y')]]), prod('B', [[nt('C')]]), prod('C', [['c'], [nt('A')]]), prod('X', [[]]), prod('Y', [[]])]).

% normalized(Grammar, NormalizedGrammar).
normalized([], []).
normalized([prod(E, [])|GrammarRest], NormalizedGrammar) :- normalized(GrammarRest, NormalizedGrammar).
normalized([prod(E, [Result|ResultsRest])|GrammarRest], [prod_1(nt(E), Result)|NormalizedGrammarRest]) :- normalized([prod(E, ResultsRest)|GrammarRest], NormalizedGrammarRest).

% start(Grammar, Symbol).
start([prod(E, _)|_], nt(E)).

% terminals(Grammar, Terminals).
% terminals(Grammar, Terminals) :- extract_terminals(Grammar, X), list_to_set(X, Terminals).
terminals(Grammar, Terminals) :-
	normalized(Grammar, NormalizedGrammar),
	extract_terminals(NormalizedGrammar, Terminals).

% extract_terminals(NormalizedGrammar, TerminalsList).
extract_terminals([], []).
extract_terminals([prod_1(E, [])|GrammarRest], Terminals) :- extract_terminals(GrammarRest, Terminals).
extract_terminals([prod_1(E, [Symbol|SymbolsRest])|GrammarRest], Terminals) :-
	( is_nonterminal(Symbol) ->
		extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], Terminals)
	;
		Terminals = [Symbol|TerminalsReduced],
		extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], TerminalsReduced)
	).

% is_terminal(Grammar, Symbol).
is_terminal(Grammar, Symbol) :- terminals(Grammar, Terminals), member(Symbol, Terminals).

% is_nonterminal(Symbol).
is_nonterminal(nt(_)).

% nonterminals(Grammar, Nonterminals).
nonterminals([], []).
nonterminals([prod(E, _)|GrammarRest], [E|NonterminalsRest]) :- nonterminals(GrammarRest, NonterminalsRest).

% nonterminals_wrapped(Grammar, Nonterminals).
nonterminals_wrapped([], []).
nonterminals_wrapped([prod(E, _)|GrammarRest], [nt(E)|NonterminalsRest]) :- nonterminals_wrapped(GrammarRest, NonterminalsRest).

% set_without_epsilon(Set, SetWithoutEpsilon).
set_without_epsilon(Set, SetWithoutEpsilon) :-
	list_remove(Set, epsilon_0, SetWithoutEpsilon).

% produces_epsilon(FirstSet)
produces_epsilon([]).
produces_epsilon(FirstSet) :- member(epsilon_0, FirstSet).

% first(Grammar, First).
first(Grammar, First) :-
	first_map(Grammar, Map),
	normalized(Grammar, NormalizedGrammar),
	first_map_expand(NormalizedGrammar, Map, First).

% first_map_keys(Grammar, Keys).
first_map_keys(Grammar, Keys) :-
	nonterminals_wrapped(Grammar, Keys).

% first_map(Grammar, Map).
first_map(Grammar, Map) :- first_map_keys(Grammar, Keys), map_from_set(Keys, [], Map).

first_map_expand(NormalizedGrammar, Map, MapExpanded) :-
	first_map_expand_step(NormalizedGrammar, Map, NewMap),
	( Map == NewMap ->
		Map = MapExpanded
	;
		first_map_expand(NormalizedGrammar, NewMap, MapExpanded)
	).

first_map_expand_step([], Map, Map).
first_map_expand_step([prod_1(Nonterminal, Result)|GrammarRest], Map, MapExpanded) :-
	% format("Expanding ~p -> ~p\n", [Nonterminal, Result]),
	first_expand_nonterminal(NormalizedGrammar, Nonterminal, Result, Map, NewMap),
	first_map_expand_step(GrammarRest, NewMap, MapExpanded).

first_expand_nonterminal(NormalizedGrammar, Nonterminal, [], Map, MapExpanded) :-
	add_to_map_of_sets(Map, Nonterminal, [epsilon_0], MapExpanded).

first_expand_nonterminal(NormalizedGrammar, Nonterminal, [Symbol|SymbolsRest], Map, MapExpanded) :-
	( is_nonterminal(Symbol) ->
		map_search(Map, Symbol, FirstSet),
		list_remove(FirstSet, epsilon_0, FirstSetWithoutEpsilon),
		add_to_map_of_sets(Map, Nonterminal, FirstSetWithoutEpsilon, NewMap),
		( member(epsilon_0, FirstSet) ->
			first_expand_nonterminal(NormalizedGrammar, Nonterminal, SymbolsRest, NewMap, MapExpanded)
		;
			NewMap = MapExpanded
		)
	;
		add_to_map_of_sets(Map, Nonterminal, [Symbol], MapExpanded)
	).

% first_from_symbols(FirstMap, Symbols, SymbolsFirstSet).
first_from_symbols(FirstMap, [], [epsilon_0]).

first_from_symbols(FirstMap, [Symbol|SymbolsRest], SymbolsFirstSet) :-
	first_from_symbols_2(FirstMap, [Symbol|SymbolsRest], SymbolsFirstSet, []).

first_from_symbols_2(_, [], SymbolsFirstSet, SymbolsFirstSet).

first_from_symbols_2(FirstMap, [Symbol|SymbolsRest], SymbolsFirstSet, Accumulator) :-
	( is_nonterminal(Symbol) ->
		map_search(FirstMap, Symbol, FirstSet),
		( produces_epsilon(FirstSet) ->
			set_without_epsilon(FirstSet, FirstSetWithoutEpsilon),
			union(Accumulator, FirstSetWithoutEpsilon, NewAccumulator),
			first_from_symbols_2(FirstMap, SymbolsRest, SymbolsFirstSet, NewAccumulator)
		;
			union(FirstSet, Accumulator, SymbolsFirstSet)
		)
	;
		union([Symbol], Accumulator, SymbolsFirstSet)
	).

%TODO: remove
% test_firsts
test_firsts(Grammar, Firsts) :-
	results(Grammar, [[H|R]|_]),
	first(Grammar, FirstMap),
	first_from_symbols(FirstMap, R, Firsts).

% follow(Grammar, Follow).
follow(Grammar, Follow) :-
	follow_map(Grammar, Map),
	normalized(Grammar, NormalizedGrammar),
	first(Grammar, First),
	follow_map_expand((Grammar, NormalizedGrammar, First), Map, Follow).


% follow_map(Grammar, Map).
follow_map(Grammar, NewMap) :-
	nonterminals_wrapped(Grammar, Keys),
	map_from_set(Keys, [], Map),
	start(Grammar, StartSymbol),
	add_to_map_of_sets(Map, StartSymbol, [eof_0], NewMap).

% follow_map_expand((Grammar, NormalizedGrammar, First), Map, MapExpanded).
follow_map_expand((Grammar, NormalizedGrammar, First), Map, MapExpanded) :-
	first_map_expand_step(NormalizedGrammar, Map, NewMap),
	( Map == NewMap ->
		Map = MapExpanded
	;
		follow_map_expand((Grammar, NormalizedGrammar, First), NewMap, MapExpanded)
	).

follow_map_expand_step((Grammar, [], First), Map, Map).

follow_map_expand_step((Grammar, [prod_1(Nonterminal, Result)|GrammarRest], First), Map, MapExpanded) :-
	% format("Expanding ~p -> ~p\n", [Nonterminal, Result]),
	follow_expand_nonterminal((Grammar, NormalizedGrammar, First), Nonterminal, Result, Map, NewMap),
	follow_map_expand_step((Grammar, GrammarRest, First), NewMap, MapExpanded).

follow_expand_nonterminal((Grammar, NormalizedGrammar, First), Nonterminal, [], Map, Map).

follow_expand_nonterminal((Grammar, NormalizedGrammar, First), Nonterminal, [Symbol|SymbolsRest], Map, MapExpanded) :-
	% format("Expanding ~p -> ~p\n", [Map, Symbol]),
	( is_nonterminal(Symbol) ->
		first_from_symbols(First, SymbolsRest, SymbolsFirstSet),
		set_without_epsilon(SymbolsFirstSet, SymbolsFirstSetWithoutEpsilon),
		add_to_map_of_sets(Map, Symbol, SymbolsFirstSetWithoutEpsilon, NewMap),
		( member(epsilon_0, SymbolsFirstSet) ->
			map_search(Map, Nonterminal, NonterminalFollow),
			add_to_map_of_sets(NewMap, Symbol, NonterminalFollow, NewMap_2)
		;
			NewMap_2 = NewMap
		),
		follow_expand_nonterminal((Grammar, NormalizedGrammar, First), Nonterminal, SymbolsRest, NewMap_2, MapExpanded)
	;
		follow_expand_nonterminal((Grammar, NormalizedGrammar, First), Nonterminal, SymbolsRest, Map, MapExpanded)
	).


% select(Grammar, Select).
select(Grammar, Select) :-
	normalized(Grammar, NormalizedGrammar),
	first(Grammar, First),
	follow(Grammar, Follow),
	select_list((NormalizedGrammar, First, Follow), Select).

% select_list((NormalizedGrammar, First, Follow), Select)
select_list(([], First, Follow), []).

select_list(([prod_1(Nonterminal, Result)|GrammarRest], First, Follow), [ProductionSelect|SelectRest]) :-
	select_from_production((First, Follow), prod_1(Nonterminal, Result), ProductionSelect),
	select_list((GrammarRest, First, Follow), SelectRest).

% select_from_production((First, Follow), prod_1(Nonterminal, Result), [jajeczko]).

select_from_production((First, Follow), prod_1(Nonterminal, Result), ProductionSelect) :-
	% format("select_from_production ~p -> ~p\n", [Nonterminal, Result]),
	first_from_symbols(First, Result, ResultFirstSet),
	( member(epsilon_0, ResultFirstSet) ->
		set_without_epsilon(ResultFirstSet, ResultFirstSetWithoutEpsilon),
		map_search(Follow, Nonterminal, NonterminalFollowSet),
		union(ResultFirstSetWithoutEpsilon, NonterminalFollowSet, ProductionSelect)
	;
		ProductionSelect = ResultFirstSet
	).

% results(Grammar, Results).
results(Grammar, Results) :- results(Grammar, Results, []).

results([], Results, Results).
results([prod(Nonterminal, Result)|GrammarRest], Results, Accumulator) :-
	union(Accumulator, Result, AccumulatorExpanded),
	results(GrammarRest, Results, AccumulatorExpanded).

% TODO
% jestCykl(Grammar)

% cycle_exists(Grammar)
cycle_exists(Grammar) :-
	cycle_map(Grammar, Map),
	self_cycle_exists(Map).

% cycle_map(Grammar, CycleMap).
cycle_map(Grammar, CycleMap2) :-
	nonterminals_wrapped(Grammar, Keys),
	map_from_set(Keys, [], Map),
	normalized(Grammar, NormalizedGrammar),
	first(Grammar, First),
	cycle_map_fill((NormalizedGrammar, First), Map, CycleMap),
	cycle_closure(CycleMap, CycleMap2).

cycle_map_fill(([], First), Map, Map).

cycle_map_fill(([prod_1(Nonterminal, Result)|GrammarRest], First), Map, MapFilled) :-
	cycle_map_for_production(First, Nonterminal, [], Result, Map, NewMap),
	cycle_map_fill((GrammarRest, First), NewMap, MapFilled).

% cycle_map_for_production(First, Nonterminal, ResultPrefix, ResultRest, Map, NewMap)
cycle_map_for_production(First, Nonterminal, _, [], Map, Map).

cycle_map_for_production(First, Nonterminal, SymbolsPrefix, [Symbol|SymbolsRest], Map, NewMap) :-
	% format("T1ying ~p -> ~p ~p ~p\n", [Nonterminal, SymbolsPrefix, Symbol, SymbolsRest]),
	first_from_symbols(First, SymbolsPrefix, SymbolsPrefixFirstSet),
	first_from_symbols(First, SymbolsRest, SymbolsRestFirstSet),
	( is_nonterminal(Symbol) ->
		( produces_epsilon(SymbolsPrefixFirstSet), produces_epsilon(SymbolsRestFirstSet) ->
			add_to_map_of_sets(Map, Nonterminal, [Symbol], MapExpanded)
		;
			MapExpanded = Map
		),
		append(SymbolsPrefix, [Symbol], NewSymbolsPrefix),
		cycle_map_for_production(First, Nonterminal, NewSymbolsPrefix, SymbolsRest, MapExpanded, NewMap)
	;
		Map = NewMap
	).

% cycle_closure(Map, MapExpanded)
cycle_closure(Map, MapExpanded) :-
	cycle_closure_step(Map, Map, NewMap),
	( Map == NewMap ->
		Map = MapExpanded
	;
		cycle_closure(NewMap, MapExpanded)
	).

cycle_closure_step([], Map, Map).
cycle_closure_step([key_value(Nonterminal, [])|MapRest], Map, NewMap) :-
	cycle_closure_step(MapRest, Map, NewMap).

cycle_closure_step([key_value(Nonterminal, [Target|TargetsRest])|MapRest], Map, NewMap) :-
	map_search(Map, Target, TargetTargets),
	add_to_map_of_sets(Map, Nonterminal, TargetTargets, MapExpanded),
	cycle_closure_step([key_value(Nonterminal, TargetsRest)|MapRest], MapExpanded, NewMap).

% self_cycle_exists(Map).
self_cycle_exists([key_value(Source, Targets)|MapRest]) :-
	member(Source, Targets).

self_cycle_exists([_|MapRest]) :-
	self_cycle_exists(MapRest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_remove([], _, []).
list_remove([X|A], X, B) :- list_remove(A, X, B). %TODO: cut here and remove not_eq check?
list_remove([Y|A], X, [Y|B]) :- X \== Y, list_remove(A, X, B).

not_member(E, []).
not_member(E, [X|L]) :- E \== X, not_member(E, L).

union([], S, S).
union([E|A], B, [E|C]) :- list_remove(B, E, B1), union(A, B1, C).

intersection([], _, []).
intersection([E|A], B, [E|C]) :- member(E, B), intersection(A, B, C).
intersection([E|A], B, C) :- not_member(E, B), intersection(A, B, C).


% map_search(Map, Key, Value).
map_search([key_value(Key, Value)|_], Key, Value).
map_search([_|MapRest], Key, Value) :- map_search(MapRest, Key, Value).

% map_insert(Map, Key, Value, NewMap).
map_insert(Map, Key, Value, [key_value(Key, Value)|Map]).

% map_delete(Map, Key, NewMap).
map_delete([], _, []).
map_delete([key_value(Key, _)|MapRest], Key, MapRest).
map_delete([key_value(DifferentKey, Value)|MapRest], Key, [key_value(DifferentKey, Value)|NewMapRest]) :- Key \== DifferentKey, map_delete(MapRest, Key, NewMapRest).

% map_replace(Map, Key, Value, NewMap).
map_replace([key_value(Key, _)|MapRest], Key, Value, [key_value(Key, Value)|MapRest]).
map_replace([key_value(DifferentKey, DifferentValue)|MapRest], Key, Value, [key_value(DifferentKey, DifferentValue)|NewMapRest]) :-
	Key \== DifferentKey,
	map_replace(MapRest, Key, Value, NewMapRest).

% map_from_set(Set, DefaultValue, ?Map).
map_from_set([], _, []).
map_from_set([E|SetRest], DefaultValue, Map) :- map_insert(MapRest, E, DefaultValue, Map), map_from_set(SetRest, DefaultValue, MapRest).

% add_to_map_of_sets(Map, Key, Values, NewMap)
add_to_map_of_sets(Map, Key, Values, NewMap) :-
	% format("Map(~p) <- ~p\n", [Key, Values]),
	map_search(Map, Key, Set),
	union(Set, Values, ExpandedSet),
	map_replace(Map, Key, ExpandedSet, NewMap).
