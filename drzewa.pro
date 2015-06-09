% Piotr Daszkiewicz 219411

user:runtime_entry(start):-
	grammar(ex23, Grammar),
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
	print_results_1X(cycle_exists, Grammar),
	print_results_2X(test_firsts, Grammar),
	print_results_2X(follow, Grammar),
	print_results_2X(select, Grammar),
	print_results_1X(direct_left_recursion_exists, Grammar),
	print_results_2X(direct_left_recursion_remove, Grammar),
	print_results_1X(is_LL1, Grammar).


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
	( call(Predicate, FirstParam, _) ->
		print_more_2X(Predicate, FirstParam)
	;
		print_result(Predicate, 'FAIL')
	).

print_more_2X(Predicate, FirstParam) :-
	call(Predicate, FirstParam, X),
	print_result(Predicate, X),
	fail ; true.


grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).
grammar(ex2, [prod('A', [[nt('A'), x], [x]])]).
grammar(ex5, [prod('A', [[a, nt('R')]]), prod('R', [[nt('B')], [nt('C')]]), prod('B', [[b]]), prod('C', [[c]])]).

% grammar(ex1, [prod('S', [[nt('A'), a, nt('A'), b], [nt('B'), b, nt('B'), a]]), prod('A', [[]]), prod('B', [[]])]).
% grammar(ex1, [prod('A', [[nt('X'), nt('B'), nt('Y')]]), prod('B', [[nt('C')]]), prod('C', [['c'], [nt('A')]]), prod('X', [[]]), prod('Y', [[]])]).
% grammar(ex1, [prod('A', [[nt('A'), a], [nt('A')], [b]]), prod('A1', [[nt('A')]])]).
% grammar(ex1, [prod('A', [[a]])]).

grammar(ex22, [prod('A', [[nt('A'), x], [x], [nt('A'), y], [y]])]).
grammar(ex23, [prod('A', [[nt('B')]]), prod('B', [[b]])]).


% normalized(Grammar, NormalizedGrammar).
normalized([], []).
normalized([prod(_, [])|GrammarRest], NormalizedGrammar) :- normalized(GrammarRest, NormalizedGrammar).
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
extract_terminals([prod_1(_, [])|GrammarRest], Terminals) :- extract_terminals(GrammarRest, Terminals).
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
	first_expand_nonterminal(Nonterminal, Result, Map, NewMap),
	first_map_expand_step(GrammarRest, NewMap, MapExpanded).

first_expand_nonterminal(Nonterminal, [], Map, MapExpanded) :-
	add_to_map_of_sets(Map, Nonterminal, [epsilon_0], MapExpanded).

first_expand_nonterminal(Nonterminal, [Symbol|SymbolsRest], Map, MapExpanded) :-
	( is_nonterminal(Symbol) ->
		map_search(Map, Symbol, FirstSet),
		list_remove(FirstSet, epsilon_0, FirstSetWithoutEpsilon),
		add_to_map_of_sets(Map, Nonterminal, FirstSetWithoutEpsilon, NewMap),
		( member(epsilon_0, FirstSet) ->
			first_expand_nonterminal(Nonterminal, SymbolsRest, NewMap, MapExpanded)
		;
			NewMap = MapExpanded
		)
	;
		add_to_map_of_sets(Map, Nonterminal, [Symbol], MapExpanded)
	).

% first_from_symbols(FirstMap, Symbols, SymbolsFirstSet).
first_from_symbols(_, [], [epsilon_0]).

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
	results(Grammar, [[_|R]|_]),
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

follow_map_expand_step((_, [], _), Map, Map).

follow_map_expand_step((Grammar, [prod_1(Nonterminal, Result)|GrammarRest], First), Map, MapExpanded) :-
	% format("Expanding ~p -> ~p\n", [Nonterminal, Result]),
	follow_expand_nonterminal((Grammar, First), Nonterminal, Result, Map, NewMap),
	follow_map_expand_step((Grammar, GrammarRest, First), NewMap, MapExpanded).

follow_expand_nonterminal((_, _), _, [], Map, Map).

follow_expand_nonterminal((Grammar, First), Nonterminal, [Symbol|SymbolsRest], Map, MapExpanded) :-
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
		follow_expand_nonterminal((Grammar, First), Nonterminal, SymbolsRest, NewMap_2, MapExpanded)
	;
		follow_expand_nonterminal((Grammar, First), Nonterminal, SymbolsRest, Map, MapExpanded)
	).


% select(Grammar, Select).
select(Grammar, Select) :-
	first(Grammar, First),
	follow(Grammar, Follow),
	select_list((Grammar, First, Follow), Select).

% select_list((Grammar, First, Follow), Select)
select_list(([], _, _), []).

select_list(([prod(Nonterminal, Results)|GrammarRest], First, Follow), [SelectList|SelectsRest]) :-
	select_from_productions((First, Follow), Nonterminal, Results, SelectList),
	select_list((GrammarRest, First, Follow), SelectsRest).

% select_from_productions((First, Follow), Nonterminal, Results, SelectList)
select_from_productions(_, _, [], []).

select_from_productions((First, Follow), Nonterminal, [Result|ResultsRest], [ProductionSelect|SelectListRest]) :-
	select_from_production((First, Follow), Nonterminal, Result, ProductionSelect),
	select_from_productions((First, Follow), Nonterminal, ResultsRest, SelectListRest).

select_from_production((First, Follow), Nonterminal, Result, ProductionSelect) :-
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
results([prod(_, Result)|GrammarRest], Results, Accumulator) :-
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

cycle_map_fill(([], _), Map, Map).

cycle_map_fill(([prod_1(Nonterminal, Result)|GrammarRest], First), Map, MapFilled) :-
	cycle_map_for_production(First, Nonterminal, [], Result, Map, NewMap),
	cycle_map_fill((GrammarRest, First), NewMap, MapFilled).

% cycle_map_for_production(First, Nonterminal, ResultPrefix, ResultRest, Map, NewMap)
cycle_map_for_production(_, _, _, [], Map, Map).

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
cycle_closure_step([key_value(_, [])|MapRest], Map, NewMap) :-
	cycle_closure_step(MapRest, Map, NewMap).

cycle_closure_step([key_value(Nonterminal, [Target|TargetsRest])|MapRest], Map, NewMap) :-
	map_search(Map, Target, TargetTargets),
	add_to_map_of_sets(Map, Nonterminal, TargetTargets, MapExpanded),
	cycle_closure_step([key_value(Nonterminal, TargetsRest)|MapRest], MapExpanded, NewMap).

% self_cycle_exists(Map).
self_cycle_exists([key_value(Source, Targets)|_]) :-
	member(Source, Targets).

self_cycle_exists([_|MapRest]) :-
	self_cycle_exists(MapRest).

direct_left_recursion_exists([Production|GrammarRest]) :-
	direct_left_recursion_exists_nonterminal(Production) ;
	direct_left_recursion_exists(GrammarRest).

direct_left_recursion_exists_nonterminal(prod(StrippedNonterminal, [[Symbol|_]|ResultsRest])) :-
	nt(StrippedNonterminal) = Symbol
	;
	direct_left_recursion_exists_nonterminal(prod(StrippedNonterminal, ResultsRest)).

direct_left_recursion_remove(Grammar, NewGrammar) :-
	direct_left_recursion_remove(Grammar, NewGrammar, []).

% direct_left_recursion_remove(Grammar, NewGrammar, Accumulator).
direct_left_recursion_remove([], NewGrammar, NewGrammar).

direct_left_recursion_remove([Production|GrammarRest], NewGrammar, Accumulator) :-
	% format("direct_left_recursion_remove ~p|..\n", [Production]),
	( direct_left_recursion_exists([Production]) ->
		nonterminals([Production|GrammarRest], NonterminalsGrammar),
		nonterminals(Accumulator, NonterminalsAccumulator),
		union(NonterminalsGrammar, NonterminalsAccumulator, Nonterminals),
		direct_left_recursion_nonterminal_remove(Nonterminals, Production, NewProductionsList),
		append(NewProductionsList, GrammarRest, ModifiedGrammar),
		direct_left_recursion_remove(ModifiedGrammar, NewGrammar, Accumulator)
	;
		append(Accumulator, [Production], NewAccumulator),
		direct_left_recursion_remove(GrammarRest, NewGrammar, NewAccumulator)
	).


direct_left_recursion_nonterminal_remove(Nonterminals, prod(StrippedNonterminal, Results), [prod(StrippedNonterminal, NewBeta), prod(NewStrippedNonterminal, NewAlpha_2)]) :-
	list_remove(Results, [nt(StrippedNonterminal)], NewResults),
	direct_left_recursion_prepare_results(prod(StrippedNonterminal, NewResults), [], Alpha, [], Beta),
	new_nonterminal(Nonterminals, StrippedNonterminal, NewStrippedNonterminal),
	add_tails(Alpha, nt(NewStrippedNonterminal), NewAlpha_1),
	append(NewAlpha_1, [[]], NewAlpha_2),
	add_tails(Beta, nt(NewStrippedNonterminal), NewBeta).

% direct_left_recursion_prepare_results(prod(), AlphaAccumulator, Alpha, BetaAccumulator, Beta).
direct_left_recursion_prepare_results(prod(_, []), Alpha, Alpha, Beta, Beta).

direct_left_recursion_prepare_results(prod(StrippedNonterminal, [Result|ResultsRest]), AlphaAccumulator, Alpha, BetaAccumulator, Beta) :-
	( Result = [nt(StrippedNonterminal)|ResultRest] ->
		NewAlphaAccumulator = [ResultRest|AlphaAccumulator],
		NewBetaAccumulator = BetaAccumulator
	;
		NewAlphaAccumulator = AlphaAccumulator,
		NewBetaAccumulator = [Result|BetaAccumulator]
	),
	direct_left_recursion_prepare_results(prod(StrippedNonterminal, ResultsRest), NewAlphaAccumulator, Alpha, NewBetaAccumulator, Beta).


new_nonterminal(Nonterminals, Nonterminal, NewNonterminal) :-
	% format("new_nonterminal ~p ~p ~p\n", [Nonterminals, Nonterminal, NewNonterminal]),
	atom_concat(Nonterminal, '1', Candidate),
	( member(Candidate, Nonterminals) ->
		new_nonterminal(Nonterminals, Candidate, NewNonterminal)
	;
		Candidate = NewNonterminal
	).

% is_LL1(Grammar)
is_LL1(Grammar) :-
	select(Grammar, Select),
	is_LL1_productions_ok(Select).

is_LL1_productions_ok([]).

is_LL1_productions_ok([Selects|SelectRest]) :-
	all_pairs(Selects, SelectsPairs),
	is_LL1_pairs_disjoint(SelectsPairs),
	is_LL1_productions_ok(SelectRest).

% is_LL1_pairs_disjoint(SelectPairs)
is_LL1_pairs_disjoint([]).

is_LL1_pairs_disjoint([(A, B)|SelectPairsRest]) :-
	intersection(A, B, []),
	is_LL1_pairs_disjoint(SelectPairsRest).

% TODO analiza LL
% parse_tree(Grammar, Word, Tree)
parse_tree(Grammar, Word, Tree) :-
	start(Grammar, Start),
	parse_LL([Start], Word, Tree).

% parse_LL(Stack, Word, Tree)
parse_LL([], [], _).

parse_LL([StackTop|StackRest], [StackTop|WordRest], [StackTop|TreeRest]) :-
	parse_LL(StackRest, WordRest, TreeRest).

parse_LL([StackTop|StackRest], [StackTop|WordRest], [StackTop|TreeRest]) :-
	parse_LL(StackRest, WordRest, TreeRest).

parse_LL([StackTop|StackRest], Word, [StackTop|TreeRest]) :-
	is_nonterminal(StackTop).
	% FIND possible translations
	% FOR EACH POSSIBLE TRANSLATION PUT RESULTS ON STACK
	% PARSE SUBTREE

% possible_actions(Grammar, Select, Nonterminal, TerminalOrNothing, Actions)
possible_actions(Grammar, Select, Nonterminal, TerminalOrNothing, Actions) :-
	find_production_and_select(Grammar, Select, Nonterminal, ResultsAndSelect),
	possible_results(ResultsAndSelect, TerminalOrNothing, PossibleResults).
	%TODO all that match terminal

% possible_results(ResultsAndSelect, TerminalOrNothing, PossibleResults)
possible_results(([], []), _, []).

possible_results(([Result|ResultsRest], [Select|SelectsRest]), TerminalOrNothing, PossibleResults) :-
	( matches_select(TerminalOrNothing, Select) ->
		PossibleResults = [Result|PossibleResultsRest]
	;
		PossibleResults = PossibleResultsRest
	),
	possible_results((ResultsRest, SelectsRest), TerminalOrNothing, PossibleResultsRest).

% matches_select(TerminalOrNothing, Select)
matches_select([], []).

matches_select([Terminal], Select) :-
	member(Terminal, Select).

% find_production_and_select(Grammar, Select, Nonterminal, ResultsAndSelect)
find_production_and_select([prod(Nonterminal, Results)|GrammarRest], [ProductionSelect|SelectsRest], Nonterminal, (Results, ProductionSelect)).

find_production_and_select([_|GrammarRest], [_|SelectsRest], Nonterminal, Pairs) :-
	find_production_and_select(GrammarRest, SelectsRest, Nonterminal, Pairs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_remove([], _, []).
list_remove([X|A], X, B) :- list_remove(A, X, B).
list_remove([Y|A], X, [Y|B]) :- X \== Y, list_remove(A, X, B).

not_member(_, []).
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

% add_tails(LisOfLists, Tail, NewListOfLists)
add_tails([], _, []).
add_tails([List|ListsRest], Tail, [NewList|NewListOfListsRest]) :-
	append(List, [Tail], NewList),
	add_tails(ListsRest, Tail, NewListOfListsRest).

add_heads([], _, []).
add_heads([List|ListsRest], Head, [[Head|List]|NewListOfListsRest]) :-
	add_heads(ListsRest, Head, NewListOfListsRest).


% all_pairs(List, Pairs).
all_pairs(List, Pairs) :-
	all_pairs(List, Pairs, []).

% all_pairs(List, Pairs, Accumulator)
all_pairs([], Pairs, Pairs).

all_pairs([E|ListRest], Pairs, Accumulator) :-
	pair_with_list(E, ListRest, ElementPairs),
	append(Accumulator, ElementPairs, NewAccumulator),
	all_pairs(ListRest, Pairs, NewAccumulator).

% pair_with_list(One, List, Pairs)
pair_with_list(_, [], []).
pair_with_list(One, [Two|ListRest], [(One, Two)|PairsRest]) :-
	pair_with_list(One, ListRest, PairsRest).
