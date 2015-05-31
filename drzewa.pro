% Piotr Daszkiewicz 219411

user:runtime_entry(start):-
	w_1(test_fail, ex1),
	w_1(test_success, ex1),
	write_grammar(ex1),
	w_1(normalized, ex1),
	w_1(start, ex1),
	w_1(terminals, ex1),
	w_1(is_terminal, ex1),
	w_1(nonterminals, ex1),
	w_1(nonterminals_wrapped, ex1),
	w_1(results, ex1),
	w_1(first_map_keys, ex1),
	w_1(first_map, ex1),
	w_1(first, ex1),
	w_1(test_firsts, ex1),
	w_1(follow, ex1),
	w_1(select, ex1),
	w_1(cycle_map, ex1).

write_grammar(N) :- grammar(N, G), write(G), write('\n').

w_1(Predicate, Name) :-
	grammar(Name, Grammar),
	print_results(Predicate, Grammar).

print_result(Predicate, Result) :-
	write(Predicate), write(' : '), write(Result), write('\n').

print_results(Predicate, FirstParam) :-
	( call(Predicate, FirstParam, X) ->
		print_more(Predicate, FirstParam)
	;
		print_result(Predicate, 'FAIL')
	).

print_more(Predicate, FirstParam) :-
	call(Predicate, FirstParam, X),
	print_result(Predicate, X),
	fail ; true.

test_fail(_, _) :- fail.
test_success(_, a).
test_success(_, z).

% grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).
grammar(ex1, [prod('A', [[a, nt('R')]]), prod('R', [[nt('B')], [nt('C')]]), prod('B', [[b]]), prod('C', [[c]])]).
% grammar(ex1, [prod('S', [[nt('A'), a, nt('A'), b], [nt('B'), b, nt('B'), a]]), prod('A', [[]]), prod('B', [[]])]).

% normalized(Grammar, NormalizedGrammar).
normalized([], []).
normalized([prod(E, [])|GrammarRest], NormalizedGrammar) :- normalized(GrammarRest, NormalizedGrammar).
normalized([prod(E, [Result|ResultsRest])|GrammarRest], [prod_1(nt(E), Result)|NormalizedGrammarRest]) :- normalized([prod(E, ResultsRest)|GrammarRest], NormalizedGrammarRest).

% start(Grammar, Symbol).
start([prod(E, _)|_], nt(E)).

% terminals(Grammar, Terminals).
% terminals(Grammar, Terminals) :- extract_terminals(Grammar, X), list_to_set(X, Terminals).
terminals(Grammar, Terminals) :- normalized(Grammar, NormalizedGrammar), extract_terminals(NormalizedGrammar, Terminals).

% extract_terminals([], []).
% extract_terminals([prod(E, [])|GrammarRest], Terminals) :- terminals(GrammarRest, Terminals).
% extract_terminals([prod(E, [[]|ResultsRest])|GrammarRest], Terminals) :- terminals([prod(E, ResultsRest)|GrammarRest], Terminals).
% extract_terminals([prod(E, [[nt(_)|SymbolsRest]|ResultsRest])|GrammarRest], Terminals) :- terminals([prod(E, [SymbolsRest|ResultsRest])|GrammarRest], Terminals), !. %TODO: this cut for nt(_)?
% extract_terminals([prod(E, [[Terminal|SymbolsRest]|ResultsRest])|GrammarRest], [Terminal|TerminalsReduced]) :- terminals([prod(E, [SymbolsRest|ResultsRest])|GrammarRest], TerminalsReduced).

% extract_terminals(NormalizedGrammar, TerminalsList).
extract_terminals([], []).
extract_terminals([prod_1(E, [])|GrammarRest], Terminals) :- extract_terminals(GrammarRest, Terminals).
extract_terminals([prod_1(E, [nt(_)|SymbolsRest])|GrammarRest], Terminals) :- extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], Terminals), !. %TODO: this cut for nt(_)?
extract_terminals([prod_1(E, [Terminal|SymbolsRest])|GrammarRest], [Terminal|TerminalsReduced]) :- extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], TerminalsReduced).

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
	( is_nonterminal(Symbol) ->
		map_search(FirstMap, Symbol, FirstSet),
		( member(epsilon_0, FirstSet) ->
			set_without_epsilon(FirstSet, FirstSetWithoutEpsilon),
			union(X, FirstSetWithoutEpsilon, SymbolsFirstSet),
			first_from_symbols(FirstMap, SymbolsRest, X)
		;
			FirstSet = SymbolsFirstSet
		)
	;
		[Symbol] = SymbolsFirstSet
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

select_from_production((First, Follow), prod_1(Nonterminal, Result), ProductionSelect) :-
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
exists_cycle(Grammar)

exists_cycle(Grammar) :-
	cycle_map(Grammar, Map),

	cycle_map_expand((NormalizedGrammar, First), Map, Follow).
	%TODO: CHECK

% cycle_map(Grammar, CycleMap).
cycle_map(Grammar, CycleMap) :-
	nonterminals_wrapped(Grammar, Keys),
	map_from_set(Keys, [], Map),
	normalized(Grammar, NormalizedGrammar),
	first(Grammar, First),
	cycle_map_fill((NormalizedGrammar, First), Map, CycleMap).

cycle_map_fill(([], First), Map, Map).

cycle_map_fill(([prod_1(Nonterminal, Result)|GrammarRest], First), Map, MapFilled) :-
	% format("Cyc1ed ~p -> ~p\n", [Nonterminal, Result]),
	cycle_map_for_production(First, Nonterminal, [], Result, Map, NewMap),
	% format("Cycled ~p -> ~p\n", [Nonterminal, Result]),
	cycle_map_fill((GrammarRest, First), NewMap, MapFilled).

% cycle_map_for_production(First, Nonterminal, ResultPrefix, ResultRest, Map, NewMap)
cycle_map_for_production(First, Nonterminal, _, [], Map, Map).

cycle_map_for_production(First, Nonterminal, SymbolsPrefix, [Symbol|SymbolsRest], Map, NewMap) :-
	% format("T1ying ~p -> ~p ~p ~p\n", [Nonterminal, SymbolsPrefix, Symbol, SymbolsRest]),
	first_from_symbols(First, SymbolsPrefix, SymbolsPrefixFirstSet),
	first_from_symbols(First, SymbolsRest, SymbolsRestFirstSet),
	( is_nonterminal(Symbol), member(epsilon_0, SymbolsPrefixFirstSet), member(epsilon_0, SymbolsRestFirstSet) ->
		add_to_map_of_sets(Map, Nonterminal, [Symbol], MapExpanded),
		append(SymbolsPrefix, [Symbol], NewSymbolsPrefix),
		% format("Udalo sie ~p\n", [MapExpanded]),
		cycle_map_for_production(First, Nonterminal, NewSymbolsPrefix, SymbolsRest, MapExpanded, NewMap)
	;
		Map = NewMap
	).

%TODO TRANSITIVE CLOSURE
cycle_map_expand((NormalizedGrammar, First), Map, MapExpanded).
cycle_map_expand((NormalizedGrammar, First), Map, MapExpanded) :-
	cycle_map_expand_step(NormalizedGrammar, Map, NewMap),
	( Map == NewMap ->
		Map = MapExpanded
	;
		cycle_map_expand((NormalizedGrammar, First), NewMap, MapExpanded)
	).

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
map_replace(Map, Key, Value, NewMap) :- map_delete(Map, Key, MapWithoutKey), map_insert(MapWithoutKey, Key, Value, NewMap).

% map_from_set(Set, DefaultValue, ?Map).
map_from_set([], _, []).
map_from_set([E|SetRest], DefaultValue, Map) :- map_insert(MapRest, E, DefaultValue, Map), map_from_set(SetRest, DefaultValue, MapRest).

% add_to_map_of_sets(Map, Key, Values, NewMap)
add_to_map_of_sets(Map, Key, Values, NewMap) :-
	% format("Map(~p) <- ~p\n", [Key, Values]),
	map_search(Map, Key, Set),
	union(Set, Values, ExpandedSet),
	map_replace(Map, Key, ExpandedSet, NewMap).
