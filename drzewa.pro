% Piotr Daszkiewicz 219411

user:runtime_entry(start):-
	process_grammar_list([ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8]).

process_grammar_list([]).
process_grammar_list([Name|NamesRest]) :-
	print_grammar(Name),
	test_grammar(Name),
	format("--------------------------------\n", []),
	process_grammar_list(NamesRest).

print_grammar(Name) :-
	grammar(Name, Grammar),
	debug_grammar(Grammar).

test_grammar(Name) :-
	grammar(Name, Grammar),
	(jestLL1(Grammar) ->
		FixedGrammar = Grammar
	;
		remLeftRec(Grammar, FixedGrammar)
	),
	test_words(Name, Words),
	check_words(FixedGrammar, Words).

check_words(_, []).
check_words(Grammar, [Word|WordsRest]) :-
	(analizaLL(Grammar, Word, Tree) ->
		format("+ ~p  ~p\n", [Word, Tree])
	;
		format("- ~p\n", [Word])
	),
	check_words(Grammar, WordsRest).

debug_grammar(Grammar) :-
	format("Grammar: ~p\n", [Grammar]),
	print_results_2X(normalized, Grammar),
	print_results_2X(start, Grammar),
	print_results_2X(terminals, Grammar),
	print_results_2X(is_terminal, Grammar),
	print_results_2X(nonterminals, Grammar),
	print_results_2X(nonterminals_wrapped, Grammar),
	print_results_2X(first_map_keys, Grammar),
	print_results_2X(first_map, Grammar),
	print_results_2X(first, Grammar),
	print_results_2X(cycle_map, Grammar),
	print_results_1X(cycle_exists, Grammar),
	print_results_2X(my_follow, Grammar),
	print_results_2X(select, Grammar),
	print_results_1X(direct_left_recursion_exists, Grammar),
	print_results_2X(direct_left_recursion_remove, Grammar),
	print_results_2X(all_left_recursion_remove, Grammar),
	print_results_1X(is_LL1, Grammar),
	print_results_1X(jestLL1, Grammar),
	print_results_1X(jestCykl, Grammar),
	print_results_2X(remDirectLeftRec, Grammar),
	print_results_2X(remLeftRec, Grammar),
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
grammar(ex3, [prod('A', [[x, nt('A')], [x]])]).
grammar(ex4, [prod('A', [[a, nt('B')], [a, nt('C')]]), prod('B', [[b]]), prod('C', [[c]])]).
grammar(ex5, [prod('A', [[a, nt('R')]]), prod('R', [[nt('B')], [nt('C')]]), prod('B', [[b]]), prod('C', [[c]])]).
grammar(ex6, [prod('S', [[nt('A'), a, nt('A'), b], [nt('B'), b, nt('B'), a]]), prod('A', [[]]), prod('B', [[]])]).
grammar(ex7, [prod('A', [[a], [nt('B'), x]]), prod('B', [[b], [nt('A'), y]])]).
grammar(ex8, [prod('A', [[nt('A'), a]])]).

test_words(ex1, [[], [id], ['(', id, ')'], [id, '+', ident], [id,'+',id]]).
test_words(ex2, [[], [x], [x, x, x]]).
test_words(ex3, Words) :- test_words(ex2, Words).
test_words(ex4, [[], [a, b], [a, c], [b], [c], [a, b, c]]).
test_words(ex5, Words) :- test_words(ex4, Words).
test_words(ex6, [[], [a], [b], [a, b], [b, a]]).
test_words(ex7, [[], [a] ,[b], [a, y], [b, x], [a, y, x], [b, x, y, x]]).
test_words(ex8, [[], [a]]).

%grammar(ex_cycle, [prod('A', [[nt('X'), nt('B'), nt('Y')]]), prod('B', [[nt('C')]]), prod('C', [['c'], [nt('A')]]), prod('X', [[]]), prod('Y', [[]])]).
%grammar(ex_all, [prod('A', [[nt('A'), a], [nt('B'), a], [c]]), prod('B', [[nt('A'), b], [nt('B'), b], [c]])]).
%grammar(ex_all_2, [
%	prod('A', [[nt('B'), a, nt('X')], [c, nt('X')]]),
%	prod('X', [[a, nt('X')], []]),
%	prod('B', [[c, nt('X'), b, nt('Y')], [d, nt('Y')]]),
%	prod('Y', [[a, nt('X'), b, nt('Y')], [b, nt('Y')], []])]).
%grammar(ex1_mod, [prod('E', [[nt('T'), '+', nt('E')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).


jestLL1(Gramatyka) :- is_LL1(Gramatyka).
jestCykl(Gramatyka) :- cycle_exists(Gramatyka).
remDirectLeftRec(ProdukcjeNT, PoprProdukcjeNT) :- direct_left_recursion_remove(ProdukcjeNT, PoprProdukcjeNT).
remLeftRec(Gramatyka, GramatykaPopr) :- all_left_recursion_remove(Gramatyka, GramatykaPopr).
follow(Gramatyka, ZbioryFollow) :-
	my_follow(Gramatyka, MyFollow),
	convert_my_follow(MyFollow, ZbioryFollow).
% select
analizaLL(Gramatyka, Slowo, Drzewo) :- parse_tree(Gramatyka, Slowo, Drzewo).

% convert_my_follow(Follow, Converted)
convert_my_follow([], []).
convert_my_follow([key_value(nt(StrippedNonterminal), FollowSet)|FollowRest], [follow(StrippedNonterminal, FollowSet)|ConvertedRest]) :-
	convert_my_follow(FollowRest, ConvertedRest).

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
	extract_terminals(NormalizedGrammar, Terminals, []).

% extract_terminals(NormalizedGrammar, Terminals, Accumulator).
extract_terminals([], Terminals, Terminals).
extract_terminals([prod_1(_, [])|GrammarRest], Terminals, Accumulator) :- extract_terminals(GrammarRest, Terminals, Accumulator).
extract_terminals([prod_1(E, [Symbol|SymbolsRest])|GrammarRest], Terminals, Accumulator) :-
	( is_nonterminal(Symbol) ->
		extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], Terminals, Accumulator)
	;
		union([Symbol], Accumulator, NewAccumulator),
		extract_terminals([prod_1(E, SymbolsRest)|GrammarRest], Terminals, NewAccumulator)
	).

% is_terminal(Grammar, Symbol).
is_terminal(Grammar, Symbol) :-
	terminals(Grammar, Terminals),
	member(Symbol, Terminals).

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

eof_terminal(#).

% my_follow(Grammar, Follow).
my_follow(Grammar, Follow) :-
	follow_map(Grammar, Map),
	normalized(Grammar, NormalizedGrammar),
	first(Grammar, First),
	follow_map_expand((Grammar, NormalizedGrammar, First), Map, Follow).


% follow_map(Grammar, Map).
follow_map(Grammar, NewMap) :-
	nonterminals_wrapped(Grammar, Keys),
	map_from_set(Keys, [], Map),
	start(Grammar, StartSymbol),
	eof_terminal(Eof),
	add_to_map_of_sets(Map, StartSymbol, [Eof], NewMap).

% follow_map_expand((Grammar, NormalizedGrammar, First), Map, MapExpanded).
follow_map_expand((Grammar, NormalizedGrammar, First), Map, MapExpanded) :-
	follow_map_expand_step((Grammar, NormalizedGrammar, First), Map, NewMap),
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
	my_follow(Grammar, Follow),
	select_list((Grammar, First, Follow), Select).

% select_list((Grammar, First, Follow), Select)
select_list(([], _, _), []).

select_list(([prod(StrippedNonterminal, Results)|GrammarRest], First, Follow), [SelectList|SelectsRest]) :-
	select_from_productions((First, Follow), StrippedNonterminal, Results, SelectList),
	select_list((GrammarRest, First, Follow), SelectsRest).

% select_from_productions((First, Follow), StrippedNonterminal, Results, SelectList)
select_from_productions(_, _, [], []).

select_from_productions((First, Follow), StrippedNonterminal, [Result|ResultsRest], [ProductionSelect|SelectListRest]) :-
	select_from_production((First, Follow), StrippedNonterminal, Result, ProductionSelect),
	select_from_productions((First, Follow), StrippedNonterminal, ResultsRest, SelectListRest).

select_from_production((First, Follow), StrippedNonterminal, Result, ProductionSelect) :-
	% format("select_from_production ~p -> ~p\n", [StrippedNonterminal, Result]),
	first_from_symbols(First, Result, ResultFirstSet),
	( member(epsilon_0, ResultFirstSet) ->
		set_without_epsilon(ResultFirstSet, ResultFirstSetWithoutEpsilon),
		map_search(Follow, nt(StrippedNonterminal), NonterminalFollowSet),
		union(ResultFirstSetWithoutEpsilon, NonterminalFollowSet, ProductionSelect)
	;
		ProductionSelect = ResultFirstSet
	).

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
	nonterminals([Production|GrammarRest], NonterminalsGrammar),
	nonterminals(Accumulator, NonterminalsAccumulator),
	union(NonterminalsGrammar, NonterminalsAccumulator, Nonterminals),
	direct_left_recursion_nonterminal_remove(Nonterminals, Production, NewProductionsList),
	append(Accumulator, NewProductionsList, NewAccumulator),
	direct_left_recursion_remove(GrammarRest, NewGrammar, NewAccumulator).

direct_left_recursion_nonterminal_remove(Nonterminals, prod(StrippedNonterminal, Results), NewProductionsList) :-
	( direct_left_recursion_exists([prod(StrippedNonterminal, Results)]) ->
		list_remove(Results, [nt(StrippedNonterminal)], NewResults),
		direct_left_recursion_prepare_results(prod(StrippedNonterminal, NewResults), [], Alpha, [], Beta),
		nonempty(Beta),
		new_nonterminal(Nonterminals, StrippedNonterminal, NewStrippedNonterminal),
		add_tails(Alpha, [nt(NewStrippedNonterminal)], NewAlpha_1),
		append(NewAlpha_1, [[]], NewAlpha_2),
		add_tails(Beta, [nt(NewStrippedNonterminal)], NewBeta),
		NewProductionsList = [prod(StrippedNonterminal, NewBeta), prod(NewStrippedNonterminal, NewAlpha_2)]
	;
		NewProductionsList = [prod(StrippedNonterminal, Results)]
	).

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

% less_in_order(A, Order, B)
less_in_order(A, [B|OrderRest], C) :-
	member(A, OrderRest),
	B = C
	;
	less_in_order(A, OrderRest, C).

% production_for_nonterminal(Grammar, Nonterminal, Production, OtherProductions)
production_for_nonterminal([prod(ProductionNonterminal, Results)|GrammarRest], Nonterminal, Production, BeforeProductions, AfterProductions) :-
	( ProductionNonterminal = Nonterminal ->
		Production = prod(ProductionNonterminal, Results),
		BeforeProductions = [],
		AfterProductions = GrammarRest
	;
		BeforeProductions = [prod(ProductionNonterminal, Results)|BeforeProductionsRest],
		production_for_nonterminal(GrammarRest, Nonterminal, Production, BeforeProductionsRest, AfterProductions)
	).

% all_left_recursion_remove(Grammar, NewGrammar)
all_left_recursion_remove(Grammar, NewGrammar) :-
	\+ cycle_exists(Grammar),
	nonterminals(Grammar, Nonterminals),
	all_left_recursion_loop(Grammar, [], Nonterminals, NewGrammar).

% all_left_recursion_loop(Grammar, Done, ToDo, NewGrammar)
all_left_recursion_loop(Grammar, _, [], Grammar).
all_left_recursion_loop(Grammar, Done, [Current|ToDoRest], NewGrammar) :-
	all_left_recursion_inner_loop(Grammar, Done, Current, ChangedGrammar),
	append(Done, [Current], NewDone),
	all_left_recursion_loop(ChangedGrammar, NewDone, ToDoRest, NewGrammar).

% all_left_recursion_inner_loop(Grammar, Done, Current, NewGrammar)
all_left_recursion_inner_loop(Grammar, [], Current, NewGrammar) :-
	production_for_nonterminal(Grammar, Current, Production, BeforeProductions, AfterProductions),
	nonterminals(Grammar, Nonterminals),
	direct_left_recursion_nonterminal_remove(Nonterminals, Production, NewProductionsList),
	append(BeforeProductions, NewProductionsList, PartialGrammar),
	append(PartialGrammar, AfterProductions, NewGrammar).

all_left_recursion_inner_loop(Grammar, [Before|DoneRest], Current, NewGrammar) :-
	% format("Inner: ~p ~p\n", [[Before|DoneRest], Current]),
	all_left_recursion_fix(Grammar, Before, Current, ChangedGrammar),
	all_left_recursion_inner_loop(ChangedGrammar, DoneRest, Current, NewGrammar).

all_left_recursion_fix(Grammar, Before, Current, NewGrammar) :-
	production_for_nonterminal(Grammar, Current, prod(Current, Results), BeforeProductions, AfterProductions),
	all_left_recursion_fix_production(Grammar, Results, Before, NewResults, []),
	append(BeforeProductions, [prod(Current, NewResults)|AfterProductions], NewGrammar).

% all_left_recursion_fix_production(Grammar, Results, Before, NewResults, Accumulator)
all_left_recursion_fix_production(_, [], _, NewResults, NewResults).
all_left_recursion_fix_production(Grammar, [Result|ResultsRest], Before, NewResults, Accumulator) :-
	% format("all_left_recursion_fix_production ~p Before: ~p\n", [[Result|ResultsRest], Before]),
	( Result = [nt(Before)|SymbolsRest] ->
		production_for_nonterminal(Grammar, Before, prod(Before, BeforeResults), _, _),
		add_tails(BeforeResults, SymbolsRest, TransformedResults),
		append(Accumulator, TransformedResults, NewAccumulator),
		all_left_recursion_fix_production(Grammar, ResultsRest, Before, NewResults, NewAccumulator)
	;
		append(Accumulator, [Result], NewAccumulator),
		all_left_recursion_fix_production(Grammar, ResultsRest, Before, NewResults, NewAccumulator)
	).

% is_LL1(Grammar)
is_LL1(Grammar) :-
	select(Grammar, Select),
	is_LL1_productions_ok(Select),
	\+ direct_left_recursion_exists(Grammar).

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

% nested_lists_to_tree(NestedLists, Tree)
nested_lists_to_tree(NestedLists, Tree) :-
	( NestedLists = (Root, Children) ->
		sublist_to_tree(Children, Subtrees),
		Tree =.. [Root|Subtrees]
	;
		Tree = NestedLists
	).

% sublist_to_tree(Sublist, Subtrees)
sublist_to_tree([], []).
sublist_to_tree([Child|ChildrenRest], [ChildTree|SubtreesRest]) :-
	nested_lists_to_tree(Child, ChildTree),
	sublist_to_tree(ChildrenRest, SubtreesRest).

% parse_tree(Grammar, Word, FillList)
parse_tree(Grammar, Word, Tree) :-
	start(Grammar, Start),
	select(Grammar, Select),
	eof_terminal(Eof),
	append(Word, [Eof], WordWithEof),
	parse_LL(Grammar, Select, [Start, Eof], WordWithEof, FillList),
	FillList = [List, Eof],
	nested_lists_to_tree(List, Tree).

% parse_LL(_, _, Stack, Word, Tree)
parse_LL(_, _, [], [], []).

parse_LL(Grammar, Select, [StackTop|StackRest], [WordTerminal|WordRest], FillList) :-
	% format("parse_LL Stack  ~p\n", [[StackTop|StackRest]]),
	% format("parse_LL Word   ~p\n", [[WordTerminal|WordRest]]),
	(StackTop = WordTerminal ->
		FillList = [ToFill|FillListRest],
		ToFill = StackTop,
		NewFillList = FillListRest,
		parse_LL(Grammar, Select, StackRest, WordRest, NewFillList)
	;
		is_nonterminal(StackTop),
		FillList = [ToFill|FillListRest],
		StackTop = nt(StrippedNonterminal),
		ToFill = (StrippedNonterminal, Unknown),
		% ToFill =.. [StrippedNonterminal|Unknown], Does Not Work :/
		NewFillList = [Unknown|FillListRest],
		possible_actions(Grammar, Select, StackTop, WordTerminal, PossibleActions),
		parse_LL_try(Grammar, Select, StackRest, [WordTerminal|WordRest], NewFillList, PossibleActions)
	).

% parse_LL_try(Grammar, Select, Stack, Word, FillList, PossibleActions)
parse_LL_try(Grammar, Select, Stack, Word, FillList, [Action|PossibleActionsRest]) :-
	append(Action, Stack, NewStack),
	list_to_variables(Action, ActionVariables),
	FillList = [ToFill|FillListRest],
	ToFill = ActionVariables,
	append(ActionVariables, FillListRest, NewFillList),
	parse_LL(Grammar, Select, NewStack, Word, NewFillList)
	;
	parse_LL_try(Grammar, Select, Stack, Word, FillList, PossibleActionsRest).

% possible_actions(Grammar, Select, Nonterminal, TerminalOrNothing, Actions)
possible_actions(Grammar, Select, nt(StrippedNonterminal), TerminalOrNothing, Actions) :-
	find_production_and_select(Grammar, Select, StrippedNonterminal, ResultsAndSelect),
	possible_results(ResultsAndSelect, [TerminalOrNothing], Actions).

% possible_results(ResultsAndSelect, TerminalOrNothing, PossibleResults)
possible_results(([], []), _, []).

possible_results(([Result|ResultsRest], [Select|SelectsRest]), TerminalOrNothing, PossibleResults) :-
	% format("possible_results ~p ~p ~p\n", [Result, Select, TerminalOrNothing]),
	( matches_select(TerminalOrNothing, Select) ->
		PossibleResults = [Result|PossibleResultsRest]
	;
		PossibleResults = PossibleResultsRest
	),
	possible_results((ResultsRest, SelectsRest), TerminalOrNothing, PossibleResultsRest).

% matches_select(TerminalOrNothing, Select)
matches_select([Terminal], Select) :-
	member(Terminal, Select).


% find_production_and_select(Grammar, Select, Nonterminal, ResultsAndSelect)
find_production_and_select([prod(Nonterminal, Results)|_], [ProductionSelect|_], Nonterminal, (Results, ProductionSelect)).

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
	append(List, Tail, NewList),
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

nonempty([_|_]).

% list_to_variables(List, Variables)
list_to_variables([], []).
list_to_variables([_|ListRest], [_|VariablesRest]) :-
	list_to_variables(ListRest, VariablesRest).
