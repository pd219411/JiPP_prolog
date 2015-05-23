user:runtime_entry(start):-
	% write500(node(7, node(5, leaf, node(6, leaf, leaf)), node(8, leaf, node(10, leaf, leaf)))).
	% write_follow(ex1).
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
	w_1(expand_test, ex1).

write_grammar(N) :- grammar(N, G), write(G), write('\n').
w_1(Predicate, Name) :- grammar(Name, Grammar), call(Predicate, Grammar, X), write(Predicate), write(' : '), write(X), write('\n').

% write_follow(N) :- grammar(N, G), follow(G, X), write(X), write('\n').
% write_wyciagnij_slowa(N) :- grammar(N, G), wyciagnij_slowa(G, X), write(X), write('\n').

grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).

% normalized(Grammar, NormalizedGrammar).
normalized([], []).
normalized([prod(E, [])|GrammarRest], NormalizedGrammar) :- normalized(GrammarRest, NormalizedGrammar).
normalized([prod(E, [Result|ResultsRest])|GrammarRest], [prod_1(nt(E), Result)|NormalizedGrammarRest]) :- normalized([prod(E, ResultsRest)|GrammarRest], NormalizedGrammarRest).

% start(Grammar, Symbol).
start([prod(E, _)|_], E).

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

% nonterminals(Grammar, Nonterminals).
nonterminals([], []).
nonterminals([prod(E, _)|GrammarRest], [E|NonterminalsRest]) :- nonterminals(GrammarRest, NonterminalsRest).

% nonterminals_wrapped(Grammar, Nonterminals).
nonterminals_wrapped([], []).
nonterminals_wrapped([prod(E, _)|GrammarRest], [nt(E)|NonterminalsRest]) :- nonterminals_wrapped(GrammarRest, NonterminalsRest).

% first_map_keys(Grammar, Keys).
first_map_keys(Grammar, Keys) :-
	nonterminals_wrapped(Grammar, Keys).
	%nonterminals_wrapped(Grammar, Nonterminals).
	%results(Grammar, Results), union(Nonterminals, Results, Keys).
	%TODO: calculate

% first_map(Grammar, Map).
first_map(Grammar, Map) :- first_map_keys(Grammar, Keys), map_from_set(Keys, [], Map).

% first_map_expand((Grammar, NormalizedGrammar), Map, MapExpanded).
first_map_expand((Grammar, NormalizedGrammar), Map, Map) :-
	first_map_expand_step((Grammar, NormalizedGrammar), Map, Map).

first_map_expand((Grammar, NormalizedGrammar), Map, MapExpanded) :-
	first_map_expand_step((Grammar, NormalizedGrammar), Map, NewMap),
	first_map_expand((Grammar, NormalizedGrammar), NewMap, MapExpanded).

first_map_expand_step((Grammar, []), Map, Map).
first_map_expand_step((Grammar, [prod_1(Nonterminal, Result)|GrammarRest]), Map, MapExpanded) :-
	format("Expanding ~p -> ~p\n", [Nonterminal, Result]),
	expand_nonterminal((Grammar, NormalizedGrammar, Terminals), Nonterminal, Result, Map, NewMap),
	first_map_expand_step((Grammar, GrammarRest), NewMap, MapExpanded).

expand_test(Grammar, Expanded) :-
	first_map(Grammar, Map),
	normalized(Grammar, NormalizedGrammar),
	first_map_expand((Grammar, NormalizedGrammar), Map, Expanded).

expand_nonterminal((Grammar, NormalizedGrammar), Nonterminal, [], Map, MapExpanded) :-
	add_to_first_set(Map, Nonterminal, [epsilon_0], MapExpanded).

expand_nonterminal((Grammar, NormalizedGrammar), Nonterminal, [Symbol|_], Map, MapExpanded) :-
	is_terminal(Grammar, Symbol),
	add_to_first_set(Map, Nonterminal, [Symbol], MapExpanded).

expand_nonterminal((Grammar, NormalizedGrammar), Nonterminal, [Symbol|SymbolsRest], Map, MapExpanded) :-
	map_search(Map, Symbol, FirstSet),
	list_remove(FirstSet, epsilon_0, FirstSetWithoutEpsilon),
	add_to_first_set(Map, Nonterminal, FirstSetWithoutEpsilon, NewMap),
	member(epsilon_0, FirstSet), !.
	% expand_nonterminal(Grammar, Nonterminal, SymbolsRest, NewMap, MapExpanded).

expand_nonterminal((Grammar, NormalizedGrammar), Nonterminal, [Symbol|_], Map, MapExpanded) :-
	map_search(Map, Symbol, FirstSet),
	list_remove(FirstSet, epsilon_0, FirstSetWithoutEpsilon), %TODO: do we need this? it does not contain epsilon from previous case
	add_to_first_set(Map, Nonterminal, FirstSetWithoutEpsilon, MapExpanded).

add_to_first_set(Map, Key, Symbols, NewMap) :-
	map_search(Map, Key, FirstSet),
	union(FirstSet, Symbols, ExpandedFirstSet),
	map_replace(Map, Key, ExpandedFirstSet, NewMap).
	%, format("First(~p) <- ~p\n", [Key, Symbols]).


%TODO:
% first(Gramatyka, ZbioryFirst).

%TODO:
% first_symbol(Gramatyka, Slowo, ZbiorFirst).


% results(Grammar, Results).
%TODO: renaming PL -> ENG
results(Gramatyka, Slowa) :- results(Gramatyka, Slowa, []).

results([], A, A).
results([prod(Nieterminal, ListaSlow)|ResztaGramatyki], Slowa, Akumulator) :-
	union(Akumulator, ListaSlow, AkumulatorPowiekszony),
	results(ResztaGramatyki, Slowa, AkumulatorPowiekszony).

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
