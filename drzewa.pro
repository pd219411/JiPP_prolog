user:runtime_entry(start):-
	% write500(node(7, node(5, leaf, node(6, leaf, leaf)), node(8, leaf, node(10, leaf, leaf)))).
	% write_follow(ex1).
	write_grammar(ex1),
	w_1(start, ex1),
	w_1(wyciagnij_slowa, ex1),
	w_1(nonterminals, ex1).

write_grammar(N) :- grammar(N, G), write(G), write('\n').
w_1(Predicate, Name) :- grammar(Name, Grammar), call(Predicate, Grammar, X), write(Predicate), write(' : '), write(X), write('\n').

write_follow(N) :- grammar(N, G), follow(G, X), write(X), write('\n').
write_wyciagnij_slowa(N) :- grammar(N, G), wyciagnij_slowa(G, X), write(X), write('\n').

grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).

% start(Grammar, Symbol).
start([prod(E, _)|_], E).

% nonterminals(Grammar, Nonterminals).
nonterminals([], []).
nonterminals([prod(E, _)|GrammarRest], [E|NonterminalsRest]) :- nonterminals(GrammarRest, NonterminalsRest).

%TODO:
jestLL1(Gramatyka).
%	 Sprawdzenie czy podana gramatyka jest typu LL(1)
%	 (sukces wtw, gdy gramatyka jest typu LL(1)).

follow(Gramatyka, ZbioryFollow).
%Dla podanej gramatyki tworzy zbiory Follow dla wszystkich symboli  nieterminalnych.
%Parametr ZbioryFollow powinien być listą elementów postaci: follow(Nieterminal, ZbiórTerminali), a
%reprezentacją zbioru terminali powinna być lista terminali (bez powtórzeń).

%TODO:
first(Gramatyka, ZbioryFirst).

%TODO:
first_symbol(Gramatyka, Slowo, ZbiorFirst).

first_symbol(Gramatyka, [], [epsilon_0]).
first_symbol(Gramatyka, [], [epsilon_0]).



wyciagnij_slowa(Gramatyka, Slowa) :- wyciagnij_slowa(Gramatyka, Slowa, []).

wyciagnij_slowa([], A, A).
wyciagnij_slowa([prod(Nieterminal, ListaSlow)|ResztaGramatyki], Slowa, Akumulator) :-
	union(Akumulator, ListaSlow, AkumulatorPowiekszony),
	wyciagnij_slowa(ResztaGramatyki, Slowa, AkumulatorPowiekszony).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list_remove([], _, []).
list_remove([X|A], X, B) :- list_remove(A, X, B).
list_remove([Y|A], X, [Y|B]) :- X \== Y, list_remove(A, X, B).

not_member(E, []).
not_member(E, [X|L]) :- E \== X, not_member(E, L).

union([], S, S).
union([E|A], B, [E|C]) :- list_remove(B, E, B1), union(A, B1, C).

intersection([], _, []).
intersection([E|A], B, [E|C]) :- member(E, B), intersection(A, B, C).
intersection([E|A], B, C) :- not_member(E, B), intersection(A, B, C).
