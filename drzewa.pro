user:runtime_entry(start):-
	write500(node(7, node(5, leaf, node(6, leaf, leaf)), node(8, leaf, node(10, leaf, leaf)))).

% write500(T) :- tree_to_list2(T, X), write(X).
write500(T) :- tree_to_levels(T, X), write(X).

tree(leaf).
tree(node(E, L, R)) :- drzewo(L), drzewo(R).

bst_tree_insert(E, leaf, node(E, leaf, leaf)).

% bst_tree_insert(E, node(N, L1, R1), node(N, L2, R1)) :- E < N, bst_tree_insert(E, L1, L2).
% bst_tree_insert(E, node(N, L1, R1), node(N, L1, R2)) :- E >= N, bst_tree_insert(E, R1, R2).

bst_tree_insert(E, node(N, L1, R1), node(N, L2, R2)) :- E =< N ->
	bst_tree_insert(E, L1, L2), R1 = R2;
	bst_tree_insert(E, R1, R2), L1 = L2.

% tree_to_list(T, L)
tree_to_list(leaf, []).
tree_to_list(node(E, L, R), Out) :- tree_to_list(L, ListLeft), tree_to_list(R, ListRight), append(ListLeft, [E|ListRight], Out).

tree_to_list2(T, L) :- tree_to_list2(T, [], L).

tree_to_list2(leaf, A, A).

tree_to_list2(node(E, L, R), A, Out) :-
	tree_to_list2(R, A, AR),
	tree_to_list2(L, [E|AR], Out).


% kolejka FIFO
% make_empty([]).
% empty([]).
% push(K1, E, K2) :- append(K1, [E], K2).
% pop([E|L], E, L).

% szybka kolejka na listach roznicowych
make_empty(queue(Head, Head)).
empty(queue(Head, Tail)) :- Head == Tail.
push(queue(Head, [E|Tail]), E, queue(Head, Tail)).
pop(queue([E|Head], Tail), E, queue(Head, Tail)).


% wypisac drzewo warstwowo
tree_to_levels(T, L) :- make_empty(Q), push(Q, T, Q0), tree_to_levels_helper(Q0, L).

tree_to_levels_helper(Q, []) :- empty(Q). % odciecie
tree_to_levels_helper(Q, Lout) :- pop(Q, leaf, Q1), tree_to_levels_helper(Q1, Lout).
tree_to_levels_helper(Q, [E|Lout]) :- pop(Q, node(E, L, R), Q1), push(Q1, L, Q2), push(Q2, R, Q3), tree_to_levels_helper(Q3, Lout).

