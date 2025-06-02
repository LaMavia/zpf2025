.decl last(a, [a]|).
last(X, [X]).
last(X, (_:L)) :- last(X, L).

% .decl parent(|P, C).
% parent("Anna", "Jimmy").

% .decl grandp(|G, C).
% grandp(G, C) :- parent(G, P), parent(P, C).
