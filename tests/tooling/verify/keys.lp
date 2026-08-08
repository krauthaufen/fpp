% How type names become KEYS (Infer.fs, arityDeclared / arityName), the
% other rule family bugs have clustered in. The rules, as implemented:
%
%   - declarations are seen in file order
%   - the FIRST argument-count seen for a name claims the undecorated
%     key (`Foo`); every different count gets a decorated one (`Foo`2`)
%   - a later declaration at an already-seen count SHARES that key —
%     this is what merges a user type with its prelude namesake
%
% Three declarations, two names, counts 0..2, all positions searched.
% Two worlds see the SAME declarations in opposite file orders.

decl(1..3).
1 { named(D, N) : tyname(N) } 1 :- decl(D).
1 { arityof(D, A) : A = 0..2 } 1 :- decl(D).
tyname(n1; n2).
world(fwd; rev).

% distinct file positions, and the reverse world flips them
1 { post(D, P) : P = 1..3 } 1 :- decl(D).
:- decl(D1), decl(D2), D1 < D2, post(D1, P), post(D2, P).
pos(D, fwd, P) :- post(D, P).
pos(D, rev, 4 - P) :- post(D, P).

% the first declaration of a name, per world, sets the undecorated count
before(N, W, D) :- named(D, N), named(D2, N), D2 != D,
                   pos(D2, W, P2), pos(D, W, P), P2 < P.
firstof(N, W, D) :- named(D, N), world(W), not before(N, W, D).
plainarity(N, W, A) :- firstof(N, W, D), arityof(D, A).

key(D, W, plain(N))  :- named(D, N), arityof(D, A), plainarity(N, W, A).
key(D, W, dec(N, A)) :- named(D, N), arityof(D, A), plainarity(N, W, A2), A != A2.

#show named/2.
#show arityof/2.
#show post/2.
#show key/3.
