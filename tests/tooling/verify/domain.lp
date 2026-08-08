% The shared universe for the class-rule model checks (DESIGN.md,
% "Typeclasses: The rules"). Everything is EXTENSIONAL over a bounded
% signature, so "more specific" is literally covered-set inclusion, with
% no unification algorithm to trust. The signature is parameterized —
% run.sh checks every lemma at several scopes (more atoms, a binary
% constructor, deeper nesting, more files and instances), because UNSAT
% only ever means "no counterexample AT THIS SCOPE": scope-stability is
% the evidence that the scope is not what the verdict hangs on.

#const dmax = 2.        % max nesting depth
#const with_pair = 0.   % add a BINARY constructor pair/2
#const with_mine2 = 0.  % add a second user-declared atom

% ---- ground types ----
depth(int, 0).
depth(mine, 0).
depth(mine2, 0) :- with_mine2 == 1.
depth(list(T), D+1) :- depth(T, D), D < dmax.
depth(pair(T1,T2), M+1) :- with_pair == 1, depth(T1, D1), depth(T2, D2),
                           M = (D1+D2+|D1-D2|)/2, M < dmax.
ty(T) :- depth(T, _).

% the atoms a USER FILE declares (int and the constructors are builtin)
ut(mine).
ut(mine2) :- with_mine2 == 1.

% names(T, U): ground type T contains user type U
names(U, U) :- ut(U).
names(list(T), U) :- names(T, U), ty(list(T)).
names(pair(T1,T2), U) :- names(T1, U), ty(pair(T1,T2)).
names(pair(T1,T2), U) :- names(T2, U), ty(pair(T1,T2)).

% ---- instance-head patterns over the same signature ----
pdepth(var, 0).
pdepth(con(int), 0).
pdepth(con(U), 0) :- ut(U).
pdepth(list(P), D+1) :- pdepth(P, D), D < dmax.
pdepth(pair(P1,P2), M+1) :- with_pair == 1, pdepth(P1, D1), pdepth(P2, D2),
                            M = (D1+D2+|D1-D2|)/2, M < dmax.
pat(P) :- pdepth(P, _).

% a head that names user type U (the orphan rule's "mentions a type")
pmentions(con(U), U) :- ut(U).
pmentions(list(P), U) :- pmentions(P, U), pat(list(P)).
pmentions(pair(P1,P2), U) :- pmentions(P1, U), pat(pair(P1,P2)).
pmentions(pair(P1,P2), U) :- pmentions(P2, U), pat(pair(P1,P2)).

% covers(P, T): head P accepts ground type T. One-way matching, as in
% Classes.matchTy — a target is never made more specific to fit. Note
% covers is componentwise, so pmentions(P,U) forces U into every type P
% accepts — the fact the ground-coherence argument stands on.
covers(var, T) :- ty(T).
covers(con(int), int).
covers(con(U), U) :- ut(U).
covers(list(P), list(T)) :- covers(P, T), ty(list(T)).
covers(pair(P1,P2), pair(T1,T2)) :- covers(P1, T1), covers(P2, T2), ty(pair(T1,T2)).

% geq(Q, P): Q accepts every type P accepts (headSubsumes).
notgeq(Q, P) :- pat(P), pat(Q), covers(P, T), not covers(Q, T).
geq(Q, P) :- pat(P), pat(Q), not notgeq(Q, P).
% strictly more specific (moreSpecific): P's set is strictly inside Q's.
morespec(P, Q) :- geq(Q, P), not geq(P, Q).
