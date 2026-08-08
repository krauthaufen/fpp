% Rule 4, the orphan rule, as a hard constraint: an instance lives in the
% file of its class or of a type its head mentions.
ok(I) :- fileof(I, F), classfile(F).
ok(I) :- headof(I, P), pmentions(P, U), fileof(I, F), utfile(U, F).
:- active(I), not ok(I).
