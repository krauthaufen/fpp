% A ground USE of the class: one file, one ground goal type, everything
% the goal names declared by then.
1 { usefile(F) : file(F) } 1.
1 { goal(T) : ty(T) } 1.
:- goal(T), names(T, U), usefile(F), utfile(U, FM), FM > F.

applies(I) :- active(I), headof(I, P), goal(T), covers(P, T).
visible(I) :- active(I), fileof(I, F), usefile(FU), F <= FU.

% the maximal (most specific) applicable sets, file-visible vs whole-program
overtakenvis(I)  :- applies(I), visible(I), applies(J), visible(J),
                    headof(I, P), headof(J, Q), morespec(Q, P).
maxvis(I)  :- applies(I), visible(I), not overtakenvis(I).
overtakenglob(I) :- applies(I), applies(J),
                    headof(I, P), headof(J, Q), morespec(Q, P).
maxglob(I) :- applies(I), not overtakenglob(I).

% incoherence: the use's answer differs from the whole program's
viol :- maxglob(I), not maxvis(I).
viol :- maxvis(I), not maxglob(I).
:- not viol.

#show usefile/1.
#show goal/1.
#show maxvis/1.
#show maxglob/1.
