% LEMMA 3 (expect SAT). The orphan rule ALONE does not make selection
% whole-program: a generic constrained binding whose parameter is open
% commits at its own file under eager semantics, and a legal later
% instance (living with its type) is never ranked. The witness is
% cross-module-specificity, rediscovered by search — the reason
% Classes.settle now defers an OPEN match to the stamp
% (ClassTests "a later file's more specific instance wins at the stamp").
#include "domain.lp".
#include "program.lp".
#include "orphan.lp".

% the generic binding: defined in a file, parameter typed by a PATTERN
% that is genuinely open (accepts at least two ground types)
1 { deffile(F) : file(F) } 1.
1 { gpat(G) : pat(G) } 1.
opencount(N) :- N = #count { T : gpat(G), covers(G, T) }.
:- opencount(N), N < 2.

% eligible for the open match: the head accepts EVERYTHING the parameter
% can be (matchTy binds an instance variable to the target's variable;
% a concrete head never matches an open target)
inel(I) :- active(I), gpat(G), covers(G, T), headof(I, P), not covers(P, T).
elig(I) :- active(I), not inel(I).

% EAGER: commit at the definition, among instances visible there
evis(I) :- elig(I), fileof(I, F), deffile(FD), F <= FD.
eovertaken(I) :- evis(I), evis(J), headof(I, P), headof(J, Q), morespec(Q, P).
epick(I) :- evis(I), not eovertaken(I).
% only determinate commits (the compiler defers an ambiguous one anyway)
:- epick(I), epick(J), I != J.

% a caller instantiates the binding at a ground type, at or after the
% definition, everything it names declared by then
1 { callfile(F) : file(F) } 1.
1 { callty(T) : ty(T) } 1.
:- callty(T), gpat(G), not covers(G, T).
:- callfile(FC), deffile(FD), FC < FD.
:- callty(T), names(T, U), utfile(U, FM), callfile(FC), FM > FC.

% the STAMP's answer: most specific over the whole program at the
% caller's ground type (sound by Lemma 1)
capplies(I) :- active(I), headof(I, P), callty(T), covers(P, T).
covertaken(I) :- capplies(I), capplies(J), headof(I, P), headof(J, Q), morespec(Q, P).
cpick(I) :- capplies(I), not covertaken(I).
:- cpick(I), cpick(J), I != J.

viol :- epick(I), cpick(J), I != J.
:- not viol.

#show deffile/1.
#show gpat/1.
#show epick/1.
#show callfile/1.
#show callty/1.
#show cpick/1.
