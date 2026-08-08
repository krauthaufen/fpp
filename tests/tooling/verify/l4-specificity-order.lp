% LEMMA 4 (expect UNSAT). "Strictly more specific" is a strict partial
% order on the bounded pattern universe — irreflexive, asymmetric,
% transitive. Rule 2's "unique most-specific match" is only well defined
% because of this.
#include "domain.lp".
viol :- morespec(P, P).
viol :- morespec(P, Q), morespec(Q, P).
viol :- morespec(P, Q), morespec(Q, R), not morespec(P, R).
:- not viol.
#show viol/0.
