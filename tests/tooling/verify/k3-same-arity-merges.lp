% K3 (expect an example). Two DISTINCT declarations — same name, same
% argument count, think different files — share one key. Deliberate:
% it is how a user type merges with its prelude namesake. Also the
% residual hazard: two unrelated private types of the same shape merge
% the same way, and nothing warns. If that hazard is ever closed (a
% same-key-different-site diagnostic), this check flips and says so.
#include "keys.lp".
viol :- key(D1, W, K), key(D2, W, K), D1 != D2.
:- not viol.
