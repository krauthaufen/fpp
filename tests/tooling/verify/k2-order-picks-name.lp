% K2 (expect an example). The undecorated key goes to whichever count is
% SEEN FIRST, and "first" is file order — so reordering files renames a
% type, and the emitted module's symbols move with it. The self-build
% comparison cannot catch this: both stages read the files in the same
% order. Known and tolerated; this check keeps it VISIBLE, and turns
% into a regression alarm if a later change accidentally makes keys
% depend on order in some NEW way (the witness would change shape).
#include "keys.lp".
viol :- key(D, fwd, K1), key(D, rev, K2), K1 != K2.
:- not viol.
