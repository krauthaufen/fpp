% K1 (expect nothing found). The decoration's whole purpose: two
% declarations of the SAME name at DIFFERENT argument counts never share
% a key, whatever the file order. Before the decoration existed they DID
% share one — two IOpReader arities shared a layout and a five-line
% program died with `missing field`.
#include "keys.lp".
viol :- key(D1, W, K), key(D2, W, K), named(D1, N), named(D2, N),
        arityof(D1, A1), arityof(D2, A2), A1 != A2.
:- not viol.
