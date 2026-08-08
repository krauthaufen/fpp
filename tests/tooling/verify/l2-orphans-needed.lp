% LEMMA 2 (expect SAT). The SAME check as l1 with the orphan rule
% removed: the solver finds the program where visible and whole-program
% selection disagree. The witness it prints is the bug found by hand
% first — a general instance with its class, a more specific orphan in a
% later file, one program answering two ways (ClassTests "an orphan
% instance is rejected" is its compiled form).
#include "domain.lp".
#include "program.lp".
#include "ground-use.lp".
