% LEMMA 1 (expect UNSAT). Under the orphan rule and declare-before-use, a
% GROUND selection made with only the instances visible at the use agrees
% with the whole program's — there is no program in the bounded universe
% where they differ. This is the lemma the compiler's deferral rests on:
% an open match may wait for the stamp because once the argument is
% ground, waiting has nothing left to see.
#include "domain.lp".
#include "program.lp".
#include "orphan.lp".
#include "ground-use.lp".
