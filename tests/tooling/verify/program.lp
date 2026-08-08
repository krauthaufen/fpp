% A GUESSED program over the bounded universe: the solver searches every
% placement of instances, user-type declarations, and a use across
% ordered files. One class, declared in file 1 (w.l.o.g.); each user
% type declared in exactly one file; each instance a head in a file.

#const nfiles = 3.
#const ninsts = 3.

file(1..nfiles).
classfile(1).
1 { utfile(U, F) : file(F) } 1 :- ut(U).

inst(1..ninsts).
{ active(I) } :- inst(I).
1 { headof(I, P) : pat(P) } 1 :- active(I).
1 { fileof(I, F) : file(F) } 1 :- active(I).
% duplicate heads add nothing to these properties
:- active(I), active(J), I < J, headof(I, P), headof(J, P).

% declare-before-use: a head naming a user type cannot precede it
:- headof(I, P), pmentions(P, U), fileof(I, F), utfile(U, FM), F < FM.

#show utfile/2.
#show headof/2.
#show fileof/2.
