# gq-germ-design board
**Approach:** family germ-extensions/host geometry; sig "SL_3(Z) versus normal-germ extensions of V"; first
falsifiable step (done in writing): FW on the BHM germ complex K puts a finite-index SL_3(Z) into SingFix(M,M'),
Margulis NST makes its germ map to prod_{p in M}(G)_p injective; in the Cor-2.10 regime (germs normalize (V)_p
at rational p, or finite index) germ groups are abelian-by-(subgroups of V) -> contradiction via Higman.
**Established (landed 1b0b067f9, not independently reviewed):** normal-germ-extensions-of-thompson-v-contain-no-sl3z (+ -proof):
 (A) any finite germ extension of V_{d,r} containing a finite-index SL_3(Z) has a torsion-free finite-index
     Gamma_1 embedded in a FINITE PRODUCT OF GERM GROUPS; (B) impossible if every singular p has
     |(G)_p:(V)_p|<inf or (p rational and (V)_p normal in (G)_p). Covers VA, bounded-automata RN groups.
 => GL_n(Q), n>=3, lies in no such germ extension. Also: normal-regime germ groups contain no BS(1,2).
**Needs:** nothing.
**Dead:** VA-pattern germ extensions of V_{d,r} (germs commuting with the local dilation) for GL_n(Q), n>=3.
**Sparks:** a host for n>=3 needs APERIODIC germ groups (not normalizing the dilation) whose finite products
 contain SL_3(Z[1/m]) virtually -- shell-type germs; nV bases not covered (gq-nv-obstruct).
