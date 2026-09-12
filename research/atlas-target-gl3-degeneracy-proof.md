---
rg: 2
id: atlas-target-gl3-degeneracy-proof
kind: route
title: Identify the target Steinberg star with simultaneous GL3 basis change
target: atlas-target-gl3-preserves-the-fifteen-type-degeneracy
requires:
  - atlas-three-transverse-shears-leave-fifteen-character-types
  - atlas-steinberg-rank-five-translation
---

For distinct `1,r,s`, Steinberg (St3) gives `(TGL2)`, while (St2) says
`R_rs` fixes every `D_(t,a)` with `t` outside the affected pair.  Since all
roots have order two, `(TGL2)` is equivalent to the conjugation formula
`(TGL3)`.

The elementary transvections `I+E_rs`, `r!=s`, generate
`SL_3(F_2)=GL_3(F_2)`.  Their conjugation action on each of the three target
coefficient vectors is the same natural basis-change action.  Passing to
characters gives the contragredient action, which is still an invertible
simultaneous linear change and proves `(TGL4)`.

If `u` is zero, equal to `w`, or linearly independent from `w`, the same is
true of `g u,g w` for every invertible `g`.  This proves invariance of the
degeneracy test.  Transitivity of `GL_3(F_2)` on the seven nonzero vectors
gives the three strata and the counts in `(TGL6)--(TGL7)`.

The target roots `R_rs` have indices wholly inside `{3,4,5}`.  Steinberg
(St2) therefore makes them commute with the source roots at `(1,2)`.  They
cannot change which of `x_12(p),x_12(q)` is negative.  On a degenerate type,
the source-shear calculation already says every marked-preserving shear word
also fixes that orientation.  A word alternating target basis changes and
source shears can be rewritten in the semidirect product normal form; basis
changes only replace `(u,w)` simultaneously and never change the source
orientation.  Thus the two marked orientation orbits remain disjoint.

Finally, the orbit projections in the finite permutation representation are
invariant under the full semidirect packet, proving the exact local
countermodels.  This does not include rows with coefficient `e,f,E,F` on
`x_rs`; those are precisely the next untested family.
