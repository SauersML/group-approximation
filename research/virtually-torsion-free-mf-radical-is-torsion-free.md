---
rg: 2
id: virtually-torsion-free-mf-radical-is-torsion-free
kind: claim
title: A virtually torsion-free group has torsion-free MF radical, so no finite-subgroup augmentation corner of it carries a no-CE algebra
distinct_from:
  virtually-torsion-free-infinite-mf-radical-gives-seed: that proves the dichotomy and the seed from case 2; this shows the radical in case 2 is torsion-free and meets W(H) trivially, so the corner-form corollary there has an empty hypothesis.
  mf-null-corner-criterion-needs-faithful-ce-trace: that constrains where MF-nullity can live over a hyperlinear host; this needs no hyperlinearity, only one finite quotient that sees K.
  torsion-free-seeds-need-kernel-descent-or-trace-corner: that shows a derivation must use both a torsion conclusion and the finite-index trace; this shows the two can never be applied in the same virtually torsion-free host.
artifacts:
  - research/mf-positive-controls.md
  - research/virtually-torsion-free-host-no-ce-augmentation-corner.md
---

**ESTABLISHED, NO PROPERTY `(T)`.**  Let `H` be any countable group.

**(R1) The radical lies in the finite residual.**  For every normal subgroup
`N` of finite index in `H`, `Rad_MF(H) <= N`.

**(R2) Torsion-freeness.**  If `H` has a torsion-free subgroup `E` of finite
index, then `Rad_MF(H) <= Core_H(E)`.  In particular `Rad_MF(H)` is
torsion-free and meets the finite radical `W(H)` trivially.

**(R3) No corner.**  Let `H` be virtually torsion-free, `1 != K <= H` finite,
and `q_K = 1 - |K|^-1 sum_(k in K) k`.  Then no unital star algebra `B` with
no Connes-embeddable tracial state admits a unital star homomorphism
`Phi : B -> q_K C[H] q_K` with `Phi(1) = q_K`.  More generally, every unital
star homomorphism `B -> q_K C[H] q_K` makes `B` carry a tracial state that
factors through a matrix algebra.

**Consequences.**

1. `virtually-torsion-free-host-no-ce-augmentation-corner` is false for
   every host, every finite `K != 1` and every no-CE algebra `B`.  The
   condition "K not in W(H)" is irrelevant.
2. So `property-t-free-seed-via-virtual-torsion-corner` is dead.
3. In case 2 of `virtually-torsion-free-infinite-mf-radical-gives-seed`,
   `Rad_MF(H)` is an infinite torsion-free normal subgroup contained in every
   finite-index normal subgroup.  Its Corollary (corner form) never applies:
   every torsion conclusion `K <= Rad_MF(H)` in a virtually torsion-free host
   forces `K = 1`.
4. The same death applies to any "MF-null corner transplant".  Take an
   algebra `B` with no nonzero star representation into a norm-matrix
   corona, for example a Leavitt involution corner `q_t C[G] q_t` if it is
   MF-null.  `B` cannot map unitally into `q_K C[H] q_K` for virtually
   torsion-free `H`, because `(R3)` gives it a matrix representation.

**Invariant and death step.**  The invariant is the finite quotient
`H/Core_H(E)`, into which every finite subgroup injects.  Every candidate dies
at the first step: its left-regular representation is a finite-dimensional
unitary representation that is faithful on `K`.
