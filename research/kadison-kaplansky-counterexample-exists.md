---
rg: 2
id: kadison-kaplansky-counterexample-exists
kind: claim
title: Some torsion-free group has a nontrivial projection in its reduced group C*-algebra
distinct_from:
  algebraic-strong-atiyah-counterexample-exists: that seeks a non-integral von Neumann kernel dimension for a matrix over K[G]; this seeks a projection other than 0 and 1 in C*_r(G), equivalently a self-adjoint element of Z[i][G] whose spectral measure has a gap.
  kadison-kaplansky-torsion-free: that is the universal conjecture; this is its negation, the target a counterexample construction must establish.
---

**Target.** There is a countable torsion-free group `G`, necessarily one for
which Baum--Connes assembly is not surjective, such that `C*_r(G)` contains a
projection other than `0` and `1`.

**Finite witness form**, by `reduced-projection-iff-gapped-spectral-measure`:
- a finitely generated torsion-free group `G`;
- a self-adjoint `a` in `Z[i][G]`, and reals `c`, `eps > 0`, such that the
  reduced spectrum of `a` misses `(c - eps, c + eps)` and meets both sides.
Equivalently, the spectral measure `mu_a` of `a` for the canonical trace has
support meeting both `(-inf, c - eps]` and `[c + eps, inf)`, and gives
`(c - eps, c + eps)` measure zero. The projection is then `chi_(-inf,c)(a)`, of
trace `mu_a((-inf, c))` in `(0,1)`.

A sum-of-squares identity in `C[G]` certifies the gap only in `C*_max(G)`. The
two-sided reduced mass is the part that uses the regular representation.

## Attempts

- **Hosts that are ruled out:** groups with torsion-free assembly surjectivity
  (Kaad--Proietti). This covers a-T-menable groups, hyperbolic groups and
  real-rank-one lattices.
- **Characteristic-p Kun--Thom actors: dead,** because they are not torsion-free.
  Details on `kadison-kaplansky-torsion-free`.
- **Compressions and Kazhdan projections: dead.**
  - Compressions give only trace-preserving endomorphisms, and every isometry in
    `M_n(C*_r(G))` is unitary.
  - Kazhdan projections vanish in `C*_r(G)` for infinite `G`.
- **Candidate hosts with no mechanism:**
  - torsion-free Kazhdan groups where Baum--Connes is open: Fournier--Facio's
    group, and torsion-free finite-index subgroups of `EL_3(Z[x_1,...,x_d])`;
  - the spectral measures that the determinant and Atiyah lanes compute over
    nonsofic groups.
  In each case the attempt dies at the same point: nothing forces a gap in
  `supp mu_a`.
