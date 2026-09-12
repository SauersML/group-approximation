---
rg: 2
id: amenable-full-group-forces-invariant-measure
kind: claim
title: An amenable group realizing a groupoid's moving bisections forces an invariant probability measure
distinct_from:
  fp-infinite-simple-amenable-group: That is the open existence question; this is an obstruction that removes compressible groupoid hosts from it.
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

**ESTABLISHED.** Let `G` be an effective, Hausdorff, ample groupoid with compact
unit space `X`, in which every orbit has at least three points. Let
`Gamma <= Homeo(X)` realize moving bisections: for every compact open bisection
`U` and every `x` in `s(U)` with `U(x) != x`, some `gamma` in `Gamma` agrees with
`U` on a clopen neighbourhood of `x`.

1. `D([[G]])` realizes moving bisections, and so does every group containing
   it. A 3-cycle `E -> U(E) -> VU(E)` is the commutator of two involutions of
   `[[G]]`.
2. If `Gamma` is amenable, then `X` carries a `G`-invariant Borel probability
   measure: `mu(U(E)) = mu(E)` for all compact open bisections `U` and Borel
   `E ⊆ s(U)`.
3. **Corollary.** Suppose `G` is minimal, and some nonempty clopen `A` contains
   disjoint clopens `B` and `C` with compact open bisections from `A` onto each.
   Then no group realizing moving bisections is amenable; in particular
   `[[G]]` and `D([[G]])` are not.
4. **Example.** For the one-sided SFT groupoid of an irreducible 0-1 matrix that
   is not a permutation matrix, there is no invariant measure. An invariant
   measure would give a nonnegative eigenvector with eigenvalue 1, contradicting
   Perron--Frobenius. So Matui's finitely presented simple full groups are not
   amenable.

The proofs are in the artifact, Section 2. They use a Markov--Kakutani fixed
point, realization on small clopen pieces, a detour through a third orbit point
at germs `U` fixes, and compactness. The result is standard; no novelty is
claimed.
