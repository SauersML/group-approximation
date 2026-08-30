---
rg: 2
id: stw99-problem-lxxii-weakly-purely-infinite
kind: claim
title: Weakly purely infinite, purely infinite, and strongly purely infinite coincide (STW Problem LXXII)
root: true
distinct_from:
  stw99-problem-lxxiv-infinite-projections-purely-infinite: that asks whether a unital simple algebra all of whose nonzero projections are infinite is purely infinite; this is the Kirchberg--Rordam question whether the weak, plain, and strong forms of pure infiniteness coincide for all (nuclear) C*-algebras, with the weak-to-plain implication as the open heart.
artifacts:
  - research/artifacts/stw99-lxxii-weakly-pi-recon-2026-08-30.md
  - research/artifacts/stw72-finite-ideal-lattice-collapse-audit-2026-08-30.md
  - research/artifacts/stw72-transfinite-composition-collapse-audit-2026-08-30.md
---

**Problem LXXII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Kirchberg--Rørdam, Question 9.5 of the AIM paper).  Do weakly purely
infinite, purely infinite, and strongly purely infinite coincide for all
(nuclear) C\*-algebras?

In Cuntz-semigroup terms, `A` is weakly purely infinite iff there is `n`
with `n·x = ∞·x` for every `x ∈ Cu(A)`, and purely infinite iff `n = 1`
works, i.e. `Cu(A)` is the ideal lattice.  Kirchberg--Rørdam: `A` is
purely infinite iff it is weakly purely infinite and has the Global Glimm
Property, so the open implication (weak ⟹ plain) is exactly the Global
Glimm Problem (`stw99-problem-lxxiii`-territory; Vilalta's survey
Corollary 3.10) restricted to traceless algebras, and by
Thiel--Vilalta's Theorem 7.1 it is equivalent to: the Cuntz semigroup of
every weakly purely infinite algebra is ideal-filtered and has property
(V).  Weakly purely infinite algebras have no dimension functions
(`n·x = ∞·x` forces `d(x) ∈ {0, ∞}`), so no functional obstruction to the
collapse exists; all residual structure is ideal-theoretic.

## Attempts

See the recon artifact.  (1) Property (V) near-miss: given
`d'_j ≪ d_j ≪ c` and `c + d_j ≪ x`, choosing `c' ≪ c` with
`d_1, d_2 ≤ k c'` and `d'_1 ≪ d''_1 ≪ d_1` gives `y := c'`, `z := d''_1`
with `y + z ≤ c + d_1 ≤ x` and `d'_1 + d'_2 ≤ ∞y`; everything holds
except the single containment `d'_2 ≤ ∞z`, i.e. the join of `d_1, d_2`
must fit beside `c` inside `x` — precisely the sup-semilattice defect
that pure infiniteness would provide, so this route is a faithful
reformulation, not a shortcut.  (2) Ideal-filteredness reduces to: for
`a_1, a_2` and `b` full in `Ideal(a_1) ∩ Ideal(a_2)`, find one `c_0` with
`c_0 ≾ a_1`, `c_0 ≾ a_2` and `(b − ε)_+ ∈ Ideal(c_0)`; the element
`c_0 = a_2^{1/2} X a_2^{1/2}` with `X ∈ her(a_1)_+` satisfies both
subequivalences for free (`c_0 ≤ ‖X‖ a_2` and
`c_0 ~ X^{1/2} a_2 X^{1/2} ≤ ‖a_2‖ X ≾ a_1`), and only the position of
`her(a_1)` against `a_2` obstructs the ideal condition (an `M_2(C_0(U))`
example makes the product vanish while the ideals overlap; rotations
repair it there).  Kirchberg--Rørdam absorption (`b ∈ Ideal(c_0)` gives
`b ≾ n c_0 = ∞ c_0` in weakly purely infinite algebras) then completes
`v' ≪ ∞z`.  So ideal-filteredness for weakly purely infinite algebras is
exactly a position/rotation problem for hereditary subalgebras, with no
size obstruction.

The position obstruction vanishes completely when the closed ideal lattice
is linearly ordered.  Weak pure infiniteness rules out finite-dimensional
representations, so `chain-ideal-lattice-solves-lxxiii` supplies the Global
Glimm Property; Kirchberg--Rordam then gives pure infiniteness.  This proves
LXXII for all chain-ideal algebras
(`stw72-chain-ideal-wpi-is-purely-infinite`).

There is now a transverse positive class allowing incomparable ideals.  If
the full closed ideal lattice is finite, a maximal ideal chain has simple
successive subquotients.  Weak pure infiniteness passes to ideals and
quotients, the simple layers fall under the chain theorem, and
Kirchberg--Rordam extension permanence glues the purely infinite layers.
Thus weak and plain pure infiniteness coincide for every finite-ideal-lattice
algebra (`stw72-finite-ideal-lattice-wpi-is-purely-infinite`).

The finite filtration argument extends through arbitrary ordinals.
`stw72-transfinite-simple-layer-wpi-is-purely-infinite` proves the collapse
whenever `A` admits a continuous transfinite composition series with simple
successor quotients.  Successor stages use extension permanence of plain
pure infiniteness, and limit stages use its permanence under directed
injective C-star inductive limits.  This is nonvacuous beyond finite or chain
ideal lattices: `c_0(alpha,O_infinity)` has such a series for every nonzero
ordinal `alpha` and has many incomparable ideals when `alpha` is infinite.

The filtration hypothesis now has an intrinsic topological source.
`stw72-scattered-primitive-spectrum-wpi-is-purely-infinite` proves the
weak-to-plain collapse whenever `Prim(A)` is topologically scattered.  One
recursively adjoins an isolated point of the remaining primitive spectrum;
the corresponding successor subquotient has one-point primitive spectrum
and is simple.  This permits non-Hausdorff spectra of arbitrary cardinality
and arbitrarily non-linear ideal lattices.
