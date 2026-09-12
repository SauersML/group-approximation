---
rg: 2
id: stw99-problem-lxxxvii-roe-algebra-nuclear-dimension
kind: claim
title: Nuclear dimension of the uniform Roe algebra equals asymptotic dimension (STW Problem LXXXVII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
  - research/artifacts/stw87-invariant-mean-retraction-audit-2026-08-30.md
  - research/artifacts/stw87-z2-boundary-limit-operator-audit-2026-08-30.md
  - research/artifacts/stw87-minimal-boundary-dimension-collapse-audit-2026-08-30.md
  - research/artifacts/stw87-diagonal-bimodular-localization-no-go-audit-2026-08-30.md
---

**Problem LXXXVII of Schafhauser--Tikuisis--White, arXiv:2506.10902** (Willett--Winter, [449, Question 9.5]).  For a
countable discrete bounded-geometry metric space `X`, is
`dim_nuc(C*_u(X))` equal to the asymptotic dimension of `X`?

Asymptotic dimension is an upper bound (Willett--Winter).  Finite-valued
positive answers are known only in asymptotic dimension zero (equivalently
`C*_u(X)` AF) and one; even `X = ℤ²` is open, and STW record that at least one
author expects a negative answer.  Li--Liao--Winter's diagonal dimension of
`ℓ^∞(X) ⊆ C*_u(X)` does equal the asymptotic dimension, so the question is
whether nuclear dimension sees the diagonal.

The equality is also automatic, with both sides infinite, when `X` does not
have property A.  Thus the unresolved cases split into finite asymptotic
dimension at least two and property-A spaces of infinite asymptotic dimension.
A search of primary-source title/abstract records through 2026-08-30 found no
later theorem settling either part.

## Attempts

Winter--Zacharias prove the upper bound.  Li--Willett prove the reverse
implication at asymptotic dimension zero, which together with the upper bound
also settles value one.  Sako's equivalence between property A and nuclearity,
combined with the Winter--Zacharias bound and the fact that finite nuclear
dimension implies nuclearity, settles every space without property A at the
value infinity.

For a subset `Y ⊆ X`, compression by `χ_Y` identifies the corner
`χ_Y C*_u(X) χ_Y` with `C*_u(Y)`.  Nuclear dimension therefore gives a
monotone lower-bound mechanism from subspaces, but no seed with nuclear
dimension at least two is presently known.  This mechanism now extends from
subspaces to arbitrary coarse embeddings: after uniformly labelling the
finite fibres, `C*_u(Y)` is a diagonal hereditary corner of a finite matrix
amplification of `C*_u(X)`
(`stw87-coarse-embedding-corner-lower-bound`).  Thus equality propagates from
any coarsely embedded full-asymptotic-dimension seed, and unbounded
nuclear-dimension seeds force infinite nuclear dimension.  Finally, the
canonical diagonal expectation has exact distance `1/2` from every diagonal
c.p.c. order-zero repair on a fixed two-point *-homomorphism.  Thus
diagonal-dimension equality cannot be converted to the missing lower bound by
averaging arbitrary nuclear approximations, even followed by an arbitrarily
small order-zero perturbation.  There is a complementary maximal obstruction:
every order-zero map from a noncommutative matrix algebra into the diagonal is
zero, and the diagonal expectation on a canonical finite matrix corner has
exact distance one from all such maps
(`stw87-diagonal-order-zero-maps-annihilate-matrix-colours`).  Hence diagonal
averaging cannot retain any noncommutative colour at all.

Property-A metric localization does not bypass this firewall.  The diagonal
expectation is the unique bounded diagonal-bimodule retraction, and every
normalized diagonal-bimodular Schur localization `S` satisfies `E_X S=E_X`.
Consequently even finite-propagation Schur localization before averaging
leaves the exact one-half and one order-zero gaps unchanged
(`stw87-diagonal-bimodular-localization-no-go`).  Any successful cover
extraction must therefore either retain genuinely non-diagonal support
information or leave the normalized diagonal-bimodular framework by a
macroscopic amount.
This obstruction is stable: any diagonal-valued c.p.c. map retaining the
commutative packet as order zero has combined diagonal-fixing and
singleton-corner bimodularity defect at least `1/2`, while retaining a matrix
packet forces defect at least `1`
(`stw87-approximate-diagonal-bimodularity-order-zero-threshold`).

For amenable groups there is another natural attempt: an invariant mean
averages crossed-product coefficients and gives a conditional expectation
`C*_u(G)->C*_r(G)`.  This does not recover quotient permanence.  If `G` has
a subgroup of index `k>=2`, the expectation sends the `k` orthogonal coset
projections to the common scalar `1/k`, at exact distance `1/k` from every
c.p.c. order-zero repair (`stw87-invariant-mean-retraction-has-coset-order-zero-gap`).
Thus even the canonical retraction `C*_u(Z^d)->C(T^d)` cannot directly
transfer nuclear-dimension colours to the group algebra.

For `Z^2`, boundary and limit-operator quotients do not repair this defect.
`stw87-z2-has-no-periodic-boundary-quotient` proves that the translation
action on `beta Z^2` is free, so there is no finite boundary orbit, no
periodic coefficient quotient, and no star-homomorphic retraction
`C*_u(Z^2)->C(T^2)` fixing the group unitaries.  Conversely every boundary
limit representation retains, for every finite-index `H<Z^2`, a subalgebra
`C(Z^2/H) crossed_product Z^2 ~= M_[Z^2:H](C(T^2))`.  These blocks carry the
expected rank-two topology but only as arbitrary subalgebras; nuclear
dimension is not upward monotone from them.  Thus limit operators and Bott
classes expose the correct two-dimensional core without giving it the
quotient or hereditary variance needed for the missing lower bound.

Passing from the full boundary to a minimal subsystem loses even more
information.  Every minimal closed invariant `M subset beta Z^d` gives a
canonical quotient

```text
C*_u(Z^d) ->> C(M) crossed_product_r Z^d
```

whose nuclear dimension is exactly one, for every `d>=1`
(`stw87-zero-dimensional-minimal-actions-have-dimension-one`).  The proof
preserves freeness and minimality in metrizable zero-dimensional factors,
collapses each separable factor's finite nuclear dimension to at most one,
and extends the incoming c.p.c. maps back to the full quotient; a Pimsner--
Voiculescu index excludes zero.  The theorem in fact applies to every infinite
finitely generated virtually nilpotent group with infinite abelianization, a
class strictly larger than the nilpotent groups; without the abelianization
hypothesis it still gives nuclear dimension at most one for every infinite
finitely generated virtually nilpotent group.  There is also a genuinely new
finite-abelianization equality case: every free minimal zero-dimensional
`D_infinity` crossed product has nuclear dimension one.  Pimsner's
free-product exact sequence forces either nonzero `K_1` or nonzero two-torsion
in `K_0`, so dimension zero is impossible although
`(D_infinity)_ab=C_2 direct_sum C_2`.  These maps already factor
through the uniform Roe corona.  Thus for every such group of asymptotic
dimension at least two, no minimal boundary quotient can carry the desired
full-dimensional nuclear-dimension lower bound.  Nonminimal quotients and
genuinely ambient lower-bound invariants remain open.

The parity computation now closes every infinite virtually cyclic group,
not only `D_infinity`.  By the standard type dichotomy, such a group either
maps onto `Z` with finite kernel or has an amalgam decomposition
`G_1 *_F G_2` with finite vertex groups and both indices equal to two.
The first case is PV; in the second, Pimsner's map is again the pair of
two-sheet orbit sums.  The same torsion-versus-odd-kernel alternative proves
`stw87-virtually-cyclic-actions-have-dimension-one`.  Hence all free minimal
zero-dimensional virtually cyclic crossed products have nuclear dimension
exactly one, including finite dihedral extensions with finite abelianization.
