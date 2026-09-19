---
rg: 2
id: amenable-rep-of-kazhdan-has-fd-subrep
kind: claim
title: An amenable representation of a Kazhdan group has a finite-dimensional subrepresentation
distinct_from:
  no-invariant-mean-on-coset-space: that is about means on a coset space and uses the quasi-regular representation; this is about states on B(H) for an arbitrary representation and uses the Hilbert-Schmidt one
  hyperlinear-near-representation-criterion: that is Kahl-Schneider's equivalence for NEAR representations, imported by citation; this is a rigidity statement about GENUINE representations, proved here, and the contrast between them is the point
  haagerup-t-exclusion: that excludes Haagerup carriers as hosts for a diffuse (T) subalgebra; this constrains the representation theory of a (T) group directly
artifacts:
  - notes/TRUE_CHARGE_EXTENSION_NEEDS_COAMENABILITY.md
---

Let `G` have property (T) and let `π : G → U(H)` be a unitary representation
that is amenable in Bekka's sense — there is a state `m` on `B(H)` with
`m(π(g)Aπ(g)^*) = m(A)`. Then `π` has a nonzero finite-dimensional
subrepresentation.

Proof (Proposition 3 of the artifact): normal states are weak-\* dense and
`Ad π` preserves them, so Day's trick gives density operators `ρ_i` with
`‖π(g)ρ_iπ(g)^* − ρ_i‖₁ → 0`; Powers–Størmer
(`‖a^{1/2} − b^{1/2}‖₂² ≤ ‖a − b‖₁`) turns these into almost invariant unit
vectors `ρ_i^{1/2}` of `Ad π` on `HS(H) ≅ H ⊗ H̄`; property (T) gives a nonzero
invariant `T ∈ HS(H)`, i.e. `T ∈ π(G)'`; and `T^*T` is a nonzero positive
trace-class operator in `π(G)'`, so a spectral projection `1_{[λ,∞)}(T^*T)` is
a nonzero finite-rank projection commuting with `π(G)`.

## Provenance

**The primary sources were not read** — Springer authentication wall — so the
statement is proved above rather than cited, from ingredients that are all
standard and none of them specific to this problem. The node was created
because a flagged-but-unread citation is not usable under the doctrine, and
deriving it was cheaper than obtaining it.

**Attribution, corrected.** An earlier version of this section credited the
statement to Bekka, *Amenable unitary representations of locally compact
groups*, Invent. Math. 100 (1990) 383–401. That is the wrong paper.
`cairn-scout` located the dichotomy as Bekka–Valette, *Kazhdan's property (T)
and amenable representations*, Math. Z. 212 (1993) 293–299, Theorem 1; Bekka's
1990 Theorem 5.1 is the separate equivalence "`π` amenable ⟺ `π ⊗ π̄` weakly
contains `1`", which is what makes the two statements look like one. See
`bekka-valette-amenable-t-dichotomy` for the verbatim record and its trust
surface. Bekka–Valette is also **stronger** than what is proved here: it is a
dichotomy, giving the converse direction (a group lacking (T) admits an
amenable representation with no nonzero finite-dimensional subrepresentation).
Only the direction stated above is established in this repository.

## Consequence for the charge lane

Kahl–Schneider characterize hyperlinearity by an essentially free amenable
**near** representation. If `π` were an essentially free amenable **genuine**
representation of `W`, restricting the invariant state to `G ≤ W` makes `π|_G`
amenable, and `G` is Kazhdan by Kun–Thom Theorem E, so `π|_G` would have a
nonzero finite-dimensional subrepresentation. That is exactly the regime where
this repository's rigidity results bite: `Criterion/CommutantRigidity.commutant_no_growth`
collapses the relative commutant for genuine finite-dimensional
representations, and `Criterion/ExactCompression.fixedSubmodule_map_eq` supplies
the invariant size (`finrank`) that `no_strict_compression_of_invariantSize`
consumes.

So the genuine case is rigid, and the whole content of the criterion for `W`
sits in the gap between *near* and *genuine*.

**Correction (2026-08-14).** An earlier version of this paragraph went on to
conclude that the charge lane is therefore *not* independent of the rigidity
branch — that it is "independent exactly to the extent that flexibility is, and
no further". That inference was wrong and is retracted. It assumed that
flexible HS-stability of `G` would let one replace an amenable near
representation by a genuine one and then apply the theorem above. It does not.
Amenability is the existence of an invariant **state on `B(H)`**, and states are
continuous for the operator norm, not for `‖·‖₂`; flexible HS-stability supplies
only Hilbert–Schmidt closeness. So invariance of the state does not transfer
along the perturbation, and there is no route from the theorem above to a
refutation of the near version.

That is a sharper reason for the lane's survival than the observation that
Bekka–Valette is a statement about homomorphisms and a near representation is
not one. The latter says the theorem does not apply; the former says no repair
is available either, because amenability and near-ness are measured in
incompatible topologies — amenability at the operator-norm scale, near-ness at
the trace scale. The two lanes really are independent, and `cairn-scout` was
right to report so.

What is genuinely open, and is the pivot: whether a near-representation
analogue of the dichotomy holds (`near-representation-amenability-dichotomy`).
If one does, the independence evaporates. Nothing read on either side bears on
it.
