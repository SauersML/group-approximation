---
rg: 2
id: thompson-f-hyperlinear-models-normalize-a-full-masa
kind: claim
title: If Thompson's F is hyperlinear, its HS microstates can be chosen to approximately normalize a full masa
distinct_from:
  hyperlinear-groups-admit-masa-normalizing-microstates: that asks for frame-coherent microstates for every hyperlinear group and needs the G * Z padding of hyperlinear-implies-sofic-via-frame-extraction; this is the single instance G = F, where no padding is needed because F already has no nontrivial abelian normal subgroup, and it can fail only if F is hyperlinear and nonsofic.
  hyperlinear-implies-sofic: that is Pestov's Question 3.4 for all groups; this is its instance at F only, rewritten as a frame-existence statement, and it is implied by that claim but not conversely.
  thompson-f-is-not-sofic: that is nonsoficity of F; this is the implication from hyperlinearity of F to soficity of F, which holds vacuously if F is not hyperlinear and says nothing about whether F is sofic.
---

**OPEN.** Suppose Thompson's group `F` is hyperlinear. Then for every finite
window `W ⊂ F` and every `ε > 0` there are `n`, unitaries `U_g ∈ U(n)`
(`g ∈ W`) and an orthonormal basis of `C^n` with diagonal masa `D_n` such that

```text
||U_g U_h - U_(gh)||_2 < ε,    |tr U_g| < ε  (g != e),    def_D(U_g) < ε,
```

with `def_D` as in `diagonal-normalizer-rigidity` and normalized trace and
Hilbert--Schmidt norm.

**Equivalent form (established here from established nodes).** This claim
holds exactly when "`F` hyperlinear implies `F` sofic", that is, when Pestov's
Question 3.4 has a positive answer at `F`.

- *Frames give soficity.* Apply `diagonal-normalizer-rigidity` clause 1 to each
  `U_g`: there is a monomial `w_g` with `||U_g - w_g||_2 <= 3 sqrt(ε)`. Then
  `||w_g w_h - w_(gh)||_2 <= ε + 9 sqrt(ε)` and `|tr w_g| <= ε + 3 sqrt(ε)`,
  because `|tr X| <= ||X||_2`. Along an ultrafilter this gives a homomorphism
  `ρ : F -> prod_ω U(1) wr S_n` with `τ(ρ(g)) = 0` for `g != e`, hence
  injective. By `block-monomial-hs-models-sofic-mod-amenable-soft-kernel`
  clause 3, its soft kernel `A` is an abelian normal subgroup of `F`, and by
  clause 1 `F/A` is sofic. A nontrivial normal subgroup of `F` contains `F'`
  (Cannon--Floyd--Parry, *Introductory notes on Richard Thompson's groups*,
  Theorem 4.3, as already cited in
  `thompson-f-weak-and-flexible-stability-are-nonsoficity-proof`), and `F'` is
  an infinite simple group (same notes, §4), so it is not abelian. Hence
  `A = 1` and `F` is sofic.
- *Soficity gives frames.* A sofic approximation with fixed-point density
  tending to `0` off the identity consists of permutation matrices. They
  normalize the coordinate masa exactly, so `def_D = 0` and the trace and
  multiplicativity bounds hold.

The general route `hyperlinear-implies-sofic-via-frame-extraction` pads `G`
to `G * Z` to kill abelian normal subgroups. At `F` the padding is not needed,
so the claim is the frame problem at the smallest candidate that is not
covered by any known permanence theorem.

**Why this node exists.** It is the exact missing step of every
entropy-measure transplant toward `thompson-f-is-not-hyperlinear`. Counting
and entropy obstructions (sofic entropy, Rokhlin-entropy maximality,
surjunctivity of cellular automata and of quantum cellular automata over
sofic groups, Kun--Thom nonsofic actions) take a finite set with an
approximate action as input. A unitary microstate supplies such a set only
through an approximately invariant frame. So such a method proves at most
`thompson-f-is-not-sofic`, and upgrades to non-hyperlinearity exactly through
this claim. See `thompson-f-not-hyperlinear-via-nonsoficity-and-frames` and
the entropy-measure attempt in `thompson-f-is-not-hyperlinear`.

**Kill test.** This claim is false iff `F` is hyperlinear and not sofic, which
would answer Question 3.4 negatively (`hyperlinear-nonsofic-from-thompson-f`).
So a refutation has the same difficulty as the separation, and a proof has at
least the difficulty of excluding it at `F`.

**Trust surface.** The two Cannon--Floyd--Parry facts are quoted from memory
of the standard notes and from the citation already in the graph, not re-read
from the PDF in this lane. The rest is a composition of established nodes.

## Attempts

1. **Easiest nontrivial case: exact finite-dimensional representations.**
   (lane swarm-0917-w2-nh-pull-1, 2026-09-17.) Every homomorphism
   `F -> U(n)` factors through `F/F' = Z^2`, so its image commutes and is
   jointly diagonalizable, giving `def_D = 0`. But such models have
   `|tr U_g| = 1` for `g ∈ F'`, so they are never regular. Regular models need
   dimensions tending to infinity with the images of `a` and `b` failing to
   commute by a definite amount in `||·||_2`
   (`thompson-f-commutator-bound-holds-in-each-fixed-dimension` records the
   fixed-dimension constants). The frame must then be coupled across two
   non-commuting generators, and joint spectral rounding
   (`all-abelian-uniform-hs-rounding-gives-global-pvm`) applies only to
   commuting families. Dies at that coupling step; no mechanism found.
2. **Disjoint-support abelian families (spark, not pursued).** The elements
   of `F'` supported in pairwise disjoint dyadic intervals (conjugates of one
   element supported in a small dyadic interval) commute and generate large
   abelian subgroups, and one could round a frame for them jointly.
   Every such family lies in a proper subgroup of infinite index, and the
   generator `x_0` moves supports between families. The approximate frame of
   one family is not approximately invariant under `U_(x_0)` without a further
   stability input, which is again this claim. Dies at the same coupling step.
