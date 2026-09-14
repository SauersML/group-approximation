---
rg: 2
id: thompson-f-is-sofic
kind: claim
title: Thompson's group F is sofic
refuted_by:
  - thompson-f-is-not-sofic
distinct_from:
  thompson-f-is-amenable: that is amenability, which implies this claim; a nonamenable F could still be sofic.
  thompson-v-is-sofic: that is soficity of V, which implies this claim because F <= V; the converse is not known.
---

**OPEN.** Thompson's group `F` embeds in the universal sofic group.

**Equivalent forms** (`thompson-f-sofic-iff-relator-system-unstable`):
- some almost-homomorphism of `F` has a fixed-point character with a regular component;
- there are `epsilon > 0` and permutation pairs `(A_n, B_n)` that satisfy both relators of `F` up to
  `delta_n -> 0` in normalized Hamming distance while `d(A_n B_n, B_n A_n) >= epsilon`.

Exact solutions commute, since finite quotients of `F` are abelian. So the second form must exploit the
error.

## Attempts

- Through `thompson-f-sofic-from-amenability` (waits on `thompson-f-is-amenable`) and `thompson-f-sofic-from-v-sofic` (waits on `thompson-v-is-sofic`). The equivalent almost-commuting form is in `research/artifacts/thompson-f-soficity-as-relator-stability-2026-09-12.md`, section 3.
- **Local embeddability into amenable groups collapses (2026-09-13).** `F` is finitely presented and every proper
  quotient is abelian, so a local embedding of a ball containing both relators and `[a,b]` into an amenable group
  is an injective homomorphism. So `F` is LEA only if amenable (`thompson-f-is-lea-only-if-amenable`), and LEA is
  not an independent soficity route.
- **Spatial permutation models almost commute (2026-09-13).**
  - **Bound.** Suppose a pair follows `F` acting on points, intervals, finite configurations or the Cantor set on all
    but a `δ` fraction of points. Then `d(AB,BA) ≤ 4δ + k sqrt(6δ)` (`thompson-f-spatial-permutation-models-almost-commute`).
  - **Consequence.** Truncated dyadic-tree models, reservoir or depth-shuffle repairs, and the Følner windows of
    `thompson-f-end-rigid-schreier-graphs-are-amenable` cannot witness this claim.
  - **Exact profiles** (`research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md`):
    - truncations keep `δ ≈ 1/4` and relator defect `≥ 0.53`;
    - `x_0`-rays drive defect and separation to 0 together;
    - perturbed commuting pairs pay about twice their separation in defect.
  - **Gap.** A witness with separation `ε` must be `min(ε/8, ε²/(24k²))`-far from following every such action.
- **Following models reduce to invariant means (2026-09-13).**
  - **Equivalence.** Models following an `F`-set with error `→ 0` separate the commutator exactly when some invariant
    mean on that `F`-set charges `Moved(c)`. Every such mean gives all nontrivial elements of `F'` the same moved mass,
    and makes slabs over the interval null (`thompson-f-following-models-separate-iff-mean-charges-commutator`).
  - **Collapse.** On pointwise stabilizers of finite unions of intervals with interior, including the end-rigid cosets
    `F_[0,a]` and `F_[a,1]`, and on `F/H` for amenable `H`, such means exist only if `F` is amenable
    (`thompson-f-interval-stabilizer-cosets-separate-only-if-amenable`).
  - **Gap.** A following witness needs a non-amenable co-amenable subgroup outside these families, or infinitely many
    orbit types. Models following no `F`-set are untouched (`research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md`).
- **Following witnesses are exactly mean-free amenable actions (2026-09-13).**
  - **Dichotomy.** For every invariant mean on every `F`-set, the stabilizer IRS is `t·δ_{e} + (1-t)μ_0`,
    where `t = m(Moved(c))` and `μ_0` lives on subgroups containing `F'`. On `Moved(c)` every nontrivial
    element of `F` fixes a null set (`thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`).
  - **Consequence.** A witness by permutation models that follow an `F`-set exists exactly when `F`
    admits a mean-free amenable action: an `F`-set with an invariant mean and `m(Fix(g)) = 0` for all
    `g ≠ e`. Truncations of non-amenable Schreier graphs keep the error at least `h/4`.
  - **Gap.** Is there a mean-free amenable action of `F`? Residually finite groups have one through
    finite quotients, and `F` has only abelian ones. Orbits must have stabilizers shrinking to `{e}`,
    e.g. configuration spaces with unboundedly many points.
- **Mean-free amenable actions are not disguised amenability (2026-09-13).**
  - **General facts.** Residually amenable groups, `F_2` among them, admit mean-free amenable actions.
    The property passes to subgroups and implies soficity, and invariant means of a nonamenable group
    are null on points with amenable stabilizers (`mean-free-amenable-actions-residually-amenable-and-sofic`).
    Under a Kazhdan pair it is equivalent to residual finiteness
    (`kazhdan-groups-mean-free-amenable-iff-residually-finite`).
  - **Consequence.** "F admits a mean-free amenable action ⇔ F is amenable" has no general proof and has to
    use the structure of `F`. If `F` is nonamenable, then in such an action mean-almost every stabilizer is
    nonamenable, yet contains no element of any fixed finite subset of `F \ {e}`.
  - **Configuration candidate.** On finite sets of dyadic rationals, mean-freeness forces almost every
    configuration to meet every open interval, since an element supported in an interval fixes every
    configuration missing it. So configurations have unboundedly many points. The pushing argument behind
    item 4 of `thompson-f-following-models-separate-iff-mean-charges-commutator` makes the mean fraction of
    configuration points in any slab `[y,z] ⊂ (0,1)` zero. Existence is undecided.
  - **Gap.** An invariant mean on some `F`-set charging `Moved(c)`, whose stabilizers are nonamenable and
    avoid every finite subset of `F \ {e}`; equivalently, following-model soficity of `F`.
- **Mean-free actions split into two shapes (2026-09-14).**
  - **Prior work.** Mean-free amenable actions are Elek–Szabó's essentially free amenable actions
    (`elek-szabo-essentially-free-amenable-actions`). Confined subgroups of `F` lie between
    `St⁰_(F')(S)` and `St_F(S)` for a finite `S` (`thompson-f-confined-subgroups-fix-finite-sets`).
  - **Split.** `F` has a mean-free amenable action exactly when (I) or (II) holds
    (`thompson-f-mean-free-actions-dense-configurations-or-unconfined`):
    - (I) finite subsets of `(0,1)` carry an invariant mean meeting every interval;
    - (II) an `F`-set with only non-confined stabilizers carries a mean-free mean.

    Every bounded configuration type, and every transitive `F/H` with `H` confined, has `t = 0`.
  - **Barrier.** Amenability of `F` gives both shapes, and both give soficity. So any refutation of
    following-model soficity proves `F` nonamenable. The obstruction subgroup `N_F` is `1` or `F'`.
  - **Gap.** Dense configurations whose points concentrate at the ends of every interval at every scale,
    or orbits whose stabilizers approach the trivial subgroup
    (`research/artifacts/hl-f-mean-free-actions-2026-09-14.md`).
