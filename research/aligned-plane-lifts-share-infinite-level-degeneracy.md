---
rg: 2
id: aligned-plane-lifts-share-infinite-level-degeneracy
kind: claim
title: Conjecture - no minimal quantum-rigid plane lift of a non-SFT input; reduced for aligned lifts to excluding one exceptional-key defect profile, and not supported for transplant lifts, where rigidity follows from explicit hypotheses
distinct_from:
  e2-for-plane-lifts-is-clustered-floating-freedom: that proves the input is central and kills bijective transports; this treats ARBITRARY cross-plane couplings of floating data in aligned lifts and reduces the conjecture to one profile.
  varying-skeleton-lifts-reduce-e2-to-skeleton-rigidity: that gives sufficient conditions for rigidity of transplant lifts; here they are read as the obstruction to proving the conjecture for them.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `e2-for-plane-lifts-is-clustered-floating-freedom`, `varying-skeleton-lifts-reduce-e2-to-skeleton-rigidity`, `plane-local-freedom-kills-rigidity-of-plane-lifts`, `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`.

**OPEN (conjecture of bh-g1-simulation, 2026-09-18).** Not proved here.
- Part 1 reduces the aligned case to excluding one profile. Its lemmas 1–3 are proved; the
  assembly is a sketch.
- Part 2 shows the transplant case is not closed by any known obstruction.
- **Recommendation:** do not retire the `Z^2`-lift route on the strength of this conjecture.

**Terms.**
- A *plane lift* is an SFT `X` over `Λ_0 x Z^2`, minimal, with an `H`-invariant factor onto a
  minimal non-SFT `Λ_0`-subshift `Y` (plane-constant letters).
- It is *aligned* if its skeleton is `Λ_0`-constant.
- It is *DR-regular* if every point whose skeleton has only finite father chains is determined
  by skeleton and letters (Durand–Romashchenko's finite regress).
- The *key functions* are `𝒢_k = { f_k(π, ·) }`: the level-`k` identities at finite chains, as
  functions of position type `π` and table.

## Part 1. Aligned DR-regular lifts

**Lemma 1 (local key functions; proved).** At any point and any level-`k` position `z`, and for
every window of planes `λF` whose level-`k` tables are pairwise distinct, the floating
identities satisfy `σ^{λf}_k(z) = g(T^{λf}_k)` for some `g ∈ 𝒢_k`.

*Proof.*
- By minimality, the window's pattern occurs at a point with a generic skeleton.
- There, DR-regularity gives identities `f_k(π, T)`.
- The skeleton is `Λ_0`-constant, so one `π` serves the whole window. ∎

This holds for **every** kind of cross-plane coupling, relational or functional.

**Lemma 2 (no global key function; proved).** Suppose some key-function field
`z ↦ g_k(z) ∈ 𝒢_k` gives the floating identities of *all* planes, at every point. Then `Y` is
an SFT.

*Proof.*
- `τ' = (skeleton, (g_k(z)))` is continuous and `Λ_0`-invariant.
- It determines the point together with `y`.
- Theorem 3(iii) of `strongly-proximal-geometries-are-disjoint-from-measured-inputs` applies.
- This is Theorem C of `e2-for-plane-lifts-is-clustered-floating-freedom`, without assuming
  transports. ∎

**Lemma 3 (far switches kill rigidity; proved).** Suppose some point has two modifications
whose plane sets `P_1, P_2 ⊆ Λ_0` are at distance `> 2D`, for instance two switches between
key functions on far regions of planes. Then `X` is not `D`-rigid.

*Proof.* The far-modification lemma. ∎

**Assembly (sketch).**
- By Lemma 2, rigid minimal aligned lifts need floating data that is *not* one global key
  function.
- By Lemma 1, it is locally a key function. So it must *switch* between key functions along
  `Λ_0`.
- By Lemma 3, switches cannot be performed independently on far regions.
- The only arrangement left is **exceptional-key defect freedom** (profile E):
  - switching is possible only at planes whose tables lie in an exceptional set
    `Bad_∞ = ∩_k Bad_k`;
  - for every `y` those planes form a set of diameter `≤ 2D`;
  - away from them, overlapping windows force a single key function.
- Profile E has three further properties:
  - **Nowhere dense.** Clopen sets recur syndetically, so `Bad_∞` has empty interior.
  - **Unbounded in `Z^2`.** Otherwise it is a finite modification, which kills rigidity in a
    minimal SFT (`minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`, and
    bh-free-09's warning).
  - **At most one infinite zone.** Otherwise the antipodal clash of
    `cross-layer-separable-modifications-kill-quantum-rigidity` returns.

**So, for aligned DR-regular lifts:** the conjecture ⟺ no minimal lift realizes profile E with
a relatively rigid defect fibre.
- The fibre at the defect is plausibly rigid. Father–child identity consistency propagates the
  branch choice by exact copy identities.
- So the burden of a proof is to exclude *realizability*. In particular, one must show that
  finite-level shadows of the defect choice, at the syndetic planes with keys in `Bad_k`,
  cannot all be matched by determined data. No argument for that is known here.

## Part 2. Transplant lifts (skeleton varying along `Λ_0` through an input cocycle)

- **Shared degeneracy is true, but harmless.** Skeleton phases in different planes differ by
  integers, so every plane is degenerate at once (bh-g1-simulation's observation). But
  degenerate freedom is then shared by all planes, so it is not separable across planes.
- **Floating data is a plane-global section field.** It is absorbed into the enlarged skeleton
  (corrected Part 3 of `varying-skeleton-lifts-reduce-e2-to-skeleton-rigidity`).
- **Theorem D then gives rigidity** from:
  - (i) rigidity of the enlarged skeleton;
  - (ii) its centrality;
  - (iii) crossing table wires.
- **Minimality** is the character criterion (PF1) for the transplant cocycle.
- **So a proof of the conjecture for transplant lifts must refute (PF1), or (i)–(ii), for every
  input cocycle.**
  - For the Busemann height cocycle of the tree-glued input, only a partial result exists: the
    Sturmian label factor cannot trivialize it (`keyed-slots-bypass-the-phase-field-on-boundary-geometry`).
  - Nothing known refutes (i)–(ii).

## Lesson for general BH

"Shared degeneracy" is not an obstruction by itself.
- In aligned lifts, the real constraint is that floating data is *locally* a key function, for
  every coupling (Lemma 1). Globally it can neither be constant (Lemma 2) nor switch in far
  places (Lemma 3). Only an exceptional-key defect survives.
- In transplant lifts, shared degeneracy makes freedom plane-global, which is what rigidity
  wants.

The decisive open tests are:
- realizability of profile E (aligned lifts);
- (PF1) plus enlarged-skeleton rigidity for the Busemann height transplant (transplant lifts).

Until one of them is settled, the `Z^2` route is open, not dead.
