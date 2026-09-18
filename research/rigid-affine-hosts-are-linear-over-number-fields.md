---
rg: 2
id: rigid-affine-hosts-are-linear-over-number-fields
kind: claim
title: If R is a rigid subring of Z_p and R^n ⋊ Q is finitely generated then Q is linear over a number field, so the LISW §6 host exists only for groups linear over Q-bar
distinct_from:
  affine-self-similar-coordinate-rings-are-one-dimensional: that shows a finitely generated section-closed (rigid) coordinate ring is algebraic; this removes the hypothesis that the ring is finitely generated, replacing it by finite generation of the affine group, which is what LISW's host needs.
  linear-groups-over-q-are-quasi-retracts-of-simple-groups: that is LISW Theorem 1.4, whose host is built from the rigid ring Z[1/N]; this shows that no rigid ring does the same job for a group not linear over Q-bar.
  polynomial-parameter-affine-groups-are-self-similar: that gets self-similarity over Z[1/m][t_1..t_k] from parameter coordinates, which change linear parts; this concerns the parameter-free digit action with constant linear parts that LISW need for a persistent retraction.
---

**ESTABLISHED** by `rigid-affine-hosts-are-linear-over-number-fields-proof`
(lane proof, not reviewed). No priority is claimed.

**Setting (LISW, arXiv:2510.01952v1, TeX `arxiv_v1.tex`).**
- **Rigid rings** (`def:p-rigid`, l.739). A subring `R ⊆ Z_p` is *rigid* if, for every `x ∈ Z_p`,
  `x ∈ R` exactly when `px ∈ R`. This is the section-closed condition (SC) of
  `affine-self-similar-coordinate-rings-are-one-dimensional`, with `O = Z_p` and `π = p`.
- **The host.** For `R` rigid and `Q ≤ GL_n(R)`, `lem:rigid-self-similar-and-retract` (l.767)
  makes `R^n ⋊ Q` self-similar on the `p^n`-ary tree, and the projection onto `Q` is a persistent
  retraction.
- **Why finite generation is needed.** `prop:realizing-G-as-persistent-retract` (l.839) needs this
  group to have the finiteness properties of the target. In particular it must be finitely generated.
  Theorem 1.4 uses `R = Z[1/N]` with `p ∤ N`.

## Statement

Let `R ⊆ Z_p` be rigid, let `Q ≤ GL_n(R)`, and suppose the group `R^n ⋊ Q` is finitely generated.
Then:
- `R` is a finitely generated ring;
- `Frac(R)` is a number field;
- `Q` is linear over a number field, hence over `Q` by restriction of scalars.

**Consequence for LISW Question 1.10.** Let `H ≤ GL_n(C)` be finitely generated and not linear over
`Q-bar`, for example `Z wr Z` (`non-fp2-groups-are-quasi-retracts-of-simple-groups`).
- **No host of this kind exists.** No finitely generated group `R^n ⋊ Q` with `R` rigid has `H` in its
  linear part. This holds for every prime `p`, every rigid `R`, and every enlargement `Q ⊇ H`.
- **So the method stops at `Q-bar`.** LISW's §6 host never exists for such `H`. This matches their
  Remark 1.5 (`Q-bar` is the reach of the method) and makes their sentence "an answer to this
  question will likely require completely new techniques" (l.299) precise for that method.
- **Each escape route on main gives up one ingredient.**
  - Parameter coordinates (`polynomial-parameter-affine-groups-are-self-similar`) give up
    persistence: linear parts change under `t ↦ a + pt`.
  - The rigid closure `R[1/p] ∩ Z_p` of a transcendental `R` gives up finite generation of the host,
    by this node.

## Lesson for general BH

- **What persistence costs.** Persistent retraction together with digit self-similarity forces the
  coordinate ring to be algebraic, as soon as the host group is finitely generated. Finite
  generation of the ring does not have to be assumed.
- **Where the transcendence has to go.** A BH-type host that keeps coarse control of a transcendental
  linear group cannot carry the transcendence in constant linear parts of tree automorphisms. It has
  to be carried by the dynamics:
  - substitution endomorphisms, as in parameter coordinates, which gives up persistence; or
  - non-residually-finite carries, that is, almost automorphisms rather than tree automorphisms.
- **Heuristic, unproven.** A solvable carry kernel cannot help either. Kropholler's theorem makes
  soluble groups of type `FP_∞` minimax, hence of finite rank.
