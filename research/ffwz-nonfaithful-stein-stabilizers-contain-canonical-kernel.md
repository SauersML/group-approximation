---
rg: 2
id: ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel
kind: claim
title: For a non-faithful action, stabilizers of SV_G on the Stein complex of SV_(G/K) contain the canonical kernel, so FFWZ Lemma 4.9(i) fails and their non-faithful finiteness proofs have a gap
distinct_from:
  abstract-btb-pairs-fp-and-relatively-simple: that imports finite presentation of the abstract group SV_G for every type [A_2] action from FFWZ Theorem 4.1(ii); this shows the published proof of that implication does not work as written when the action has a kernel.
  twisted-brin-thompson-type-fn-implies-type-an: that is the necessity half of FFWZ Theorem B, proved by a quasi-retraction and unaffected; this concerns only the sufficiency halves.
  twisted-brin-thompson-type-fn-criterion: that is the faithful type F_n characterization, where the kernel is trivial and the stabilizer computation is correct; this is about the non-faithful case.
---

**ESTABLISHED** by the proof below (lane proof, elementary, not reviewed). It exhibits a gap in
a proof. It does not refute any theorem.

## Statement

Let `G` act on `S` with kernel `K ≠ 1`, and let `π : SV_G → SV_(G/K)` be the quotient map of
Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Remark 2.13, with kernel `SK_G`. Let `SV_G`
act on the Stein complex `SX_(G/K)` through `π`, as in FFWZ §4.2 (text lines 928–931).
1. Every cell stabilizer contains `SK_G`.
2. The stabilizer of a rank-1 vertex is `π^{−1}(G/K) = ι(G)·SK_G ≠ ι(G) = W(1)`. So FFWZ
   Lemma 4.9(i) ("the stabilizer in SV_G of x is conjugate in SV_G to W(n) ≅ Σ_n ⋉ G^n") is
   false for `n = 1`, and likewise items (ii) and (iii).

## Proof

- `SK_G = ker π` acts trivially on `SX_(G/K)`, which gives (1).
- Take `k ∈ K \ {1}`, a color `s`, and `u = [x_s, id, (k, 1), x_s]`. Then `u ∈ SK_G` by FFWZ
  Definition 2.12.
- The germinal twist (FFWZ Definition 2.15, well defined on `SV_G`) of `u` is `k` at points
  of the first half and `1` at points of the second half. Every element of `ι(G)` has constant
  germinal twist. So `u ∉ ι(G) = W(1)`.
- If the rank-1 stabilizer were conjugate to `W(1)`, it would be a conjugate `c ι(G) c^{−1}`
  containing the normal subgroup `SK_G`, hence `SK_G ⊆ ι(G)`, contradicting `u`. This gives
  (2).

## What loses its proof

FFWZ derive the "if" directions of Theorem B(ii) (`[A_2] ⇒ SV_G` finitely presented) and
(iii) (`[A_∞] ⇒ F_∞`) from Lemma 4.9: Proposition 4.10, Proposition 4.12, Corollary 4.13.
The same holds for Corollary 4.14 (`[HA_2] ⇒ FP_2`) and the structure statement
`SV_G ≅ P/N`.
- For faithful actions (`K = 1`) nothing changes.
- For non-faithful actions these implications are **unproven, not refuted**. For `S` a single
  point, `SV_G` is Thompson's labeled group `V(G)`, and there finite presentation for finitely
  presented `G` is classical (Thompson 1980; not re-read here).
- A natural repair is to run the argument on the abstract Stein complex `SX_G`, whose vertex
  stabilizers are the `W(n)`. That needs its connectivity, which FFWZ (lines 919–922) expect
  but do not prove.

## Nodes on main that use a non-faithful sufficiency direction

Found by grep of 2026-09-18; the list may be incomplete.
- `abstract-btb-pairs-fp-and-relatively-simple`, item 1, and through it
  `relatively-simple-removal-via-twisted-product-actor`,
  `relatively-simple-removal-between-pbh-and-bh-of-quotient`,
  `bh-product-closure-via-relatively-simple-kernel-removal` and other consumers.
- `a2-non-fp-image-via-diagonal-normalizer-proof`, step (6). It concerns only the extra claim
  that `SV_(G~)` is finitely presented; the answer to FFWZ Question 5.8 does not use it.
- `bbmz-oligomorphic-twisted-questions-proof`, step 4 (this lane's; caveat added there).
- Consumers of FFWZ Corollary 4.14 for non-faithful actions, if any; for example
  `fixed-actor-orbit-quotients-are-finitely-many` should be checked.

These are the owners' to re-grade. This node does not edit them.

## Repair

The statements are re-proved for every action in `abstract-twisted-bt-type-fn-criterion`. That
route realizes the abstract group as the `S`-colored subgroup of the faithful `S'V_G`, with
`S' = S ⊔ G` (`abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one`). It then uses
the `S`-colored Stein complex, whose vertex stabilizers are the correct `G ≀ Σ_m`. The nodes
listed above can cite that node in place of FFWZ Theorem B(ii), (iii) for non-faithful
actions.

## Lesson for general BH

A stabilizer computation does not survive passing to an action through a quotient. The
kernel sits in every stabilizer. The relative-simplicity route
(`boone-higman-implies-relative-permutational-bh` followed by finite presentation of the
abstract `SV_G`) currently rests on this unproven step, so any removal-of-kernel strategy
built on it inherits the gap until non-faithful finite presentation is re-proved.
