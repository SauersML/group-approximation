---
rg: 2
id: cyclic-centralizer-subgroups-of-v-touch-attractors
kind: claim
title: In a torsion-free subgroup of Thompson's V with cyclic centralizers, every nontrivial support meets the attractors, repellers or identity region of every other nontrivial element's flow power
requires:
  - cyclic-centralizer-subgroups-of-nv-have-meeting-supports
distinct_from:
  cyclic-centralizer-subgroups-of-nv-have-meeting-supports: that holds in every nV and uses only centralizers; this adds V's one-dimensional source-sink dynamics and fails for nV, n >= 2 (baker-type elements have no attractors).
  closed-hyperbolic-surface-groups-embed-in-thompson-v: that is the open survey Question 4.7; this is a V-specific necessary condition on any positive answer and does not decide it.
---

**ESTABLISHED** (lane proof below, elementary; not reviewed; no priority claimed). It relies on one input
recalled but not read at source here: the source–sink structure of elements of `V` (Brin's revealing pairs;
Salazar-Díaz, *Thompson's group V from a dynamical viewpoint*).

**Structure input (S), recalled.** For `g ∈ V` of infinite order there is `k ≥ 1` with the following
properties.
- `C = W ⊔ F`, with both clopen, where `W = W(g^k)` is the identity region of `g^k` and `F = supp(g^k)`.
- `g^k` has finitely many fixed points in `F`, split into attractors `A` and repellers `R`. Each is a
  rational point with a clopen attracting (respectively repelling) cone neighbourhood.
- Every `x ∈ F \ (A ∪ R)` converges to `A` under `g^{kn}` as `n → +∞`, and to `R` as `n → −∞`.

**Claim.** Let `Γ ≤ V` be torsion-free with cyclic centralizers, for example a closed hyperbolic surface
group, if one embeds in `V`. Let `g ∈ Γ` be nontrivial, and let `k, A, R, W` be as in (S). Then every
nontrivial `h ∈ Γ` has
`supp(h) ∩ (A ∪ R ∪ W) ≠ ∅`.

**Proof.**
1. Suppose instead that `supp(h) ⊆ F \ (A ∪ R)`. That set is compact, since `supp(h)` is clopen by
   `cyclic-centralizer-subgroups-of-nv-have-meeting-supports`.
2. Choose a clopen union `U` of attracting cones, one around each point of `A`, inside the clopen set
   `C \ supp(h)`, which contains `A`. Take `U` forward-invariant under `g^k` and contracting to `A`.
3. By (S), each `x ∈ supp(h)` has an iterate `g^{kn_x}x` in the interior of `U`. By continuity the same `n_x`
   works on a neighbourhood of `x`, and forward invariance keeps later iterates in `U`. Compactness gives one
   `N` with `g^{kN}(supp h) ⊆ U`.
4. Then `h' = g^{kN} h g^{-kN}` is nontrivial with `supp(h') = g^{kN}(supp h) ⊆ U`, which is disjoint from
   `supp(h)`. This contradicts the translate clause of
   `cyclic-centralizer-subgroups-of-nv-have-meeting-supports` with `γ = g^{kN}`. ∎

**Corollaries.**
- If some nontrivial `g ∈ Γ` has a flow power with full support (`W(g^k) = ∅`), then the support of every
  nontrivial element of `Γ`, and of all its `Γ`-translates, contains one of the finitely many rational points
  in `γ(A ∪ R)`, for every `γ ∈ Γ`.
- No nontrivial element of `Γ` is supported in `W(g^k)`. Such an element would commute with `g^k`, so by
  cyclic centralizers it would be a power of the root of `g`, whose support lies in `F`.

**Scope.** This is a necessary condition only. It does not decide Question 4.7. It is the first place where
the obstruction side uses dynamics specific to `V` rather than all of `nV`, which is where any
`V`-versus-`2V` separation for surface groups must come from.
