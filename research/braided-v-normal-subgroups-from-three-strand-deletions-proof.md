---
rg: 2
id: braided-v-normal-subgroups-from-three-strand-deletions-proof
kind: route
title: Three-strand deletions commute with conjugation and cloning, and commutators die on cloned pairs
target: braided-v-normal-subgroups-from-three-strand-deletions
requires: []
artifacts:
  - research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md
---

Artifact §1–§2 (Theorem A). The graph-theoretic inputs are the correspondence and normality criteria of
Zaremsky, arXiv:1403.8132v2 §4 (Proposition 4.1, Lemmas 4.2–4.4), read verbatim from the arXiv source on
2026-09-16. The artifact also re-derives the parts it uses.

1. **Normality in `B_n`.** Let `p ∈ G_n(M)` and `b ∈ B_n`. Keeping the strands that end at positions `S` in the
   stack `b p b^{-1}` gives `pi_S(b p b^{-1}) = beta pi_{S_1}(p) beta^{-1}`, with `beta ∈ B_3` and `S_1` the
   positions where those strands cross `p`. This lies in `M` because `M ◁ B_3`. Also
   `b p b^{-1} ∈ [PB_n, PB_n]`.
2. **Coherence (⊇).** Let `p ∈ G_n(M)` and let `S'` be a 3-subset of `{1..n+1}`.
   - If `S'` contains at most one of the clones `k, k+1`, then `pi_{S'}(clone_k p) = pi_{c_k(S')}(p) ∈ M`.
   - If `S' ⊇ {k, k+1}`, then `pi_{S'} ∘ clone_k` factors through `PB_2 ≅ Z`, so it kills `p ∈ [PB_n, PB_n]`.
3. **Completeness (⊆).** Let `clone_k(p) ∈ G_{n+1}(M)`.
   - Deleting clone `k+1` is a homomorphism left inverse to `clone_k`, so `p ∈ [PB_n, PB_n]`.
   - With `S(k)` as in [Z, proof of Lemma 4.4], `pi_S(p) = pi_{S(k)}(clone_k p) ∈ M`.
4. **Extension to `V_br`.** By steps 2–3, Zaremsky's equation holds, so `N_M = Th(G_*(M))` is a well-defined
   subgroup of `P_br`, normal in `F_br`. Membership of `(T, p, T)` is invariant under expansion. By step 1 and
   [Z, Lemma 4.3], `N_M` is normal in `V_br`: `(S,b,T)(T,p,T)(T,b^{-1},S) = (S, b p b^{-1}, S)`. Also
   `N_M ≤ Th([PB_*, PB_*]) = [P_br, P_br]`.
5. **Three-strand stage.** `G_3(M) = M ∩ [PB_3, PB_3] = M`, because the only 3-subset of `{1,2,3}` is the whole
   set. By well-definedness, `N_M ∩ PB_T` corresponds to `G_3(M)` for `n(T) = 3`. If `M ≤ M'`, then
   `G_n(M) ≤ G_n(M')` for every `n` by the definition of `G_n`, so `N_M ≤ N_{M'}`. Conversely, if
   `N_M ≤ N_{M'}`, then intersecting with `PB_T` for a 3-leaf tree `T` gives `M ≤ M'` by this step.
