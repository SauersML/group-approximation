---
rg: 2
id: baumslag-solitar-groups-are-free-by-metabelian
kind: claim
title: Every Baumslag--Solitar group BS(m,n) with m, n nonzero is free-by-metabelian, so it is residually solvable and is the limit of its solvable quotients BS(m,n)/BS(m,n)^(k)
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that embeds BS(m,n) in a finitely presented simple group; this is a structural fact about its normal subgroups, used to approximate it by solvable quotients in the space of marked groups.
  residual-solvability-reduces-cgp-question-1-to-question-3: that is the consequence for Cornulier--Guyot--Pitsch Questions 1 and 3; this is the group-theoretic input.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed: this is
classical folklore, for example it is quoted without proof on main in
`nonsingular-magnus-extremes-separable-piece-sofic-proof`, "BS(2,3) is free-by-metabelian").

**Statement.** Let `G = BS(m,n) = ⟨a, t | t a^m t^{-1} = a^n⟩` with `m, n ≠ 0`, and let `K` be
the kernel of `G → Z`, `a ↦ 0`, `t ↦ 1`. Then `K'` is a free group, `G/K'` is metabelian, and
`G^(2) ≤ K'`. Hence `⋂_k G^(k) = 1`: `G` is residually solvable, and the marked groups
`(G/G^(k), (a,t))` converge to `(G, (a,t))` in the space of 2-marked groups as `k → ∞`.

**Proof.**
1. *Presentation of `K`.* Reidemeister--Schreier with transversal `{t^i}` gives
   `K = ⟨a_i (i ∈ Z) | a_{i+1}^m = a_i^n⟩`, `a_i = t^i a t^{-i}`.
2. *The vertex groups survive in `K^ab`.* The assignment `a_i ↦ (n/m)^i ∈ (Q,+)` respects the
   relations (`m (n/m)^{i+1} = n (n/m)^i`), so it defines a homomorphism `θ: K → Q` with
   `K' ≤ ker θ`. Since `θ(a_i^k) = k (n/m)^i ≠ 0` for `k ≠ 0`, `⟨a_i⟩ ∩ K' = 1` for every `i`.
3. *`K'` acts freely on the Bass--Serre tree.* `G` acts without inversions on the Bass--Serre
   tree `T` of the HNN extension, with vertex set `G/⟨a⟩` and vertex stabilizers
   `g⟨a⟩g^{-1}`. Write `g = k t^i` with `k ∈ K` (take `i` = image of `g` in `Z`); then
   `g⟨a⟩g^{-1} = k⟨a_i⟩k^{-1}`, and since `K' ⊴ K`,
   `K' ∩ k⟨a_i⟩k^{-1} = k(K' ∩ ⟨a_i⟩)k^{-1} = 1` by step 2. So `K'` acts on `T` freely, hence is
   free.
4. *Conclusion.* `G/K` is abelian, so `G' ≤ K` and `G^(2) = [G',G'] ≤ [K,K] = K'`. `G/K'` is an
   extension of the abelian group `K/K'` by `Z`, so metabelian. A free group `F` satisfies
   `⋂_j F^(j) = 1` (free groups are residually nilpotent by Magnus, and `F^(j) ≤ γ_{2^j}(F)`), so
   `⋂_k G^(k) ≤ ⋂_j (K')^(j) = 1`. A decreasing chain of normal subgroups with trivial
   intersection gives convergence of the quotients in the space of marked groups: a word is
   trivial in `G/G^(k)` for all large `k` iff it is trivial in `G`.
