---
rg: 2
id: artin-sigma1-is-union-of-finite-depth-level-systems
kind: claim
title: "Sigma^1 of an Artin group at a discrete dominant character is the increasing union of finite Z[ker chi]-linear depth-m level systems, and level-0 descent is exactly collapse of this hierarchy at m = 0"
distinct_from:
  artin-sigma1-equals-dead-cut-laplacian-surjectivity: that is the criterion over the Novikov ring N_chi, an infinite object; this rewrites it as an increasing union of finite linear systems over Z[H], each using only levels -m..0
  artin-sigma1-is-level-zero-laplacian-surjectivity: that open claim is the statement that the hierarchy here collapses at depth 0; this proves the hierarchy and identifies the first obstruction to collapse (the depth-1 map d^1)
  artin-level-zero-laplacian-surjectivity-is-decidable: that asks whether the depth-0 system is decidable; this concerns all depths and their union
  artin-sigma1-dead-edge-ring-obstruction: that certifies failure of every depth at once through a ring; this is a membership criterion depth by depth
---

**Setting.** `χ : A_Γ -> Z` is surjective and dominant, `H = ker χ`, and `t ∈ A_Γ` has
`χ(t) = 1`. `θ(h) = t h t^{-1}` is an automorphism of `H`. `L_χ`, `L_0`, the generators
`g_ρ = ε_ρ σ_ρ + δ_ρ` (`ε_ρ = ±1`, `σ_ρ ∈ Z[H]`, `δ_ρ ∈ N_{>0}`) and the basis
`f_i = e_i - e_r` of `K_r` are those of `artin-sigma1-equals-dead-cut-laplacian-surjectivity`
(Step 7 of its proof). Every `g_ρ` lies in `Z G_{≥0}` with finite support.

**Depth-m system.** For `m >= 0`, let `P_m` be the set of `c ∈ (ZG)^{Rel}` supported at levels
`-m, ..., 0`. Write `(v)_{≤0}` for the part of `v ∈ (ZG)^r` at levels `≤ 0`. Then
`R_m` is the statement: for every `i < r` there is `c^{(i)} ∈ P_m` with

  `( Σ_ρ c^{(i)}_ρ g_ρ (e_{a_ρ} - e_{b_ρ}) )_{≤0} = f_i`.

Writing `c_ρ = Σ_{n=-m}^{0} c_{ρ,n} t^n` and `g_ρ = Σ_k g_{ρ,k} t^k` (`c_{ρ,n}, g_{ρ,k} ∈ Z[H]`),
`R_m` is a finite, block-triangular `Z[H]`-linear system. Its unknowns are the `c_{ρ,n}`. Its
level-`s` equation is `Σ_{n+k=s} c_{ρ,n} θ^n(g_{ρ,k})`, and its diagonal blocks are the
twists `θ^n(L_0)`.

**Claim.**
1. *Membership is finite depth.* `[χ] ∈ Σ^1(A_Γ)` iff `R_m` holds for some `m`.
2. *Monotone, with base case `L_0`.* `R_m ⇒ R_{m+1}`, and `R_0` holds iff `L_0` is onto.
3. *Descent is collapse.* The open claim `artin-sigma1-is-level-zero-laplacian-surjectivity`
   holds for `(Γ, χ)` iff `R_m ⇒ R_0` for all `m`. It already fails if `R_1 ⇏ R_0`.
4. *The first obstruction to collapse, `d^1`.* Take `r = 2`. Let `D_1` be the set of
   D-generators `S_k(pq)(p - 1)` with `χ(p) = 1`, and for these write `p_ρ = h_ρ t`, with
   `h_ρ ∈ H`. Let `J_0 = Σ_ρ Z[H] σ_ρ`, and let
   `Syz_0 = {ν ∈ Z[H]^{Rel} : Σ_ρ ν_ρ ε_ρ σ_ρ = 0}` be the level-0 syzygies. Define

     `d^1 : Syz_0 -> Z[H]`, `d^1(ν) = Σ_{ρ ∈ D_1} ν_ρ σ_ρ h_ρ`.

   Then `R_1` holds iff `θ(J_0) + d^1(Syz_0) = Z[H]`. So `R_1` holds while `R_0` fails
   exactly when `J_0 ≠ Z[H]` and `d^1(Syz_0)` reaches `1` modulo `θ(J_0)`.

**What it shows for Problem 1.6.**
- `Σ^1(A_Γ)` becomes a countable increasing union of *finite* linear conditions over `Z[H]`.
  Each one uses only the D, V and W data on the `m + 1` levels `-m, ..., 0`. No Novikov completion
  is needed to state membership.
- The corrected conjecture now says precisely that the hierarchy never grows past depth 0. The
  first place it could grow is the explicit map `d^1` of part 4, which gives a concrete
  search target. A counterexample would need a mixed D–D syzygy `ν` with
  `d^1(ν) ≡ unit mod θ(J_0)` while `J_0 ≠ Z[H]`.
- `novikov-level-descent-fails-for-d-shaped-laplacian-systems` shows that `d^1` is really
  nonzero for abstract D-shaped systems. So collapse must come from Artin-specific structure.

Proof: `artin-sigma1-is-union-of-finite-depth-level-systems-proof`.
