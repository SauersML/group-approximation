---
rg: 2
id: c2-character-bound-excludes-cyclic-edge-level-splittings-proof
kind: route
title: Fox calculus over Hom(H, C*) gives Delta_omega = gcd of the specialised derivatives, which is 1 - omega(d)t on S and 1 off it. Mayer-Vietoris over the infinite cyclic cover of a level splitting bounds deg Delta_omega by the twisted first Betti numbers of the cycle edge groups. S is irreducible and not binomial, so cyclic cycle edges must lie in [H,H]. With H_1(H) = Z^4 and Kurosh, this kills every FFLS with one cyclic cycle edge
target: c2-character-bound-excludes-cyclic-edge-level-splittings
requires:
  - c2-mapping-torus-realizations-are-free-factor-level-splits
artifacts:
  - experiments/c2-ffls-2026-09-19/RESULTS.md
  - experiments/c2-ffls-2026-09-19/chars.py
  - experiments/c2-ffls-2026-09-19/delta.py
---

Notation is as in the claim. Throughout, `Λ = C[t^{±1}]` is a PID, and degree means the span of a Laurent polynomial.

## 1. `Δ_ω` from Fox calculus (Theorem B.1)

- `r` is not a proper power, so the presentation 2-complex `X` of `H` is aspherical (Lyndon).
- The cellular chain complex of the cover with coefficients `Λ_ω` is `Λ → Λ^4 → Λ`.
  - `∂_2 = (∂r/∂x)^ω`, the Fox derivatives with `x ↦ ω(x)t^{ε(x)}` applied.
  - `∂_1 = (x^ω − 1)`.
- `H_1 = ker ∂_1 / Λ v` with `v = ∂_2(1)`. Since `im ∂_1 ⊂ Λ` is free, `ker ∂_1` is a direct summand of `Λ^4` of rank 3.
  - So the content of `v` in `ker ∂_1` equals its content in `Λ^4`.
  - The torsion of `H_1` is `Λ/(gcd of the entries of v)`.
- By Shapiro, `H_1(H; Λ_ω) ≅ H_1(N; C_ω)` as `Λ`-modules, with `t` acting as the deck transformation.
- The derivatives are abelian, so only their images in `Z[H_1(H)] = Z[B^±, C^±, D^±, E^±]` matter. `chars.py` computes them exactly:
  - `∂_b = (D−1)/D`.
  - `∂_c = −B(D−1)/(CD)`.
  - `∂_e = (C+1)(D−1)(D+1)/(CD²)`.
  - `∂_d = −(BD + CDE − 2CD + CE − C + DE − D + E − 1)/(CD²)`.
- Specialise `B = ω(b)t³`, `C = ω(c)`, `D = ω(d)t`, `E = ω(e)t`.
  - `∂_b` is a unit times `ω(d)t − 1`, so `Δ_ω | 1 − ω(d)t`.
  - `∂_b`, `∂_c` and `∂_e` vanish at `t_0 = ω(d)^{-1}`.
  - `C · ∂_d |_{D=1} = −B − 2CE + 3C − 2E + 2`. At `t = t_0` it equals `−(ω(b)ω(d)^{-3} + 2ω(c)ω(e)ω(d)^{-1} − 3ω(c) + 2ω(e)ω(d)^{-1} − 2)`.
  - So `deg Δ_ω = 1` iff `ω ∈ S`, and `deg Δ_ω = 0` otherwise.
- `chars.py` confirms this on four random rational points of `S` (gcd `= t − t_0`) and four points off `S` (gcd `= 1`).

## 2. Mayer-Vietoris degree bound (Theorem B.2)

- Take a level splitting `(Δ, V_v, E_j)` of `H` and let `N` act on the Bass-Serre tree.
- `N` is the fundamental group of the infinite cyclic cover graph of groups. Its vertex groups are `t^k V_v t^{-k}` and its edge groups are `t^k E_j t^{-k}`, for `k ∈ Z`.
  - A tree edge joins two vertices at the same level `k`.
  - A cycle edge `j` from `v` to `w`, with stable letter `s_j` of `ε = 1`, joins level `k` to level `k+1`.
- Mayer-Vietoris with coefficients `C_ω` gives an exact sequence of `Λ`-modules:
  `⊕_j H_1(E_j;ω)⊗Λ  →A→  ⊕_v H_1(V_v;ω)⊗Λ → H_1(N;ω) → ⊕_j H_0(E_j;ω)⊗Λ → ⊕_v H_0(V_v;ω)⊗Λ`.
- The kernel `K` of the last map is a submodule of a free module over a PID, hence free.
  - So `H_1(N;ω) ≅ coker A ⊕ K`, and `Tors H_1(N;ω) = Tors coker A`.
- The column of `A` for a tree edge is `(ι_*, −j_*)` with constant entries. The column for a cycle edge is `(ι_*, −t·j'_*)`.
  - After scaling by powers of `t`, the entries of column `c` lie in degrees `[0, s_c]`, where `s_c = 0` for tree edges and `s_c ≤ 1` for cycle edges.
- Let `ρ = rank A`. The torsion order of `coker A` is the gcd `d_ρ` of the `ρ×ρ` minors.
  - Every nonzero minor has degree `≤ Σ_c s_c ≤ Σ_{cycle j} dim H_1(E_j; ω)`.
- For a free group `E` of rank `k`, `dim H_0(E;ω) − dim H_1(E;ω) = 1 − k`. So `dim H_1(E;ω) = k − 1 + [ω|E = 1]`. This proves B.2.
  - The same count with an `n`-dimensional `ρ` gives `(k−1)n + dim coinv ρ(E)`.

## 3. Rigidity of `S` (Theorem B.3)

- Write `β = bd^{-3}`, `γ = c`, `η = ed^{-1}` and `δ = d`, a monomial change of coordinates on `(C^*)^4`.
- Then `S = V(f)` with `f = β + 2γη − 3γ + 2η − 2`.
  - `f` is linear in `β` with unit coefficient, so it is irreducible in `C[β^±,γ^±,η^±,δ^±]`: a factor free of `β` divides both `1` and the rest.
  - `S` is irreducible of dimension 3.
- Let `g ∈ H` have `[g] ≠ 0` in `H_1(H) = Z^4`. Then `{ω(g) = 1}` is a closed subgroup of codimension 1. Its components are cosets `{x^α = ζ}` with `α ≠ 0` primitive.
  - If `S` were contained in it, irreducibility and equal dimension would make `S` one such component.
  - That would give `(f) = (x^α − ζ)` up to a monomial unit. But `f` has five monomials, so this is impossible.
- If `[g] = 0` then `{ω(g) = 1}` is the whole torus, since `H_1(H)` is torsion-free and characters separate it.

## 4. Corollaries B1 and B2

**B1.**
- Let `J` be the set of cycle edges with `E_j ⊄ [H,H]`, equivalently whose image in `H_1(H)` is nonzero.
- For `j ∈ J`, `S ∩ {ω|E_j = 1}` is a proper closed subset of `S` (B.3). `S` is irreducible, so it is not a finite union of proper closed subsets. Pick `ω ∈ S` outside all of them.
- By B.1 and B.2, `1 = deg Δ_ω ≤ Σ_{j∈J}(rk E_j − 1) + Σ_{j∉J} rk E_j`.
  - Suppose no cycle edge has rank at least 2. Then the first sum is at most 0, so some `j ∉ J` has `rk E_j = 1`.
  - That `E_j` is infinite cyclic and lies in `[H,H]`.

**B2.**
- Let `(Δ, V_v, E_j)` be an FFLS with `b_1(Δ) = 1`. Collapse the tree edges to get an HNN `H = V*_E` with stable letter `s`, `ε(s) = 1`, `V ≤ N` f.g. free, and `E` a free factor of `F_4`.
  - A subset of a free factor system is again one.
- Since `E ≤ V ≤ F_4` and `E` is a free factor of `F_4`, `E` is a free factor of `V` by Kurosh, as in the corollary of Theorem A.
- `χ(H) = χ(V) − χ(E)` gives `rk V = rk E + 2`, and the budget of Theorem A gives `rk V ≤ 6`.
  - `rk E = 0`: `H ≅ F_2 * Z` is free, contradicting `H_1(H) = Z^4` with `χ = −2`.
  - `rk E = 4`: `E = F_4`, so `V = F_4` has rank 4, not 6.
  - `rk E = 1`, `E = ⟨g⟩`, `h = sgs^{-1} ∈ V`: then `H_1(H) = H_1(V)/⟨[g]−[h]⟩ ⊕ Z = Z^3/⟨[g]−[h]⟩ ⊕ Z`.
    - This equals `Z^4` only if `[g] = [h]` in `H_1(V)`.
    - Then `H_1(V) → H_1(H)` is injective, and B1 (the only cycle edge has rank 1) gives `g ∈ [H,H]`. Hence `g ∈ [V,V]`.
    - But a generator of a cyclic free factor of `V` is primitive, so its class is nonzero in `H_1(V)`. Contradiction.
- So `rk E ∈ {2,3}`.

## 5. Dead ends

**D1. Bi-monicity holds for every f.g. `H ≤ F_n ⋊ Z`.**
- `N` is free, so `M = H_1(N; Q)` is a `Q[t^±]`-module that is the rationalisation of `H_1(N; Z)`, a free abelian group.
- `H` is f.g., so `M` is f.g. over `Q[t^±]`, and so is its torsion part `T_Q`.
- Let `L = H_1(N;Z) ∩ T_Q`. It is `t`-stable, `Z`-pure and of finite `Q`-rank, since `T_Q` is finite-dimensional. So `L ≅ Z^m` spans `T_Q`.
- `t` and `t^{-1}` preserve `L`, so `t|_L ∈ GL_m(Z)`. Its characteristic polynomial is the torsion order, and it has leading and constant coefficients `±1`.
- The same holds for each finite-index `H'`, so every twisted order over permutation representations is bi-monic.
- Hence the FFLS ⇒ bi-monic implication (Lemma M) has no content. The `twisted.py` scans up to degree 4 are only a code check.
  - Non-bi-monic factors printed without the exact `rank_mod` certificate come from random minors, not the gcd.

**D2. The `D_N` degree.**
- Let `R = D_N[t^±]`, where `D_N` is the Linnell skew field of `N`, `t = d`.
- The torsion degree of `H_1(H; R)` is `deg λ`, where `λR = Σ_x ∂_x r · R`.
- `∂_c r = −PC(1−u)` with `P = eDDEddb`, `u = BzbD`, `z = eDDEdd`, `ε(u) = −1`. So `deg λ ≤ 1`, with equality iff each `f_x = (PC)^{-1}∂_x r` lies in `(1−u)R`.
- If `f_x = (1−u)g` with `g ∈ R`, expand `g = Σ_{k≥0} u^k f_x` in the Novikov completion in the `t^{-1}` direction.
  - The expansion is unique, and every coefficient lies in `QN`.
  - Finite `t`-support of `g` then gives `g ∈ QH`.
- So `deg λ = 1` iff `f_x ∈ (1−u)QH = ker(QH → Q[⟨u⟩\H])` for `x = b, d, e`.
- `delta.py` computes the images exactly. It uses coset representatives `u^{ε(h)}h ∈ N` and the word problem in the fibre `F_4`.
  - All are nonzero: 2, 10 and 4 cosets.
  - So the `D_N` torsion is 0. The Mayer-Vietoris count over `D_N` (all `H_0(E_j; D_N)` vanish) then gives only `0 ≤ Σ_j (rk E_j − 1)`, which is weaker than B1.

**D3. The c-block bound.**
- For an `n`-dimensional `ρ`, `Tors H_1(H; Λ^n_ρ)` is a submodule of `Tors(Λ^{4n}/im ∂_2)`, whose order divides every `n×n` minor of `∂_2`.
  - This includes the `c`-block `J_c = −ρ(PC)(I − ρ(u)t^{-1})`, whose determinant is a unit times `det(tI − ρ(u))`.
- So `deg Δ_ρ ≤ n ≤ (k−1)n` whenever an edge of rank `k ≥ 2` is present. No twisted degree argument can exclude `rk E ∈ {2,3}`.
