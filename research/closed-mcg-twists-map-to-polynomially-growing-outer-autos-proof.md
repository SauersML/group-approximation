---
rg: 2
id: closed-mcg-twists-map-to-polynomially-growing-outer-autos-proof
kind: route
title: A central element of a subgroup of Out(F_n) with a power in its commutator subgroup is polynomially growing, and lanterns make Dehn twists such elements
target: closed-mcg-twists-map-to-polynomially-growing-outer-autos
requires: []
artifacts:
  - research/artifacts/closed-mcg-twists-polynomial-growth-2026-09-16.md
---

Full details, with the exact source statements, are in the artifact. For `n ≤ 1`,
`Out(F_n)` is finite and there is nothing to prove; let `n ≥ 2`.

**Inputs** (Bestvina--Feighn--Handel, *The Tits alternative for Out(F_n) I*, Ann. of
Math. 151 (2000), arXiv:math/9712217v2, read 2026-09-16). `L(ψ)` is the set of
attracting laminations of `ψ` (Definitions 3.1.5), a set of closed subsets of the
space of lines `B`. `L(ψ)` is finite, and `L(ψ^p) = L(ψ)` for `p ≥ 1` (Lemma 3.1.13
and its proof). `L(ψ) ≠ ∅` iff `ψ ∉ PG(F_n)` (Lemmas 3.1.9, 3.1.10(1), the proof of
Lemma 3.1.13, and the definition of `PG` in Section 5.1). Corollary 3.3.1: on
`Stab(Λ^+) = {θ : θ_#Λ^+ = Λ^+}` there is a homomorphism `PF_{Λ^+} : Stab(Λ^+) → Z`
with `PF_{Λ^+}(θ) = 0` iff `Λ^+ ∉ L(θ)` and `Λ^+ ∉ L(θ^{-1})`. Every PG subgroup has a
finite-index UPG subgroup (Corollary 5.7.6).

**Step 1: naturality.** `θ_#(L(ψ)) = L(θψθ^{-1})` for all `θ, ψ ∈ Out(F_n)`: run the
proof of the lemma "`L(O)` is `O`-invariant" (right after Definitions 3.1.5) with `θ`
in place of `O`. Birecurrence is preserved (Lemma 3.1.4), `θ_#` carries an attracting
neighborhood of a generic leaf for `ψ^s` to one for `(θψθ^{-1})^s`, and a periodic
rank-one free factor carrying `θ_#λ` pulls back by `θ^{-1}` to one carrying `λ`.

**Step 2: transfer.** If `D_0` is normal of finite index `m` in `D`, the transfer
`V : D → D_0^{ab}` satisfies `V(g) = g^m [D_0, D_0]` for central `g ∈ D` (the cycles of
`g` on `D/D_0` all have the length `f` of the order of `g D_0`, and each cycle
contributes `t_i^{-1} g^f t_i = g^f`).

**Step 3: Lemma A.** Let `ψ ∈ D ≤ Out(F_n)` be central with `ψ^k ∈ [D, D]`, `k ≥ 1`.
If `ψ ∉ PG(F_n)`, then `L(ψ)` is finite and nonempty, and `D` permutes it by Step 1
(`θ_#L(ψ) = L(θψθ^{-1}) = L(ψ)`). Let `D_0` be the kernel, of index `m`, and fix
`Λ^+ ∈ L(ψ)`, so `D_0 ≤ Stab(Λ^+)`. By Step 2, `χ = ψ^m ∈ D_0` satisfies
`χ^k [D_0, D_0] = V(ψ^k) = 1`. So `k · PF_{Λ^+}(χ) = 0`, hence `PF_{Λ^+}(χ) = 0` and
`Λ^+ ∉ L(χ) = L(ψ)`, a contradiction. So `ψ ∈ PG(F_n)`.

**Step 4: lantern.** Let `Σ = S_{h,b}`, `h ≥ 2`, `b ≥ 1`, with boundary component `∂`.
Then the boundary twist `T_∂` is central in `MCG(Σ)` (every mapping class fixes a
boundary-parallel curve up to isotopy; `fT_cf^{-1} = T_{f(c)}`) and
`T_∂ ∈ [MCG(Σ), MCG(Σ)]`. Glue a four-holed sphere `P` with boundary `b_1, …, b_4` to
`R = S_{h-2,b+2}` along `b_2, b_3, b_4`; the result is `S_{h,b}` with `b_1` a boundary
component (Euler characteristic and boundary count agree). Since `P` and `R` are
connected and each pair of pants cut from `P` by a lantern curve `x, y, z` contains one
of `b_2, b_3, b_4`, the six curves `b_2, b_3, b_4, x, y, z` are nonseparating in `Σ`.
Nonseparating curves are related by homeomorphisms fixing `∂Σ` pointwise (cut, apply
the classification of surfaces with the boundary components matched, and straighten in
collars), so their twists are conjugate and have one class `t` in `MCG(Σ)^{ab}`. The
lantern relation `T_xT_yT_z = T_{b_1}T_{b_2}T_{b_3}T_{b_4}` (Farb--Margalit Proposition
5.1) gives `3t = [T_∂] + 3t`, so `[T_∂] = 0`.

**Step 5: Dehn twists.** Let `g ≥ 3` and `c ⊂ S_g` essential. If `c` is nonseparating,
let `Σ ≅ S_{g-1,2}` be its complement; if it is separating, let `Σ ≅ S_{h,1}` be a side
of genus `h ≥ 2` (the genera of the two sides are positive and add to `g ≥ 3`). The
inclusion homomorphism `ι : MCG(Σ) → MCG(S_g)` sends a boundary twist to `T_c`. By Step
4, `T_c^{±1}` is central in `C = ι(MCG(Σ))` and lies in `[C, C]`, so `φ(T_c)^{±1}` is
central in `D = φ(C)` and lies in `[D, D]`. Step 3 with `k = 1` gives item 1.

**Step 6: multitwists.** Let `ψ_i = φ(T_{c_i})` for disjoint curves; they commute and
`ψ_i^{±1} ∈ PG(F_n)`. If `a = ∏ ψ_i^{k_i} ∉ PG(F_n)`, pick `Λ^+ ∈ L(a)` and `p ≥ 1`
with every `ψ_i^p` fixing every element of `L(a)` (they permute `L(a)` by Step 1).
Since `L(ψ_i^{±p}) = L(ψ_i^{±1}) = ∅`, Corollary 3.3.1 gives `PF_{Λ^+}(ψ_i^p) = 0`, so
`PF_{Λ^+}(a^p) = Σ k_i PF_{Λ^+}(ψ_i^p) = 0` and `Λ^+ ∉ L(a^p) = L(a)`, a contradiction.
The group `φ(⟨T_{c_1}, …, T_{c_r}⟩)` is therefore a PG subgroup; Corollary 5.7.6 gives a
finite-index UPG subgroup, which contains a common power of the `ψ_i`. This is item 2.
The same argument uses only that the `ψ_i` commute and `ψ_i^{±1} ∈ PG(F_n)`.

**Step 7: finite-index subgroups.** Let `Γ ≤ MCG(S_g)` have finite index,
`φ : Γ → Out(F_n)`, and `T_c^k ∈ Γ`, `k ≠ 0`, with `c` essential. With `C` as in Step
5, `Γ ∩ C` has finite index in `C`; let `N ≤ Γ` be its normal core in `C`, of index
`m`. The transfer `V : C → N^{ab}` kills `T_c ∈ [C, C]` and, by Step 2, sends the
central `T_c` to `T_c^m [N, N]`; so `T_c^m ∈ [N, N]` is central in `N`, and Step 3
applied to `D = φ(N)` gives `φ(T_c^m)^{±1} ∈ PG(F_n)`. Since `L(ψ^p) = L(ψ)`, an
element is in `PG(F_n)` iff a positive power is. `φ(T_c^k)^m = φ(T_c^m)^k` is a nonzero
power of `φ(T_c^m)`, hence in `PG(F_n)`, and so `φ(T_c^k)^{±1} ∈ PG(F_n)`. Step 6
applied to `ψ_i = φ(T_{c_i}^{k_i})` gives item 3.
