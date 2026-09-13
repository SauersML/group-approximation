---
rg: 2
id: expanding-matchings-need-a-shared-stabilizer-proof
kind: route
title: The graph of the bijection occupies at most half of each non-coincident diagonal orbit, and Selberg property (tau) passes to the Iwahori subgroup
target: expanding-matchings-need-a-shared-stabilizer
requires:
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
---

**Lemma G.** Put `H = {(v, τv) : v ∈ V_0} ⊆ V_0 × V_1`. For `s ∈ S`,

```text
(v, τv) ∈ H and s·(v, τv) = (sv, sτv) ∉ H     ⟺     τ(sv) != sτ(v),
```

so the left side of `(G1)` equals `Σ_s |∂_s H|`, where `∂_s U = {u ∈ U : su ∉ U}`. The diagonal
action preserves orbits, so `∂_s H = ⊔_O ∂_s(H ∩ O)`.

Let `O` be a non-coincident orbit and `(x,y) ∈ O`. Its projections are the orbits `Bx ⊆ V_0` and
`By ⊆ V_1`, and

```text
|O| = |Bx| · [Stab(x) : Stab(x) ∩ Stab(y)] = |By| · [Stab(y) : Stab(x) ∩ Stab(y)].
```

`H` is the graph of a bijection, so both projections are injective on `H`, and
`|H ∩ O| <= min(|Bx|, |By|)`. If `|H ∩ O| > |O|/2`, both indices equal `1`. Then
`Stab(x) = Stab(x) ∩ Stab(y) = Stab(y)`, so `O` is coincident, a contradiction. Hence
`|H ∩ O| <= |O|/2`, and the expander hypothesis gives `Σ_s |∂_s(H ∩ O)| >= h|H ∩ O|`. Summing over
the non-coincident orbits proves `(G1)`. ∎

**Item 2: no even-level pair coincides.** Every point of `C_0/Γ(L)` has `B`-stabilizer
`Γ(L) ∩ B`, and every point of `C_1/Γ_1(L')` has `Γ_1(L') ∩ B`, because the principal congruence
subgroups are normal in their vertex groups. Explicitly,

```text
Γ(2^M m)     = {a ≡ d ≡ ±1, b ≡ c ≡ 0 mod 2^M m},
Γ_1(2^M' m') = {a ≡ d ≡ ±1 mod 2^M' m', b ≡ 0 mod 2^(M'-1) m', c ≡ 0 mod 2^(M'+1) m'},
```

with `m, m'` odd. When `M' = 0`, `Γ_1(m')` is `C_1` intersected with the odd congruence kernel,
and its `b`-entries lie in `(1/2)Z`. Suppose `M >= 1`.
* If `M' >= 1`: the unipotent `[[1,0],[2^M m,1]]` lies in `Γ(2^M m)`, and it lies in `Γ_1` only
  if `M >= M'+1`. The unipotent `[[1, 2^(M'-1) m'],[0,1]]` lies in `Γ_1(2^M' m') ∩ B`, and it lies in
  `Γ(2^M m)` only if `M'-1 >= M`. These cannot both hold.
* If `M' = 0`: `[[1, m'],[0,1]] ∈ Γ_1(m') ∩ B` but not in `Γ(2^M m)`.

The case `M = 0 <= M'` is symmetric, using `[[1,0],[2m,1]]` on the `C_0` side. So a pair can
coincide only when both levels are odd.

**Item 2: uniform expansion.** Let `O ⊆ V_0 × V_1` be a diagonal orbit through `(x,y)` with levels
`L`, `L'`. Its stabilizer contains `Γ(L) ∩ Γ_1(L') ⊇ Γ(L) ∩ Γ(2L') ⊇ Γ(2LL')`. Here
`Γ(2N) ⊆ gΓ(N)g^(-1)` is checked entrywise. Hence `O` is a quotient `B`-set of `B/Γ(N)`,
`N = 2LL'`. A quotient map of transitive `B`-sets has fibres of constant size, and Cheeger bounds
pass down such quotients by lifting sets. So it suffices to find `κ_S > 0` with

```text
max_(s∈S) ||s f − f||  >=  κ_S ||f||     for f ∈ ℓ^2(B/Γ(N)), Σ f = 0, all N.   (G3)
```

Then for `U ⊆ O` with `|U| <= |O|/2`, the vector `f = 1_U − |U|/|O|` has `||f||^2 >= |U|/2` and
`||sf − f||^2 = 2|∂_s U|`, which gives `h_S = κ_S^2/4`.

*Proof of `(G3)`.* The required node records Selberg's theorem as property `(τ)` of `C = PSL_2(Z)`
with respect to congruence subgroups. Selberg's bound `λ_1 >= 3/16` holds at every level `N`,
including powers of `2`. So there is `κ_C > 0` with the `(G3)` bound on the orthogonal complement of
the `C`-invariant vectors of every congruence `C`-set. For a unitary `C`-representation `π`,
`Ind_B^C Res_B π ≅ π ⊗ ℓ^2(C/B)`. For `π = ℓ^2(C/Γ(N))` this is `ℓ^2(C/Γ(N) × C/Γ_0(2))`, a sum of
`ℓ^2(C/Π)` with `Π ⊇ Γ(2N)`, so it is again congruence. A `B`-almost-invariant `f` induces a
`C`-almost-invariant `f̃`. The loss depends only on fixed coset representatives of `C/B` and on the
word lengths of `S_C` in terms of `S`. By Frobenius reciprocity, `f ⊥ π^B` gives
`f̃ ⊥ (Ind π)^C`. Functions on the orbit `B/Γ(N) ⊆ C/Γ(N)` with mean zero are orthogonal to the
`B`-invariant vectors of `π`. So `(G3)` holds with a constant depending only on `S`. ∎

**Frame systems.** At depth `M`, `K = SL_2(Z_2)` acts on `K/K(2^M)` through the surjection
`PSL_2(Z) → PSL_2(Z/2^M)`. So each `K`-orbit of depth-`M` frames is `C_0/Γ(2^M)`. The adjacent
vertex group gives `C_1/Γ_1(2^M)` by conjugation with `g`. Both have even level, and `(G2)` applies
to all points.
