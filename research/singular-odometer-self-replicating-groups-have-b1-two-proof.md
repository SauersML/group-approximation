---
rg: 2
id: singular-odometer-self-replicating-groups-have-b1-two-proof
kind: route
title: Integrate the odometer displacement off shrinking cylinders at the singular points; tree automorphisms carry cylinders to cylinders and preserve Haar measure, so the truncated flux is additive up to d^-K, and the slope of a copy below a vertex shifts its index
target: singular-odometer-self-replicating-groups-have-b1-two
requires:
  - fully-self-replicating-fp-infinity-groups-are-acyclic
  - m11-linear-activity-self-replicating-group
artifacts:
  - experiments/odometer-flux-index-2026-09-17/flux_index.py
  - experiments/odometer-flux-index-2026-09-17/flux_index.out
---

The notation is that of the target.

## 0. Two facts about tree automorphisms

For `g ∈ Aut(X*)` and every `K`:

- **(F1)** `g` maps `C_K(q)` onto `C_K(q^g)`, because it permutes the level-`K` vertices.
- **(F2)** `g` preserves `μ`, by (F1), since `μ` is determined by its values `d^{−K}` on
  cylinders.

Throughout, `t` takes values in `ℤ ⊂ ℤ_d` off the singular sets, and integrals are real
integrals of integer-valued, locally constant functions on compact sets.

## 1. Composition and the singular set

Maps act on the right, so `x^{gh} = (x^g)^h`. Then, in `ℤ_d`,

`t_{gh}(x) = t_g(x) + t_h(x^g)`.   (1)

- If `x ∉ S_g` and `x^g ∉ S_h`, then both terms are constant integers near `x`, because `g` is
  continuous. So `S_{gh} ⊆ T`, where `T := S_g ∪ (S_h)^{g^{−1}}`. This is finite, which gives
  (O1) for `gh`.
- Because `ℤ → ℤ_d` is injective, (1) holds in `ℤ` at every point of `ℤ_d ∖ T`.

**Choice of `K_0`.** Choose `K_0` so that for every `K ≥ K_0`:

- the cylinders `C_K(q)`, `q ∈ T`, are pairwise disjoint;
- the cylinders `C_K(p)`, `p ∈ T^g = (S_g)^g ∪ S_h`, are pairwise disjoint;
- `t_g` is constant on `C_K(q)` for `q ∈ T ∖ S_g`;
- `t_{gh}` is constant on `C_K(q)` for `q ∈ T ∖ S_{gh}`;
- `t_h` is constant on `C_K(p)` for `p ∈ T^g ∖ S_h`.

Such a `K_0` exists because `T` is finite and each function listed is locally constant at the
points listed.

## 2. Near-additivity (item 1)

Fix `K ≥ K_0`. Put `U_K(Y) = ∪_{q ∈ Y} C_K(q)` and `Ω = ℤ_d ∖ U_K(T)`. By (F1),
`Ω^g = ℤ_d ∖ U_K(T^g)`. Integrate (1) over `Ω` and change variables by (F2):

`∫_Ω t_{gh} = ∫_Ω t_g + ∫_{Ω^g} t_h`.   (2)

Each integral in (2) differs from a truncated flux by finitely many cylinders on which the
integrand is constant:

- `D_K(g) = ∫_Ω t_g + d^{−K} Σ_{q ∈ T ∖ S_g} t_g(q)`, since `U_K(S_g) ⊆ U_K(T)`, and the
  remaining cylinders of `U_K(T)` are the `C_K(q)` with `q ∈ T ∖ S_g`, disjoint from
  `U_K(S_g)`.
- `D_K(h) = ∫_{Ω^g} t_h + d^{−K} Σ_{p ∈ T^g ∖ S_h} t_h(p)`, in the same way, since
  `S_h ⊆ T^g`.
- `D_K(gh) = ∫_Ω t_{gh} + d^{−K} Σ_{q ∈ T ∖ S_{gh}} t_{gh}(q)`, since `S_{gh} ⊆ T`.

Substituting into (2) gives, for all `K ≥ K_0`,

`D_K(gh) − D_K(g) − D_K(h) = d^{−K}·E(g, h)`, where
`E = Σ_{T ∖ S_{gh}} t_{gh}(q) − Σ_{T ∖ S_g} t_g(q) − Σ_{T^g ∖ S_h} t_h(p)`,

a fixed integer.

**Inverses.** `t_{g^{−1}}(y) = −t_g(y^{g^{−1}})`, so `S_{g^{−1}} = (S_g)^g`. By (F1) and (F2),
`D_K(g^{−1}) = −D_K(g)` exactly.

**The group and the homomorphism.** If `g, h` satisfy (O2), then
`D_K(gh) = (A(g) + A(h)) + K (B(g) + B(h)) + o(1)`. So `gh ∈ 𝒪_d` and `g^{−1} ∈ 𝒪_d`. The
coefficients of an expansion `α + Kβ + o(1)` are unique, so `(A, B)` is additive. The identity
has `D_K = 0`.

**Germ locality.** For `K ≥ K_0(g)` the sets `U_K(S_g)` decrease, and
`D_{K+1}(g) − D_K(g) = ∫_{U_K(S_g) ∖ U_{K+1}(S_g)} t_g`. So
`B(g) = lim_K ∫_{U_K ∖ U_{K+1}} t_g`, which only involves `g` on arbitrarily small neighbourhoods
of `S_g`. `A(g)` involves `t_g` everywhere.

## 3. Values (item 2)

- **Topological full group.** If `S_g = ∅`, then `D_K(g) = ∫ t_g dμ` for all `K`. So `B = 0` and
  `A = ∫ t_g`.
- **Finitary elements.** A finitary `g` of depth `n` induces a permutation `π` of `ℤ/d^n` and
  satisfies `t_g(x) = π(r) − r`, with `r ∈ {0, …, d^n − 1}` the residue of `x`. Then
  `A = d^{−n} Σ_r (π(r) − r) = 0`.
- **Odometer.** `t = 1`, so `A = 1`.

## 4. Sub-tree copies (item 3)

The point `x·w` of `ℤ_d` is `x + d·w`. So `t_{g@x}(x·w) = d·t_g(w)`, and `t_{g@x} = 0` off the
cylinder `[x]`. Hence:

- `S_{g@x} = x·S_g`;
- `C_K(x·q) = x·C_{K−1}(q)` for `K ≥ 1`;
- `μ(x·E) = μ(E)/d`.

Therefore

`D_K(g@x) = ∫_{[x] ∖ U_K(x·S_g)} d·t_g(w) dμ(x·w) = ∫_{ℤ_d ∖ U_{K−1}(S_g)} t_g dμ = D_{K−1}(g)
= (A(g) − B(g)) + K·B(g) + o(1)`.

So `g@x ∈ 𝒪_d`, with `A(g@x) = A(g) − B(g)` and `B(g@x) = B(g)`.

## 5. Rank (item 4)

Let `v = (A, B)(g)` and `v' = (A, B)(g@x) = (A(g) − B(g), B(g))`. Then
`det(v, v') = A(g)B(g) − (A(g) − B(g))B(g) = B(g)²`.

- **If `B(g) ≠ 0`.** The image of `(A, B)|_R` is a torsion-free abelian subgroup of `ℝ²`
  containing two `ℝ`-independent vectors, so it has rank at least `2`. It is finitely
  generated because `R` is. It is a quotient of `R^ab`, so `b_1(R) = dim_ℚ H_1(R; ℚ) ≥ 2`.
- **If `(A, B)|_R ≠ 0`.** The same argument gives rank at least `1`.

## 6. The Tits-route kill (item 5)

By the setting of `fully-self-replicating-fp-infinity-groups-are-acyclic`, a fully
self-replicating `R` with transitive root image `P` satisfies `R ≅ R ≀_X P`. Its item 3, for
`P ≤ Alt(X)`, states verbatim:

> (d) if `R` is finitely presented and `d ≥ 4`, then `dim_k H_1(R; k) ≤ 1`. In
> particular `rank H_1(R; Z) ≤ 1`. If `d = 3`, then `H_1(R; k) = 0`. If `R` is of type
> `FP_{d−1}`, then `R^{ab}` is finite with order divisible only by primes dividing `|P|`.

Take `k = ℚ`. Condition (B) gives `R@x ⊆ R` for every `x`.

- **(a)** Suppose `d ≥ 4` and `R` is finitely presented. Then `b_1 ≤ 1`, so item 4 forces
  `B ≡ 0` on `R`.
- **(b)** Suppose `d = 3` and `R` is finitely presented. Then `H_1(R; ℚ) = 0`. A nonzero
  homomorphism `R → ℝ` would factor through `R^ab ⊗ ℚ = 0`, so `A ≡ B ≡ 0`.
- **(c)** Suppose `R` is of type `FP_{d−1}`. Then `R^ab` is finite, so every homomorphism
  `R → ℝ²` is `0`.
- **Index is invariant.** Conjugation inside `𝒪_d` preserves `A`, because `A` is a
  homomorphism. So an odometer, an `𝒪_d`-conjugate of one, or a copy `a@u` below any vertex
  (`A(a@u) = 1` by item 3, since `B(a) = 0`) cannot lie in `R`.

## 7. The M_11 instance (item 6)

The digit map `letter k ↦ k − 2` (`k = 2, …, 11`), `letter 1 ↦ 10` turns `α = (1, …, 11)`
into `e ↦ e + 1 mod 11`.

- **The odometer `a`.** Since `a = (a, 1, …, 1) α` has its section `a` at digit `10`, it is
  `x ↦ x + 1`. So `A(a) = 1` and `B(a) = 0`.
- **`M_11`.** Its elements are finitary, so `A = B = 0`.
- **`c = (c, a, 1, …, 1)`.** Its sections are `c` at digit `10` and `a` at digit `0`, with
  trivial root.
  - On `[10^k 0]`, `c` adds `11^{k+1}`.
  - On `[10^k e]` with `e ∉ {0, 10}`, it is the identity.
  - So `S_c = {−1}`, where `t_c` is unbounded.
  - `μ[10^k 0] = 11^{−(k+1)}`, and `C_K(−1) = [10^K]`.
  - Hence `D_K(c) = Σ_{k<K} 11^{k+1}·11^{−(k+1)} = K`, so `A(c) = 0` and `B(c) = 1`.
- **`b = (b, α, β, 1, …, 1)`.** Its sections are `b` at digit `10`, `α` at digit `0` and `β` at
  digit `1`.
  - On `[10^k 0 e]`, `t_b = 11^{k+1}(α(e) − e)`.
  - On `[10^k 1 e]`, `t_b = 11^{k+1}(β(e) − e)`.
  - Elsewhere off `−1`, `t_b = 0`.
  - Both digit permutations have zero mean displacement, so each shell integrates to `0`.
  - Hence `D_K(b) = 0` for all `K`, so `A(b) = B(b) = 0`.

So `R ≤ 𝒪_11` and `(A, B) : R ↠ ℤ²`, sending `a ↦ (1, 0)` and `c ↦ (0, 1)`. It agrees with
`(e_a, e_c)` on the generators, hence everywhere. This reproves `b_1(R) ≥ 2` without examining
a single relation.

**Consistency with the section recursion.** `c = c@10 · a@0` gives
`A(c) = (A(c) − B(c)) + A(a) = 0 − 1 + 1 = 0`, as item 3 requires.

## 8. Numerical check

`flux_index.py` computes `t_w` exactly modulo `11^N` for words `w` over
`a, b, c, α, β, γ` and their inverses, where `γ` is the second ATLAS generator of `M_11`. It
evaluates `D_K(w)`, excluding the level-`K` cylinders around the pull-backs of `−1` under the
prefixes of `w`. This set contains `S_w` by §1, and excluding extra cylinders where `t_w` is
locally constant changes `D_K` only by `O(11^{−K})`.

On 45 words of length up to 7:
- `D_K(w)` is the same for `N = 5` and `N = 6`.
- The maximum of `|D_K(w) − e_a(w) − K e_c(w)|` is `1.18`, `0.107` and `0.0098` for `K = 2, 3, 4`.
  It shrinks by a factor of exactly `11` per level, which is the `E(g, h)·d^{−K}` law of item 1.

