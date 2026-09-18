---
rg: 2
id: brin-thompson-nv-haagerup-iff-cocycle-kernel-domination-proof
kind: route
title: "Identify cosets of the cocycle kernel with cocycle values, bound the values by scale and pattern depth, and apply the split lemma"
target: brin-thompson-nv-haagerup-iff-cocycle-and-kernel-domination
requires:
  - haagerup-splits-as-coset-plus-subgroup-properness
  - cantor-maps-by-v-embed-in-next-brin-thompson-group
  - brothier-problem-b-reduces-to-value-range-domination
  - brin-thompson-nv-fibre-elements-are-cubically-elliptic
  - thompson-v-has-haagerup-property
---

Notation as in the target. Cnd functions satisfy `ψ(e) = 0`, `ψ(g^{-1}) = ψ(g)`, and restrictions
and pullbacks along homomorphisms of cnd functions are cnd. In "dominates" we may take `F`
nondecreasing, replacing `F(t)` by `inf_{s ≥ t} F(s)`.

**Step 0 (bricks and cubes).** If `B = [u_1]×...×[u_n]` has all `|u_i| ≤ m`, every level-`m` cube
meeting `B` lies in `B`. A prefix replacement restricted to a sub-brick is a prefix replacement.

**Step 1 (K is locally finite).** Let `k ∈ K` be a prefix replacement on the bricks of a finite
partition, all of whose words have length `≤ m`. By Step 0, each level-`m` cube `Q` lies in one
such brick, and `k|_Q` is a prefix replacement preserving every length, so `k(Q)` is a level-`m`
cube. As `k` is a bijection, `k ∈ K_m`. Conversely `K_m ⊆ K` and `K_m ⊆ K_{m+1}`. So
`K = ⋃_m K_m` with `K_m ≅ Sym(2^{nm})` finite.

**Step 2 (cosets are cocycle values).** For `g, g' ∈ nV` put `h = g^{-1} g'`. The cocycle identity
gives `c(g'^{-1}) = c(h^{-1} g^{-1}) = c(h^{-1})∘g^{-1} + c(g^{-1})`. Hence
`c(g'^{-1}) = c(g^{-1})` iff `c(h^{-1}) = 0` iff `h ∈ K` iff `gK = g'K`. So
`gK ↦ c(g^{-1})` is well defined and injective.

**Step 3 (finitely many values).** A function `C^n → Z^n` that is constant on level-`m` cubes and
bounded by `r` is one of at most `(2r+1)^{n 2^{nm}}` functions. So for every `r, m` the set
`{c(g) : ‖c(g)‖ ≤ r, pd(g) ≤ m}` is finite.

**Step 4 (2 ⇒ 1).** Let `ψ = ψ_1 + ψ_2 + ψ_3` with nondecreasing `F_1, F_2 → ∞`. Fix `R`.
If `ψ(g) ≤ R`, then `F_1(‖c(g)‖) ≤ R` and `F_2(pd(g)) ≤ R`, so `‖c(g)‖ ≤ r` and `pd(g) ≤ m` for
some `r, m` depending on `R`. By Step 3, `c(g)` takes finitely many values on `{ψ ≤ R}`. This set is
symmetric, so `c(g^{-1})` also takes finitely many values, and by Step 2 the set lies in finitely many
left cosets of `K`. Thus `ψ_1 + ψ_2` is proper modulo `K`, `ψ_3` is proper on `K`, and
`haagerup-splits-as-coset-plus-subgroup-properness` makes `ψ_1 + ψ_2 + ψ_3` proper.

**Step 5 (1 ⇒ 2).** Let `ψ` be proper and `d` be `‖c(·)‖`, `pd`, or the kernel depth on `K`. Every
sublevel set `{ψ ≤ R}` is finite, so `d` is bounded on it, say by `D(R)`, with `D`
nondecreasing. Each `d` is unbounded (by Step 8 for `‖c‖` and `pd`; `K_m ≠ K_{m+1}` for the
kernel depth), and every `g` lies in some sublevel set, so `D(R) → ∞`. Put
`F(t) = sup{R ∈ N : D(R) < t}`, finite, and `0` if the set is empty. If `d(g) = t` and
`D(R) < t`, then `g ∉ {ψ ≤ R}`, so `ψ(g) ≥ F(t)`. For every `R_0`, `t > D(R_0)` gives
`F(t) ≥ R_0`, so `F(t) → ∞`. Take `ψ_1 = ψ_2 = ψ_3 = ψ`.

**Step 6 (supplement (a)).** If `ψ` satisfies P1 and P2, Step 4 shows `ψ` is proper modulo `K`.
Conversely, if `ψ` is proper modulo `K`, each sublevel set meets finitely many cosets. By Step 2 and
symmetry, `c(g)` takes finitely many values on it, so `‖c‖` and `pd` are bounded there, and the
argument of Step 5 gives P1 and P2 for `ψ`.

**Step 7 (supplement (b)).** For `g ∈ nV`, `(g × id)(x, y) = (gx, y)` with `y ∈ C^{m−n}`. Then
`c(g × id)(x, y) = (c(g)(x), 0)`, which has the same scale and the same pattern depth, and `g × id`
permutes level-`k` cubes of `C^m` by prefix replacements iff `g` does so for `C^n`. Restrict the
cnd functions along the homomorphism `g ↦ g × id`.

**Step 8 (the element `x_0`).** Let `x_0 ∈ V` be `0y ↦ 00y`, `10y ↦ 01y`, `11y ↦ 1y`. By induction,
for `M ≥ 1`:
- `x_0^M(0y) = 0^{M+1} y`, so `c(x_0^M) = M` on `[0]`;
- `x_0^M(1^{M+1} y) = 1y`, so `c(x_0^M) = −M` on `[1^{M+1}]`;
- `x_0^M(1^M 0 y) = 01y`, since `M − 1` steps take `1^M 0 y` to `10y` and one more to `01y`. So
  `c(x_0^M) = 1 − M` on `[1^M 0]`;
- `x_0^{−M}(0^{M+1} y) = 0y`, so `c(x_0^{−M}) = −M` on `[0^{M+1}]`.

Hence `‖c(x_0^k)‖ ≥ |k|` for all `k ∈ Z`. Also `c(x_0^M)` is not constant on the level-`M` cylinder
`[1^M]`, so its pattern depth is at least `M + 1`. For `z = id × x_0 × id^{n−2} ∈ nV` with
`n ≥ 2`, `c(z^M)(x, p, q) = (0, c(x_0^M)(p), 0)`. So `‖c(z^M)‖ ≥ M` and `pd(z^M) ≥ M + 1`. In
particular `‖c‖` and `pd` are unbounded on `nV`, and for `n = 1` the same holds with `x_0` itself.

**Step 9 (supplement (c)).** Put `Γ = ⟨x_0⟩ ≤ V`, infinite cyclic. By
`cantor-maps-by-v-embed-in-next-brin-thompson-group`, `Φ(f,h)(x,p) = (hx, f(hx)(p))` embeds
`G = C(C,Γ) ⋊ V ≅ C(C,Z) ⋊ V` in `2V`. Identify `f ∈ C(C,Z)` with `x ↦ x_0^{f(x)}`. Then
`Φ(f, id)(x,p) = (x, x_0^{f(x)} p)`, so `c(Φ(f,id))(x,p) = (0, c(x_0^{f(x)})(p))`. By Step 8,
`‖c(Φ(f,id))‖ ≥ ‖f‖_∞`. If `ψ_1` satisfies P1 on `2V` with nondecreasing `F`, then `ψ_1∘Φ` is a cnd
function on `G` with `ψ_1(Φ(f)) ≥ F(‖f‖_∞)` for every `f ∈ C(C,Z)`. That is
`cantor-integer-maps-sup-norm-is-cnd-dominated`, and `brothier-problem-b-reduces-to-value-range-domination`
turns it into the Haagerup property of `C(C,Z) ⋊ V`.

**Step 10 (supplement (d)).** Let `n ≥ 2` and `ℓ(g) = |gA Δ A|` for a commensurating action of `nV`.
The element `z` of Step 8 lies in `V^n`, so by item 2 of
`brin-thompson-nv-fibre-elements-are-cubically-elliptic` the values `ℓ(z^M)` are bounded. If `ℓ` satisfied
P1 or P2 with a nondecreasing `F → ∞`, then `‖c(z^M)‖ ≥ M` and `pd(z^M) ≥ M + 1` would give
`ℓ(z^M) ≥ F(M) → ∞`, a contradiction.

**Step 11 (supplement (e)).** `V` has a proper cnd function (`thompson-v-has-haagerup-property`), so
Step 5 with `n = 1` gives P1, P2 and P3 for `V`. ∎
