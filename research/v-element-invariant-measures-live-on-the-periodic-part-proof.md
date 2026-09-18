---
rg: 2
id: v-element-invariant-measures-live-on-the-periodic-part-proof
kind: route
title: Track how many letters an element of V reads and writes along an orbit; new lows expand deep cones onto shallow ones, and a nonnegative height either repeats a cone or contracts one, so atomless invariant mass sits on the periodic part
target: v-element-invariant-measures-live-on-the-periodic-part
requires: []
---

Lane proof, elementary, self-contained. Notation as in the claim. `x[1..c]` is the prefix of length `c`,
`C_w` is the cone of `w`, and `σ` is the shift.

**Data.** `ψ(α_i y) = β_i y` on a cone partition `{C_(α_i)}`. Put `N = max |α_i|` and
`λ(x) = |β_i| − |α_i|` for `x ∈ C_(α_i)`. Write `x_j = ψ^j x` and `h_j(x) = Σ_(i<j) λ(x_i)`.

**Lemma B (bookkeeping).** For all `x` and `j >= 0` there are `c_j >= 0` and a word `F_j` such that:
- `ψ^j y = F_j σ^(c_j) y` for every `y ∈ C_(x[1..c_j])`;
- `|F_j| − c_j = h_j(x)`;
- `c_j <= N − min_(i<j) h_i(x)` for `j >= 1`, and `c_0 = 0`.

*Proof.* Induction, starting from `F_0` empty and `c_0 = 0`. Let `C_α` (`|α| = r <= N`) be the piece
containing `x_j = F_j σ^(c_j) x`.
- If `r <= |F_j|`, write `F_j = α G`. For `y ∈ C_(x[1..c_j])` we have `ψ^(j+1) y = β G σ^(c_j) y`. Put
  `F_(j+1) = β G` and `c_(j+1) = c_j`.
- Otherwise `α = F_j · x[c_j+1 .. c_j+r−|F_j|]`. Put `c_(j+1) = c_j + r − |F_j| = r − h_j <= N − h_j`
  and `F_(j+1) = β`. For `y ∈ C_(x[1..c_(j+1)])` we have `ψ^j y ∈ C_α`, so `ψ^(j+1) y = β σ^(c_(j+1)) y`.
In both cases `|F_(j+1)| − c_(j+1) = h_j + λ(x_j)` and `c_(j+1) <= max(c_j, N − h_j)`. ∎

Since `ψ^j` is injective and equals `y ↦ F_j σ^(c_j) y` on `C_(x[1..c_j])`, it maps that cone **onto**
`C_(F_j)`.

**Fact M.** For atomless `μ`, `ε_n := max_(|w|=n) μ(C_w) → 0`. Otherwise the words with
`μ(C_w) >= ε > 0` form an infinite, finitely branching, prefix-closed tree. König gives a branch `z`,
and `μ({z}) >= ε`.

**Proof of 1.** Let `μ` be atomless and `ψ`-invariant, and put `S = supp μ`. `S` is closed and
`ψ`-invariant, and every open set meeting `S` has positive mass. Fix `x ∈ S` and write `h_j = h_j(x)`.
- **Case 1: `inf_j h_j = −∞`.** Then infinitely many `j >= 1` are new lows, `h_j < min_(i<j) h_i`.
  - At a new low, Lemma B gives `c_j <= N − h_j − 1`, so `|F_j| = c_j + h_j <= N − 1`, and
    `c_j >= −h_j → ∞`.
  - By invariance, `μ(C_(F_j)) = μ(C_(x[1..c_j])) <= ε_(c_j)`.
  - One word `F` with `|F| < N` equals `F_j` for infinitely many new lows, so `μ(C_F) = 0`.
  - But `x_j ∈ C_F ∩ S`. Contradiction.
- **Case 2: `inf_j h_j > −∞`.** The minimum is attained at some `j_0`. Put `x' = x_(j_0) ∈ S` and
  `g_j = h_(j_0+j) − h_(j_0) >= 0`; these are the heights of `x'`.
  - Lemma B at `x'` gives `c'_j <= N`. So with `w = x'[1..N]`, every `y ∈ C_w` satisfies
    `ψ^j y = F'_j σ^(c'_j) y`, and `ψ^j(C_w) = C_(Q_j)` with `Q_j = F'_j · w[c'_j+1..N]` of length
    `N + g_j`.
  - *2a: `g_j → ∞`.* Then `μ(C_w) = μ(C_(Q_j)) <= ε_(N+g_j) → 0`, but `x' ∈ C_w ∩ S`. Contradiction.
  - *2b: some value `D` occurs as `g_j` infinitely often.* Only finitely many words have length
    `N + D`, so `Q_j = Q_(j')` for some `j < j'`. Then `ψ^j y = Q_j σ^N y = ψ^(j') y` on `C_w`.
    So `ψ^(j'−j)` is the identity on `K = ψ^j(C_w)`, which contains `x_(j_0+j)`. Hence
    `x_(j_0+j) ∈ T(ψ)`, and so `x ∈ T(ψ)`, because `T(ψ)` is `ψ`-invariant.
  - A nonnegative integer sequence either tends to `∞` or repeats some value infinitely often. 2a is
    impossible, so 2b holds.
So `S ⊆ T(ψ)`. The sets `int Fix(ψ^n)` are open and increase along divisibility, and `S` is compact.
So `S ⊆ int Fix(ψ^J)` with `J` the lcm of a finite subcover. ∎

**Proof of 2.**
- Let `𝓜` be the set of `ρ(L)`-invariant probability measures. It is nonempty, because `L` is amenable
  and `C` is compact, and it is convex and weak-* compact.
- `ψ_*` maps `𝓜` into itself: `ψ_*μ(ρ(a)E) = μ(ψ^-1 ρ(a) E) = μ(ρ(α^-1 a) ψ^-1 E) = ψ_*μ(E)`.
- It is affine and continuous, so the Cesàro averages of `ψ_*^n μ_0` have a fixed limit point `μ`.
  This `μ` is invariant under `ψ` and `ρ(L)`.
- **If `μ` has atoms,** let `S` be the atoms of maximal mass. It is finite, nonempty and invariant
  under `ψ` and `ρ(L)`, so `ψ^(|S|!)` is the identity on `S`.
- **Otherwise,** put `S = supp μ`, which is `ρ(L)`-invariant, and use 1.
- For `z ∈ S`: `ρ(α^J a) z = ψ^J ρ(a) ψ^-J z = ψ^J ρ(a) z = ρ(a) z`, because `ψ^(±J)` fixes `S`
  pointwise and `ρ(a) z ∈ S`.
- If the action is free, `α^J(a) = a` for all `a`. ∎

**Proof of 3.** By 2, `(m^J − 1)·a ∈ ker(ρ|_S)` for every `a ∈ L`. Since `L` is divisible and
`m^J − 1 ≠ 0`, `(m^J − 1) L = L`. ∎

**Consequences (checks).**
- *Skew products.* If `δ(z, y) = (ψ z, ·)` and `q(z, y) = (ρ(q) z, ·)`, then `δ q δ^-1 = 2q` gives
  `ψ ρ(q) ψ^-1 = ρ(2q)` on the base. So 3 applies with `L = Q` and `m = 2`.
- *Hosts.* In `nV`, in the free colour of `2V_τ`, and in `SV_G`, an element that is a skew product over
  one coordinate with homeomorphic base is locally a prefix replacement in that coordinate. So its
  base lies in `V`. For `SV_G`: the `k`-th output of `w g` is `w_k(x_(g^-1 k))`, which depends on `x_k`
  alone only if `g` fixes `k`.
- *BS conjugators.* `L = ⋃_k ψ^-k ⟨a⟩ ψ^k` is abelian, hence amenable, and conjugation by `ψ` is the
  automorphism `a^t ↦ a^(mt)` of `L`.
