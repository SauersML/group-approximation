---
rg: 2
id: thompson-f-degree-aware-automaton-flows-cannot-certify-proof
kind: route
title: A vine pump with independent coins spreads the total leaf count binomially, so the joint law of automaton profile, tree count and caret count is split-stationary up to O(1/sqrt N), and a right translate carries flows on F into the monoid
target: thompson-f-degree-aware-automaton-flows-cannot-certify
requires:
  - thompson-f-finite-state-flows-cannot-prove-nonamenability
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
artifacts:
  - experiments/thompson-f-degree-aware-flow-certificates-2026-09-17/check_pumped_leaf_model.py
  - experiments/thompson-f-degree-aware-flow-certificates-2026-09-17/output.txt
---

## 0. Imported from the required claims

From the proof of `thompson-f-finite-state-flows-cannot-prove-nonamenability` (`FSF` below):

- **Forest model (FSF Lemma 1.1).** `M` acts on forests `y = (t_0, t_1, ...)` by `x_k y = merge_k(y)`,
  and `m ↦ m·e` is a bijection. For `s = x_(i_1) ... x_(i_d)` in normal form, `s y = z` iff
  `split_s z := split_(i_d)(... split_(i_1)(z))` is defined and equals `y`. Here `d = deg s` is the
  number of carets added.
- **Averaging principle (FSF Lemma 3.1).** Let `Ψ : M → X` be a map to a countable set, and
  `w(s, y) = G(s, Ψ(y))` with `G >= 0`, for a finite `S ⊆ M`. Suppose that for every `ε > 0` there is a
  random forest `Y` with countable support such that
  - `split_s Y` is defined almost surely for every `s ∈ S`, and
  - `TV(Ψ(split_s Y), Ψ(Y)) <= ε` for every `s ∈ S`.

  Then `sup_z (in-sum at z) >= inf_y (out-sum at y)`. The proof is four lines: in-sums bound every value
  of `w` by `C`, and `C >= E(in-sum at Y) = Σ_s E G(s, Ψ(split_s Y)) >= E(out-sum at Y) − |S| C ε`.
- **Towers (FSF Lemma 4.2).** Let `(Q', δ', ℓ')` be a tree invariant and `π` a probability on its states
  with `δ'_*(π ⊗ π) = π`. A complete binary top of depth `h`, with independent `π`-typed trees hung at
  its bottom leaves, has a `π`-distributed state.

From the proof of `thompson-f-nonamenable-iff-some-monomial-set-doubles`, Step 0: finitely many elements
of `M` have a common right multiple, and for every finite `S ⊆ F` there is `c ∈ M` with `S c ⊆ M`.

Notation for a forest `y`:
- `N_y = 1 + max{a : t_a ≠ •}`, with `N_e = 0`;
- `deg y` is the total number of carets;
- `Λ_y` is the number of leaves of `t_0, ..., t_(N_y − 1)`, so `Λ_y = N_y + deg y`.

## 1. The pump

Let `(Q, δ, ℓ)` be a finite tree automaton and `f : Q → Q`, `f(q) = δ(ℓ, q)`. The sequence of maps
`f^0, f^1, ...` takes finitely many values, so there are `j0 >= 0` and `m >= 1` with `f^(j0 + m) = f^(j0)`.

**Refined automaton.** `Q_m = Q × Z/m` with `ℓ_m = (ℓ, 1)` and
`δ_m((q, α), (q', α')) = (δ(q, q'), α + α')`. Then `q_m(T) = (q(T), leaves(T) mod m)`. The `Q`-profile is
a function of the `Q_m`-profile.

**Lemma 1.1.** Let `V_j = • ∧ (• ∧ (... ∧ •))` be the right vine with `j` carets, so `V_j = c^j(•)` with
`c(T) = • ∧ T`. Then `q_m(V_(j0)) = q_m(V_(j0 + m))` and `leaves(V_(j0 + m)) = leaves(V_(j0)) + m`.

*Proof.* `q(c^j(•)) = f^j(ℓ)` and `leaves(c^j(•)) = j + 1`. The first coordinates agree because
`f^(j0 + m) = f^(j0)`. The leaf counts differ by `m`, so their residues mod `m` agree. ∎

**Lemma 1.2 (substitution).** If `T'` arises from `T` by replacing one subtree `U` by `U'` with
`q_m(U) = q_m(U')`, then `q_m(T') = q_m(T)`.

*Proof.* Induct up the path from `U` to the root. At each node one child keeps its state and the other is
unchanged, so `δ_m` returns the same value. ∎

**Lemma 1.3 (measure on pumpable states).** Let `R` be the set of `Q_m`-states of all trees and `R_V` the
set of states of trees containing `V_(j0)` as a subtree. Then `R_V ≠ ∅`, and
`δ_m(R_V × R) ∪ δ_m(R × R_V) ⊆ R_V`. There is a probability `π` on `R_V` with `(δ_m)_*(π ⊗ π) = π`.

*Proof.* `V_(j0)` contains itself. If `L` contains `V_(j0)`, so do `L ∧ R` and `R ∧ L`. So `R_V` is
closed under `δ_m`, and `π ↦ (δ_m)_*(π ⊗ π)` is a continuous self-map of the simplex on the finite set
`R_V`. Brouwer's theorem gives a fixed point. ∎

For each `r ∈ R_V`:
- fix a tree `T^0_r` containing `V_(j0)` with `q_m(T^0_r) = r`;
- let `T^1_r` be `T^0_r` with one copy of `V_(j0)` replaced by `V_(j0 + m)`.

By Lemmas 1.1 and 1.2, `q_m(T^1_r) = r` and `leaves(T^1_r) = leaves(T^0_r) + m`. Put
`L_max = max_r leaves(T^1_r)`.

## 2. The pumped leaf model and the monoid form

Fix a finite `S ⊆ M`. Put:
- `D = max_(s ∈ S) deg s` and `H = D + 1`;
- `I` the largest generator index in the normal forms of `S` (`I = 0` if there is none);
- integers `n_0 >= I + D + 1`, `L >= n_0` and `K = L − n_0 + 1`.

**Model.** Choose `N` uniformly in `{n_0, ..., L}`. Given `N`, for `a < N` and `b < 2^H` choose
independently `r_(a,b) ~ π` and `ε_(a,b) ∈ {0, 1}` with probability `1/2` each. Let `t_a` be the complete
binary tree of depth `H` with `T^(ε_(a,b))_(r_(a,b))` hung at its `b`-th bottom leaf. Put `t_a = •` for
`a >= N` and `Y = (t_a)`. The support is countable.

The statistic is `Ψ(y) = (p_m(y), N_y, Λ_y)`, where `p_m` is the `Q_m`-profile. It determines
`(p(y), N_y, deg y)`.

**Lemma 2.1 (splits).** Fix `s = x_(i_1) ... x_(i_d) ∈ S`. Then `split_s Y` is defined. Its trees
`u_0, ..., u_(N+d−1)` are the subtrees of `Y` at an antichain `v_0, ..., v_(N+d−1)` of nodes in the tops,
listed left to right. The depth `k_a` of `v_a` satisfies `k_a <= d`. The sequence `(k_a)` depends only on
`s`: it is `(0, ..., 0)` modified in its first `I + d + 1` places. At most `d` of the `N` roots are split,
so at least `N − d` of the `v_a` are roots. Moreover `N_(split_s Y) = N + d` and
`Λ_(split_s Y) = Λ_Y`.

*Proof.* The first part is the induction of FSF Theorem 4.3: each split acts on an index `<= I < N` at a
node of depth `< H`, which is internal. The depth sequence evolves by replacing the entry at index `i_j`
by two copies of itself plus one, independently of `N` and of the hung trees. All `N + d` final nodes have
depth `< H`, so they are nontrivial and `N_(split_s Y) = N + d`. Splitting a tree into its two children
keeps the multiset of leaves, so `Λ` is unchanged. ∎

**Lemma 2.2 (conditional structure).** For a node `v` of depth `k` in a top, let `W_v` be its subtree. Then:

- (a) the pairs `(q_m(W_(v_a)), leaves(W_(v_a)))`, `a < N + d`, are independent given `N`;
- (b) the law of each pair depends only on `k_a`, and each state is `π`-distributed;
- (c) given the bottom states `r_b` under `v_a`, `leaves(W_(v_a)) = c + m · Bin(2^(H − k_a), 1/2)`, where
  `c = Σ_b leaves(T^0_(r_b))`;
- (d) `leaves(W_(v_a)) ≡ α_a (mod m)`, where `α_a` is the `Z/m`-coordinate of `q_m(W_(v_a))`.

*Proof.*
- (a) Antichain nodes sit over disjoint sets of bottom leaves, and the hung data are independent.
- (b) `W_(v_a)` is a complete top of depth `H − k_a` over independent hung trees, each of state
  `r ~ π` whatever its coin. Lemma 1.3 and FSF Lemma 4.2 give a `π`-distributed state.
- (c) Coins are independent of states, and `T^1_r` has `m` more leaves than `T^0_r`.
- (d) This is the definition of `q_m`. ∎

Let `ν_n` be the law of `Ψ(Y)` given `N = n`, and `ν'_n` the law of `Ψ(split_s Y)` given `N = n`.

**Lemma 2.3.** `TV(ν'_n, ν_(n+d)) <= 2 d · 2^(H/2) · L_max / (m · √(n − d))`.

*Proof.*
- *Profiles.* Under both laws the second coordinate is `n + d`. The first `n + d` profile entries are
  i.i.d. `π` (Lemma 2.2(b)), and all later entries equal `ℓ_m`. So the profile marginals agree, and
  `TV = E_ξ TV(law(Λ | ξ), law'(Λ | ξ))` over the common profile law.
- *Splitting `Λ`.* Fix `ξ`. Let `J` be the set of positions with `k_a > 0` in `split_s Y`, so
  `|J| <= 2d`. Its complement `J^c` has at least `n − d` positions. In `ν_(n+d)` every position is a
  depth-0 top. By Lemma 2.2(a), given `ξ`, `Λ` is a sum of independent position terms. The terms at `J^c`
  have the same conditional law in both models. So `Λ = A + B` under `ν'_n` and `Λ = A + B'` under
  `ν_(n+d)`, where:
  - `A` has the same law in both, and `A` is independent of `B` and of `B'`;
  - the nodes in `J` lie below at most `d` roots, so `0 <= B <= d · 2^H · L_max`;
  - `0 <= B' <= 2d · 2^H · L_max`;
  - by Lemma 2.2(d), `B ≡ B' ≡ Σ_(a ∈ J) α_a (mod m)`.
- *Conditioning on the bottom states.* Condition also on the bottom states under `J^c`. By Lemma 2.2(c),
  `A = c + m · Bin(n_A, 1/2)` with `n_A = 2^H |J^c| >= 2^H (n − d)`. For fixed values `x` of `B` and `x'`
  of `B'`, `t = (x' − x)/m` is an integer with `|t| <= 2d · 2^H · L_max / m`, and
  `TV(A + x, A + x') = TV(Bin, Bin + t)`. Total variation is convex under mixtures, so it suffices to bound
  `TV(Bin(n_A, 1/2), Bin(n_A, 1/2) + t)`.
- *Binomial estimate.* By the triangle inequality this is at most `|t| · TV(Bin, Bin + 1)`. The binomial
  law is unimodal, so `Σ_k |p_k − p_(k−1)| = 2 max_k p_k` and `TV(Bin, Bin + 1) = max_k p_k`. The bound
  `max_k p_k <= 1/√(n_A)` follows from these steps:
  - `(binom(2j, j)/4^j)^2 = Π_(i=1)^j ((2i−1)/(2i))^2 <= Π_(i=1)^j ((2i−1)/(2i)) · ((2i)/(2i+1)) = 1/(2j+1)`;
  - this settles `n_A = 2j`;
  - for `n_A = 2j+1`, `max p = binom(2j, j)/4^j · (2j+1)/(2j+2)`, which is also `<= 1/√(n_A)`.
- *Conclusion.* `TV <= (2d · 2^H · L_max / m) / √(2^H (n − d))`, which is the stated bound. ∎

**Theorem 2.4 (monoid form).** For every `G >= 0`, the rule `w(s, y) = G(s, p(y), N_y, deg y)` satisfies
`sup_z (in-sum at z) >= inf_y (out-sum at y)`.

*Proof.* The rule is a function of `(s, Ψ(y))`. Let `μ = K^-1 Σ_(n=n_0)^L ν_n` be the law of `Ψ(Y)`
and `μ_s = K^-1 Σ_n ν'_n` the law of `Ψ(split_s Y)`. The `ν_n` have disjoint supports (second
coordinate), so `TV(K^-1 Σ_n ν_(n+d), μ) <= d/K`. With Lemma 2.3,

`TV(μ_s, μ) <= D/K + 2D · 2^(H/2) · L_max / (m √(n_0 − D))`.

`H`, `L_max` and `m` do not depend on `n_0` or `K`. Taking `n_0` and then `K` large makes this `<= ε`
for all `s ∈ S`. The averaging principle applies. ∎

## 3. The group form

**Theorem 3.1.** Let `S ⊆ F` be finite and `Ψ_F : F → X` a map such that `Ψ_F(y) = Φ(p(y), N_y, deg y)`
for `y ∈ M`, for some finite automaton and some map `Φ`. No `w(s, g) = G(s, Ψ_F(g)) >= 0` satisfies (out)
with `λ > 1` and (in) `<= 1` on `F`.

*Proof.* Suppose it does.
- *Translate into `M`.* By Step 0 choose `c = x_(j_1) ... x_(j_e) ∈ M` with `S c ⊆ M`. Put `S' = S c`;
  `s ↦ s c` is injective. For `y ∈ M` define `w'(s c, y) = w(s, c y)`.
- *Out-sums.* `Σ_(s' ∈ S') w'(s', y) = Σ_s w(s, c y) >= λ`.
- *In-sums.* For `z ∈ M`, the in-sum of `w'` at `z` is the sum of `w(s, c y)` over pairs `(s, y)` with
  `y ∈ M` and `s c y = z`. The map `(s, y) ↦ (s, c y)` is injective into the pairs `(s, g)` with `s g = z`.
  So this in-sum is at most the in-sum of `w` at `z`, which is `<= 1`.
- *`w'` is a monoid rule.* `c y = merge_(j_1)(... merge_(j_e)(y))` lies in `M`, and
  `w'(s', y) = G(s, Φ(p(c y), N_(cy), deg(c y)))`. One merge changes these data through `(p, N, deg)`
  alone:
  - `p(merge_k y)` replaces entries `k, k+1` by `δ(p_k, p_(k+1))` and shifts the rest left;
  - `N_(merge_k y)` is `N_y − 1` if `k + 1 < N_y`, is `N_y` if `k + 1 = N_y`, and is `k + 1` if
    `k >= N_y`;
  - `deg` increases by 1.

  So `w'(s', y) = G'(s', p(y), N_y, deg y)`.
- *Contradiction.* Theorem 2.4 for `S'` gives `1 >= sup(in) >= inf(out) >= λ > 1`. ∎

*Example.* Every `g ∈ F` has a unique Cannon–Floyd–Parry normal form
`x_(i_1) ... x_(i_k) x_(j_l)^-1 ... x_(j_1)^-1` (Cannon–Floyd–Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996), §2; imported, used only for this example). Put
`p_g = x_(i_1) ... x_(i_k)` and `q_g = x_(j_1) ... x_(j_l)`. For `y ∈ M` the positive normal form satisfies
the normal-form conditions, which only concern letters occurring with both signs. So `p_y = y` and
`q_y = 1`. Hence `Ψ_F(g) = (p(p_g), N_(p_g), deg p_g, q_g)` meets the hypothesis, and rules may read `q_g`
without restriction.

## 4. Calibration and the gate

- *Free group, `S = {a, b}`.* The rule `w ≡ 1` is a certificate with `λ = 2`. Step 0 fails there, since
  `a M ∩ b M = ∅` in the free monoid, and so do Lemma 2.1 and the translate `c`.
- *The coin is necessary.* With `ε ≡ 0`, a one-state support gives `Λ = 2^H · N · leaves(T^0)`. That is
  a function of `N`, and `Λ_(split_s Y) = Λ_Y` sits at the wrong value for `N + d`. The script finds
  `TV = 1` for all `n` tested.
- *The refinement mod `m` is necessary.* Without it `B − B'` need not be a multiple of the pump
  increment, and `A + x`, `A + x'` could lie on disjoint cosets.
- *Gate.* The data used jointly are:
  - all automaton states;
  - a global additive counter, via a single binomial smoothing;
  - the negative part.

  Per-tree unbounded data (individual sizes, depths, exact shapes) are not covered. For them the model
  would need the size law of a split child to match that of a root, which the min-size argument of FSF §5
  rules out for product laws.

## 5. Computation

`experiments/thompson-f-degree-aware-flow-certificates-2026-09-17/check_pumped_leaf_model.py` (stdlib and
numpy, single thread; output in `output.txt`):

1. Checks Lemma 1.1 and finds `π` (residual `<= 1.1e-16`) for 6 automata: leaves mod 2, depth truncated at
   2, "is a right vine", and three random automata with 2 or 3 states.
2. Brute force for `N = 2`, `H = 2` and `s ∈ {x_0, x_1}`. It enumerates all forests of the model, applies
   real splits, and checks `N + d`, `deg − d`, and that the law of `(p_m, N, deg)` equals the product law
   of Lemma 2.2, with difference `0`.
3. Exact `TV(ν'_n, ν_(n+d))` for `s = x_1` (`H = 2`) and `s = x_0 x_2` (`H = 3`), up to `n = 512`. Every
   value lies below Lemma 2.3's bound, and `√n · TV` levels off.
4. Control without coins: `TV = 1.0000` at `n = 4, 16, 64` for the two one-state examples.
