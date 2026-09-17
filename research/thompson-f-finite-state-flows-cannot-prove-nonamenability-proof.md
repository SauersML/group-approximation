---
rg: 2
id: thompson-f-finite-state-flows-cannot-prove-nonamenability-proof
kind: route
title: An idempotent state measure makes a random forest split-stationary for the automaton profile, and averaging the flow inequalities over it gives inflow at least outflow
target: thompson-f-finite-state-flows-cannot-prove-nonamenability
requires:
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
artifacts:
  - experiments/thompson-f-finite-automaton-certificates-2026-09-17/check_idempotent_forest_model.py
  - experiments/thompson-f-finite-automaton-certificates-2026-09-17/output.txt
---

Throughout, `M` is the positive monoid of `F`:
- generators `x_0, x_1, ...`;
- relations `x_j x_i = x_i x_(j+1)` for `i < j`;
- unique normal forms `x_(i_1) ... x_(i_d)` with `i_1 <= ... <= i_d`.

`M` embeds in `F`, so it is cancellative on both sides.

## 1. Forest model

A *forest* is a sequence `y = (t_0, t_1, ...)` of finite binary trees, all but finitely many equal to
the one-vertex tree `•`. Let `Φ` be the set of forests and `e = (•, •, ...)`. Two maps act on `Φ`:
- `merge_k` replaces `t_k, t_(k+1)` by the single tree `t_k ∧ t_(k+1)` and shifts `t_(k+2), ...` one
  place left;
- `split_k` is defined when `t_k ≠ •` and replaces `t_k = L ∧ R` by `L, R`, shifting later trees right.

`merge_k` is injective with image `{z : z_k ≠ •}`, and `split_k` is its inverse there.

**Lemma 1.1.** `x_k · y := merge_k(y)` extends to a left action of `M` on `Φ`, and `m ↦ m·e` is a
bijection `M → Φ`.

*Proof.* Let `i < j`. First apply `merge_(j+1)`, which joins roots `j+1, j+2`, then `merge_i`, which
joins roots `i, i+1`. The result has both pairs joined, the second pair at index `j`. First applying
`merge_i` moves roots `j+1, j+2` to `j, j+1`, and `merge_j` then joins them. So
`merge_j ∘ merge_i = merge_i ∘ merge_(j+1)`. The defining relations hold, and the action is well
defined.

*Surjective.* Induct on the number of carets. If `z ≠ e`, pick `k` with `z_k ≠ •`. Then
`z = merge_k(split_k z)`.

*Injective.* Let `m = x_(i_1) ... x_(i_d)` be in normal form and `u = x_(i_2) ... x_(i_d) · e`. By
induction, all trees of `u` with index `< i_2` are trivial (vacuous if `d = 1`). Since `i_1 <= i_2`,
`merge_(i_1)` leaves indices `< i_1` trivial and makes index `i_1` nontrivial. So `i_1` is the least
nontrivial index of `m·e`, `u = split_(i_1)(m·e)`, and `d` is the number of carets. By induction on `d`,
`m·e` determines the normal form of `m`. ∎

From now on `M` and `Φ` are identified. For `s = x_(i_1) ... x_(i_d)` in normal form, `s y = z` holds iff
`split_s z := split_(i_d)( ... split_(i_1)(z))` is defined and equals `y`. Such a `y` is unique. The
experiment checks the relations and injectivity on all 462 normal forms of degree `<= 5` in `x_0..x_5`.

## 2. Certificates

For finite `S ⊆ M`, a certificate is `w : S × M → [0, ∞)` with (out) `Σ_s w(s, y) >= λ` for all `y`
and (in) `Σ_(s: split_s z defined) w(s, split_s z) <= 1` for all `z`.

**Lemma 2.1.**
- (a) If a certificate with `λ > 1` exists, then `F` is not amenable.
- (b) If `F` is not amenable, then for some `d, m` there is a certificate with `S = S_(m+1,m+d+1)`,
  `λ = 2` and `w ∈ {0,1}`.

*Proof of (a).* For finite `Y`:
`λ|Y| <= Σ_(y ∈ Y) Σ_s w(s,y) <= Σ_(z ∈ SY) (in-sum at z) <= |SY|`.
Iterating gives `|S^k Y| >= λ^k |Y| >= 2|Y|` for `k` with `λ^k >= 2`, so the finite set `S^k ⊆ M` is
doubling. By item 1 of `thompson-f-nonamenable-iff-some-monomial-set-doubles`, `F` is not amenable.

*Proof of (b).* By item 2 of that claim, `S = S_(m+1,m+d+1)` is doubling for some `d, m`. Form the
bipartite graph with left vertices `M × {1,2}`, right vertices `M`, and edges `(y,c) — s y` for
`s ∈ S`. Left degrees are finite. Hall's condition holds: for finite `A` with projection `Y`,
`|N(A)| = |SY| >= 2|Y| >= |A|`. By M. Hall's theorem for bipartite graphs with finite left degrees
(M. Hall, *Distinct representatives of subsets*, Bull. AMS 54 (1948)), there is a matching saturating
the left side.

Put `w(s,y) = 1` iff `(y,1)` or `(y,2)` is matched to `s y`, and `0` otherwise. The two copies of `y` go
to distinct right vertices, and `s y = s' y` forces `s = s'`. So the out-sum is exactly 2. Distinct
pairs `(s, y)` with `w = 1` and `s y = z` correspond to distinct left vertices matched to `z`, so the
in-sum is at most 1. ∎

## 3. Split-stationary statistics

**Lemma 3.1 (averaging principle).** Let `Ψ : M → X` be any map to a countable set, and let
`w(s, y) = G(s, Ψ(y))` with `G >= 0`. Suppose that for every `ε > 0` there is a random forest `Y` with
countable support such that:
- `split_s Y` is defined almost surely for every `s ∈ S`;
- for every `s ∈ S`, the laws of `Ψ(split_s Y)` and `Ψ(Y)` are within total variation `ε`.

Then `sup_z (in-sum at z) >= inf_y (out-sum at y)`.

*Proof.* Let `C = sup_z (in-sum at z)` and `λ = inf_y (out-sum at y)`. Assume `C < ∞`. Every term of an
in-sum is nonnegative, so `w(s,y) <= (in-sum at s y) <= C` for all `s, y`. Hence `0 <= G(s, ξ) <= C` for
every value `ξ = Ψ(y)`, and in particular on the supports of both laws. For `f` with values in `[0, C]`,
`|E f(ξ) − E f(ξ')| <= C · TV(ξ, ξ')`. Because all splits of `Y` are defined,

`C >= E (in-sum at Y) = Σ_s E G(s, Ψ(split_s Y)) >= Σ_s E G(s, Ψ(Y)) − |S| C ε = E (out-sum at Y) − |S| C ε >= λ − |S| C ε.`

Let `ε → 0`. ∎

*Remark.* With `Ψ = id`, the hypothesis says that the finite set `S` admits approximately split-invariant
random forests. Lemma 3.1 then excludes every certificate for that `S`, and Lemma 2.1(b) turns this for
all `S_(m+1,m+d+1)` into amenability of `F`. So the lemma is useful only for coarse statistics `Ψ`. The
theorem below says every finite-state statistic is coarse enough.

## 4. Finite tree invariants

Let `(Q, δ, ℓ)` be a tree invariant: `q(•) = ℓ`, `q(L ∧ R) = δ(q(L), q(R))`. Let `R = q(trees)` be the
set of reachable states. It contains `ℓ` and is closed under `δ`. For each `r ∈ R`, fix a tree `T_r`
with `q(T_r) = r`. For a forest `y`, let `N_y = 1 + max{a : t_a ≠ •}` (`N_e = 0`) and
`p(y) = (q(t_a))_(a >= 0)`. Put `Ψ(y) = (p(y), N_y)`.

**Lemma 4.1 (idempotent measure).** If `Q` is finite, there is a probability `π` on `R` with
`δ_*(π ⊗ π) = π`.

*Proof.* The map `π ↦ δ_*(π ⊗ π)` sends the simplex of probability vectors on `R` into itself, since
`δ(R × R) ⊆ R`. Its coordinates are quadratic polynomials, so it is continuous, and Brouwer's theorem
gives a fixed point. ∎

**Lemma 4.2 (towers).** Let `π` be idempotent. Attach independent `π`-distributed states `r_b` to the
`2^h` bottom leaves of the complete binary tree of depth `h`, and hang `T_(r_b)` there. The state of
the resulting tree is `π`-distributed.

*Proof.* Induct on `h`. The two halves are independent and each is `π`-distributed by induction, so the
root state has law `δ_*(π ⊗ π) = π`. ∎

**Theorem 4.3.** Let `S ⊆ M` be finite and `(Q, δ, ℓ)` a finite tree invariant, or more generally any
tree invariant into a countable set whose reachable states carry an idempotent probability `π`. For
every `G >= 0`, the rule `w(s,y) = G(s, p(y), N_y)` satisfies `sup (in-sum) >= inf (out-sum)`. In
particular no certificate with `λ > 1` has this form.

*Proof.* We verify the hypothesis of Lemma 3.1 for `Ψ = (p, N)`.

*Parameters.* Let `D_S = max_(s ∈ S) deg s`, `H = D_S + 1`, and let `I` be the largest generator index
occurring in the normal forms of `S` (`I = 0` if there is none). Put `n_0 = I + 1`, and let `L > n_0`,
`K = L − n_0 + 1`.

*Model.* Choose `N` uniformly in `{n_0, ..., L}`. Given `N`, choose independent states `r_(a,b) ~ π` for
`a < N` and `b < 2^H`. Let `t_a` be the complete binary tree of depth `H` with `T_(r_(a,b))` hung at its
`b`-th bottom leaf (for `a < N`), and `t_a = •` for `a >= N`. Let `Y = (t_a)`. Then `N_Y = N`, since the
tops have depth `H >= 1`.

*All splits exist.* Fix `s = x_(i_1) ... x_(i_d) ∈ S`. We claim that after `j <= d` splits the forest
has the form `(u_0, ..., u_(N+j−1), •, ...)`, where the `u_a` are the subtrees of `Y` rooted at an
antichain of nodes `v_0, ..., v_(N+j−1)`, listed left to right, in the tops, each of depth `<= j`.

This holds for `j = 0`. At step `j+1` we split index `i_(j+1) <= I < n_0 <= N <= N + j`. The node
`v_(i_(j+1))` has depth `<= j < H`, so it is internal to its top and `u_(i_(j+1)) ≠ •`. The split is
defined and replaces that node by its two children, of depth `<= j + 1`. The antichain and ordering
are preserved.

After `d` splits, all `N + d` nodes have depth `<= d < H`. Their subtrees are nontrivial, so
`N_(split_s Y) = N + d`.

*Profile law.* The subtree at `v_a`, of depth `k`, is a complete depth-`(H−k)` top over the `T_r` below
`v_a`. By Lemma 4.2 its state is `π`-distributed. Antichain nodes have disjoint sets of bottom leaves,
so the `N + d` states are independent. Entries of index `>= N + d` equal `ℓ`.

Let `ν_n` be the law of `(ξ, n)`, where `ξ` has i.i.d. `π` entries in positions `< n` and `ℓ` after. The
same argument with `d = 0` shows that `Ψ(Y)` has law `μ = K^(−1) Σ_(n=n_0)^L ν_n`, while
`Ψ(split_s Y)` has law `μ_s = K^(−1) Σ_(n=n_0+d)^(L+d) ν_n`. The `ν_n` have disjoint supports (second
coordinate), so `TV(μ, μ_s) = d / K <= D_S / K`. That tends to 0 as `L → ∞`.

The model has countable support, so Lemma 3.1 applies. ∎

**Corollary 4.4.** No certificate for any finite `S` and any `λ > 1` is a function of `s`, the profile of
a finite tree automaton, and the number of trees. Examples of such rules:
- the shape of each tree truncated at depth `K` (states: truncated shapes, `δ` = join and truncate);
- the sizes or depths of the trees modulo fixed integers;
- membership of each tree in finitely many regular tree languages;
- any finite combination of these, read jointly over all trees.

## 5. Calibration and the gate

*The free monoid.* In `{a,b}*` with `S = {a,b}`, the rule `w ≡ 1` gives out-sum 2 and in-sum `<= 1`.
It is a constant rule, so it is a function of any profile. Lemma 3.1 cannot apply, since `split_a z` and
`split_b z` are never both defined. The step of Theorem 4.3 that uses a property of `M` is "all splits
exist": `Y` lies in `∩_(s ∈ S) sM`, which is nonempty because any two elements of `M` have a common right
multiple (the Ore property).

*Consistency with both answers.* The theorem is a statement about rules, not about `F`. If `F` is not
amenable, the certificates of Lemma 2.1(b) exist and must depend on data outside every finite automaton.

*Exact gate.* The proof uses finiteness of `Q` only through Lemma 4.1, and Theorem 4.3 is already stated
for countable invariants with idempotent measures. The natural infinite invariants fail exactly there.
- *Identity (free magma), size, number of leaves.* If `π` is a probability on trees, or on sizes with
  `δ(a,b) = a + b + 1`, and `m` is the least size in its support, then the least size in the support of
  `δ_*(π ⊗ π)` is `2m + 1 > m`. So no idempotent `π` exists.
- *Depth.* `depth(L ∧ R) >= 1 + min` gives the same conclusion.
- *Free binary system.* Moore, arXiv:1807.05469, shows it carries no idempotent mean (finitely
  additive). This refuted his earlier route to amenability. The present theorem is the countably
  additive finite-quotient counterpart: every finite quotient of the free binary system does carry an
  idempotent measure, and so is useless for certificates.

A certificate must therefore read a tree invariant without idempotent measures, such as sizes, depths or
exact shapes, and in a way that is not coarse in the sense of Lemma 3.1.

## 6. Not covered

- Rules that also depend on the total number of carets. In the model it correlates with `N`, and
  splitting changes it by `−deg s` while changing `N` by `+deg s`, so the shift trick does not apply
  as it stands.
- Flows on the Cayley graph of `F` (pairs of forests) and rules continuous in a compact infinite state
  space.

## 7. Computation

`experiments/thompson-f-finite-automaton-certificates-2026-09-17/check_idempotent_forest_model.py` (stdlib,
output in `output.txt`):
1. checks Lemma 1.1 on degree `<= 5`;
2. finds idempotent `π` for 16 random automata with `|Q| ∈ {2, 3}` and support of at least 2 states, with
   residual `<= 3.9e-16`;
3. enumerates the model exactly for `N = 4`. With `H = 2` (support 2) it uses `S = X_2 ∪ S_(3,5)`; with
   `H = 1` (support 3) it uses `S = X_2`. The profile law of `split_s Y` equals the i.i.d. law of length
   `N + deg s` up to `9.7e-15`;
4. runs a control with the non-idempotent uniform `π` on a constant automaton, which gives total variation
   `0.875`, so the test detects failures.

In item 3, `H = deg s` is used rather than `D_S + 1`. That is enough for the profile law. Theorem 4.3
takes `H = D_S + 1` only so that `N_(split_s Y) = N + deg s`.
