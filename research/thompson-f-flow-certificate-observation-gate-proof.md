---
rg: 2
id: thompson-f-flow-certificate-observation-gate-proof
kind: route
title: Sion's minimax theorem turns "no flow rule reading Psi has ratio above lambda" into "Psi admits lambda-dominated shadow laws", and a padded idempotent forest model supplies such laws for profile, tree count and caret count
target: thompson-f-flow-certificate-observation-gate
requires:
  - thompson-f-finite-state-flows-cannot-prove-nonamenability
  - thompson-f-nonamenable-iff-some-monomial-set-doubles
---

Notation. `M` is the positive monoid of `F`, identified with the set of forests as in Section 1 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` (`x_k` merges roots `k, k+1`; `M` is
cancellative; `s y = z` iff `split_s z` is defined and equals `y`). For a finite `S ⊆ M` and a map
`Ψ : M → X` into any set, a *rule reading `Ψ`* is a function `G : S × X → [0, ∞)`. It defines

- `out_G(y) = Σ_(s ∈ S) G(s, Ψ(y))`,
- `in_G(z) = Σ_(s ∈ S, z ∈ sM) G(s, Ψ(split_s z)) = Σ_(s ∈ S) Σ_(y : s y = z) G(s, Ψ(y))`.

`P(M)` is the set of probability vectors in `l^1(M)` (countable support allowed). For `η ∈ P(M)` and
`s ∈ S` put `ρ^η_s(y) = η(s y)`. This is a sub-probability vector, since `y ↦ s y` is injective. For a
finite signed measure `ν` on `X`, `||ν_+||` is the total mass of its positive part.

**Defect.** For `λ >= 1`, `μ, η ∈ P(M)`:

`D_λ(μ, η) = Σ_(s ∈ S) || (Ψ_* μ − λ Ψ_* ρ^η_s)_+ ||`,  and  `δ_λ(Ψ) = inf_(μ, η ∈ P(M)) D_λ(μ, η)`.

The group version replaces `M` by `F`, `S` by a finite subset of `F`, `split_s z` by `s^-1 z`, and
`ρ^η_s(g) = η(s g)`, which is then a probability vector. Every step below is unchanged.

## 1. The minimax gate

**Theorem A.** Let `S ⊆ M` be finite, `Ψ : M → X`, and `λ >= 1`. The following are equivalent.

1. There is a rule `G` reading `Ψ` with `sup_z in_G(z) < ∞` and `inf_y out_G(y) > λ · sup_z in_G(z)`.
2. `δ_λ(Ψ) > 0`.

*Reduction to a box.* Replace `X` by `Ψ(M)`; values of `G` off `Ψ(M)` enter neither sum. If `G` is as in
item 1, put `c = sup in_G`. Then `c > 0`: if `c = 0` then `G(s, Ψ(y)) = 0` for all `s, y`, because the
term `G(s, Ψ(y))` occurs in `in_G(s y)`, so `out_G ≡ 0`, which contradicts `inf out_G > 0`. Every term of
an in-sum is at most the in-sum, so `G(s, Ψ(y)) <= c` for all `s, y`. Hence `G/c` takes values in
`[0,1]` on `S × Ψ(M)`, and item 1 is equivalent to

`V := sup_(G ∈ 𝒢) ( inf_y out_G(y) − λ sup_z in_G(z) ) > 0`,  where `𝒢 = [0,1]^(S × X)`.

(Conversely `G ∈ 𝒢` with positive value has `sup in_G <= |S| < ∞`.)

*Payoff.* For `G ∈ 𝒢` and `(μ, η) ∈ P(M)^2` let

`Φ(G; μ, η) = Σ_y μ(y) out_G(y) − λ Σ_z η(z) in_G(z) = Σ_(s ∈ S) Σ_(x ∈ X) G(s, x) (Ψ_* μ − λ Ψ_* ρ^η_s)(x)`.

The second form follows by reindexing `z = s y`. All sums converge absolutely, with
`|Φ| <= |S|(1 + λ)`.

- For fixed `G`, `inf_(μ,η) Φ = inf_y out_G(y) − λ sup_z in_G(z)`: the two parts separate, and a linear
  functional of a probability vector has the same infimum (supremum) as over point masses.
- For fixed `(μ, η)`, `max_G Φ = D_λ(μ, η)`: take `G(s, x) = 1` exactly where the bracket is positive.

*Topologies.* Give `𝒢` the product topology; it is compact (Tychonoff) and convex. For fixed `(μ, η)`,
`G ↦ Φ(G; μ, η)` is continuous. Indeed `Φ = Σ_(s,x) G(s,x) w(s,x)` with `w ∈ l^1(S × X)`. Given `ε`, pick
a finite set `E` carrying all but `ε` of `||w||`. If a net `G_α → G` pointwise, the sum over `E` converges
and the rest changes by at most `2ε`. Give `P(M)^2` the norm topology of `l^1(M)^2`; it is a convex
subset of a normed space. For fixed `G`, `(μ, η) ↦ Φ` is affine and Lipschitz, since `||Ψ_* ν|| <= ||ν||`
and `||ρ^η_s − ρ^(η')_s|| <= ||η − η'||`.

*Sion.* Sion's minimax theorem (M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958)
171–176; elementary proof in H. Komiya, Kodai Math. J. 11 (1988) 5–7; quoted in its standard form, the
corollary number was not re-read): if `A` is a compact convex subset of a topological vector space, `B` a convex
subset of a topological vector space, and `f : A × B → R` is lower semicontinuous and quasi-convex in the
first variable and upper semicontinuous and quasi-concave in the second, then
`min_(a) sup_(b) f = sup_(b) min_(a) f`. Apply it with `A = 𝒢` (inside `R^(S × X)` with the product
topology), `B = P(M)^2`, and `f = −Φ`, which is affine and continuous in each variable separately:

`max_G inf_(μ,η) Φ = inf_(μ,η) max_G Φ = δ_λ(Ψ)`.

The left side is `V`. So `V > 0` iff `δ_λ(Ψ) > 0`. ∎

**Corollary A.1 (class kill).** If `δ_λ(Ψ) = 0` for every `λ > 1`, then no rule reading `Ψ` is a
certificate in the sense of `thompson-f-finite-state-flows-cannot-prove-nonamenability` (out-sum
`>= λ > 1`, in-sum `<= 1`). Since `D_λ` is nonincreasing in `λ`, it suffices that `δ_1(Ψ) = 0`.

*Proof.* A certificate with ratio `λ > 1` satisfies item 1 for every `λ' ∈ [1, λ)`. ∎

**Corollary A.2 (Lemma 3.1 of the finite-state proof is the case `μ = η`).** If for every `ε > 0` there
is `μ ∈ P(M)` with `μ(∩_s sM) = 1` and `||Ψ_* ρ^μ_s − Ψ_* μ|| <= ε` for all `s`, then `δ_1(Ψ) = 0`.

*Proof.* `ρ^μ_s` is then the law of `split_s Y` for `Y ~ μ`, a probability vector, and
`D_1(μ, μ) <= Σ_s ||Ψ_* μ − Ψ_* ρ^μ_s|| <= |S| ε`. ∎

**Corollary A.3 (the gate).** `F` is not amenable iff there are `d, m >= 1` and `λ > 1` with
`δ_λ(id_M) > 0` for `S = S_(m+1,m+d+1)`.

*Proof.* If `F` is not amenable, Lemma 2.1(b) of the finite-state proof gives a `{0,1}`-valued
certificate with ratio 2 for some such `S`, which reads `id_M`; apply Theorem A with `λ = 3/2`. If
`δ_λ(id_M) > 0` with `λ > 1`, Theorem A gives a rule with `inf out > λ sup in`; rescaling gives a
certificate with ratio `> 1`, and Lemma 2.1(a) of that proof makes `F` non-amenable. ∎

**Lemma A.4 (coarsening).** If `Ψ = φ ∘ Ψ'` for a map `φ : X' → X`, then `δ_λ(Ψ) <= δ_λ(Ψ')`.

*Proof.* `Ψ_* = φ_* Ψ'_*`, and pushing forward a signed measure does not increase the mass of its
positive part: `(φ_* ν)_+ <= φ_*(ν_+)`. ∎

So the dead observations (`δ_1 = 0`) form a down-set under coarsening, and a surviving certificate must
read an observation outside it.

## 2. Dead observations

**B.1 (constant observation).** `Ψ` constant has `δ_1(Ψ) = 0`. Take `z ∈ ∩_(s ∈ S) sM`, which exists
because any two elements of `M` have a common right multiple, and `μ = η = δ_z`. Then every `ρ^η_s` is a
point mass, so `Ψ_* μ = Ψ_* ρ^η_s` and `D_1 = 0`. In the group version `S ⊆ F` is arbitrary and the same
holds. *Calibration:* in the free monoid `{a,b}*`, `aM ∩ bM = ∅`, `ρ^η_a + ρ^η_b` has mass at most 1, and
`w ≡ 1` is a certificate with ratio 2.

**B.2 (Schreier observations, group version).** Let `H <= F` and `Ψ(g) = gH` in `X = F/H`. If the left
action of `F` on `F/H` has Følner sets (for every `ε` a finite nonempty `A ⊆ F/H` with
`|s^-1 A Δ A| <= ε|A|` for `s ∈ S`), then `δ_1(Ψ) = 0`. Choose one representative of each coset in `A`
and let `μ` be uniform on them. Then `(Ψ_* ρ^μ_s)(x) = Σ_(g ∈ x) μ(s g) = (Ψ_* μ)(s x)`, the uniform
measure on `s^-1 A`, and `D_1(μ, μ) <= Σ_s |s^-1 A Δ A| / |A| <= |S| ε`. This covers every `H` recorded as
co-amenable or end-rigid (`thompson-f-end-rigid-schreier-graphs-are-amenable`), so it is the flow form of
that kill.

**B.3 (finite-state profile and tree count).** `Ψ = (p, N)` for a finite tree invariant: Theorem 4.3 of
`thompson-f-finite-state-flows-cannot-prove-nonamenability-proof` constructs the laws required by
Corollary A.2.

**Theorem B (profile, tree count and caret count).** Let `S ⊆ M` be finite, `(Q, δ, ℓ)` a finite tree
invariant, and `Ψ(y) = (p(y), N_y, |y|)`, where `|y|` is the total number of carets (the degree of `y`).
Then `δ_1(Ψ) = 0`. So no certificate with ratio `> 1` is a function of `s`, the automaton profile, the
number of trees and the total caret count (hence also of the number of leaves `|y| + N_y`).

*Proof.* We build laws as in Corollary A.2.

*Pumping period.* Let `C_0 = •`, `C_(V+1) = C_V ∧ •` (right combs, `|C_V| = V`). Their states
`q(C_V) = φ^V(ℓ)`, with `φ(q) = δ(q, ℓ)`, are eventually periodic: there are `i_0 >= 0`, `p >= 1` with
`q(C_(i_0 + kp)) = q* := φ^(i_0)(ℓ)` for all `k >= 0`.

*Product invariant.* `Q̂ = Q × Z/p`, `q̂(T) = (q(T), |T| mod p)`, `δ̂((a,i),(b,j)) = (δ(a,b), i + j + 1)`,
leaf state `(ℓ, 0)`. It is finite, so by Lemma 4.1 of the finite-state proof its reachable set `R̂`
carries an idempotent `π̂`. Fix trees `T_r` with `q̂(T_r) = r` for `r ∈ R̂`, and `B_T = max_r |T_r|`.

*Parameters.* `D_S = max deg s`, `H = D_S + 1`, `I` the largest generator index in the normal forms of
`S`, `n_0 = I + 1`, `L > n_0`, `K = L − n_0 + 1`, `L' >= 1`.

*Model.* Choose `N` uniform in `{n_0, ..., L}`, independent states `r_(a,b) ~ π̂` (`a < N`, `b < 2^H`) and
an independent `k` uniform in `{1, ..., L'}`. Let `t_a` (`a < N`) be the complete binary tree of depth `H`
with `T_(r_(a,b))` hung at its `b`-th bottom leaf, `t_N = C_V` with `V = i_0 + kp`, and `t_a = •` for
`a > N`. Put `Y = (t_a)`. The support is finite, `N_Y = N + 1`, `p(Y) = (q(t_0), ..., q(t_(N−1)), q*, ℓ, ...)`
and `|Y| = Σ_(a < N) |t_a| + V`.

*Splits.* Fix `s = x_(i_1) ... x_(i_d) ∈ S`. As in Theorem 4.3, by induction on `j <= d`: after `j` splits
the forest is `(u_0, ..., u_(I+j), t_(I+1), ..., t_(N−1), C_V, •, ...)`, where `u_0, ..., u_(I+j)` are the
subtrees of `t_0, ..., t_I` at an antichain of nodes of depth `<= j`, in left-to-right order. The next
split has index `i_(j+1) <= I`, so it acts inside the first block, on a node of depth `<= j < H`, which is
internal. Hence `split_s Y` is defined, `Y ∈ ∩_s sM`,
`split_s Y = (u_0, ..., u_(I+d), t_(I+1), ..., t_(N−1), C_V, •, ...)`, all displayed trees are nontrivial,
`N_(split_s Y) = N + d + 1` and `|split_s Y| = |Y| − d`.

*Coupling at fixed `N = n`.* Let `W'_n` be the law of `Ψ(split_s Y)` given `N = n`, and `W_(n+d)` the law of
`Ψ(Y)` given `N = n + d`.

- In `split_s Y`, each `u_c` is a complete top of depth `H − depth(v_c)` with independent `π̂` states hung
  below, on pairwise disjoint sets of bottom leaves. By Lemma 4.2 (for `Q̂`) the vector
  `(q̂(u_0), ..., q̂(u_(I+d)))` is i.i.d. `π̂`, and it is independent of the block
  `𝔅 = (t_(I+1), ..., t_(n−1))` and of `k`.
- In `Y` with `N = n + d`, the vector `(q̂(t_0), ..., q̂(t_(I+d)))` is i.i.d. `π̂`, independent of the block
  `(t_(I+d+1), ..., t_(n+d−1))`, which has the law of `𝔅`, and of `k`.

Couple the two: the same state vector `ξ`, the same block `𝔅` and the same `k`, with the first-block trees
realized on each side from their conditional laws given `ξ`. Under the coupling both forests have the
same profile `(ξ_Q, q(t_(I+1)), ..., q*, ℓ, ...)` (with `ξ_Q` the `Q`-coordinates of `ξ`) and the same tree
count `n + d + 1`. Their caret counts are `U + |𝔅| + V` and `U* + |𝔅| + V`, where `U`, `U*` are the caret
counts of the two first blocks. Equal second coordinates of `ξ` give `U ≡ U* (mod p)`, and each top-with-hung
tree has at most `2^H (1 + B_T)` carets, so `|U − U*| <= B := (I + D_S + 1) 2^H (1 + B_T)`. Conditionally on
everything except `k`, the two caret counts are uniform on `{U + |𝔅| + i_0 + kp}` and
`{U* + |𝔅| + i_0 + kp}`, `k = 1..L'`: two arithmetic progressions of step `p` and length `L'` offset by
`|U − U*|/p <= B` steps. Their total variation is at most `B/L'`. Averaging the conditional total variation
over the coupling,

`TV(W'_n, W_(n+d)) <= B / L'`.

*Mixing over `N`.* `Ψ_* μ = K^-1 Σ_(n=n_0)^L W_n` and `Ψ_* ρ^μ_s = K^-1 Σ_(n=n_0)^L W'_n`, where `μ` is the
law of `Y`. The laws `W_n` have disjoint supports (tree count `n + 1`), so

`||Ψ_* ρ^μ_s − Ψ_* μ|| <= 2 B/L' + 2 d/K`.

Letting `L, L' → ∞` and applying Corollary A.2 gives `δ_1(Ψ) = 0`. ∎

*Where the padding matters.* Without the comb `C_V` the caret count is tied to `N` (splitting lowers it
by `d` while raising `N` by `d`), which is the gap recorded in Section 6 of the finite-state proof. The
comb gives the caret count a free uniform coordinate, and the mod-`p` product invariant makes the offset a
multiple of the comb's pumping period, so the two progressions overlap.

## 3. What is not covered, and the one fact that is not an obstruction

- *Unbounded tree invariants.* Theorem A is exact, so the finite-state kill cannot be pushed to sizes,
  depths or exact shapes of individual trees by Theorem A alone; they have no idempotent measure (Section 5
  of the finite-state proof), and whether they are dead is the open part of the gate.
- *Finite-state readings of both forests of a reduced diagram* (group version, bounded flows on the
  Cayley graph of `F`). Theorem A applies verbatim, but no shadow law is constructed here: reduction of a
  pair of random forests cancels common carets and does not preserve the profile law.
- *Finite-window data is not an obstruction.* A certificate that reads the labelled ball of radius `R`
  around a vertex cannot be killed by indistinguishability from another marked group. Let `R` exceed the
  lengths of the two relators of `F` and of a word for a fixed nontrivial element `c` of `[F,F]`. A marked group with the same `R`-ball is a quotient `F/N` in which
  `c ≠ 1`. Every nontrivial normal subgroup of `F` contains `[F,F]` (import pinned in
  `thompson-f-almost-kernels-force-linear-commutator-bounds-proof`: Cannon–Floyd–Parry, every proper
  quotient of `F` is abelian), so `N = 1`. Hence window data determine `F`, and every kill must, as above,
  come from a coarse observation together with a shadow law, not from locality.
