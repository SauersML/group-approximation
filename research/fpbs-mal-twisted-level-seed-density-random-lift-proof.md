---
rg: 2
id: fpbs-mal-twisted-level-seed-density-random-lift-proof
kind: route
title: For each depth take a tower of random N-lifts; matrix-coefficient strong convergence keeps every twisted level a Kesten expander, and a closure-counting plus expander-mixing bound turns the gap into seed density 1/60
target: fpbs-mal-twisted-level-seed-density-uniform-witness
requires:
  - kesten-amenable-stabilizer-uniform-gap
artifacts:
  - experiments/fpbs-random-lift-twisted-gap-2026-09-17/random_lift_gap.py
  - experiments/fpbs-random-lift-twisted-gap-2026-09-17/random_lift_gap_out.txt
---

**Complete route, modulo two imported theorems quoted verbatim in §0.**

How it differs from its neighbours:
- `fpbs-strongly-ergodic-actions-have-fold-seed-floor-proof` bounds the seed
  density of one non-atomic action by its Markov gap. Proposition 3 below is
  the finite-level analogue of that bound.
- `fpbs-profinite-relcost-equals-fold-seed-density-proof` settles depth 0
  with the fixed Sanov 3-adic tower. Here that tower is replaced by random
  lifts chosen for each depth, which is what makes the constant independent
  of `j`.

Notation is as in the target. `L = F(a,b)` acts on the right. `φ(a) = a`,
`φ(b) = b a b^{-2}`, `t_j = φ^j(b)`, and `L_j = <a, t_j>`. For a finite
right `L`-set `Q` with `n = |Q|`, `Q^{(j)}` is `Q` with `b` acting as `t_j`.
`r(Q^{(j)})` is the least size of a set `S ⊆ Q` whose 2-of-3 closure is `Q`.
The closure uses the triples `T_y = (y, y·a, y·t_j)`, `y ∈ Q`, counted with
multiplicity. The target's orientation `(y, y·a^{-1}, y·t_j^{-1})` gives the
same bound: §2 only uses `|C ∩ C a^{-1}| = |C ∩ C a|`, and the same for
`t_j`.

For a unitary action write `(U_g f)(y) = f(y·g)`. Then `U_{gh} = U_g U_h`, so
`U` is a representation of `L`. Put

```text
M_j = (U_a + U_a^* + U_{t_j} + U_{t_j}^*)/4,
λ_j(Q) = ‖M_j restricted to ℓ²_0(Q)‖,   ℓ²_0(Q) = {f : Σ f = 0}.
```

**Result.** For every `j ≥ 0` there is an essentially free profinite action
`X_j = lim Q_m` of `L` whose levels are all transitive and satisfy
`λ_j(Q_m) ≤ λ_0 := (1+ρ)/2`, where `ρ` is the Kesten spectral radius of
`F_2` on a free basis. Hence

```text
r(Q_m^{(j)})  ≥  (1 − λ_0) |Q_m| / 6  =  (1 − ρ) |Q_m| / 12      for all m,
```

so the target holds with `c = (1−ρ)/12`. The constant is the same for every
`j`. With Kesten's value `ρ = √3/2` this is `(2 − √3)/24 ≈ 0.0112`. The proof
works with any fixed `λ_0 ∈ (ρ, 1)`; taking `λ_0 = 0.9 > √3/2` gives
`c = 1/60`.

The only property of `ρ` used for uniformity is that it does not depend on
`j`. `L_j` is free on `{a, t_j}` for every `j`, so the Markov operator of
§3 is the same free-group operator at every depth, even though
`|t_j| → ∞`.

## 0. Imports

**(K) Kesten.** From `kesten-amenable-stabilizer-uniform-gap` (ESTABLISHED
via `kesten-amenable-stabilizer-gap-citation`), taken with `A = F_2`,
`H = {1}` and `S` a free basis with its inverses:
`ρ = ‖(1/4) Σ_{s∈S} λ_{F_2}(s)‖ < 1`, since `F_2` is nonamenable.
- For the numerical value only: H. Kesten, *Symmetric random walks on
  groups*, Trans. AMS 92 (1959), Theorem 3, gives `ρ(F_k) = √(2k−1)/k`.
- CGTV (below) restate it in arXiv 2405.16026v3 as "It is a
  classical fact due to Kesten [43] that ‖A_F‖ = 2√(2d−1)". Here `A_F` is the
  adjacency operator of the `2d`-regular tree. With `d = 2`, this gives
  `ρ = 2√3/4 = √3/2`.

**(SC) Strong convergence with matrix coefficients.** C.-F. Chen,
J. Garza-Vargas, J. A. Tropp, R. van Handel, *A new approach to strong
convergence*, Ann. of Math. 203 (2026); arXiv 2405.16026v3, §3.3. Verbatim:

> Definition 3.1. "Let S̄^N_1, . . . S̄^N_d be i.i.d. random permutation
> matrices of dimension N, and denote by S^N_i := S̄^N_i|{1_N}⊥ their
> restriction to the invariant subspace {1_N}⊥ ⊂ C^N."
>
> Definition 3.2. "Let s = (s1, . . . , sd) be defined by si := λ(gi), where
> g1, . . . , gd are the free generators of Fd and λ : Fd → B(l2(Fd)) is the
> left-regular representation"
>
> Theorem 3.9. "Let d ≥ 2, and let P ∈ MD(C) ⊗ C⟨s, s∗⟩ be any self-adjoint
> noncommutative polynomial of degree q0. Then we have
> P[‖P(S^N, S^N∗)‖ ≥ ‖P(s, s∗)‖ + ε] ≲ (D/N)(Kq0 log d/ε)^8 log(eK/ε)
> for all ε < K − ‖P(s, s∗)‖, where K = ‖P‖_{MD(C)⊗C∗(Fd)}."

Two further quotes from the same section:
- On the polynomials: "P (s, s∗) = Σ_w A_w ⊗ w(s, s∗), where the sum is over
  a finite set of words w in the symbols s1, . . . , sd, s∗1, . . . , s∗d and
  A_w ∈ MD(C) are matrix coefficients".
- On `K`: "In practice, ‖P‖MD(C)⊗C∗(Fd) may be bounded trivially by the sum
  of the norms of the matrix coefficients of P."

The earlier qualitative form is Bordenave–Collins, *Eigenvalues of random
lifts and polynomials of random permutation matrices*, Ann. of Math. 190
(2019), arXiv 1801.00876. Its Theorem 3 says: "For symmetric random
permutations, the permutation operators restricted to 1I⊥, ((Si)|1I⊥),
i ∈ [d], are asymptotically strongly free in probability". Only the
qualitative consequence of Theorem 3.9 is used here:
`P[‖P(S^N)‖ ≥ ‖P(s)‖ + ε] → 0` as `N → ∞`, for fixed `P` and `ε`.

Everything else below is proved in full.

## 1. Counting lemma: closures of size m hold at least m − |S| full triples

Let `Q` be a finite `L`-set, fix `j`, and let `S` percolate `Q^{(j)}`. Run
the closure one point at a time: `C_0 = S`, and `C_{k+1} = C_k ∪ {z}` when some
triple `T_y` has two of its three positions in `C_k` and its third position
equal to `z ∉ C_k`. Say that step `k+1` uses `T_y`.

- After step `k+1` all three positions of `T_y` lie in `C_{k+1}`, so `T_y` is
  full.
- A full triple has no missing position, so no later step uses it. Hence
  distinct steps use distinct triples, that is, distinct indices `y`.
- Every full triple `T_y ⊆ C` has `y ∈ C`, `y·a ∈ C` and `y·t_j ∈ C`.

For `C ⊆ Q`, put `F(C) = #{y ∈ C : y·a ∈ C, y·t_j ∈ C}`. Each step adds exactly
one point and `S` percolates, so the sizes `|C_k|` run through every integer
from `|S|` to `n`.

**Lemma 1.** If `|S| ≤ m ≤ n`, then the closure stage `C = C_{m−|S|}` has
`|C| = m` and `F(C) ≥ m − |S|`.

*Proof.* The `m − |S|` steps so far used `m − |S|` distinct triples. Each of
them is full inside `C`, so its index is counted by `F(C)`. ∎

## 2. Expander mixing on a level

Let `A ⊆ Q` with `|A| = m`, and put `i_s(A) = |A ∩ A·s^{-1}| =
#{y ∈ A : y·s ∈ A}` for `s = a, t_j`. Then:

- `⟨1_A, U_s 1_A⟩ = ⟨1_A, U_s^* 1_A⟩ = i_s(A)`, so
  `⟨1_A, M_j 1_A⟩ = (i_a + i_{t_j})/2`.
- Write `1_A = (m/n)·1 + f` with `f ∈ ℓ²_0(Q)`, so `‖f‖² = m − m²/n`.
  Since `M_j 1 = 1` and `M_j` is self-adjoint and preserves `ℓ²_0`,
  `⟨1_A, M_j 1_A⟩ = m²/n + ⟨f, M_j f⟩ ≤ m²/n + λ_j(Q)(m − m²/n)`.
- `F(A) ≤ min(i_a, i_{t_j}) ≤ (i_a + i_{t_j})/2`.

**Lemma 2.** `F(A) ≤ m²/n + λ_j(Q)·m(1 − m/n)`.

**Proposition 3.** Let `λ = λ_j(Q)`. Then `r(Q^{(j)}) ≥ (1 − λ)·n/6`.

*Proof.*
- `n = 1`: `r = 1 ≥ 1/6`.
- `n ≥ 2`: put `m = ⌊n/2⌋`. Then `n/3 ≤ m ≤ n/2`, so `1 − m/n ≥ 1/2`. Let
  `S` percolate.
  - If `|S| > m`, then `|S| > n/3 ≥ (1−λ)n/6`.
  - Otherwise Lemmas 1 and 2 applied to `C` give
    `m − |S| ≤ F(C) ≤ m²/n + λ m(1 − m/n)`. So
    `|S| ≥ (1 − λ)·m(1 − m/n) ≥ (1 − λ)(n/3)(1/2)`. ∎

Proposition 3 is the finite analogue of Theorem S of
`fpbs-strongly-ergodic-actions-have-fold-seed-floor`, and has a slightly
worse constant. It is proved here directly because Theorem S is stated for
non-atomic spaces. `spectral_check.py` of that node checks the analogous
finite bound `r ≥ n(1−λ_2)/4` numerically.

## 3. Random N-lifts, and the operator on the new part

Let `Q` be a finite `L`-set with `D = |Q|`, and let `N ≥ 2`. Choose
independent uniform permutations `σ_{s,q} ∈ Sym(N)`, one for each `s ∈ {a,b}`
and `q ∈ Q`. There are `d = 2D ≥ 2` of them. The **lift** `Q̃ = Q × [N]`
carries

```text
(q, i)·s = (q·s, σ_{s,q}(i)),      s ∈ {a, b}.
```

Any choice of bijections for the free generators defines a right action of
`L`. The projection `Q̃ → Q` is `L`-equivariant and `N`-to-`1`.

**Decomposition.** Identify `ℓ²(Q̃) = ℓ²(Q) ⊗ C^N`, and write `P_σ` for the
permutation matrix `(P_σ v)(i) = v(σ(i))`, with `E_{p,q}` the matrix units of
`M_D(C)`. Then

```text
U_s = Σ_{q∈Q} E_{q, q·s} ⊗ P_{σ_{s,q}},     s ∈ {a, b}.
```

Every `P_σ` fixes `1_N` and preserves `1_N^⊥`. So

```text
ℓ²_0(Q̃) = (ℓ²_0(Q) ⊗ 1_N)  ⊕  (ℓ²(Q) ⊗ 1_N^⊥)          ("old" ⊕ "new")
```

is invariant under every `U_g`.
- On the old part `U_g` acts as it does on `ℓ²_0(Q)`. So
  `‖M_j|old‖ = λ_j(Q)`.
- On the new part, `U_s = Σ_q E_{q,q·s} ⊗ S_{s,q}` with
  `S_{s,q} = P_{σ_{s,q}}|_{1^⊥}`.
- The operator `U_{s^{-1}}` is `U_s^* = Σ_q E_{q·s, q} ⊗ S_{s,q}^*`.
- `t_j` is a fixed reduced word of length `q_0 = |t_j|`, and
  `U_{t_j}` is the product of the corresponding letter operators.

Multiplying out gives a fixed polynomial

```text
P_j ∈ M_D(C) ⊗ C⟨s, s^*⟩,   in the d = 2D symbols s_{s,q},
```

of degree `q_0`. It depends only on `Q` and `j`, and satisfies
`M_j|new = P_j(S^N, S^{N*})`. It is self-adjoint as a formal polynomial,
because `M_j` is given by the same formula in `U_g` and `U_g^*`.

The `S_{s,q}` are exactly CGTV's `S^N_1, …, S^N_d`: restrictions of i.i.d.
uniform random permutation matrices to `1_N^⊥`. Its coefficient norm `K` is
finite and independent of `N`. Moreover `‖P_j(S^N)‖ ≤ K` always, because
`S^N` extends to unitaries on `C^N`.

## 4. The limit operator is Kesten's operator at every depth

Substitute `s_{s,q} = λ(g_{s,q})`, the free generators of `F_d` acting on
`ℓ²(F_d)` by left translation. The same formula then gives, on
`ℓ²(Q) ⊗ ℓ²(F_d) = ℓ²(Q × F_d)`,

```text
V_s = Σ_q E_{q,q·s} ⊗ λ(g_{s,q}),   (V_s f)(q, x) = f(q·s, g_{s,q}^{-1} x).
```

This is the Koopman operator of the right action of `L` on
`Ω = Q × F_d` with `(q, x)·s = (q·s, g_{s,q}^{-1} x)`. So `P_j(s, s^*)` is
`M_j` of this action.

**Lemma 4. The action of `L` on `Ω` is free.**

*Proof.* Let `w = s_1^{ε_1} ⋯ s_ℓ^{ε_ℓ}` be reduced with `ℓ ≥ 1`. Follow
`(q_0, x)·w`, with `q_k = q_{k−1}·s_k^{ε_k}`. The inverse of
`(q,x) ↦ (q·s, g_{s,q}^{-1}x)` is `(q',x') ↦ (q'·s^{-1}, g_{s,q'·s^{-1}} x')`.
So step `k` multiplies `x` on the left by

```text
h_k = g_{s_k, e_k}^{−ε_k},   where e_k = q_{k−1} if ε_k = +1 and e_k = q_k if ε_k = −1.
```

Here `e_k` is the tail of the `s_k`-edge crossed at step `k`.

Suppose `h_{k+1} = h_k^{-1}`. Then `s_{k+1} = s_k`, `ε_{k+1} = −ε_k`, and the
same edge is used. That means `w` contains `s s^{-1}` or `s^{-1} s`, which
contradicts reducedness.

So `h_ℓ ⋯ h_1` is a reduced word of length `ℓ ≥ 1` in `F_d`. Hence
`h_ℓ ⋯ h_1 x ≠ x`, and `(q_0,x)·w ≠ (q_0,x)`. ∎

**Consequence.**
- By Lemma 4, `ℓ²(Ω)` is a direct sum of copies of the right-regular
  representation of `L`, which is equivalent to `λ_L`.
- `φ^j` is an injective endomorphism of `L` with image `L_j`. So `L_j` is
  free on `{a, t_j}`, and `λ_L|_{L_j}` is a multiple of `λ_{L_j}`.
- So `P_j(s, s^*) = M_j` is a direct sum of copies of
  `(1/4)(λ(a) + λ(a)^* + λ(t_j) + λ(t_j)^*)` on `ℓ²(L_j)`, for the free basis
  `{a, t_j}`.

Hence, by (K),

```text
‖P_j(s, s^*)‖ = ρ      for every j and every finite Q.
```

## 5. One lift step

Fix `j`, a finite `L`-set `Q` with `λ_j(Q) ≤ λ_0`, and `λ_0 ∈ (ρ, 1)`.

**Lemma 5 (gap survives).** `P[λ_j(Q̃) > λ_0] → 0` as `N → ∞`.

*Proof.* By §3, `λ_j(Q̃) = max(λ_j(Q), ‖P_j(S^N)‖)`. The first term is
`≤ λ_0`. For the second, there are two cases.
- If `K ≤ λ_0`, then `‖P_j(S^N)‖ ≤ K ≤ λ_0` always.
- Otherwise put `ε = min(λ_0 − ρ, (K − ρ)/2) > 0`, so that `ε < K − ρ`.
  Theorem 3.9, with `‖P_j(s)‖ = ρ` from §4, gives
  `P[‖P_j(S^N)‖ ≥ ρ + ε] → 0`, and `ρ + ε ≤ λ_0`. ∎

**Lemma 6 (few fixed points).** Let `w ∈ L` be nontrivial and reduced of
length `ℓ`, and let `N > ℓ`. Put `fix_Q(w) = |Fix_Q(w)|/|Q|`. Then:
- deterministically, `fix_{Q̃}(w) ≤ fix_Q(w)`;
- `E[fix_{Q̃}(w)] ≤ fix_Q(w)·ℓ²/(N − ℓ)`.

*Proof.* A fixed point `(q, i)` of `w` projects to a fixed point `q`, which
gives the first bound. Now fix `q ∈ Fix_Q(w)`.
- Its `Q`-path under `w` is fixed. So `(q,i)·w = (q, π_q(i))`, where
  `π_q = W_q(σ)` is a word of length `ℓ` in the independent uniform
  permutations `σ_{s,e}`, with the letters indexed by the edges crossed.
- As in Lemma 4, `W_q` is reduced as a word in free generators indexed by
  edges. Two consecutive letters are inverse only if the edge repeats with
  opposite exponent, and that would make `w` non-reduced.

Now expose `i_0 = i, i_1, …, i_ℓ = π_q(i)` step by step, revealing only the
values of the `σ_{s,e}^{±1}` that the path queries.

- Call step `k` *fresh* if the queried value was not yet revealed. Given the
  history, a fresh value is uniform on the at least `N − k + 1 ≥ N − ℓ`
  unrevealed values of that permutation, in that direction.
- A step is a *coincidence* if it is fresh and lands in `{i_0, …, i_{k−1}}`.
  This has conditional probability at most `k/(N − ℓ)`.
- Suppose there is no coincidence up to step `k−1`, and `i_0, …, i_{k−1}`
  are distinct. Then step `k` is fresh.
  - The only revealed pair of the letter `σ_{s_k,e_k}` involving `i_{k−1}`
    could come from step `k−1`.
  - It answers the query at step `k` only if step `k` reverses step `k−1` on
    the same letter, which is excluded by reducedness.
  - So by induction, with no coincidence at all, the points `i_0, …, i_ℓ`
    are distinct and `π_q(i) ≠ i`.

Hence `P[π_q(i) = i] ≤ Σ_{k≤ℓ} k/(N−ℓ) ≤ ℓ²/(N − ℓ)`. Summing over
`q ∈ Fix_Q(w)` and `i ∈ [N]`, and dividing by `|Q̃| = N|Q|`, gives the second
bound. ∎

## 6. The tower, and proof of the target

Fix `j` and `λ_0 ∈ (ρ, 1)`. Enumerate the nontrivial elements of `L` as
`w_1, w_2, …`, with lengths `ℓ_1, ℓ_2, …`. Put `Q_0 = {pt}`, so
`λ_j(Q_0) = 0`. Given `Q_m` with `λ_j(Q_m) ≤ λ_0`, choose `N = N_{m+1}`
large enough that both:
- `P[λ_j(Q̃_m) > λ_0] < 1/2`, by Lemma 5;
- `(m+1)·ℓ_i²/(N − ℓ_i) < 1/(4(m+1))` for `i ≤ m+1`.

By Markov's inequality and Lemma 6, the second condition makes
`P[fix_{Q̃}(w_i) > 1/(m+1)] < 1/(4(m+1))` for each `i ≤ m+1`. A union bound
over those `i` gives total probability below `1/4`.

So with probability `> 1/4` the lift satisfies all of:
- `λ_j(Q̃_m) ≤ λ_0`;
- `fix(w_i) ≤ 1/(m+1)` for every `i ≤ m+1`.

Let `Q_{m+1}` be such a lift.

- **Transitive levels.** `λ_j(Q_m) < 1` means `M_j` has no nonzero fixed
  vector in `ℓ²_0(Q_m)`. The indicator of an `L_j`-invariant set would give
  one after centering. So `L_j` acts transitively on `Q_m`. Then `L` acts
  transitively on `Q_m`, and `Q_m^{(j)}` is transitive too.
- **Essential freeness.** Let `X_j = lim Q_m`, with the inverse-limit
  measure. The measure is non-atomic, since `|Q_m| ≥ 2^m`. For each `w_i`,
  `μ(Fix_X(w_i)) = lim_m fix_{Q_m}(w_i)`, a decreasing limit by Lemma 6.
  This is at most `1/m` for all `m ≥ i`, so it is `0`.
- **Density.** By Proposition 3, `r(Q_m^{(j)}) ≥ (1 − λ_0)|Q_m|/6` for
  every `m`, including `m = 0`.

`λ_0` does not depend on `j`. This proves the target with
`c = (1 − λ_0)/6`. With `λ_0 = 0.9`, which is allowed since `ρ = √3/2`, this
is `c = 1/60`. ∎

**Why one tower per depth.** A single tower good for all `j` at once would
need infinitely many polynomial norms controlled on each level, and the
degrees `|t_j|` are unbounded. Theorem 3.9 controls finitely many at a time,
and the target only asks for a witness `X_j` depending on `j`.

## 7. Numerical sanity check (not used in the proof)

`random_lift_gap.py` builds random-lift towers from `Q_0 = {pt}` for
`j = 0..3`, where `|t_j| = 1, 4, 11, 28`. The output is in
`random_lift_gap_out.txt`. The runs are `N = 6` with 3 levels (up to
`n = 216`) and `N = 16` with 2 levels (up to `n = 256`). In `select` mode a
lift is kept only if `λ_j ≤ 0.9` for every `j ≤ 3`, which mimics §6.

- **Spectra.** At the top level of the selected towers, `λ_j` is between `0.851` and
  `0.891`, against the free limit `√3/2 = 0.866`. So the new parts sit at the
  Kesten value even for `|t_j| = 28`.
- **Selection matters.** The unselected `N = 16` tower has
  `λ_2 = 0.926 > 0.9` at level 1. The excess is inherited through the old
  part, which is why §6 selects lifts.
- **Densities.** Greedy upper bounds for `r/n` at the top levels are
  `0.121` to `0.134` for every `j`. The proven lower bounds
  `(1 − λ)n/6` are about `0.02 n`. The two do not conflict, and neither
  decays with `j`.

## 8. What this changes

- The target, (W) of `fpbs-mal-depth-floor-from-overfold-domination`, is
  closed with `c = 1/60`. By item 4 of
  `fpbs-mal-depth-promotion-equals-overfold-merge-number`, this means
  `Q_j^law(X_j) ≥ 1/60` for every `j`, where `X_j` is the random-lift
  tower above.
- The remaining premise of that route is (O),
  `fpbs-mal-overfold-merges-never-help`, which says `deep_j = law_j`.
  - Its weak form `deep_j(Q_m) ≥ c_1·law_j(Q_m)`, with `c_1` independent of
    `j`, suffices.
  - It is needed only on the random-lift towers built here, whose levels
    are Kesten expanders for `M_j`.
  - With (O), the route gives the Bernoulli floor
    `fpbs-mal-bernoulli-single-stage-floor`, and
    `fpbs-mal-floor-gives-fixed-price-counterexample` then gives
    `fpbs-fixed-price-counterexample-exists`.
- (O) is now the last open premise on this path to the flagship's negation.
