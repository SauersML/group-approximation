---
rg: 2
id: folded-dkkms-line-hosts-gap-proof
kind: route
title: Proof that the l = 1 folded DKKMS host has gap at least 1 - sqrt(rho_k + 2 delta), by exact identification of the classes, a Markov-chain reduction in beta, and an Efron-Stein bound for an ordered lift of the S-to-tuple walk
target: folded-dkkms-line-hosts-have-uniform-spectral-gap
requires: []
artifacts:
  - experiments/ugc-folded-gap-2026-09-17/folded_l1_gap.py
---

The notation is that of the target. Only the DKKMS construction is used, quoted
below from ECCC TR16-198 (Dinur, Khot, Kindler, Minzer, Safra). The source
hypotheses (R1) and (R2) are those of the target. All vectors lie in
`F_2^X`. For a set `Y` of variables, `1_Y` is its indicator vector, and
`vars(U)` is the set of the `3k` variables of `U`.

## Quoted inputs (verbatim, TR16-198)

* **(D1) Tuples.** "Let U be the set of all k-tuples of equations
  U = (e1,...,ek) from the regular Gap3Lin instance (X, eq) that are
  “legitimate”, namely such that (a) the equations e1,...,ek are distinct and
  do not share variables and (b) for any pair of variables x∈ei and y∈ej, i≠j,
  x,y do not appear together in any equation in the instance (X, eq)."
* **(D2) Vertices.** "A = {(U,L) | U∈U, L∈Gr(XU,ℓ), L∩HU = {0}}" and
  "B = {(V,L′) | V∈V, L′∈Gr(XV,ℓ−1)}", where `X_U` ("elements have support in
  U"), `H_U = Span(x_e : e∈U)`, and `V` is "the collection of all sets V of up
  to 3k variables".
* **(D3) Edges.** "1. Choose a k-tuple U = (e1,...,ek)∈U uniformly at random
  and then construct a k-tuple V such that independently for 1 ⩽ i ⩽ k, the
  ith element of V is the equation ei with probability 1−β and is a variable in
  the equation ei with probability β. 2. Choose a random L′∈Gr(XV,ℓ−1) and a
  random L∈Gr(XU,ℓ) such that L′⊆L. 3. Output (U,L), (V,L′)."
* **(D4) Folding.** "Given (U0,L0)∈A, we define C(U0,L0) by
  C(U0,L0) = {(U,L)∈A | L+HU+HU0 = L0+HU+HU0}", "Ã = {C(U,L) | (U,L)∈A}",
  and "choose a random edge ((U,L),(V,L′))∈E and then output
  (C(U,L),(V,L′))∈Ã×B." together with "The weights are summed up as well."

As in `folded-dkkms-host-gap-vanishes-proof`, the edge law is the law of (D3)
conditioned on `G = {L ∩ H_U = {0}}`. That is needed because (D3) can output
an `L` that is not in `A`.

## Step 0: the edge law at l = 1

At `l = 1`, `Gr(X_V, 0) = {{0}}`, so a B-vertex is just `V`. The space `L` is
`span(v)` for a uniform nonzero `v ∈ X_U`, and the event `G` is `v ∉ H_U`.
`Pr[G | U, V] = (2^(3k) − 2^k)/(2^(3k) − 1)` does not depend on `(U, V)`.

So under the edge law:
- `U` is uniform on `𝒰`;
- `V ~ Q_β(· | U)` as in (D3);
- `v` is uniform on `X_U \ H_U`;
- `V` and `v` are independent given `U`.

Distinct `v` give distinct A-vertices `(U, span v)`.

## Step 1: block geometry of two legitimate tuples

Let `U, U' ∈ 𝒰` and `H = H_U + H_U'`. Since the equations of a legitimate tuple
are variable-disjoint, `Σ_{e ∈ T} x_e = 1_{∪T}` for every `T ⊆ U`.

**(1a) An equation inside `vars(U)` is a block of `U`.** Suppose `f ∈ Eq` has
`f ⊆ vars(U)`, and that `f` meets two blocks `e_i ≠ e_j` of `U`, in `x` and
`y`. Then `x` and `y` appear together in `f`, contrary to (b) for `U`. So `f`
lies in one block, and since both have 3 variables, `f = e_i`.

**(1b) `X_U ∩ H = H_U`.** Let `y = h + h' ∈ X_U`, with `h ∈ H_U` and
`h' = 1_{∪T'} ∈ H_U'`. Then `h' = y + h ∈ X_U`, so every `f ∈ T'` satisfies
`f ⊆ vars(U)`. By (1a), `T' ⊆ U`, so `h' ∈ H_U` and `y ∈ H_U`.

**(1c) Partial matching.** Each block `e` of `U` falls into exactly one of three
cases:
- `e` is a block of `U'`;
- `e` meets exactly one block of `U'`, in exactly one variable;
- `e` meets no block of `U'`.

Proof: if `e` met two blocks `f ≠ f'` of `U'`, in `x ∈ f` and `y ∈ f'`, then
`x` and `y` would appear together in `e`, contrary to (b) for `U'`. If `e`
meets a single block `f ≠ e`, then `|e ∩ f| = 1` by (R2).

## Step 2: Lemma A

For `v ∈ X_U` and a block `e`, the restriction `v|_e ∈ F_2^3` modulo `111` has a
unique representative of weight at most 1. So `v + H_U` contains a unique
`r = r(U, v)` of weight at most 1 on each block. Write `S = S(U, v) = supp r`.
It contains one variable from each block where `v|_e ∉ {000, 111}`. Moreover,
`S = ∅` iff `v ∈ H_U`.

Each nonempty partial transversal `S` of `U` arises from exactly `2^k` vectors
`v`, namely `v ∈ 1_S + H_U`. There are `4^k − 1` such `S`, and
`(4^k − 1) 2^k = |X_U \ H_U|`. So under Step 0, **`S(U, v)` is uniform over the
nonempty partial transversals of `U`**, independently of `V` given `U`.

**Lemma A.** Let `v ∈ X_U \ H_U` and `v' ∈ X_U' \ H_U'`, with sets `S` and
`S'`. Then

```text
span(v) + H = span(v') + H   iff   S = S'.
```

*Proof.* By (1b), `v ∉ H` and `v' ∉ H`. The left side therefore holds iff
`v' ∈ v + H`, which holds iff `y := 1_S + 1_S' ∈ H`.

(⇐) If `S = S'`, then `y = 0 ∈ H`.

(⇒) Write `y = 1_{∪T} + 1_{∪T'}`, with `T ⊆ U` and `T' ⊆ U'`. Take `e ∈ T`.
- If `e` is a block of `U'` but `e ∉ T'`: by (1c), `1_{∪T'}` vanishes on `e`.
  So `y|_e = 111`. But `1_S|_e` and `1_S'|_e` each have weight at most 1, so
  `y|_e` has weight at most 2. This is a contradiction.
- If `e` is not a block of `U'`: by (1c), at least two variables `z ∈ e` lie
  in no block of `U'`. At each such `z`, both `1_S'` and `1_{∪T'}` vanish,
  because `S' ⊆ vars(U')`. So `1_S(z) = y(z) = 1`. Then `1_S` has weight at
  least 2 on `e`, a contradiction.

Hence `T ⊆ T'`, and by symmetry `T = T'`. So `y = 0` and `S = S'`. ∎

**Consequences.**
- The relation in (D4) is an equivalence relation at `l = 1`. The class of
  `(U, span v)` is determined by `S = S(U, v)` alone, and is
  `C(S) = {(U', span v') : U' ∈ Cov(S), v' ∈ 1_S + H_U'}`.
- `S` is a partial transversal of every `U' ∈ Cov(S)`. Two variables of `S`
  lie in different blocks of `U`, so by (b) for `U` they are in no common
  equation, and in particular in no common block of `U'`. Hence
  `r(U', v') = 1_S` for `v' ∈ 1_S + H_U'`, and these are exactly the `v'` with
  `S(U', v') = S`.
- Two tuples with no common variable are never related.
- This is what part (1) of the artifact checks by brute-force union-find. The
  check agrees exactly when (b) is imposed and fails without (b).

## Step 3: reduction to the class–tuple graph (all β)

By (D4) and Step 2, the folded graph is the bipartite graph on `Ã × B` whose
edge weights are the joint law of `(S, V)`, where `S = S(U, v)` and `(U, V, v)`
follow the edge law of Step 0. For a joint law of `(X, Y)`, `σ_2` of the
normalized bipartite matrix is the maximal correlation

```text
σ_2(X, Y) = sup { E[g(X) f(Y)] : E g = E f = 0, E g² = E f² = 1 }.
```

By Step 0, `S` is a function of `(U, v)`, and `V` is independent of `v` given
`U`. So `S – U – V` is a Markov chain.

Take mean-zero `g(S)` and `f(V)` of unit norm, and put `(Rf)(U) = E[f(V) | U]`.
Then:
- `E[g(S) f(V)] = E[g(S) (Rf)(U)]`;
- `E[Rf] = 0` and `E[(Rf)²] <= 1`.

Hence, for every `β`,

```text
σ_2(folded) = σ_2(S, V) <= σ_2(S, U).
```

## Step 4: the two-step walk

Let `P = K K*` on `L²(𝒰, uniform)`, where `(K* f)(S) = E[f(U) | S]`. Then
`σ_2(S, U)² = λ_2(P)`, the second largest eigenvalue of the positive
semidefinite self-adjoint operator `P`.

By Step 2:
- given `U`, `S` is uniform over the `4^k − 1` nonempty partial transversals
  of `U`;
- given `S`, `U` is uniform on `Cov(S)`, because every `U' ∈ Cov(S)` gives
  `S` the same probability `1/(4^k − 1)`.

Therefore

```text
P(U, U') = Σ_S 1[S ⊆ vars(U), S partial transversal of U, U' ∈ Cov(S)] / ((4^k − 1) |Cov(S)|).
```

Equivalently, `S` can be drawn as follows. Let `F ⊆ [k]` contain each index
independently with probability `1/4`, conditioned on `F ≠ [k]`. Then choose
`x_i ∈ e_i` uniformly for each `i ∉ F`, and put `S = {x_i : i ∉ F}`. With
`m = k − |F|`, this gives `Pr[F] = q_F := 3^m/(4^k − 1)`, and each `S` gets
probability `q_F 3^(−m) = 1/(4^k − 1)`.

## Step 5: the ordered lift

Let `Ω_L ⊆ Eq^k` be the set of orderings of legitimate tuples. Each tuple has
`k!` orderings, and we give `Ω_L` the uniform measure. For `F ≠ [k]` and a
labelled choice `x = (x_i)_{i ∉ F}`, call `ω' ∈ Ω_L` *aligned* if `x_i ∈ ω'_i`
for all `i ∉ F`. Write `m = k − |F|`.

**Counting aligned tuples.** Given `U' ∈ Cov(S)`:
- the blocks of `U'` containing the `x_i` are distinct, because `S` is a
  partial transversal of `U'`;
- so `U'` has exactly `(k − m)!` aligned orderings.

There are `D^m N^(k−m)` tuples `ω' ∈ Eq^k` with `x_i ∈ ω'_i` for `i ∉ F`, by
(R1). Define `p(F, x) ∈ (0, 1]` by

```text
|Cov(S)| (k − m)! = #{aligned ω' ∈ Ω_L} = p(F, x) D^m N^(k−m).
```

**The lifted kernel.** Define `P̂` on `Ω_L` by three draws: draw `(F, x)` from
`ω` as in Step 4; draw `ω'` uniformly among the aligned elements of `Ω_L`;
output `ω'`. So `P̂ = Σ_F q_F P̂_F`, with

```text
P̂_F(ω, ω') = 3^(−m) Σ_{x : x_i ∈ ω_i ∩ ω'_i (i ∉ F)} 1 / (p(F, x) D^m N^(k−m)).
```

This is symmetric in `(ω, ω')`, and stochastic. So `P̂_F` and `P̂` are
self-adjoint on `L²(Ω_L, uniform)`.

The unordered image of `ω'` is uniform on `Cov(S)`, and the law of `S` given
`ω` depends only on the set of `ω`. Hence, for `f(ω) = f̃(set ω)`:
- `P̂ f = (P f̃) ∘ set`;
- `<f, P̂ f> = <f̃, P f̃>` and `||f|| = ||f̃||`;
- `f̃ ⊥ 1` implies `f ⊥ 1`.

Therefore

```text
λ_2(P) <= sup { <f, P̂ f> / ||f||² : f ⊥ 1 on Ω_L }.
```

## Step 6: legitimacy is a δ-perturbation of a product

Fix `F`, and split `ω = (a, b)`, where `a = ω|_{[k]∖F} ∈ Eq^m` and
`b = ω|_F ∈ Eq^(k−m)`. Sub-tuples of legitimate tuples are legitimate.

**Bad completions are rare.** Fix `e ∈ Eq` and let `f` be uniform on `Eq`. The
pair `(e, f)` violates (a) or (b) only in one of three ways:
- `f = e`: 1 choice;
- `f ≠ e` shares a variable with `e`: at most `3(D − 1)` choices, by (R1);
- `f` shares no variable with `e`, but contains a variable `y` that appears
  together with some `x ∈ e` in an equation `g`. Here:
  - `g ∋ x` with `g ≠ e`, since `g = e` would put `y` in `e`: at most
    `3(D − 1)` choices of `(x, g)`;
  - `y ∈ g ∖ {x}`: 2 choices;
  - `f ∋ y` with `f ≠ g`, since `f = g` would share `x` with `e`: at most
    `D − 1` choices;
  - in total at most `6(D − 1)²`.

So the pair is bad with probability at most `c_D / N`. Now take `a` legitimate
and `b` uniform on `Eq^(k−m)`. Each of the at most `C(k, 2)` pairs of
positions with at least one position in `F` has one uniform entry, independent
of the other. A union bound shows that `(a, b)` fails to be legitimate with
probability at most `δ`.

**The factor `p_1`.** Let `p_1(F, x) D^m` be the number of legitimate
`a ∈ Eq^m` with `x_i ∈ a_i`. Then `p(F, x) = p_1(F, x) · γ`, where `γ` is the
average over those `a` of `Pr_b[(a, b) legitimate]`, so `γ ∈ [1 − δ, 1]`.

**The kernel `Y_F`.** On legitimate `m`-tuples, put

```text
Y_F(a, a') = 3^(−m) Σ_{x : x_i ∈ a_i ∩ a'_i} 1 / (p_1(F, x) D^m).
```

`Y_F` is the kernel "pick `x_i ∈ a_i` uniformly, then a uniform legitimate
`a'` with `x_i ∈ a'_i`". It is stochastic and symmetric, hence doubly
stochastic, so its operator norm on `ℓ²` (counting measure) is at most 1 by
the Schur test.

**The error term.** For `ω, ω' ∈ Ω_L`, compare the two kernels term by term
in `x`: `1/p = (1/p_1)(1/γ)` and `1/γ ∈ [1, 1/(1 − δ)]`. This gives

```text
P̂_F(ω, ω') = N^(−(k−m)) ( Y_F(a, a') + E_F(ω, ω') ),     0 <= E_F <= (δ/(1−δ)) Y_F(a, a').
```

`E_F` is symmetric. For each `ω`, the row sum of `N^(−(k−m)) E_F` over
`ω' ∈ Ω_L` is at most

```text
(δ/(1−δ)) Σ_{a'} Y_F(a, a') · #{b'} / N^(k−m) <= δ/(1−δ).
```

## Step 7: the one-F bound

Let `f` be a function on `Ω_L` with `f ⊥ 1`, and let `h` be its extension by 0
to `Eq^k`. Norms below are counting norms, and `||h||² = Σ_{Ω_L} f²`.

Let `(Π_F h)(a, b) = N^(−(k−m)) Σ_{b''} h(a, b'')` be the average over the
coordinates in `F`, and `H(a) = Σ_b h(a, b)`. Then:
- The main term is
  `N^(−(k−m)) Σ_{a,a'} Y_F(a, a') H(a) H(a') <= N^(−(k−m)) Σ_a H(a)² = ||Π_F h||²`.
  Here `H(a) = 0` for non-legitimate `a`, and `||Y_F|| <= 1`.
- The error term is at most `(δ/(1−δ)) ||h||²`, by the Schur test for the
  symmetric nonnegative kernel `N^(−(k−m)) E_F`, whose row sums are at most
  `δ/(1−δ)`.

So

```text
Σ_{ω,ω'} f(ω) P̂_F(ω, ω') f(ω') <= ||Π_F h||² + (δ/(1−δ)) ||h||².
```

## Step 8: Efron–Stein and conclusion

Expand `h = Σ_{T ⊆ [k]} h_T` in the orthogonal Efron–Stein decomposition of
the uniform product measure on `Eq^k`. Two facts are needed:
- `h_∅ = N^(−k) Σ_{Ω_L} f = 0`;
- `Π_F h = Σ_{T ∩ F = ∅} h_T`.

For `T ≠ ∅`, the event `T ∩ F = ∅` forces `F ≠ [k]`, so

```text
Pr[T ∩ F = ∅] = (3/4)^|T| / (1 − 4^(−k)) <= ρ_k.
```

Averaging Step 7 over `F` gives

```text
<f, P̂ f> <= Σ_{T ≠ ∅} Pr[T ∩ F = ∅] ||h_T||² + (δ/(1−δ)) ||h||² <= (ρ_k + δ/(1−δ)) ||f||².
```

By Steps 3–5,

```text
σ_2(folded)² <= λ_2(P) <= ρ_k + δ/(1−δ) <= ρ_k + 2δ     (δ <= 1/2),
```

and `λ_2(folded) = 1 − σ_2 >= 1 − sqrt(ρ_k + 2δ)`.

Finally, `ρ_k <= ρ_2 = 4/5` for `k >= 2`. So `δ <= 0.002` gives
`λ_2 >= 1 − sqrt(0.804) > 0.103`. ∎

## Where the route stops for l >= 2 (for the parent conjecture)

- **Step 3 fails.** `(V, L')` depends on `L` through `L' ⊆ L`, so
  `C – U – B` is not a Markov chain.
- **Step 5 fails.** Given `(U, L')`, the free blocks must avoid the support of
  `L'`, so the law of `F` depends on the state. `P̂` is then no longer a
  state-independent mixture of product-coordinate resamplings, and Step 8 has
  nothing to average over.
- **What survives.** Steps 1–2 generalise to singled-out sets for
  `l`-dimensional `L` (Claim 4.5), but the class is no longer determined by `S`
  alone.
- **What is missing.** A proof needs the Grassmann fibre chain (P4) together
  with a decomposition theorem.
- **What any such proof must respect.** By
  `folded-dkkms-host-gap-vanishes-as-l-grows`, the resulting constant must
  decay at least like `12 · 2^(−l)`.

## Numerical cross-check

`experiments/ugc-folded-gap-2026-09-17/folded_l1_gap.py` does two things:
- It checks Lemma A by union-find against the `S`-fibres. They agree exactly
  under (b), on three instances, and disagree on all three instances without
  (b).
- It computes `λ_2` at `β = 0` for `n` up to 240 (`k = 2`) and up to 90
  (`k = 3`). Every value is above `1 − sqrt(ρ_k)`. The values are listed in the
  target.
