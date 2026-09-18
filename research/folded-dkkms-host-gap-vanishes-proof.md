---
rg: 2
id: folded-dkkms-host-gap-vanishes-proof
kind: route
title: Proof that the folded DKKMS host gap is at most 2(beta + 6 * 2^(-l)), by a random-sign frozen-triple test function
target: folded-dkkms-host-gap-vanishes-as-l-grows
requires:
  - orientation-lift-selectors-need-vanishing-host-gap
artifacts:
  - experiments/ugc-folded-gap-upper-2026-09-17/check_folded_gap_upper.py
---

Notation is that of the target. Only the DKKMS construction is used, quoted
below from ECCC TR16-198 (Dinur, Khot, Kindler, Minzer, Safra). The required
node is used only in Corollary F1, for the meaning of the gate.

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
* **(D4) Folding.** "We further define the set of edges Ẽ by a random process:
  choose a random edge ((U,L),(V,L′))∈E and then output (C(U,L),(V,L′))∈Ã×B."
  and "The weights are summed up as well."
* **(D5) Singled-out coordinates (Definition 4.4).** "For each i∈U there is a
  single equation containing i whose variables are contained in U. For each
  point x∈L let IU(x) = {i∈[n] | xi≠xj = xk, where {i,j,k} are the variables
  of the unique equation containing i}", "IU(L) = ⋃_{x∈L} IU(x), and
  I(C) = ⋃_{(U,L)∈C} IU(L)."
* **(D6) Claim 4.5.** "If (U1,L1),(U2,L2)∈C then IU1(L1) = IU2(L2)."
* **(D7) Legitimacy mass.** "the fraction of U that are not legitimate is
  negligible, i.e. O(k²/|X|)".

Since the edge process (D3) can output `L` with `L ∩ H_U ≠ {0}`, which is not
a vertex of `A` by (D2), the edge law `mu` of the graph is the law of (D3)
conditioned on the event `G = {L ∩ H_U = {0}}`. We write `P` for the law of
(D3) and `P_mu = P( . | G)`. For any event `E`,

```text
P_mu(E) <= P(E) / P(G),        P_mu(E) >= P(E) - P(not G).          (0)
```

## Step 1: frozen triples are a class invariant

For a triple `t = {i, j, k}` of variables let `T_t : F_2^n -> F_2^t / <111>`
be the projection followed by the quotient; its target is `F_2^2`. Its three
nonzero values are the classes of `100`, `010` and `001`. For a subspace `L`,
put `rk_t(L) = dim T_t(L)`.

**Lemma 1.** Let `(U, L) in A` and let `t` be the variable triple of an
equation `e` of `U`. Then `t ⊆ I_U(L)` iff `rk_t(L) = 2`.

*Proof.* By (D5), for `x in L`, the variable `i in t` is in `I_U(x)` iff
`x|_t in {100, 011}` (with `i` first), that is iff `T_t(x)` is the class of
`100`. So `t ⊆ I_U(L)` iff `T_t(L)` contains all three nonzero classes. A
subspace of `F_2^2` containing all three nonzero vectors is `F_2^2`. ∎

**Definition.** For a class `C`, `Frozen(C)` is the set of variable triples of
equations of the instance that are contained in `I(C)`.

**Lemma 2.** For every `(U, L) in C`, `Frozen(C)` is the set of triples `t`
of equations of `U` with `rk_t(L) = 2`.

*Proof.* By (D6), `I(C) = I_U(L)`. By (D5), `I_U(L)` consists of variables of
`U`. Let `t` be an equation triple with `t ⊆ I(C)`. Each variable of `t` lies
in some equation of `U`. If two of them lay in different equations `e_a ≠ e_b`
of `U`, they would appear together in an instance equation (the one with
triple `t`), which (D1)(b) forbids. So all three lie in one equation of `U`,
whose triple is then `t`. By Lemma 1, `rk_t(L) = 2`. The converse is Lemma 1
again. ∎

So `Frozen` is a function on classes, and on each member it is read off
block by block.

## Step 2: what a two-step walk keeps

The class-level two-step walk is sampled from edges. Draw
`eps1 = ((U, L), (V, L')) ~ mu` and put `C = C(U, L)`. Then draw
`eps2 = ((U', L''), (V, L')) ~ mu` conditioned on its B-endpoint being
`(V, L')`, and put `C' = C(U', L'')`. By (D4), `(C, (V, L'))` then has law
`W[C, b] / W` and `C'` given `b = (V, L')` has law proportional to `W[C', b]`.
This is exactly the walk `C -> b -> C'` of the folded weighted graph. `C` is
distributed by the stationary class law `pi`, and `(C, C')` is exchangeable.

Write `t_i` for the triple of the `i`-th equation of `U`. Say block `i` is
*kept* if the `i`-th element of `V` is the equation `e_i` (probability
`1 - beta` in (D3)), and *dropped* otherwise.

**Lemma 3.** If block `i` is kept and `rk_(t_i)(L') = 2`, then
`t_i in Frozen(C')` for every `eps2` with B-endpoint `(V, L')`.

*Proof.* The variables of `t_i` lie in `V`. Since `eps2` is an edge,
`V` arises from `U'` by step 1 of (D3), so every variable of `V` is a variable
of an equation of `U'`. As in Lemma 2, (D1)(b) forces the three variables of
`t_i` into a single equation of `U'`, whose triple is `t_i`. By (D3),
`L' ⊆ L''`, so `rk_(t_i)(L'') >= rk_(t_i)(L') = 2`. Also `(U', L'') in A`.
Lemma 2 applied to the member `(U', L'')` of `C'` gives `t_i in Frozen(C')`. ∎

By Lemma 2, `Frozen(C) = {t_i : rk_(t_i)(L) = 2}`. By Lemma 3,

```text
|Frozen(C) \ Frozen(C')|  <=  #{ i : block i dropped }  +  #{ i : block i kept, rk_(t_i)(L') <= 1 }.   (1)
```

The right side depends on `eps1` only.

## Step 3: the rank-drop lemma

**Lemma 4.** Let `T : F_2^N -> F_2^2` be onto and `d >= 0`, with `L'` uniform
in `Gr(F_2^N, d)`. Then `P(dim T(L') <= 1) <= 3 * 2^(-d)`.

*Proof.* `dim T(L') <= 1` iff `L' ⊆ T^(-1)(ℓ)` for one of the three lines
`ℓ` of `F_2^2`. Each `T^(-1)(ℓ)` is a hyperplane. The fraction of
`d`-subspaces of `F_2^N` inside a fixed hyperplane is
`[N-1, d]_2 / [N, d]_2 = (2^(N-d) - 1)/(2^N - 1) <= 2^(-d)`, because
`2^d (2^(N-d) - 1) = 2^N - 2^d <= 2^N - 1`. Take a union bound over the three
lines. ∎

Under `P`, given `U` and `V`, `L'` is uniform in `Gr(X_V, l - 1)` by (D3).
If block `i` is kept, then `t_i ⊆ V`, so `T_(t_i)` restricted to `X_V` is
onto. So

```text
P(block i kept and rk_(t_i)(L') <= 1)  <=  (1 - beta) * 3 * 2^(1-l)  <=  3 * 2^(1-l).   (2)
```

Part (a) of the artifact checks Lemma 4 exactly by inclusion–exclusion for
`2 <= l <= 40` and `N` up to `l + 58`. The ratio to the bound tends to `1`, so
the constant `3` is sharp.

## Step 4: the conditioning on `L ∩ H_U = {0}`

**Lemma 5.** If `l <= 3k`, then `P(not G) <= gamma = 2^(l-2k) (e^(3 beta k)/2 + 1)`.

*Proof.* Fix `U` and `V`. Let `k_e` be the number of kept blocks. Then
`N = dim X_V = 3 k_e + (k - k_e)`, and `H_U ∩ X_V` is spanned by the `x_e` of
kept blocks, so it has dimension `k_e`. Each nonzero vector of the uniform
`L'` is uniform on `X_V \ {0}`, so it lies in `H_U` with probability at most
`2^(k_e - N) <= 4^(-k_e)`. A union bound over the `2^(l-1) - 1` vectors gives
`2^(l-1) 4^(-k_e)`.

Given `L'`, a uniform `l`-space `L ⊇ L'` of `X_U` is `L' + <z>` with `z`
uniform on `X_U \ L'`. Every such `L` has exactly `2^(l-1)` vectors outside
`L'`, so this induces the uniform law. For each `y in L'`, `z + y` is uniform
on `X_U \ L'`. So it lies in `H_U` with probability at most
`2^k / (2^(3k) - 2^(l-1)) <= 2^(1-2k)`. A union bound over the `2^(l-1)`
choices of `y` gives `2^(l-2k)`.

Finally, `k_e ~ Bin(k, 1 - beta)` gives
`E 4^(-k_e) = ((1 - beta)/4 + beta)^k = 4^(-k)(1 + 3 beta)^k <= 4^(-k) e^(3 beta k)`. ∎

At `beta = ln ln k / k` we have `e^(3 beta k) = (ln k)^3`, so `gamma -> 0` as
`k -> infinity` at fixed `l`.

## Step 5: numerator and denominator

By (1), (2), (0) and Lemma 5,

```text
E |Frozen(C) \ Frozen(C')|  <=  k (beta + 3 * 2^(1-l)) / (1 - gamma).        (3)
```

By Lemma 2 applied to the member `(U, L)` of `eps1`, and by `L' ⊆ L`, (0), (2)
and Lemma 5,

```text
E_pi |Frozen(C)|  =  sum_i P_mu(rk_(t_i)(L) = 2)
                 >=  sum_i [ P(block i kept, rk_(t_i)(L') = 2) - gamma ]
                 >=  k [ (1 - beta)(1 - 3 * 2^(1-l)) - gamma ].                  (4)
```

Let `p(t) = P_pi(t in Frozen(C))`. Then `sum_t p(t) = E_pi |Frozen(C)|` and
`p(t) <= pi*`, so

```text
sum_t p(t)^2  <=  pi* E_pi |Frozen(C)|.                                            (5)
```

*Bound on `pi*`.* `p(t) <= P_mu(t` is the triple of an equation of `U`) and
`P_mu <= P / (1 - gamma)`. Let `mu_t` be the number of instance equations with
triple `t`, and let `nu` be the illegitimate fraction of the `m^k` ordered
`k`-tuples, which is `O(k^2/|X|)` by (D7). `U` is uniform on the legitimate
tuples, so `P(e in U) <= k P(e_1 = e) <= k m^(k-1) / ((1 - nu) m^k)`. Hence
`pi* <= mu k / ((1 - nu)(1 - gamma) m)` with `mu = max_t mu_t`, as stated in
the target.

## Step 6: the random-sign Rayleigh quotient

Let `N = D_A^(-1/2) W D_B^(-1/2)` be the normalized bipartite matrix, with
singular values `1 = sigma_1 >= sigma_2 >= ...`. The two-step operator
`(P f)(C) = E[f(C') | C]` on `L^2(pi)` is conjugate to `N N^T`. So it is
self-adjoint and positive semidefinite, it fixes constants, and its second
eigenvalue is `sigma_2^2`. For any `f` that is not `pi`-a.s. constant, the
exchangeability of `(C, C')` gives

```text
sigma_2^2  >=  <f - E f, P (f - E f)> / Var_pi(f)  =  1 - D(f) / (2 Var_pi(f)),
D(f) = E (f(C) - f(C'))^2.                                                         (6)
```

Let `w` be independent uniform signs `+-1` on the finitely many triples, and
put `f_w(C) = sum over t in Frozen(C) of w(t)`. Then

```text
E_w D(f_w)       =  E |Frozen(C) Δ Frozen(C')|  =  2 E |Frozen(C) \ Frozen(C')|,
E_w Var_pi(f_w)  =  E_pi |Frozen(C)| - sum_t p(t)^2.
```

The second equality in the first line is exchangeability. Put
`rho_0 = E|Frozen(C) \ Frozen(C')| / (E_pi|Frozen(C)| - sum_t p(t)^2)` and
suppose the denominator is positive. Then
`E_w [D(f_w) - 2 rho_0 Var(f_w)] = 0`. A sign vector with `Var(f_w) = 0` has
`f_w` constant `pi`-a.s., and then `D(f_w) = 0` because `C'` is also
`pi`-distributed. Since `E_w Var(f_w) > 0`, some `w` has `Var(f_w) > 0` and
`D(f_w) <= 2 rho_0 Var(f_w)`. By (6), `sigma_2^2 >= 1 - rho_0`.

By (3), (4) and (5),

```text
rho_0  <=  (beta + 3 * 2^(1-l)) / ( (1 - gamma)(1 - pi*)((1 - beta)(1 - 3 * 2^(1-l)) - gamma) )  <=  rho,
```

because `(1 - pi*)(a - gamma) >= a - gamma - pi*` for `a - gamma <= 1`. So
`lambda_2 = 1 - sigma_2 <= 1 - sqrt(1 - rho) <= rho` whenever `rho < 1`.
This is Theorem F. (If `rho < 1`, the denominator of `rho_0` is positive.)

*Simplified form.* Take `l >= 6` (so `3 * 2^(1-l) <= 3/32`), `beta <= 1/32`
and `gamma + pi* <= 1/32`. The denominator of `rho` is then at least
`(31/32)((31/32)(29/32) - 1/32) = 26877/32768 > 0.82`. So
`rho <= 1.22 (beta + 6 * 2^(-l)) <= 2 (beta + 6 * 2^(-l))`. Part (b) of the
artifact checks this on a grid.

## Step 7: corollaries

*F1.* Under the hypotheses of F1, `lambda_2 <= 2 beta + 12 * 2^(-l)`. We have
`12 * 2^(-l) <= X(delta) eta' / 2` by the choice of `l`, and
`2 beta < X(delta) eta' / 2`. So `lambda_2 < X(delta) eta'`, and the
hypothesis `min(lambda_2, 1) >= X(delta) eta'` of
`orientation-lift-selectors-need-vanishing-host-gap` fails. That node
notes that `lambda_2` is a property of the host alone, the same for every
orientation lift, so this holds for every selector. The same applies to (G) of
`akkstv-rounding-holds-on-all-loop-free-constraint-graphs`, whose hypothesis
is `lambda_2(G) >= X(s)(1 - val(U_o(G)))`.

*F2.* Verbatim from TR16-198:
- "Hypothesis 3.6. For every constant δ > 0, there exist integers r,q > 0, a
  constant C > 0, such that for all sufficiently large integers 𝓁, for all
  sufficiently large integers n, the following holds."
- "Lemma 3.17. Assume Hypothesis 3.6. For all δ > 0 there are constants C > 0
  and q,r ∈ N, a function α(·) > 0, ... such that for all sufficiently large
  𝓁 > 0, for all sufficiently large n, the following holds."
- In the proof of Lemma 3.20: "Since 𝓁 could have been chosen large enough,
  one contradicts Equation (10)."
- In the proof of Lemma 5.3: "where all hidden constants may depend on δ and
  𝓁 but are independent of k. So for large enough k this contradicts the
  soundness of Lemma 5.4."
- In Section 5.3: "Fix δ > 0. For this δ Hypothesis 3.6 guarantees a global
  linear function as long as 𝓁 and k are large enough ... We choose k large
  enough so that soundness holds".

So the soundness argument is valid at every `l` above a threshold depending on
`delta`, with `k` then taken large for `(delta, l)`. Lemma 5.3 itself is
stated as "there exists large enough 𝓁 ≪ k". A designer may therefore take
`l >= max(l_0(delta), log2(24/(X(delta) eta')))`. The recorded implication
"`eta' >= c(l)/X(delta)` with `l = l(delta)`" then bounds nothing uniformly,
because `c(l) <= lambda_2 <= 12 * 2^(-l) + o(1)` by Theorem F.
F1 does not use this reading.

## Numerical cross-check

Part (c) of the artifact (`--instance`, about 2 minutes) rebuilds the
`n = 24`, `k = 2`, `l = 2` sparse instance of
`experiments/ugc-akkstv-regularize-2026-09-17`. It computes the exact
canonical folded `lambda_2` and the exact `rho_0` of the class statistic
"intersection of member frozen sets". That statistic is a class function even
where the small instance violates legitimacy (b).

| beta | lambda_2 | rho_0 | 1 - sqrt(1 - rho_0) | frozen-invariant classes |
|---|---|---|---|---|
| 0 | 0.03491 | 0.4806 | 0.27934 | 1799 / 1828 |
| 0.1 | 0.03919 | 0.5011 | 0.29367 | 1799 / 1828 |

At `l = 2` the bound is loose, as expected from the constant `6 * 2^(-l)`. The
statement is asymptotic in `l`, and part (b) tabulates it: for example,
`lambda_2 <= 1.2 * 10^(-2)` at `l = 8` and `lambda_2 <= 7.4 * 10^(-4)` at
`l = 12`, for `k >= 10^6`.
