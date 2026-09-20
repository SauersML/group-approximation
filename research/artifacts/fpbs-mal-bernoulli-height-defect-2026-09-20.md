# Heights on the Bernoulli shift of Gamma_mal have a uniform defect

Worker swarm-0917-w22-w22-fp-break (belief breaker, operator-algebras),
September 20, 2026. Target: `fpbs-mal-bernoulli-single-stage-floor`.

## 0. Setting

- `Gamma = Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>`.
  Its stages `H_n = <a, b_n>` are free on `{a, b_n}`. `Gamma` is torsion-free,
  since it is an increasing union of free groups.
- `beta` is the Bernoulli shift of `Gamma` on `(X, mu) = ([0,1]^Gamma, Leb)`.
- A **height** at stage `n` is a Borel map `f : X -> Y`, where `Y` is a
  countable set with an action of `H_n`. Its **defect** at `s in H_n` is
  `d_s(f) = mu{ x : f(s x) != s f(x) }`.
  Write `p_y = mu(f^{-1}(y))` and `p* = max_y p_y`.
- The motivating example is the odometer coordinate of
  `fpbs-mal-odometer-product-actions-have-cost-two`. There
  `Y = Z/N`, `h` acts by `+chi(h)`, and the height is exactly equivariant on
  `beta x Z^_chi`. Its seed set `{z mod N in {0,1,2}}` gives relative
  cost `3/N -> 0`.

## 1. Result

**Theorem H.** Fix a stage `n` and a height `f : X -> Y`.

1. `d_a(f) + d_{b_n}(f) >= (2 - sqrt 3) (1 - sum_y p_y^2)`.
2. Suppose some `s in {a, b_n}` has no fixed point on `Y`. Then
   `d_a(f) + d_{b_n}(f) >= kappa := (2 - sqrt 3)/(4 - sqrt 3) = 0.1181...`.

The constants do not depend on `n`, on `Y`, or on `|Y|`.

**Corollary H'.** Let `chi` be any character with `chi(b_n) != 0` or
`chi(a) != 0`. Take `N` not dividing that value, or take `Y = Z` or
`Y = Z^` (profinite). Then no height of `beta` into `Y` with the action
`+chi` has `d_a + d_{b_n} < 0.118`, at any stage and for any `N`. In
particular no sequence of heights mod `N` has defect tending to 0 as
`N -> infinity`.

## 2. Proof

**Step 1 (Koopman of a stage).** Let `H <= Gamma` be torsion-free. The
Koopman representation of `beta|H` on `L^2_0(X)` is a multiple of `lambda_H`.

*Proof.* Fix an orthonormal basis `{1} u {e_i}` of `L^2[0,1]`. Then
`L^2(X)` has the orthonormal basis of finite tensor products
`e_{i_1}(x_{g_1}) ... e_{i_m}(x_{g_m})`. Each is indexed by a finitely
supported labelling `F -> {i}`, with `F` a finite subset of `Gamma`. The
constant function corresponds to `F` empty. `H` permutes these basis vectors
by left translation of `F`. Suppose `h F = F` with `F` nonempty. Then `h`
permutes `F`, so `h^{|F|!}` fixes a point of `Gamma` under left
multiplication. Hence `h^{|F|!} = 1`, and `h = 1` because `H` is torsion-free.
So `H` acts freely on the basis of `L^2_0`, and `L^2_0` is a direct sum of
copies of `l^2(H) = lambda_H`. ∎

**Step 2 (Fell absorption).** For every unitary representation `pi` of `H`,
`lambda_H ⊗ pi ≅ (dim pi) · lambda_H`.

*Proof.* `U(delta_h ⊗ v) = delta_h ⊗ pi(h)^{-1} v` intertwines
`lambda ⊗ pi` with `lambda ⊗ 1`. ∎

**Step 3 (Kesten).** For `H` free on `{s_1, s_2}`,
`|| sum_{i, ±} lambda(s_i^{±1}) || = 2 sqrt 3`. This is H. Kesten,
*Symmetric random walks on groups*, Trans. AMS 92 (1959): the spectral
radius of simple random walk on the free group of rank `k` is
`sqrt(2k-1)/k`. For `k = 2` this is `sqrt 3/2`, times the degree 4. The
same norm holds on every multiple of `lambda`. It is the input already used
in `fpbs-mal-twisted-level-seed-density-uniform-witness`.

So for every `v` in a multiple of `lambda_{H_n}`, with `S = {a, b_n}`:

```text
sum_{s in S} ||s v - v||^2 = 4||v||^2 - < sum_{s in S^{±}} s v , v >
                           >= (4 - 2 sqrt 3) ||v||^2.
```

**Step 4 (graph vector).** Let `H_n` act diagonally on `L^2(X x Y)`, with
counting measure on `Y`. Put `xi(x, y) = 1[f(x) = y]`, so `||xi|| = 1`.
- `(s xi)(x, y) = 1[ s f(s^{-1} x) = y ]`, so
  `<s xi, xi> = mu{ x : f(s x) = s f(x) }` (substitute `x -> s x`) and
  `||s xi - xi||^2 = 2 d_s(f)`.
- `L^2(X x Y) = l^2(Y) ⊕ (L^2_0(X) ⊗ l^2(Y))`. Both summands are
  invariant. By Steps 1 and 2 the second is a multiple of `lambda_{H_n}`.
- The component of `xi` in `l^2(Y)` is `y -> p_y`, of squared norm
  `sum p_y^2`. So the component `w` in the second summand has
  `||w||^2 = 1 - sum p_y^2`. Projection onto an invariant summand commutes
  with the action, so `||s w - w|| <= ||s xi - xi||`.
- By Step 3, `2 (d_a + d_{b_n}) >= (4 - 2 sqrt 3)(1 - sum p_y^2)`. This is
  item 1.

**Step 5 (concentration).** Let `s` have no fixed point on `Y`, and let
`A = f^{-1}(y*)` with `mu(A) = p*`. For `x in A ∩ s^{-1} A`,
`f(s x) = y* != s y* = s f(x)`. So `d_s >= mu(A ∩ s^{-1}A) >= 2 p* - 1`.
Since `sum p_y^2 <= p*`, item 1 gives
`d_a + d_{b_n} >= max( (2 - sqrt 3)(1 - p*), 2 p* - 1 )`. The two terms
are equal at `p* = (3 - sqrt 3)/(4 - sqrt 3)`, which gives the minimum
`kappa = (2 - sqrt 3)/(4 - sqrt 3)`. This is item 2. ∎

*Checked numerically:* `kappa = 0.118146...`, and both terms equal it at
`p* = 0.559073...`.

## 3. What it kills: approximate-odometer refutations of the floor

**The class.** One way to refute the floor would be to show `C(beta) < infinity`
by moving the odometer proof into `beta` itself:
1. find a height `z_N : X -> Z/N` of `beta` that is nearly `chi`-equivariant
   on `H_{n+1}`;
2. seed `b_{n+1}` on `{z_N in {0,1,2}}`, which has mass about `3/N`;
3. run the 2-of-3 closure on the triples `{w, a w, b_{n+1} w}`, as in the
   odometer claim, and bound the error by the defect.

Step 3 needs the closure to follow about `N/3` consecutive residue classes.
So the errors must satisfy at least `d_a + d_{b_{n+1}} -> 0`, and in fact
`N (d_a + d_{b_{n+1}}) -> 0`, for the leftover mass to be `o(1)`.

**Where it dies: step 1.** For `chi` of the odometer claim, `chi(a) = 1`, so
`a` has no fixed point on `Z/N` for `N >= 2`. Theorem H(2) gives
`d_a + d_{b_{n+1}} >= 0.118` for every `N`, every `n`, and every Borel `z_N`.
The same holds for heights into `Z`, into `Z^`, or into any finite or
profinite `Gamma`-set on which `a` or `b_{n+1}` has no fixed point. This
covers dihedral and congruence heights, and any map to a finite quotient
level.

**Invariant.** The Kesten gap `4 - 2 sqrt 3` of the Koopman representation
of `beta|H_n` twisted by the permutation representation `l^2(Y)`. By Fell
absorption it is the gap of `infinity · lambda_{F_2}`, whatever `Y` is.

**What is new against the graph.**
- `fpbs-mal-fixed-price-iff-bernoulli-finite-cost` already excludes,
  qualitatively, actions with a compact factor from its item 5. It does
  this via Koopman weak containment. The qualitative argument allows
  approximate heights whose defect `eps_0(N)` tends to 0 as `N` grows, which
  would still feed step 3. Theorem H excludes that, because the constant is
  uniform in `N`, `n` and `Y`.
- `fpbs-mal-stage-block-sprinkling-threshold` covers iid or block sprinkles.
  The odometer claim's own `distinct_from` notes that compact-factor
  sprinkles escape it. Theorem H closes that gap for heights on `beta`.
- The heuristic "compact or character structure" paragraph of
  `research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md` §5 was
  not recorded as a kill. Theorem H is its rigorous form, in the direction
  that bears on refutations.

**Amenability is the reason.** For `a` alone, the bound fails. `<a> ≅ Z`
acts freely, so the Rokhlin lemma gives heights mod `N` with `d_a < eps`
for every `eps` and every `N`. The defect is forced only by using two free
generators of a stage together, which is exactly what the 2-of-3 triples
`{w, a w, b w}` use.

## 4. What survives

- **Seed sets that are not functions of an approximate height.** Theorem H
  says nothing about seed sets that pay the defect in a different way. For
  example, a cheap seed set could correct the defect region of a height with
  its own long-generator pieces. `fpbs-mal-long-generator-packing-growth`
  and the telescoping of Proposition Q remain the live refutation shapes.
- **The lower-bound side is untouched.** Lower bounds for `Q_j(rho)` come
  from free witnesses `X` with `Q_j(rho) >= Q_j(X)`, and finite levels are
  allowed there. So the `(O)`/`(RI)` route is not affected.
- **Remark (not established).** Refutation witnesses must be tempered: if a
  free `a` satisfies `a ≼ beta`, then its Koopman representation on
  `L^2_0` is weakly contained in `lambda_Gamma`. This follows from the
  Koopman weak-containment import `burton-kechris-koopman-weak-containment`
  together with Step 1 for `H = Gamma`. Conversely, Gaussian actions
  `G(pi)` with `pi ≼ lambda_Gamma` should satisfy `G(pi) ≼ G(infinity · lambda) = beta`,
  and hence have cost exactly `C(beta)` when free. That gives a wider
  family of equivalent test actions. The Gaussian transfer is only sketched
  here and is not recorded.

## 5. Not claimed

- No bound on `relC(E_beta; E_{beta|H_1})` in either direction.
- No statement about graphings of `beta` that are not built from heights.
- Nothing about actions other than `beta` and its restrictions to stages.
