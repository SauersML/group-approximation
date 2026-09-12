# Ring rank-approximability of the Leavitt algebra collapses (2026-09-12)

Lane `w4-r4-approx`, family R4 (lead `w3-strategist-gate`, verifier `w4-vf-gate`).

## 0. Summary

Plan 2 of `rank-four-associativity-gate-plans-2026-09-12.md` proposed
`leavitt-unit-linear-soficity-is-ring-rank-approximability`: `R^x` is `F_p`-linear sofic iff
`R = L_K(1,2)` is rank-approximately representable. It named "approximately proper isometries" as the
remaining gap.

- **The right-hand side is false.** Three of the Leavitt relations already rule it out, with an explicit
  constant (Theorem 3, Corollary 4).
- **The gap is empty.** `rk(1 - st) = rk(1 - ts)` holds in every Sylvester matrix rank function
  (Lemma 1), so isometries are never approximately proper.
- **So the claim is equivalent to "`R^x` is not `F_p`-linear sofic"** (Theorem 5). It restates the gate's
  negative answer and is not an intermediate step. Its backward direction is vacuous, and its forward
  direction is the gate.
- **Payoff for Plan 1** (Section 3): to reach a contradiction, the end of
  `rank-four-isometry-relations-give-corner-cuntz-family` only needs a left-invertible `S` and a nonzero
  `X` with `XS = 0` inside one corner.
  - The completeness relation (check (b)) is not needed, and neither is `T_0 S_1 = 0`.
  - `rk(e) = rk(D)` (check (c)) can be replaced by any positive lower bound on `rk(X)`.

## 1. Sylvester rank inequalities

**Setup.** `A` is a unital ring and `rk` a Sylvester matrix rank function on matrices over `A`. The axioms
used are:
- `rk(1) = 1`;
- `rk(MN) <= min(rk M, rk N)` for rectangular products;
- `rk(diag(M, N)) = rk M + rk N`.

Examples are the normalized rank on `M_n(k)`, rank ultraproducts `prod_omega M_(n_i)(k)/d_omega`, and
the rank function induced on `F_p[G]` by an `F_p`-linear sofic approximation of `G`. Consequences:
- invertible matrices preserve `rk`;
- `rk(M + N) <= rk M + rk N`, since `M + N = [1 1] diag(M, N) [1 1]^T`.

**Orthogonal additivity.** Let `e` be an idempotent, `a in eAe` and `b in (1-e)A(1-e)`. Put
`u = [e, 1-e]` (a row) and `v = u^T` (a column). Then `u diag(a, b) v = a + b`, and
`v (a + b) u = diag(a, b)` because `eb = be = 0` and `(1-e)a = a(1-e) = 0`. So
`rk(a + b) = rk(a) + rk(b)`.

**Lemma 1 (push-through).** For all `x, y in A`, `rk(1 - xy) = rk(1 - yx)`. If `e` is idempotent and
`x, y in eAe`, then `rk(e - xy) = rk(e - yx)`.

*Proof.* Block elimination with invertible elementary matrices gives

```text
[[1,0],[-y,1]] [[1,x],[y,1]] [[1,-x],[0,1]] = [[1,0],[0,1-yx]],
[[1,-x],[0,1]] [[1,x],[y,1]] [[1,0],[-y,1]] = [[1-xy,0],[0,1]].
```

So `1 + rk(1 - yx) = rk [[1,x],[y,1]] = rk(1 - xy) + 1`. For the corner form, write
`1 - xy = (e - xy) + (1 - e)`. The two summands lie in `eAe` and `(1-e)A(1-e)`, so orthogonal
additivity gives `rk(1 - xy) = rk(e - xy) + rk(1 - e)`. The same holds for `yx`. ∎

Over `M_n(k)` this is the kernel bijection `v -> yv` from `ker(1 - xy)` onto `ker(1 - yx)`. It is
recorded on main in step 1 of `leavitt-algebra-has-no-unital-rank-model-proof`
(Arzhantseva–Păunescu, Prop. 2.8). The block form uses no kernels, so it holds for every Sylvester
matrix rank function.

**Lemma 2 (annihilators of near-isometries).** Let `e` be idempotent, `S, T in eAe` and `X in Ae`. Then

```text
rk(X) <= rk(e - TS) + rk(XS).
```

*Proof.* `X = Xe = X(e - ST) + (XS)T`. The first term has rank at most `rk(e - ST) = rk(e - TS)` by
Lemma 1, and the second at most `rk(XS)`. ∎

**Theorem 3 (Toeplitz defect bound).** Let `e` be idempotent and `S_0, S_1, T_0, T_1 in eAe`. Then

```text
rk(e) <= rk(e - T_0 S_0) + rk(e - T_1 S_1) + rk(T_1 S_0).
```

*Proof.* Lemma 2 with `S = S_0`, `T = T_0`, `X = T_1` gives
`rk(T_1) <= rk(e - T_0 S_0) + rk(T_1 S_0)`. Also `e = T_1 S_1 + (e - T_1 S_1)`, so
`rk(e) <= rk(T_1 S_1) + rk(e - T_1 S_1) <= rk(T_1) + rk(e - T_1 S_1)`. ∎

- **Sharp.** Take `A = k`, `e = 1`, `S_0 = T_0 = 1` and `S_1 = T_1 = 0`: the defects are `0 + 1 + 0 = 1`.
- **Relations used:** only `t_0 s_0 = 1`, `t_1 s_1 = 1` and `t_1 s_0 = 0`. The theorem does not use
  `s_0 t_0 + s_1 t_1 = 1`, `t_0 s_1 = 0`, simplicity, or the characteristic.

**Corollary 4 (no rank-approximate representations, explicit).** Let `K` and `k` be any fields,
`d >= 2` and `R = L_K(1,d)`. Let `phi : R -> M_n(k)` be any map with `phi(0) = 0` and `phi(1) = 1`. Then
on at least one of the pairs `(t_0, s_0)`, `(t_1, s_1)`, `(t_1, s_0)`, the defect
`rk(phi(ab) - phi(a) phi(b))` is at least `1/3` in normalized rank.

*Proof.* Since `t_0 s_0 = t_1 s_1 = 1` and `t_1 s_0 = 0`, the three defects are `rk(1 - T_0 S_0)`,
`rk(1 - T_1 S_1)` and `rk(T_1 S_0)`, where `S_i = phi(s_i)` and `T_i = phi(t_i)`. They sum to at least 1
by Theorem 3 with `e = 1`. ∎

When `phi(1)` is not the identity, the images of `1` must have rank tending to `0`. That qualitative
statement is the scope remark of `leavitt-algebra-has-no-unital-rank-model-proof`, through corners of
the ultraproduct.

## 2. The Plan 2 claim is the gate's negative answer

**Theorem 5.** Let `K` be a finite field of characteristic `p` and `R = L_K(1,2)`.
- The right-hand side of `leavitt-unit-linear-soficity-is-ring-rank-approximability` fails. Once `F`
  contains `0, 1, s_0, s_1, t_0, t_1` and `eps <= 1/3`, Corollary 4 rules out every unital `F_p`-linear
  `phi` with the required multiplicativity, for every value of `c`.
- So the claim holds iff `R^x` is not `F_p`-linear sofic.

*Remarks on the node's Attempts.*

- **The gap.** "Approximately proper isometries", meaning `rk(t_i s_i - 1) -> 0` with `rk(1 - s_i t_i)`
  bounded below, do not exist: the two ranks are equal (Lemma 1).
- **Backward.** The hypothesis is false, so this direction is vacuous.
- **Forward.** The sketch cites `[x_12(a), x_21(b)]` as carrying the multiplication, but opposite roots
  have no Steinberg commutator formula. Multiplication enters only through
  `[x_12(a), x_23(b)] = x_13(ab)` in `EL_3`. Turning the root maps `n_ij(a) = sigma(x_ij(a)) - 1` into an
  approximately multiplicative `phi` needs the two-root identities, which is the open
  `el3-rank-models-factor-through-ring-rank-models`. By Theorem 5 no model of `R^x` ever yields such a
  `phi`, so any proof of the forward direction is a proof that no model exists.

**Wiring.** There are two routes:
- `ring-rank-approximability-forces-non-linear-soficity`: the claim plus Theorem 3 gives
  `non-linear-sofic-group`;
- `ring-rank-approximability-from-leavitt-el3-triviality`: the gate instance plus Theorem 3 gives the
  claim.

So the claim is at least as strong as the payoff, and it follows from the gate instance. It is not an
easier intermediate step.
