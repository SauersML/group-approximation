---
rg: 2
id: qudit-code-rounding-factor-one-plus-inv-sqrt-d-proof
kind: route
title: Post-select a ground state on its most satisfied code projector and bound the leak by equal principal angles
target: qudit-code-rounding-factor-one-plus-inv-sqrt-d
requires: []
artifacts:
  - experiments/qudit-stabilizer-rounding-constant-2026-09-17/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane sw-078b, 2026-09-17.

## Setting

`d` is prime. A *stabilizer group* `S` is an abelian group of `n`-qudit Weyl operators
(with phases) that contains no scalar other than `I`. Its code projector is
`Pi_S = |S|^(-1) sum_(g in S) g`, the projector onto the joint `+1` eigenspace. The
trivial group gives `Pi = I`. For commuting stabilizer groups `S, T`, the product
`Pi_T Pi_S` is `Pi_(<S,T>)` if `<S,T>` contains no nontrivial scalar, and `0`
otherwise.

Put `h(r) = sqrt(r) - r` for `0 <= r <= 1/4` and `h(r) = 1/4` for `1/4 <= r < 1`. Put
`kappa_d = h(1/d)/(1 - 1/d)` and `gamma_d = 1/(1 - kappa_d)`. Then
`kappa_d = 1/(sqrt(d)+1)` and `gamma_d = 1 + 1/sqrt(d)` for `d >= 5`, while
`kappa_3 = 3/8`, `gamma_3 = 8/5`, `kappa_2 = 1/2` and `gamma_2 = 2`.

(F0) `r -> h(r)/(1-r)` is increasing on `[0,1)`. On `[0,1/4]` it equals
`sqrt r/(1+sqrt r)`; on `[1/4,1)` it equals `1/(4(1-r))`; both pieces take the value `1/3`
at `r = 1/4`. Hence `h(r) <= kappa_d (1-r)` for every `r in {d^(-1), d^(-2), ...}`.

## Statement proved (relative form, for induction)

Fix a stabilizer group `S_0`, `P_0 = Pi_(S_0)`, and an *instance on `P_0`*. This is a
finite list of pairs `(w_a, Q_a)` with `w_a >= 0`. Each `Q_a` is either `0` or
`Pi_(S_a)` for a stabilizer group `S_a` containing `S_0`. For unit vectors `v` in the
range of `P_0` put

```text
F(v) = sum_a w_a (1 - <v|Q_a|v>).
```

**Theorem.** Some stabilizer state `phi` in the range of `P_0` has
`F(phi) <= gamma_d inf_v F(v)`.

With `S_0 = {I}` this is the claim: `F(v) = <v|H|v>` for
`H = sum_a w_a (I - Pi_(S_a))`, and `inf_v F = lambda_min(H)`.

## Lemma (equal principal angles)

Let `P, Q` be projectors with `PQP = r P'` for a projector `P'` and some `0 < r < 1`.
Let `psi` be a unit vector with `q := <psi|Q|psi> <= M := <psi|P|psi>`. Then

```text
Re <psi| P Q (I-P) |psi>  <=  h(r) M.
```

*Proof.* By Jordan's lemma the space splits orthogonally into subspaces invariant
under both `P` and `Q`, each of dimension one or two. On a two-dimensional block,
`P = |p_i><p_i|` and `Q = |q_i><q_i|` with `0 < |<p_i|q_i>| < 1`. The squared cosines
`|<p_i|q_i>|^2` are the nonzero eigenvalues of `PQP` on the range of `P`, so they all
equal `r`. Choose phases so that `q_i = sqrt(r) p_i + sqrt(1-r) p_i^perp`, with `p_i^perp`
the unit vector of the block orthogonal to `p_i`. The one-dimensional blocks lie in
`P cap Q^perp`, `P^perp cap Q`, `P^perp cap Q^perp` or `P cap Q`, and the last is
impossible since `r < 1`. Write the block components of `psi` as
`alpha_i p_i + beta_i p_i^perp`, and put `A = sum|alpha_i|^2`, `B = sum|beta_i|^2`,
`C = sum Re(conj(alpha_i) beta_i) <= sqrt(AB)`.

- The range of `Q(I-P)` applied to `psi` meets `P psi` only inside two-dimensional blocks.
  Components in `P^perp cap Q` are orthogonal to `P psi`, and the others are killed by
  `Q` or `I-P`. So `Re<psi|PQ(I-P)|psi> = sum_i Re(conj(alpha_i) sqrt(r(1-r)) beta_i) = sqrt(r(1-r)) C =: u`.
- `M >= A`, and `q >= sum_i |sqrt(r) alpha_i + sqrt(1-r) beta_i|^2 = rA + (1-r)B + 2u`.

Assume `u > 0`. Put `s = sqrt(rA)` and `t = sqrt((1-r)B)`, so `u <= st`, `s^2 <= rM`, and
`s^2 + t^2 + 2u <= q <= M`. First, `s^2 + t^2 >= 2st >= 2u`, so `4u <= M`. Second,
`u^2 <= s^2 t^2 <= s^2 (M - 2u - s^2)`. For `r <= 1/4` the right side increases in `s^2`
on `[0, rM]`, because `rM <= M/4 <= (M - 2u)/2` by `u <= M/4`. So
`u^2 <= rM (M - rM - 2u)`, i.e. `u^2 + 2rMu - r(1-r)M^2 <= 0`, i.e. `u <= (sqrt r - r) M`.
Hence `u <= h(r) M`. QED.

## Proof of the theorem

Induction on `k = log_d rank P_0`.

*Trivial terms.* Call a term trivial if `Q_a = 0` or `Q_a = P_0`. Then `<v|Q_a|v>` is
constant on the range of `P_0`. If all terms are trivial, `F` is constant there, and
any stabilizer state in the range works. One exists, since `S_0` extends to a maximal
stabilizer group. This covers `k = 0`.

Otherwise let `psi` minimize `F` over unit vectors in the range of `P_0`. Put
`K = sum_a w_a P_0 Q_a P_0` and `lambda = <psi|K|psi>`. Then `psi` is a top eigenvector of
`K` restricted to that range, and `F(psi) = W - lambda` with `W = sum_a w_a`. Put
`q_a = <psi|Q_a|psi>`. Let `R` be a nontrivial term maximizing `q_a`, and `M = q_R`.

*Case `M = 0`.* Then every nontrivial term has `q_a = 0`, so
`F(psi) = sum_(nontrivial) w_a + sum_(Q_a = 0) w_a`. Every stabilizer state `phi` in the
range has `F(phi)` at most that same sum, and `gamma_d >= 1`.

*Case `M > 0`.* Put `P = Q_R = Pi_(S_R)`. `S_R` properly contains `S_0` (nontrivial),
so `rank P < rank P_0`. For each term `a` with `Q_a = Pi_(S_a)`, put
`T_a = S_a cap C(S_R)` (the elements commuting with all of `S_R`) and
`r_a = |T_a|/|S_a| in {1, 1/d, 1/d^2, ...}`. A Weyl operator `g` that fails to commute
with some `h in S_R` maps the range of `P` into an orthogonal eigenspace of `h`, so
`P g P = 0`. For `g in C(S_R)`, `P g P = g P`. Hence

```text
P Q_a P = r_a Q''_a,      Q''_a := Pi_(T_a) P,                                   (1)
```

and `Q''_a` is `0` or `Pi_(<T_a, S_R>)`, a projector of a group containing `S_R`. For
`Q_a = 0` put `r_a = 1`, `Q''_a = 0`. The *reduced instance on `P`* is
`(w_a r_a, Q''_a)`, with frustration `F''`. By (1), for unit `v` in the range of `P`,

```text
F(v) = sum_a w_a (1 - r_a) + F''(v).                                              (2)
```

*Energy after post-selection.* Put `psi_1 = P psi / sqrt(M)`. Since `P <= P_0` and
`K psi = lambda psi` in the range of `P_0`, `<psi|P K|psi> = lambda M`. So

```text
lambda - <psi_1|K|psi_1> = <psi| P K (P_0 - P) |psi> / M = sum_a w_a Re<psi|P Q_a (I-P)|psi> / M,
```

using `(P_0 - P) psi = (I - P) psi` and that the total is real. If `r_a = 1`, then
`S_a` commutes with `S_R`, `Q_a` commutes with `P`, and the summand vanishes. If
`r_a < 1`, then `Q_a != 0` and (1) says `P Q_a P = r_a` times a projector. Also
`q_a <= M`, because a term with `r_a < 1` is nontrivial (`Q_a = P_0` would give
`r_a = 1`). By the Lemma and (F0),

```text
F(psi_1) - F(psi) = lambda - <psi_1|K|psi_1> <= sum_a w_a h(r_a) <= kappa_d sum_a w_a (1 - r_a).   (3)
```

*Induction.* The reduced instance lives on `P`, of smaller rank. So some stabilizer
state `phi` in the range of `P` (hence of `P_0`) has
`F''(phi) <= gamma_d F''(psi_1)`. Put `L = sum_a w_a (1 - r_a)`. By (2) and (3),

```text
F(phi) = L + F''(phi) <= L + gamma_d (F(psi_1) - L)
       <= gamma_d F(psi) + (gamma_d kappa_d - (gamma_d - 1)) L = gamma_d F(psi),
```

since `gamma_d kappa_d = gamma_d - 1`. QED.

## Sharpness

On one qudit, `H = (I - |0><0|) + (I - |+><+|)`, where `|+> = d^(-1/2) sum_j |j>` spans the
`X = 1` eigenspace. Two rank-one projectors with overlap `|<0|+>|^2 = 1/d` have top
eigenvalue `1 + 1/sqrt(d)` for their sum, so `lambda_min(H) = 1 - 1/sqrt(d)`. A stabilizer
state in the `Z` or `X` basis gives at least `1 - 1/d`, with equality at `|0>` and `|+>`.
Any other stabilizer state is mutually unbiased to both and gives `2 - 2/d`. The ratio
is `(1 - 1/d)/(1 - 1/sqrt(d)) = 1 + 1/sqrt(d)`. So `gamma_d` is optimal for `d >= 5`.

The proof is tight exactly where (F0) is tight at `r = 1/d`. This is a single
non-commuting partner with `q_a = M`, all of `P psi` inside the two-dimensional blocks
(`A = M`), and `s = sqrt(M/d)`, `t = sqrt(M)(1 - 1/sqrt d)`. That is the one-qudit example.

## Gaps and what is not claimed

- `d = 3`: (F0) peaks at `r = 1/3 > 1/4`, where `h = 1/4`. The extremal configuration
  needs `A = 3M/4`, so a quarter of `P psi` lies in `P cap Q^perp`. That configuration
  exists for multi-qutrit code spaces, but the numerics never realize the ratio `8/5`.
  The dual LP and the rounding both peak at `1 + 1/sqrt3` for `n <= 2`. Closing `d = 3`
  at `1 + 1/sqrt3` would need either a choice of `R` that avoids this configuration or
  use of the eigen-equation beyond (3).
- `d = 2`: this argument gives only `2`. The Pauli proof
  (`stabilizer-rounding-constant-is-one-over-sqrt2-proof`) gives `1 + 1/sqrt2`, which
  is sharp by the same example.
- The result is about nonnegative combinations of code projectors. For general
  Hermitian Weyl sums the additive constant is not bounded in `d`; see
  `qudit-weyl-rounding-sharp-constant`.

## NP consequence (verification)

A stabilizer state on `n` prime-`d` qudits has a polynomial-size `F_d` tableau.
`<phi|Pi_S|phi>` is `|T|/|S|` or `0`, computed by `F_d` linear algebra as in
`qudit-stabilizer-rounding-for-code-constraint-hamiltonians-proof` step 6. So the
verifier computes `<phi|H|phi>` exactly. YES (`lambda_min <= a`) gives a witness with
value `<= gamma_d a`, and NO (`lambda_min >= b`) forces every value `>= b`. The problem
is in NP once `b > gamma_d a`. Extra terms `0 <= h <= I` of weight `V` shift the YES
witness value by at most `V`.
