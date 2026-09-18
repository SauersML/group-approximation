---
rg: 2
id: qudit-code-rounding-sharp-factor-all-primes-proof
kind: route
title: Average the post-selection leak over the terms and bound each pair by the operator inequality PQ+QP-PQP-QPQ <= (sqrt r - r)(P+Q)
target: qudit-code-rounding-sharp-factor-all-primes
requires: []
artifacts:
  - experiments/qudit-code-rounding-symmetric-averaging-2026-09-17/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane w3-078, 2026-09-17. The skeleton is the
post-selection induction of `qudit-code-rounding-factor-one-plus-inv-sqrt-d-proof`. Two changes:
the post-selected term `R` is no longer the most satisfied one, and the one-sided per-term leak
lemma (which needed `q_a <= M` and lost at `r > 1/4`) is replaced by a two-sided operator
inequality with no side condition. This removes the `d = 3` gap (`8/5`) and the `d = 2` gap (`2`).

## Setting

`d` is prime (including `d = 2`). A *stabilizer group* `S` is an abelian group of `n`-qudit Weyl
operators, with phases, containing no scalar other than `I`. Its code projector is
`Pi_S = |S|^(-1) sum_(g in S) g`. For commuting groups `S, T`, `Pi_T Pi_S` is `Pi_(<S,T>)` when
`<S,T>` contains no nontrivial scalar and `0` otherwise.

Put `kappa_d = 1/(1 + sqrt d)` and `gamma_d = 1/(1 - kappa_d) = 1 + 1/sqrt d`.

(F0) The map `r -> (sqrt r - r)/(1 - r) = sqrt r/(1 + sqrt r)` is increasing on `[0,1)`. Hence
`sqrt r - r <= kappa_d (1 - r)` for every `r in {d^(-1), d^(-2), ...}`.

## Statement proved (relative form)

Fix a stabilizer group `S_0` with `P_0 = Pi_(S_0)`. An *instance on `P_0`* is a finite list of
pairs `(w_a, Q_a)` with `w_a > 0`, where each `Q_a` is `0` or `Pi_(S_a)` for a stabilizer group
`S_a` containing `S_0`. For unit vectors `v` in the range of `P_0`, put
`F(v) = sum_a w_a (1 - <v|Q_a|v>)`.

**Theorem.** Some stabilizer state `phi` in the range of `P_0` has `F(phi) <= gamma_d inf_v F(v)`.

With `S_0 = {I}` and `H = sum_a w_a (I - Pi_(S_a))`, this is the claim, since `F(v) = <v|H|v>`.
Terms with `w_a = 0` can be deleted first.

## Step 1: compression (unchanged)

Let `P = Pi_(S_R)` with `S_R` containing `S_0`, and let `Q = Pi_(S_a)`. Put `T_a = S_a cap C(S_R)`,
the elements of `S_a` that commute with all of `S_R`, and `r_a = |T_a|/|S_a| in {1, 1/d, 1/d^2, ...}`.
If `g` fails to commute with some `h in S_R`, then `gh = omega^t hg` with `t != 0`, and `g` maps the
range of `P` into the `omega^(-t)` eigenspace of `h`. So `P g P = 0`. If `g in C(S_R)`, then
`PgP = gP`. Hence

```text
P Q P = r_a Q''_a,      Q''_a := Pi_(T_a) P  in {0, Pi_(<T_a, S_R>)}.                  (1)
```

For `Q_a = 0` put `r_a = 1` and `Q''_a = 0`. If `S_a` commutes with `S_R`, then `r_a = 1`.

## Step 2: the pair inequality (new)

**Lemma.** Let `P, Q` be orthogonal projectors such that `PQP = r P'` for a projector `P' != 0`
and some `0 < r < 1`. Then, as operators,

```text
PQ + QP - PQP - QPQ  <=  (sqrt r - r) (P + Q).                                          (2)
```

*Proof.* The nonzero spectrum of `PQP` is `{r}`. Since `PQP = (QP)^*(QP)` and `QPQ = (PQ)^*(PQ)`, the
nonzero spectrum of `QPQ` is also `{r}`. By Jordan's lemma the space is an orthogonal sum of
subspaces invariant under `P` and `Q`, each of dimension 1 or 2. A one-dimensional block lies in
`P cap Q`, `P cap Q^perp`, `P^perp cap Q` or `P^perp cap Q^perp`. The first is impossible, because it
would give the eigenvalue `1` of `PQP`. On a block in `P cap Q^perp`, the left side of (2) is `0` and
the right side is `sqrt r - r >= 0`. The same holds for `P^perp cap Q`, and both sides vanish on
`P^perp cap Q^perp`. On a two-dimensional block, `P = |p><p|` and `Q = |q><q|` with
`|<p|q>|^2 in (0,1)`. This number is the eigenvalue of `PQP` on the block, so it is `r`. Choose the
phase of `q` so that `<p|q> = sqrt r`. Then `PQ = sqrt r |p><q|`, `QP = sqrt r |q><p|`,
`PQP = r|p><p|` and `QPQ = r|q><q|`. So the left side minus the right side of (2) is

```text
sqrt r (|p><q| + |q><p|) - sqrt r (|p><p| + |q><q|)  =  - sqrt r (|p> - |q>)(<p| - <q|)  <=  0.
```

QED.

**Corollary (pair leak).** For projectors `P, Q` as in the Lemma, and every vector `psi`,

```text
Re<psi|P Q (I-P)|psi> + Re<psi|Q P (I-Q)|psi>  <=  (sqrt r - r)(<psi|P|psi> + <psi|Q|psi>).
```

*Proof.* `Re<psi|PQ(I-P)|psi> = Re<psi|PQ|psi> - <psi|PQP|psi>` and
`Re<psi|QP(I-Q)|psi> = Re<psi|QP|psi> - <psi|QPQ|psi>`, and `Re<psi|QP|psi> = Re<psi|PQ|psi>`. The
sum is `<psi|(PQ + QP - PQP - QPQ)|psi>`. Apply (2). QED.

The Lemma needs no hypothesis on `psi`. It replaces the one-sided lemma of the earlier proof, which
needed `<Q> <= <P>` and only gave `1/4` for `r > 1/4`.

## Step 3: proof of the theorem

Induction on `k = log_d rank P_0`. Call a term *trivial* if `Q_a in {0, P_0}`. Then `<v|Q_a|v>` is
constant on the range of `P_0`. If every term is trivial, `F` is constant there. Any stabilizer
state in the range works, and one exists because `S_0` extends to a maximal stabilizer group. This
covers `k = 0`.

Otherwise let `psi` minimize `F` over unit vectors in the range of `P_0`. Put
`K = sum_a w_a P_0 Q_a P_0` and `lambda = <psi|K|psi>`. Then `K psi = lambda psi`, and
`F(psi) = W - lambda` with `W = sum_a w_a`. Let `N` be the set of nontrivial terms. For `R in N` put
`P_R = Q_R`, `M_R = <psi|P_R|psi>`,

```text
Leak_R = sum_a w_a Re<psi|P_R Q_a (I - P_R)|psi>,      L_R = sum_a w_a (1 - r_(a,R)),
```

where `r_(a,R)` is the number `r_a` of Step 1 computed with `S_R` in place of the post-selected group.

*Case: `M_R = 0` for every `R in N`.* Then `F(psi) = sum_(a in N) w_a + sum_(Q_a = 0) w_a`. Every
stabilizer state `phi` in the range of `P_0` has `F(phi)` at most that sum, because the trivial
terms `Q_a = P_0` contribute `0` and all others at most `w_a`. Since `gamma_d >= 1`, we are done.

*Case: some `R in N` has `M_R > 0`.*

(a) **Leak identity.** Fix `R in N` with `M_R > 0`, put `P = P_R` and `psi_1 = P psi/sqrt(M_R)`. Since
`P <= P_0`, `P_0 psi = psi` and `K psi = lambda psi`, we get `<psi|P K|psi> = lambda M_R`, and
`(P_0 - P) psi = (I - P) psi`. So

```text
lambda - <psi_1|K|psi_1> = <psi|P K (P_0 - P)|psi>/M_R = Leak_R / M_R.                   (3)
```

The left side is real, so taking real parts termwise is legitimate.

(b) **Averaging.** We claim

```text
sum_(R in N) w_R Leak_R  <=  kappa_d sum_(R in N) w_R M_R L_R.                              (4)
```

Expand the left side as `sum_(R in N) sum_a w_R w_a ell(R,a)`, with
`ell(R,a) = Re<psi|Q_R Q_a (I - Q_R)|psi>`.
- If `a = R`, `ell = 0`.
- If `a` is trivial, `Q_a in {0, P_0}` commutes with `Q_R <= P_0`, so `ell = 0`. The right side of (4)
  contains `w_R w_a M_R (1 - r_(a,R)) = 0` for these pairs.
- For `R != a` both in `N`, group the ordered pairs `(R,a)` and `(a,R)`.
  - If `S_a` and `S_R` commute, `Q_a` and `Q_R` commute, so both `ell` vanish, and
    `r_(a,R) = r_(R,a) = 1`.
  - If `Q_R Q_a Q_R = 0`, then `Q_a Q_R = 0`, so both `ell` vanish, and the right side has the
    nonnegative terms `w_R w_a M_R (1 - r_(a,R))` and `w_a w_R M_a (1 - r_(R,a))`.
  - Otherwise, by (1), `Q_R Q_a Q_R = r Q''` with `Q'' != 0` a projector and `r = r_(a,R) < 1`. The
    Lemma applies to `(P, Q) = (Q_R, Q_a)`, and its proof shows `Q_a Q_R Q_a` has the same nonzero
    spectrum `{r}`. By (1) applied with the roles exchanged, `Q_a Q_R Q_a = r_(R,a) Q'''`, so
    `r_(R,a) = r`. By the Corollary and (F0),
    `ell(R,a) + ell(a,R) <= (sqrt r - r)(M_R + M_a) <= kappa_d [(1 - r_(a,R)) M_R + (1 - r_(R,a)) M_a]`.
  Multiply by `w_R w_a` and sum over unordered pairs. This gives (4).

(c) **Choice of `R`.** If `M_R = 0` then `P_R psi = 0`, so `Leak_R = 0` and `M_R L_R = 0`: such `R`
contribute nothing to either side of (4). So (4) reads
`sum_(R in N, M_R > 0) w_R (Leak_R - kappa_d M_R L_R) <= 0`, and the sum is over a nonempty set with
`w_R > 0`. Some `R in N` with `M_R > 0` has

```text
Leak_R  <=  kappa_d M_R L_R.                                                               (5)
```

Post-select on this `R`. Put `P = Q_R`. `S_R` properly contains `S_0` because `R` is nontrivial, so
`rank P < rank P_0`.

(d) **Reduction.** The *reduced instance on `P`* is `(w_a r_a, Q''_a)`, where `r_a = r_(a,R)` and
`Q''_a` come from (1). Terms with `Q''_a = 0` are kept with `Q'' = 0`. Its frustration `F''`
satisfies, for unit `v` in the range of `P`,

```text
F(v) = L + F''(v),      L := L_R = sum_a w_a (1 - r_a),                                    (6)
```

because `<v|Q_a|v> = <v|PQ_aP|v> = r_a <v|Q''_a|v>`. By (3), (5) and `F = W - <K>` on the range of
`P_0`, we get `F(psi_1) - F(psi) = Leak_R/M_R <= kappa_d L`.

(e) **Induction.** The reduced instance lives on `P`, of smaller rank, and it is an instance in the
sense above: each `Q''_a` is `0` or the projector of a group containing `S_R`. (Terms with
`w_a r_a = 0` do not occur, since `r_a > 0` whenever `Q_a != 0`.) So some stabilizer state `phi` in the
range of `P`, hence of `P_0`, has `F''(phi) <= gamma_d F''(psi_1)`. By (6),

```text
F(phi) = L + F''(phi) <= L + gamma_d (F(psi_1) - L) <= L + gamma_d (F(psi) + kappa_d L - L)
       = gamma_d F(psi) + (1 - gamma_d (1 - kappa_d)) L = gamma_d F(psi).
```

QED.

## Sharpness

On one qudit, `H = (I - |0><0|) + (I - |+><+|)` with `|+> = d^(-1/2) sum_j |j>`. The two rank-one
projectors have overlap `1/d`, so `lambda_min(H) = 1 - 1/sqrt d`. A stabilizer state in the `Z` or
`X` basis gives `1 - 1/d` at best, attained at `|0>` and `|+>`. Every other stabilizer state is
unbiased to both bases and gives `2 - 2/d`. The ratio is `(1 - 1/d)/(1 - 1/sqrt d) = 1 + 1/sqrt d`.
On `n` qudits, let `H` act on the first qudit. `lambda_min` is unchanged. The reduced state of an
`n`-qudit stabilizer state on one qudit is a uniform mixture over a one-qudit stabilizer code
space, hence a convex combination of one-qudit stabilizer states, so its energy is still at least
`1 - 1/d`. The ratio stays `1 + 1/sqrt d` for every `n`. So `gamma_d` is optimal for every
prime `d` and every `n >= 1`.

In the proof, equality needs (F0) tight at `r = 1/d` and every block vector along `|p> + |q>` in (2).
That is the example.

## Remarks

- For `d = 2` this gives the qubit factor `1 + 1/sqrt 2` for code-space Hamiltonians, the same value
  as the Pauli-sum proof in `stabilizer-rounding-constant-is-one-over-sqrt2-proof`, by a different
  argument. That agreement is a calibration check.
- The rounding is effective. Each step computes the top eigenvector in the current code space and
  picks any `R` satisfying (5); the averaging shows one exists. There are at most `n` steps.
- Only three facts about code projectors are used: the compression rule (1), the constant principal
  angle within each pair, and the values `r in {d^(-k)}`. The same proof gives factor
  `1/(1 - sup_r sqrt r/(1 + sqrt r))` for any family of projectors that is closed under compression
  and whose pairwise compressions are multiples of projectors with `r <= r_max`.
- The NP consequence is as in `qudit-code-rounding-factor-one-plus-inv-sqrt-d-proof`: the problem is
  in NP when `b > (1 + 1/sqrt d) a`, now for every prime `d`.

## Numerical cross-check (not used in the proof)

`experiments/qudit-code-rounding-symmetric-averaging-2026-09-17/cc_symmetric_check.py` checks (2) on
every pair of code projectors (all pairs for `n = 1` and `d = 2, n = 2`; 16300 of the
480-projector pairs for `d = 3, n = 2`). The largest eigenvalue found is `3e-16`. It also runs this
rounding on random instances. The averaged inequality (4) never exceeds `5e-15`, and the worst ratio
is exactly `gamma_d`: `1.707107` (`d = 2`, `n = 1, 2`), `1.577350` (`d = 3`, `n = 1, 2`), `1.447214`
(`d = 5`, `n = 1`).
