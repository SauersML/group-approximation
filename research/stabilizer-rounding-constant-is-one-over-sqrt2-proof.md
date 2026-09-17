---
rg: 2
id: stabilizer-rounding-constant-is-one-over-sqrt2-proof
kind: route
title: Post-select the top eigenvector on its best term and induct on the number of qubits
target: stabilizer-rounding-constant-is-one-over-sqrt2
requires: []
artifacts:
  - experiments/stabilizer-rounding-constant-2026-09-17/README.md
---

Ordinary proof, unreviewed, not Lean-verified. Lane sw-078, 2026-09-17.

## Statement

For an explicit real Pauli decomposition `K = sum_P beta_P P` on `n` qubits, with
weight `W = sum_P |beta_P|` and `lambda = lambda_max(K)`,

```text
max_(phi stabilizer) <phi|K|phi>  >=  lambda - (1/sqrt2)(W - lambda).        (SR*)
```

Put `c = 1/sqrt2`, `t = c/(1+c) = sqrt2 - 1`. (SR*) says
`stab(K) >= (1+c) lambda - c W`.

## Reductions

(R1) *Identity terms.* Adding `+wI` (`w>=0`) raises `stab`, `lambda` and `W` by `w`,
so it leaves (SR*) unchanged. A term `-wI` lowers `stab` and `lambda` by `w` but
raises `W` by `w`, so it only weakens the claim. Hence we may assume there are no
identity terms.

(R2) *Repeated Paulis.* Merging all occurrences of one Pauli into a single
coefficient keeps `K`, `stab` and `lambda`, and does not increase `W`. The right
side of (SR*) is decreasing in `W`. So we may assume the Paulis are distinct.

Write `beta_P = w_P s_P`, `w_P > 0`, and `A_P = s_P P`.

## Two facts

(F1) *Anticommuting pairs.* If Hermitian involutions `A, B` anticommute, then for
every state `<A>^2 + <B>^2 <= 1`. Indeed `(aA + bB)^2 = (a^2+b^2) I`, so
`a<A> + b<B> <= sqrt(a^2+b^2)`; take `a = <A>`, `b = <B>`.

(F2) *A scalar inequality.* For `M in [0,1]`, `min{M, sqrt(1-M^2)} <= t(1+M)`.
If `M <= 1/sqrt2`: `t(1+M) - M = t - (1-t)M >= t - (1-t)/sqrt2 = 0`, because
`(1-t)/sqrt2 = (2-sqrt2)/sqrt2 = sqrt2 - 1 = t`. If `M >= 1/sqrt2`: the claim
`sqrt(1-M^2) <= t(1+M)` is equivalent to `1 - M <= t^2 (1+M)`, i.e.
`M >= (1-t^2)/(1+t^2)`. With `t = tan(pi/8)` this threshold is `cos(pi/4) = 1/sqrt2`.
Equality holds exactly at `M = 1/sqrt2`.

## Proof of (SR*)

Induction on `n`. For `n = 0` (or `K = 0`) both sides vanish. Let `n >= 1`, `K != 0`,
with distinct non-identity Paulis. Let `psi` be a top eigenvector, `K psi = lambda psi`,
and put `x_P = <psi|A_P|psi>`. Since `lambda = sum_P w_P x_P` and `lambda >= 0`
(`tr K = 0`), some term has `x_P >= 0`.

**Step 1 (choice of the post-selected term).** Let `R` maximize `x_P` over the terms,
`M = x_R >= 0`. Split the other terms into `C` (commuting with `R`) and `A`
(anticommuting with `R`), and write

```text
K = w_R A_R + K_C + K_A,   K_C = sum_(Q in C) w_Q A_Q,   K_A = sum_(Q in A) w_Q A_Q,
W_A = sum_(Q in A) w_Q,    a = <psi|K_A|psi> = sum_(Q in A) w_Q x_Q.
```

For `Q in A`, `x_Q <= M` by maximality and `x_Q <= sqrt(1-M^2)` by (F1). By (F2),

```text
a  <=  t (1+M) W_A.                                                          (1)
```

**Step 2 (energy after post-selection).** Put `Pi = (I + A_R)/2`. Then
`||Pi psi||^2 = (1+M)/2 > 0`; let `psi_1 = Pi psi / ||Pi psi||`. Let
`K_c = w_R A_R + K_C` (the part commuting with `A_R`), so `K = K_c + K_A`. Since
`A_R K_c A_R = K_c` and `A_R K_A A_R = -K_A`,

```text
(I + A_R) K (I + A_R) = K + A_R K + K A_R + A_R K A_R = 2 (I + A_R) K_c .
```

Hence `<psi_1|K|psi_1> = <psi|(I+A_R)K_c|psi> / (1+M)`. The operator `(I+A_R)K_c` is
Hermitian (a product of commuting Hermitian operators), so `<psi|A_R K_c|psi>` is
real. The operator `A_R K_A` is anti-Hermitian, so `<psi|A_R K_A|psi>` is purely
imaginary. Their sum is `<psi|A_R K|psi> = lambda M`, which is real; so
`<psi|A_R K_c|psi> = lambda M`. Also `<psi|K_c|psi> = lambda - a`. Therefore

```text
<psi_1|K|psi_1> = (lambda - a + lambda M)/(1+M) = lambda - a/(1+M).           (2)
```

**Step 3 (the smaller instance).** Choose a Clifford unitary `U` with
`U A_R U^* = Z_n`. The range of `Pi` is `U^*(C^(2^(n-1)) tensor |0>)`. For `Q in C`,
`U A_Q U^*` commutes with `Z_n`, so it equals `+-B_Q tensor I` or `+-B_Q tensor Z`
for an `(n-1)`-qubit Pauli `B_Q`. On the range of `Pi` it acts as `eps_Q B_Q` with
`eps_Q = +-1`. `B_Q = I` would force `A_Q = +-A_R`, which is excluded because the
Paulis are distinct. Define the `(n-1)`-qubit Pauli sum

```text
K' = sum_(Q in C) w_Q eps_Q B_Q ,     W' <= sum_(Q in C) w_Q = W - w_R - W_A .
```

For every `v` in the range of `Pi`, written `v = U^*(v' tensor |0>)`:
`<v|A_R|v> = 1`, `<v|K_A|v> = 0` (since `K_A` anticommutes with `A_R` and `v` is a
`+1` eigenvector), and `<v|K_C|v> = <v'|K'|v'>`. So

```text
<v|K|v> = w_R + <v'|K'|v'> .                                                 (3)
```

Applying (3) to `v = psi_1` and using (2), `lambda' := lambda_max(K') >= lambda - a/(1+M) - w_R`.
Applying (3) to `v = U^*(phi' tensor |0>)`, which is a stabilizer state whenever
`phi'` is, gives `stab(K) >= w_R + stab(K')`.

**Step 4 (induction).** By the induction hypothesis on `n-1` qubits (the hypothesis
covers repeated Paulis and the zero sum by (R2)), and since `(1+c)lambda' - cW'`
increases in `lambda'` and decreases in `W'`,

```text
stab(K) >= w_R + (1+c) lambda' - c W'
        >= w_R + (1+c)(lambda - a/(1+M) - w_R) - c (W - w_R - W_A)
         = (1+c) lambda - c W + [ c W_A - (1+c) a/(1+M) ] .
```

By (1), `(1+c) a/(1+M) <= (1+c) t W_A = c W_A`, so the bracket is nonnegative. This
proves (SR*). QED.

**Sharpness.** For `K = (X+Z)/2`: `W = 1`, `lambda = 1/sqrt2`, and every one-qubit
stabilizer state has `<X> + <Z> <= 1`, so `stab = 1/2`. Then
`lambda - stab = (1/sqrt2)(W - lambda)` exactly. So `1/sqrt2` is optimal, and (F2) is
tight exactly at this configuration (`M = 1/sqrt2`, one anticommuting partner at
the same expectation).

**Model check of the steps.** (2) is the energy of a post-selected top eigenvector.
For `K = (X+Z)/2`: `psi` has `x_X = x_Z = 1/sqrt2`, `R = X`, `a = 1/(2sqrt2)`, and
(2) gives `1/sqrt2 - (1/(2sqrt2))/(1+1/sqrt2) = 1/2`, the energy of `|+>`. The
recursion stops at `K' = 0`, and `stab >= w_R = 1/2`.

## Consequences (each replaces `2+sqrt2` by `1+1/sqrt2` in an existing proof)

The derivations are those of `research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md`
§3 and of `pauli-projector-hamiltonians-are-stabilizer-approximable-proof`, with
Theorem SR replaced by (SR*); only the constant changes.

- **Pauli projectors and code-space constraints.** For
  `H = sum_a w_a (I - Pi_a)` with stabilizer code projectors `Pi_a` (single Pauli
  projectors included), `K = sum_a w_a Pi_a` has a Pauli decomposition of weight
  `W = sum_a w_a` (identity terms allowed, by (R1)), and `H = W I - K`. So
  `min_stab <H> = W - stab(K) <= (1 + 1/sqrt2)(W - lambda_max K) = (1+1/sqrt2) lambda_min(H)`.
- **NP thresholds.** `lambda_min(H) <= a` versus `>= b` for such `H` is in NP when
  `b > (1+1/sqrt2) a`. For explicit Pauli sums, `lambda_max >= W - F_Y` versus
  `<= W - F_N` is in NP when `F_N > (1+1/sqrt2) F_Y`. With non-stabilizer terms of total
  weight `V`, the Pauli-projector problem is in NP when `V < b - (1+1/sqrt2) a`.
- **Sharpness of the witness method.** `H = (I-X)/2 + (I-Z)/2` has
  `lambda_min = 1 - 1/sqrt2` and stabilizer minimum `1/2`, ratio `1+1/sqrt2`. So
  stabilizer witnesses decide these promise problems exactly above ratio `1+1/sqrt2`
  and fail at or below it. This does not show hardness below the threshold.
- **Games window.** For the Pauli energy test of Natarajan--Nirkhe
  (`pauli-norm-games-qpcp-needs-imperfect-completeness`), inputs with promise
  `1-1/p` versus `1-1/q` are in NP once `p > (1+1/sqrt2) q`. The open window for
  their open problem 1 shrinks from `1 < p/q <= 2+sqrt2` to `1 < p/q <= 1+1/sqrt2`.
- **Bearing on the root.** Unless QMA is in NP, a QMA-hard family of
  Pauli-projector Hamiltonians with NO floor `b` has YES energy at least
  `b/(1+1/sqrt2) = (2-sqrt2) b ~ 0.586 b`. So its relative gap `(b-a)/b` is at most
  `1/(1+sqrt2) ~ 0.414`. With non-stabilizer weight `V`, the bound is
  `a >= (2-sqrt2)(b - V)`.

## Why the old proof could not reach this and this one does

The averaging proof keeps only terms with expectation above `1/sqrt2`, which commute,
and zeroes all others. Its loss per term is `x/(1-x)`, which is `1+sqrt2` at
`x = 1/sqrt2`. The new rounding post-selects one term at a time. It keeps every
commuting term alive for the next round, and the energy identity (2) charges only the
anticommuting mass `a/(1+M)`. The Clifford bound (F1) then gives (1) termwise.

## Numerical cross-checks (not used in the proof)

`experiments/stabilizer-rounding-constant-2026-09-17/README.md` records: the rounding
above run on 3000 random instances with `n <= 4` never violated (SR*) (minimum slack
`-2e-15`, i.e. tight cases occur); primal Nelder--Mead searches at `n = 1,2,3`
and the state-side dual LP at `n = 1,2,3` both peak at `0.7071068`.
