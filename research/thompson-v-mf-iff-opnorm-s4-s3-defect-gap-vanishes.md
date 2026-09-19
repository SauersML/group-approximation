---
rg: 2
id: thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes
kind: claim
title: Thompson's V is MF iff nontrivial irreducible unitary representations of S4 *_Z2 S3 have arbitrarily small operator-norm defect on the four long Bleak--Quick words
distinct_from:
  thompson-v-hyperlinear-iff-unitary-s4-s3-gluings-fix-long-words: that is the tracial criterion, which must pad to the regular representation and so sees the normalized 2-norm of large free gluings; this is the operator-norm criterion, where padding is only by trivial summands, the defect of a direct sum is the maximum over its summands, and the criterion therefore reduces to single irreducible representations of G0.
  thompson-v-sofic-iff-s4-s3-gluings-nearly-fix-long-words: that is the permutation (Hamming) criterion for soficity; this is the operator-norm criterion for MF, with no trace and no counting.
  mf-radical-words-have-linear-certificates: that says a word lies in the MF radical of a finitely presented group iff its operator-norm defect is linearly bounded by the relator defect over all unitary tuples; this replaces arbitrary unitary tuples by exact representations of the virtually free group G0, and replaces the linear bound by a single positive gap on nontrivial irreducibles.
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that turns ratio witnesses with vanishing size into metric models by tensor powers; this needs no amplification, because an exact representation of G0 with rho(a) != 1 already has ||rho(a) - 1|| = 2.
  thompson-v-has-no-nontrivial-fd-unitary-representation: that is the exact statement delta(rho) = 0 implies rho trivial, used here for positivity of each delta_n; this is the uniform-in-dimension question.
  mf-recognition-has-a-pi2-upper-bound: that bounds the arithmetic complexity of MF recognition for general finitely presented groups; this gives, for V, an explicit decidable matrix Pi_2 form in terms of compact real-algebraic minimisation problems.
artifacts:
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/delta_n.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/scan_n2.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/calibrate_ctrl2.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_scan_n2_V.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_V.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/log_V.txt
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/log_CTRL2.txt
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_CTRL2.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_calibrate_ctrl2_opnorm.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_calibrate_ctrl2_hswarm.json
  - experiments/thompson-v-models/rel_V.txt
---

**ESTABLISHED** by `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-proof` (written proof).

## Setting

Use the Bleak--Quick generators `a = (00 01)`, `b = (01 10 11)`, `c = (1 00)` and the four long words
`r5, ..., r8` of `thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`:

```text
G0 = S4 *_<a> S3 = < a, b, c | a^2, b^3, (ab)^4, c^2, (ac)^3 >,      V = G0 / << r5, r6, r7, r8 >>.
```

For a finite-dimensional unitary representation `rho : G0 -> U(n)` put

```text
D(rho) = max_(5 <= i <= 8) || rho(r_i) - 1 ||_op ,
delta_n = inf { D(rho) : rho : G0 -> U(n) a homomorphism with rho(a) != 1 }     (n >= 1).
```

## Statement

1. **(Each dimension is gapped.)** For every `n >= 1` the infimum `delta_n` is attained and is `> 0`.
   Also `delta_(n+1) <= delta_n`, and `delta_1 = 2`.
2. **(Irreducible form.)** For every `n`,
   `delta_n = min { D(sigma) : sigma a nontrivial irreducible unitary representation of G0, dim sigma <= n }`.
   Moreover `rho(a) != 1` holds iff `rho` is not the trivial representation.
3. **(Criterion.)** `V` is MF iff `delta_n -> 0`. Equivalently, **`V` is not MF iff there is
   `epsilon_0 > 0` such that every nontrivial irreducible finite-dimensional unitary representation
   `sigma` of `G0` satisfies `||sigma(r_i) - 1||_op >= epsilon_0` for some `i` in `{5,6,7,8}`.**
4. **(Normal form.)** Up to unitary conjugacy, every `rho` with `rho(a) = diag(1_(n-k), -1_k)` is
   `rho = rho_4 * (W rho_3 W^*)`. Here `rho_4`, `rho_3` are fixed block sums of irreducibles of `S4` and `S3`
   with `rho_4(a) = rho_3(a) = diag(1_(n-k), -1_k)`, and `W` is in `U(n-k) x U(k)`. So `delta_n` is a minimum of
   a continuous function over finitely many compact real-algebraic sets.
5. **(Arithmetic form.)** For rational `q`, the statement `delta_n < q` is decidable (Tarski--Seidenberg).
   So "V is MF" is the explicit Pi_2 sentence `forall k exists n : delta_n < 1/k`, and "V is not MF" is
   Sigma_2.

## Why it matters for `thompson-v-is-not-mf`

- **Target.** The hole `thompson-v-is-not-mf` is exactly the uniform gap in (3). It is a statement about
  **exact** representations of a virtually free group, one irreducible at a time. By (1), every fixed
  dimension is already gapped, so any proof must be uniform in the dimension, and nothing else is needed.
- **What is lost against the tracial criterion.** The HS criterion must pad models to near-regular ones
  and measure a normalized 2-norm. Here padding is only by trivial summands, and the defect of
  `rho_1 (+) rho_2` is `max(D(rho_1), D(rho_2))`. So a single low-defect irreducible summand hidden in a
  large model is already a witness, and a certificate of non-MF-ness is a lower bound on
  `D(sigma)` over irreducibles.
- **Witness shape for MF.** A disproof of the hole (`V` is MF) is a sequence of nontrivial irreducible
  representations `sigma_j` of `G0` with `D(sigma_j) -> 0`, necessarily with `dim sigma_j -> infinity`.
  Such a sequence is checkable, one matrix at a time.
- **Relation to Kazhdan blindness.** `G0` is virtually free and every finite-dimensional unitary
  representation of `G0` is a free gluing of an `S4`- and an `S3`-representation. So the uniform gap
  in (3) is a statement about a group with the Haagerup property and a huge exact representation
  variety. That is consistent with `thompson-v-has-no-rigid-compression-defect`: no Kazhdan subgroup
  of `V` enters.

## Computation (upper bounds, not certified)

`experiments/thompson-v-opnorm-defect-gap-2026-09-17/delta_n.py` minimises `D` over every multiplicity
pattern in (4) by local search, and `scan_n2.py` computes `delta_2` by a Lipschitz grid scan. The planted
control is the PSL(2,17) word set, which has exact nontrivial solutions (in dimensions 9 and 17). The
outcome, including a failed calibration of the local search, is recorded in the proof route's
"Computation" section and in `thompson-v-is-not-mf`'s Attempts.
