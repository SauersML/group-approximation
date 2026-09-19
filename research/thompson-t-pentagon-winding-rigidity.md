---
rg: 2
id: thompson-t-pentagon-winding-rigidity
kind: claim
title: Pentagon-winding rigidity for T — exact pairs A^4 = B^3 = 1 with small defect on the Lochak--Schneps relators have Tr log (BA)^5 = 0
distinct_from:
  thompson-t-has-full-mf-radical: that is the uniform-gap statement (every small-defect exact pair is trivial); this asks only that the integer invariant 12 kappa_P vanish on small-defect pairs. It is implied by that, and it implies that T is not quasidiagonal.
  thompson-t-pentagon-winding-sandwich: that proves the two implications around this statement and the identities kappa(r_1) = 0 and e(x_0) = 1; this is the open middle term.
  exel-loring-relative-quasirep-invariant: that is a relative winding invariant of a candidate extension; this is an absolute vanishing statement for one explicit word on the representation variety of Z/4 * Z/3.
---

**OPEN.**

## Statement (PW)

There is `delta > 0` with the following property. Let `(A, B)` be unitaries in any `U(n)` with
`A^4 = B^3 = 1` and

```text
max( ||[X, JXJ] - 1||, ||[X, W X W^(-1)] - 1||, ||(BA)^5 - 1|| ) < delta,
X = BAB,  J = A^2,  W = A^2 B^2 A^2.
```

Then `Tr log((BA)^5) = 0`, using the principal branch. Equivalently, `kappa((BA)^60) = 0`.

## Position

By `thompson-t-pentagon-winding-sandwich`,

```text
thompson-t-has-full-mf-radical  ==>  (PW)  ==>  T is not a quasidiagonal group.
```

- **Refuting (PW) proves that T is MF.** A refutation is a sequence of exact pairs with defect `-> 0` and
  `12 kappa_P` a nonzero integer. It refutes `thompson-t-has-full-mf-radical`, and with it the `T`-route to
  `thompson-v-is-not-mf`.
- **Proving (PW) proves that T is not quasidiagonal.** This is weaker than the target, but it is the first
  non-approximation statement for `T` that a K-theoretic argument could reach.

## Constraints on a proof

- **It must use `r_2`.**
  - By the sandwich, item (5), the triangle group `Delta(4,3,5)` gives pairs with `(BA)^5 -> 1` and
    `kappa_P != 0`. So the order and pentagon relations alone do not force (PW).
  - By item (2), `kappa([X, JXJ]) = 0` identically, so `r_1` contributes no winding term.
  - A proof must therefore use the smallness of `r_1` or `r_2` beyond winding bookkeeping. The natural
    candidate is the `r_2`-winding `kappa(r_2)`, which lies in `Z`, together with its interaction with the
    Euler class.
- **It must be uniform in dimension.** `kappa` is locally constant only along paths inside `SU(n)`.
  Scalars `e^(2 pi i/n) 1_n` show that it is not uniformly continuous as `n` grows. The integer bound
  `|12 kappa_P| >= 1` is compatible with arbitrarily small defect.
- **Relevant homology.** Rationally, `H_2(T)` has rank 2 (Ghys--Sergiescu; not load-bearing here). The
  Euler class `x_0` accounts for one generator. A second, Godbillon--Vey type class may be carried by
  `r_2`.

## Attempts

- **2026-09-19 (swarm-0917-w16-w16-ptl-follow): node created with its sandwich. The obvious attacks
  die as follows.**
  - *Winding bookkeeping.* Write the Euler class `c_0` as a product of conjugates of the relators. For
    near-relator pairs this expresses `12 kappa_P` in terms of `kappa(r_1)` and `kappa(r_2)`. But
    `kappa(r_1) = 0` identically, and `kappa(r_2)` is an unconstrained integer, so nothing forces
    `kappa_P = 0`. The attack dies at `r_2`.
  - *Zero-winding reduction does not split the problem.* Let (Z) say that small-defect pairs with
    `kappa_P = 0` are trivial. Then (Z) alone already implies (PW): from a pair with `kappa_P = k != 0`,
    the direct sum with its conjugate has `kappa_P = 0` and is nontrivial. So "(PW) and (Z)" is a
    renaming of `thompson-t-has-full-mf-radical`, not a decomposition. (PW) is the only strictly weaker
    necessary condition that has been found.
  - *Small dimensions.* Each fixed dimension is gapped (`delta_n > 0`), so a finite-dimensional search
    can refute (PW) only through a sequence with dimension going to infinity. It cannot prove (PW).
- **2026-09-19 (swarm-0917-w19-w19-ptl-last1, reframing): (PW) is equivalent to T not MF, so it is not a
  weaker intermediate.** See `thompson-t-pentagon-winding-rigidity-equals-full-radical`, which is
  ESTABLISHED.
  - *Obstruction.* The obstructing invariant is the twisted spectrum `Lambda`. It is the set of
    `lambda in S^1` for which there are pairs with
    - `U^4 ≈ V^3 ≈ lambda` and `(VU)^5 ≈ lambda^3`;
    - `r_1, r_2 ≈ 1`.

    `Lambda` is a closed subgroup of `S^1`.
  - *Death step.* Suppose `T` is MF. From a corona model `rho`, the dilation maps
    `T̄ -> C_T(t_k)` together with the exact spectral projections of the finite-order unitary
    `rho(t_k)` put `e^(2 pi i/2^k)` in `Lambda`. So `Lambda = S^1`.
  - *Rescaling.* The rescaling `(e^(-i theta/4) U, e^(-i theta/3) V)`, rounded, leaves `r_1` and `r_2`
    unchanged, because they are commutators. It sends `(BA)^5` to about `e^(i theta/12)`. So
    `kappa_P != 0` at defect about `|theta|/12`.

  Hence (PW) implies T not MF, and the sandwich collapses. The same argument kills every "arc-detecting"
  vanishing statement for `(BA)^5`. Status of this node: still OPEN, and now equivalent to
  `thompson-t-has-full-mf-radical`.
  - *Relator-drop census (experiments/thompson-t-relator-drop-2026-09-17).* No `SL_2(C)` lift of a rigid
    `Delta(4,3,5)` character satisfies `r_1` or `r_2`. `Delta/<<r_1>>` maps onto `A_5` and `Delta/<<r_2>>`
    maps onto `A_6`. These are finite images only, so there is no non-torsion `H_2` class that separates
    `r_2`. The "must use `r_2`" constraint above is confirmed but gives no handle.

## What a computation should look for

- Low-defect exact pairs, in normal form `A = diag`, `B = Y diag Y^*`, with `12 kappa_P != 0`.
- The target value is an integer, so a candidate is certified by one high-precision evaluation.
- Planted control: drop `r_1` and `r_2` and keep only the pentagon. Pairs with `12 kappa_P != 0` then
  exist by sandwich item (5), so a search method must find them before its negative results on the
  full problem mean anything.
