---
rg: 2
id: leavitt-disjoint-cylinder-defects-strictly-submultiplicative
kind: claim
title: In fixed-point-free rank models of the binary Leavitt unit group, two-root defects on disjoint cylinders multiply strictly below independence
distinct_from:
  near-minimal-defect-models-have-multiplicative-cylinder-defects: that shows products of disjoint cylinder defects have the ranks of independent tensor factors when the defect is near its infimum; this asserts a uniform strict deficit from independence, which excludes such models.
  rank-models-of-el3-satisfy-the-two-root-identities: that is the gate itself, asking for vanishing defects; this asks only for a strict deficit in products of commuting cylinder defects, which together with the defect gap implies the gate for the binary Leavitt unit group.
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

**OPEN.** There is `theta < 1` with the following property. Let `sigma` be a nontrivial
fixed-point-free characteristic-two rank model of `R^x = L_(F_2)(1,2)^x`, and let `A`, `B` be
disjoint proper cylinders with proper union. Then

```text
rk(D_A D_B)  <=  theta · rk(D_A) · rk(D_B) .
```

**Payoff** (route `leavitt-rank-triviality-via-strict-defect-submultiplicativity`).
* Proposition 4.1 of the artifact gives `rk(D_A D_B) >= delta^2/(1+eps)` for near-minimal models.
  So `eps < 1/theta - 1` is impossible, and no nontrivial fixed-point-free model exists.
* Every nontrivial model has a nontrivial fixed-point-free quotient, so every model is trivial.
* So `R^x` is not `F_2`-linear sofic.

Given the landed results the claim is equivalent to the `F_2` gate: if the gate holds there are no
such models and the statement is vacuous. What it adds is the weaker ask, a strict deficit rather
than vanishing.

## Attempts

- **Range and kernel restrictions (w4-gate-descent, 2026-09-12): borderline, so they give no
  `theta < 1`.** At near-minimal defect both restricted models have normalized defect within
  `O(eps)` of `delta`, and `rk(D_(A_1)...D_(A_k)) = delta^k + O(eps delta)`
  (`near-minimal-defect-models-have-multiplicative-cylinder-defects`).
- **Square zero: gives the wrong shape.** It gives `rk(D_A D_B) <= rk(D_A)/2`, not
  `theta rk(D_A)^2`. Since `delta <= 1/2`, it never yields `theta < 1`.
- **Independent tensor factors realize `theta = 1`.** Commuting groups acting through
  `rho_1 (x) rho_2` have `rk(D_1 (x) D_2) = rk(D_1) rk(D_2)`. A proof must show that the
  `V`-conjugate cylinder subgroups of the simple group `R^x` cannot act as independent factors.
- **Halving relation: open, and the natural input.**
  * `iota_A(x_12(1)) = (1 + S[A00]T[A100])(1 + S[A01]T[A101])`, so `N^A_12 = a + b + ab` with
    commuting square-zero `a`, `b`.
  * `D_A` expands into two child-triple defects plus cross terms on four disjoint cylinders. This
    ties depth-`j` defects to depth-`j+1` defects, which independent tensor factors need not respect.
  * No bound extracted yet (artifact Section 5).
- **Halving relation: locally finite data, so it cannot give `theta < 1` (w4-r4-orth, 2026-09-12;
  artifact `research/artifacts/rank-four-orthogonality-check-2026-09-12.md`, Section 5).**
  * **Prepend form.** `iota_A(Delta(g)) = iota_(A0)(g) iota_(A1)(g)` with
    `Delta(r) = s_0 r t_0 + s_1 r t_1`. A dyadic permutation `u` in `V` carries
    `Delta(x_ab(1))` back to `x_ab(1)`. So the defect of the diagonal `D_8` inside
    `<X_0,Y_0> x <X_1,Y_1>` has rank `delta`, as do both child defects, and the child product has
    rank `f(2)`.
  * **Why it dies.** All of these relations, the swap `iota_A(w)` included, live in the locally finite
    group `L x| <iota_A(w)>`, with `L = iota_(A0)(UT_3(R)) x iota_(A1)(UT_3(R))`. Its regular rank
    model (Theorem G) satisfies them together with the rank equalities, and there
    `delta = 3/8` and `f(2) = delta^2`, so `theta = 1`.
  * **Free-type mixtures.** On mixtures of trivial and free factor modules, halving forces
    `f(2) = (3/8) delta` and `f(2)/delta^2 = 1/b >= 1`. That is supermultiplicative unless the profile
    is fully free.
  * **Still untested:** opposite roots at a child cylinder, the compressors, the nine-leaf
    configuration, and the block root groups of `GL_2(R)` normalized by the torus
    `iota_0(R^x) x iota_1(R^x)`.
