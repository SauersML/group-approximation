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
- **Weyl elements, torus units and compressors: finite-subgroup data, so no `theta < 1` (w4-sub-weyl,
  2026-09-12; artifact `research/artifacts/cylinder-commutant-independence-and-weyl-firewall-2026-09-12.md`).**
  * **Firewall** (`finite-subgroup-data-cannot-force-defect-submultiplicativity`). The regular assignment
    `rk_reg(alpha) = dim(alpha F_2[K])/|K|` on all finite-subgroup algebras of `R^x` is consistent,
    invariant under conjugation by every unit, a rank model on every locally finite subgroup, and has
    `rk(D_A) = 3/8` with exactly multiplicative disjoint defects.
  * **Covered.** Weyl elements over `F_2` (`iota_A(GL_3(F_2))`), iterated sheets `EL_3(C_n)`, prefix
    doubling (w4-r4-orth's Lemma 5.1), the swap, and torus units or compressors used as conjugators.
    This extends w4-r4-orth's Proposition 5.2 from one configuration to all finite subgroups at once.
  * **Products are pinned too** (`near-minimal-defects-are-rank-independent-of-cylinder-commutants`,
    passed by w4-vf-gate). At near-minimal defect, `rk(D_(AP) X) = delta rk(X)` up to `eps delta` for
    every `X` commuting with `sigma(iota_A(R^x))`, including the whole complementary model. So no
    commuting factor produces a deficit.
  * **What is left.** A unit of infinite order as a factor, not a conjugator (the block root groups
    `x_12(r)`, `r` in `R`, over the torus `iota_0(R^x) x iota_1(R^x)`, or the isometry-coefficient root
    elements), or a global input turned into an upper bound. At `delta = c_*` every invariant summand of
    `iota_A` carries defect exactly `c_*`, so one invariant summand with a different normalized defect
    would finish; it must be built from an infinite-order unit.
- **Opposite roots at child cylinders, the nine-leaf frame, and compressors used as conjugators: still
  `theta = 1` (w4-sub-adversary, 2026-09-12; artifact
  `research/artifacts/locally-finite-conjugation-defect-firewall-2026-09-12.md`).**
  * **Frame tree** (`leavitt-right-child-frames-generate-infinite-order-units`, item 1). One prefix
    replacement conjugates the following into `union_n GL_(2^n)(F_2)`, which is locally finite:
    * the frames at `A`, `A0`, `A10` and `A11` (roots of both signs, Weyl elements, `F_2`-torus);
    * the nine-leaf `GL_9(F_2)` at `A`;
    * every halving unit.
  * **Single conjugations** (`locally-finite-hnn-data-allow-independent-cylinder-defects`). Take a
    locally finite subgroup `L` and an HNN letter for every unit, acting on `L cap u^-1 L u`. This
    covers compressors, torus units and the `V`-conjugacies of Fact 1.2.
    * It has a fixed-point-free rank model with the free profile on the finite subgroups of `L`.
    * There `delta = 3/8` and `f(k) = (3/8)^k`.
  * **First escapes** (same claim, items 2–3). These configurations lie in no locally finite
    subgroup:
    * the frames at `A` and at the right child `A1` give `b = iota_A(w_23) iota_(A1)(w_12)` of
      infinite order, a first generator of Thompson's `F` on `A1`;
    * `x^A_12(s_0) x^A_21(1)` has infinite order, so the `GL_2(R)` block root groups with
      coefficients of nonzero degree, together with an opposite root, are not locally finite.
  * **Torus normalization.** Single conjugations by units of `iota_0(R^x) x iota_1(R^x)` are covered.
    Identities multiplying torus units, or expressing `b` through the two frames (`b = tau sigma`),
    are not.
  * **Where a `theta < 1` argument must live.** It has to use identities from the escaping
    configurations beyond single conjugation, or a global input: the defect gap through corner
    locality, globality, or compactness.
- **Halving expansion, parent form (w4-sub-halving, 2026-09-12): dies at the same locally finite group.**
  In the `iota_P` frame the halving is coefficient additivity `x_12(1) = x_12(e_0) x_12(e_1)`, so
  `D_P = (gamma zeta - 1)(alpha beta - 1)` with children in `iota_P(UT_3(R))`. For a disjoint `Q`, everything
  lies in `iota_P(UT_3(R)) x iota_Q(UT_3(R))`. Its regular model has `rk(D_P) = rk(X) = rk(Y) = 3/8`, cross
  terms of rank `1/4`, and `rk(D_P D_Q) = 9/64` (artifact
  `research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md`, Section 3, agreeing with
  `w4-r4-orth` above).
- **General form (w4-sub-halving): commutant faithfulness.**
  `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`: at near-minimal defect, the range of a
  frame-triple defect is rank-faithful, up to `eps/(1+eps)`, for every element and matrix of the commutant of
  its clopen cylinder group. So this claim is the instance `Z = D_A` of the weaker sufficient statement
  `some-commutant-element-distorts-defect-range-rank` (route
  `commutant-distortion-from-strict-defect-submultiplicativity`), which closes the gate by route
  `leavitt-rank-triviality-via-commutant-rank-distortion`.
- **Block root groups normalized by the torus (w4-sub-halving): bound, no deficit.** Disjoint transvection
  halves `a, b` satisfy `rk(a) = rk(b) = rk(a+b) = rho`, so `rk(aM + bM) + rk(Ma + Mb) <= 3 rho`
  (`disjoint-root-halves-row-plus-column-rank-at-most-three-rho`). Halves independent in rows and columns
  displace `0` or `1/2`. At near-minimal displacement their ranges overlap in rank at least
  `rho - rho^2 - eps rho`. None of this distorts a defect-range rank.
- **Opposite roots at a child cylinder (w4-sub-halving): split only.** The `S_3 = <tau(C<-C'), tau(C'<-C)>`
  central idempotent gives `rho = d_3/2 + rk(a q_3)`. With the unitriangular data these roots generate a copy of
  `R^x`, so no firewall applies, but no identity forcing a deficit was found (artifact Section 5).
- **Scope (w4-upg-audit).** The route's other inputs hold for homomorphisms into every faithful von Neumann regular rank ring of characteristic two (`leavitt-defect-descent-chain-holds-in-regular-rank-rings`), and the route's argument goes through there (`research/artifacts/rank-gate-axiom-audit-2026-09-12.md`, Consequence 3.2). So a `theta < 1` proof that avoids matrix-level steps excludes nontrivial homomorphisms into all such rings. With `sylvester-rank-functions-on-leavitt-units-are-regular` it would also decide `binary-leavitt-units-carry-nonaugmentation-rank-function` negatively.
