---
rg: 2
id: factorial-leavitt-models-have-external-corner-commutants
kind: claim
title: Canonical Leavitt models with factorial global commutant have no internal native corner commutant
distinct_from:
  native-s3-algebra-enlargement-obstructs-scalar-commutants: that gets a nonscalar, not necessarily central, element of the global commutant from a finite-observable S3 enlargement; this starts from rounding the whole native L-heat, gets a central element, and so excludes factorial global commutants, not only scalar ones.
  leavitt-channel-rounding-forces-nonhyperlinearity: that is the two-use conditional theorem from unrestricted channel rounding to nonhyperlinearity; this is its second use on its own, for an arbitrary canonical model, with factoriality instead of scalarity as the contradiction.
  at-op62-holds-for-representation-lifts: that proves Alekseev--Thom Open Problem 6.2(a) when the coordinate lifts are genuine representations; this shows 6.2(a) fails for the native corner of every canonical Leavitt model with factorial global commutant.
  native-enlargements-require-external-haar-mass: that bounds the Haar mass outside the canonical group factor for small-leakage S3 enlargements; this is about uniform rounding of the native heat and factoriality of the whole-group commutant.
---

**ESTABLISHED (written proof in two audited artifacts; not Lean-verified).**

Setting:
* `H = L_(F_2)(1,2)^x`, and `L = EL_3(R)` is the native rank-three corner
  subgroup of the rank-four cell, with native compressor `u`
  (`u L u^(-1) <= L`).
* A *canonical model* is a homomorphism `pi : H -> U(M)`,
  `M = prod_omega M_(d_n)`, with regular trace `tau o pi = delta_1`. Its lifts
  are full canonical microstates, with admissible heat times
  `t_n -> infinity`, `epsilon_n t_n -> 0`. Every hyperlinear approximation of
  `H` gives one.
* `C = pi(H)' cap M` is the global commutant, and `D = pi(L)' cap M` the native
  corner commutant.

1. **Rounding yields a central height.** Suppose the native `L`-heat maps
   `P_n = exp(-t_n A^L_n)` have unital finite-dimensional algebras
   `A_n subset M_(d_n)` with `||P_n - E_(A_n)||_(infinity->2) -> 0` along
   `omega`. Equivalently, `D = prod_omega A_n` as in Alekseev--Thom Open
   Problem 6.2(a), even allowing dimension ratios tending to one. Then `Z(C)`
   contains a self-adjoint `z` with

   ```text
   tau(z) = 0,       ||z||_op <= 1,       ||z||_2 >= 1/8.
   ```

2. **Factorial commutants force failure.** If `C` is a factor, `D` is not an
   ultraproduct of finite-dimensional coordinate algebras, even with
   `m_n/d_n -> 1`. So the restriction `pi|_L` is a negative instance of 6.2(a),
   and its native heat maps admit no uniform expectation rounding.

## Derivation

* **Heat identification.** The maps `P_n` induce `E_D` on `M`
  (`research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md`,
  Section 3, (8b)).
* **6.2(a) is uniform rounding.** `D = prod_omega A_n` holds exactly when
  `||P_n - E_(A_n)||_(infinity->2) -> 0` along `omega`. Negligible dimension
  changes are absorbed by the corner-rounding bound `25((m_n-d_n)/m_n)^(1/4)`
  (`research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md`,
  Section 5, (12)).
* **Central height.** Put `F_n = Ad(U_n) o E_(A_n) o Ad(U_n^*)`.
  * Its forward defect tends to `0` because `u L u^(-1) <= L`.
  * Its reverse defect tends to `1` because `u k_+ u^(-1) = x_14(a)` has an
    infinite `L`-orbit and canonical trace.
  * The balanced-flow median lemma then gives `z_n in Z(A_n)` with trace `0`,
    `||z_n||_2 >= 1/8` and `||[U_n, z_n]||_2 -> 0`. The limit `z` lies in
    `Z(D)` and commutes with `pi(u)`
    (`research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md`,
    Sections 1--2).
* **Native generation.**
  * `z` commutes with `pi(k_+)` and `pi(k_-)`, which integrated retention
    captures in `A_n`.
  * The commutator ledger (11) for the native swap `w`, together with
    `H = <L, w>`, puts `z` in `C`.
  * Since `z in Z(D)` and `C subset D`, `z in Z(C)` (same artifact, Sections
    3--5).
* **Conclusion 2.** In a factor `Z(C) = C1`, which contradicts `tau(z) = 0`
  with `||z||_2 >= 1/8`.

## Consequences and scope

* **Unstable branch.** Every canonical model of `H` with factorial global
  commutant is automatically a negative 6.2(a) instance for its native
  corner. Any construction of such a model has to live exactly in the
  non-internal regime, where the compressor enlarges `D` like `R` inside
  `R (x) M_2`, with no central height.
* **Stable branch.** Suppose some theorem makes every hyperlinear `H` admit a
  canonical model with factorial global commutant. Then nonhyperlinearity of
  `H` is equivalent to the absence of such models. By item 2 it would follow
  from internality of the native corner commutant in those models alone.
  The first rounding use of `leavitt-channel-rounding-forces-nonhyperlinearity`,
  component selection, would then be unnecessary.
* **That existence input is an open problem.** For `N = L(H)` it is the
  factorial commutant embedding problem in its matrix-ultraproduct form.
  * Goldbring, arXiv:2003.10004, Question 1.1: open even for property (T)
    factors. Kunnawalkam Elayavalli, arXiv:2511.20377v3, Problem 37.
  * Brown, arXiv:1010.1214, Proposition 5.2 characterizes extreme points by
    factorial commutants, but only in `R^omega`, and existence of extreme
    points is open.
  * The known case `L(SL_3(Z))` uses high-dimensional finite irreducible
    representations, which `H` does not have
    (`binary-leavitt-unit-group-is-minimally-almost-periodic`).
  * The trivial-commutant constructions for positive 1-bounded entropy do not
    apply, since Kazhdan factors are strongly 1-bounded.
  * The withdrawn Brown--Capraro preprint arXiv:1010.6033 must not be cited
    for existence.
* Neither the existence of canonical models nor hyperlinearity of `H` is
  decided here.

DERIVATION
factorial-leavitt-models-external-corner-commutant-proof
