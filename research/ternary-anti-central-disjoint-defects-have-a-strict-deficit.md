---
rg: 2
id: ternary-anti-central-disjoint-defects-have-a-strict-deficit
kind: claim
title: Compressing an anti-central ternary rank function along a disjoint cylinder defect lowers its two-root defect by a fixed factor
distinct_from:
  leavitt-disjoint-cylinder-defects-strictly-submultiplicative: that is the characteristic-two target comparing a product of disjoint defects with the product of their ranks, which pays off through near-minimal multiplicativity; this is the characteristic-three target in the only form the sector-limited descent supports, a strict defect drop under compression together with positivity of disjoint products.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the abstract No branch itself; this is a strict deficit statement which, with the attained gap and the descent bounds, implies it.
  ternary-disjoint-cylinder-defects-strictly-submultiplicative: that is the literal characteristic-three transcription of the binary target, whose payoff needs a port of near-minimal multiplicativity that does not exist in either scope; this is the form the established sector-limited descent supports, with a route that closes.
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

**OPEN.** There is `theta < 1` with the following property. Let `N` be an anti-central Sylvester matrix rank
function on `F_3[G]`, with `G = L_(F_3)(1,2)^x`, and let `A` and `B` be disjoint nonempty proper cylinders with
proper union. Then:
1. `N(D_A D_B) > 0`;
2. the compressed function `N'(X) = N(F_3[iota_B](X) Q_B D_A) / N(Q_B D_A)`, which is anti-central, satisfies
   `N'(D) <= theta N(D)`.

Item 1 makes the denominator positive, by the positivity item of
`ternary-cylinder-defect-products-descend-in-sign-sectors`.

**Payoff** (route `ternary-rank-kill-via-anti-central-defect-deficit`).
* A minimizer `N_0` of the gap has `N_0'(D) >= c_3 = N_0(D)`, so item 2 fails at `N_0`.
* So no anti-central function exists, and every Sylvester rank function on `F_3[G]` kills `1 - [z]`.

**What it asks.**
* **Independent factors.** In an independent tensor configuration the compressed function is a copy of the factor
  at `B`, so `theta = 1`. The target asks that compressing along a disjoint defect strictly lowers the defect,
  which independent factors never do. So a proof must use the Leavitt relations.
* **Minimizers suffice.** Since `c_3` is attained, item 2 is only needed at minimizers.

## Attempts

- **2026-09-12, `w5-c3-descent`: opened.**
  * **The literal transcription does not close.** Transcribing `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`
    to characteristic three proves nothing, because near-minimal multiplicativity does not port (Remark 3.3 of the
    artifact).
  * **This form matches what is proved.** It fits the established lower bound
    `N(D_B Q_B D_A) >= c_3 N(Q_B D_A)`.
- **Positivity (item 1): open in both scopes.** By the positivity item of the descent claim, its failure means the
  complement of `A` acts centrally on the range of `D_A`: a disjoint two-root identity for the model.
- **Firewalls to re-check.** Two characteristic-two firewalls should be checked in characteristic three before
  anyone attacks item 2:
  * halving data are locally finite, so regular models give `theta = 1` (w4-r4-orth, f25ccc5958);
  * finite-subgroup data force nothing (w4-sub-weyl).
- **Firewall already on main** (w5-c3-submult, `anti-central-sofic-data-cannot-force-defect-submultiplicativity`).
  * **What it gives.** Sofic subgroups and locally finite HNN data carry anti-central models with `rk(N_12) = 2/3`,
    which meets the Frobenius bound, `rk(D_A) = 5/9` and exactly multiplicative disjoint defects `(5/9)^k`.
  * **Consequence here.** Those profiles are independent across disjoint cylinders. So a proof of item 2 that
    consumes only such data should be expected to give `theta = 1`. The compression in item 2 has not been
    computed on that profile.
- **Toeplitz data in characteristic three (w5-sub-fock): covered, no deficit.**
  * Over `F_3` the Toeplitz pair generates a Heisenberg group of order 27. With `z` it is a finite subgroup containing
    `z`, so `anti-central-sofic-data-cannot-force-defect-submultiplicativity` covers it.
  * The generation theorem holds over `F_3` (`toeplitz-pair-and-weyl-elements-generate-jacobson-el3`). The Toeplitz
    relation is load-bearing only inside `<iota_A(EL_3(J_3)), iota_B(EL_3(J_3)), z>`, which is sofic iff `EL_3(J_3)` is.
  * The compression of item 2 on the independent anti-central profile is not computed here. Artifact
    `research/artifacts/fock-toeplitz-input-and-sofic-independence-2026-09-12.md`, Remark 3.3.
- **2026-09-12, `w6-upg-separate`: the route runs on matrix states.**
  * **What transfers.** Theorems 2.1.1 (positivity and attainment), 2.1.2, 3.1.2 and 3.1.4, and compression
    along commuting elements, hold over anti-central matrix states `A_mat`
    (`two-root-gate-lower-bounds-hold-for-matrix-states`).
  * **Consequence.** If items 1–2 hold over `A_mat`, with compression in the matrix-state sense, the route gives
    `A_mat = ∅`. Then `S_-` fails the rank condition and the swap corner is full
    (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`), with no state upgrade.
  * **Warning.** Item 2 is an upper bound, and matrix states can break upper bounds that rank functions obey
    (artifact Example 3.3). So item 2 over `A_mat` is stronger than over `A_S`, and may fail. A proof of item 2
    that uses the triangular axiom on non-idempotent values is where a mixing step would first appear.
    Artifact `research/artifacts/two-root-certificates-separate-2026-09-12.md`, Section 4.2.
- **2026-09-12, `w7-matrix-state-deficit`: this claim restates the kill claim.**
  * **Converse of the payoff.** If `A_S = ∅`, the claim holds vacuously (route
    `rank-kill-makes-ternary-strict-deficit-vacuous`). With `ternary-rank-kill-via-anti-central-defect-deficit`,
    the claim is equivalent to `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`. The Payoff's
    "item 2 fails at `N_0`" holds whenever `A_S` is nonempty.
  * **Matrix states.** The same inequality over `A_mat` is `ternary-anti-central-matrix-state-defects-have-a-strict-deficit`.
    It is equivalent to failure of the rank condition on `S_-`, which is the counterexample. When `S_-` has the
    rank condition, the `A_mat` minimizer violates it on the largest weakly finite image, through a lower bound
    and not a Jordan bound. So the warning in the previous entry is true exactly under the rank condition.
  * **Where it dies.** Any proof of item 2 at every `N` implies emptiness. In scope `A_S` that means a triangular
    certificate for `S_-` exists. In scope `A_mat` it means a minor certificate exists. Artifact
    `research/artifacts/matrix-state-deficit-item-two-2026-09-12.md`, Sections 2–4 and 7.
