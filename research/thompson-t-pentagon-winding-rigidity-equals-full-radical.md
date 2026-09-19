---
rg: 2
id: thompson-t-pentagon-winding-rigidity-equals-full-radical
kind: claim
title: "Pentagon-winding rigidity for T is equivalent to T not MF: the twisted spectrum of the lifted relations is a subgroup of the circle, T MF fills it through the rotation centralizers, and a small-angle twist rescales to an exact pair with nonzero pentagon winding"
distinct_from:
  thompson-t-pentagon-winding-rigidity: that states (PW) and records it as a strictly weaker necessary condition for T not MF; this proves that (PW) is equivalent to T not MF, so it is not weaker.
  thompson-t-pentagon-winding-sandwich: that proves T not MF => (PW) => T not QD; this closes the loop (PW) => T not MF, so both arrows of the sandwich become equivalences or trivialities.
  thompson-t-has-full-mf-radical: that is the target statement itself; this is a proved equivalence of it with (PW) and with one-point twisted-spectrum statements. It does not decide the target.
  central-eigencorners-die-over-full-radical-quotients: that assumes an exact eigencorner and shows it is fixed; this produces exact eigencorners of the rotation r_k from any corona representation of T, and uses item 1 there only for the "Lambda = {1}" half of the dichotomy.
  lifted-thompson-t-mf-radical-dichotomy: that is about the radical of T-bar with z unrestricted; this is about corona representations of T-bar in which z acts by a fixed scalar, and the rescaling to exact Z/4 * Z/3 pairs.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that characterises T not MF by triviality of small-defect exact pairs; this characterises it by the vanishing of one integer invariant, and by the absence of one twisted scalar.
artifacts:
  - experiments/thompson-t-relator-drop-2026-09-17/sl2_triangle.py
  - experiments/thompson-t-relator-drop-2026-09-17/low_index.py
  - experiments/thompson-t-relator-drop-2026-09-17/low_index_detail.py
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`thompson-t-pentagon-winding-rigidity-equals-full-radical-proof`.

## Notation

- `alpha, beta` are the Lochak--Schneps generators of `T`, of orders 4 and 3.
- `X = bab`, `J = a^2`, `W = a^2 b^2 a^2`, `r_1 = [X, JXJ^(-1)]`, `r_2 = [X, WXW^(-1)]`.
- `T̄` is the lift of `T` to `R`, and `z(x) = x + 1`. The lifts are
  `alpha-bar(x) = x + 1/4` and `beta-bar`, with `beta-bar(0) = 1/2`.
  In `T̄` these satisfy `alpha-bar^4 = beta-bar^3 = z`,
  `(beta-bar alpha-bar)^5 = z^3` and `r_1 = r_2 = 1`.
  These are the Euler numbers `e(a^4) = e(b^3) = 1`, `e((ba)^5) = 3` and `e(r_i) = 0` of the sandwich.
- For `lambda` in `S^1` and unitaries `U, V` in `U(n)`, the *twisted defect* is

  ```text
  D_lambda(U,V) = max( ||U^4 - lambda||, ||V^3 - lambda||, ||(VU)^5 - lambda^3||,
                       ||r_1(U,V) - 1||, ||r_2(U,V) - 1|| ).
  ```

- The *twisted spectrum* is `Lambda = { lambda in S^1 : inf D_lambda(U,V) = 0 }`. The infimum is over all
  `n >= 1` and all unitaries `U, V` in `U(n)`.

## Statement

1. **(Subgroup.)** `Lambda` is a closed subgroup of `S^1`.
2. **(T MF fills the twisted spectrum.)** If `T` is MF, then for every `k >= 1` the root
   `e^(2 pi i / 2^k)` lies in `Lambda`, and hence `Lambda = S^1`.
3. **(Small twist gives winding.)** Let `e^(i theta)` lie in `Lambda`, with `0 < |theta| <= pi`. Then for
   every `eta > 0` there is an exact pair `A^4 = B^3 = 1` with
   - `D(A,B) < |theta|/12 + 20 eta`, where `D` is the untwisted defect of `thompson-t-pentagon-winding-rigidity`;
   - `(BA)^5` within `6 eta` of the scalar `e^(i theta/12)`.

   If `6 eta < 2 sin(|theta|/24)`, every eigenvalue angle of `(BA)^5` lies strictly between 0 and
   `theta/6`. Then `kappa_P = (1/2 pi i) Tr log (BA)^5` is a nonzero element of `(1/12) Z` with the sign of `theta`.
4. **(Equivalence.)** The following are equivalent:
   - (PW), that is, `thompson-t-pentagon-winding-rigidity`;
   - `T` is not MF, that is, `thompson-t-has-full-mf-radical`;
   - `Lambda = {1}`;
   - `Lambda != S^1`;
   - `lambda_0` is not in `Lambda`, for one (equivalently every) fixed `lambda_0 != 1`.

   So `Lambda` is either `{1}` or `S^1`.
5. **(Concrete one-point form.)** Take `lambda_0 = -1` and replace `V` by `-V`. Then `T` is MF if and only if
   there is a sequence of unitary pairs `(U, V)` with
   - `U^4 -> -1`, `V^3 -> 1` and `(VU)^5 -> 1`;
   - `r_1(U,V) -> 1` and `r_2(U,V) -> 1`, all in norm.

   Equivalently, the centralizer `C_T(J)` of the half-turn `J = alpha^2` has a corona representation with
   `J -> -1`. This uses `lifted-thompson-t-quotients-are-rotation-centralizers` with `k = 1`, which gives
   `T̄/<z^2> ≅ C_T(J)` with `z -> J`. (That node writes the rotation by `2^(-k)` as `r_k`. It is not the
   relator `r_1`.)

## What this changes

- **(PW) is not an intermediate.** It had been recorded as "the only strictly weaker necessary condition"
  for `T` not MF. By item 4 it is equivalent to `T` not MF. The sandwich collapses to one equivalence
  plus the trivial implication "not MF implies not QD". A proof of (PW) is a proof of the flagship.
- **The class of approaches it kills.** Call a conjugation-invariant function `I` of `(BA)^5`
  *arc-detecting* if `I(M) != I(1)` whenever `M` is a unitary, of any size `n >= 1`, whose whole spectrum lies
  in an open arc `(0, t)` or `(-t, 0)` with `t` small. Examples:
  - `kappa_P`;
  - the number of eigenvalues in the arc `(0, phi)`;
  - any winding that is additive under direct sums and nonzero on a matrix near a nontrivial scalar
    `e^(i s) 1`.

  (A statement that `det (BA)^5` is trivial is *not* of this kind. It is not claimed here.) Every proof of
  "small-defect exact pairs have `I = I(1)`" for an arc-detecting `I` is a proof of the flagship.
  - *Named invariant:* the twisted spectrum `Lambda`, a closed subgroup of `S^1`.
  - *Death step:* item 2. `T` MF puts `e^(2 pi i/2^k)` in `Lambda`, and item 3 rescales this to exact pairs
    with `(BA)^5 ≈ e^(2 pi i/(12 2^k))`.

  Such an invariant can hold on small-defect pairs only if `T` has no MF model at all. So it cannot be a
  "cheaper" route to non-quasidiagonality.
- **Where the rescaling comes from.** The words `r_1` and `r_2` are commutators whose two arguments have
  the same exponent sums. So they do not see the scalar twist `(U, V) -> (s^3 U, s^4 V)`. The pentagon
  word sees it with weight `35 - 36 = -1` against `lambda^3`. This is the Euler number `e((ba)^5) = 3`,
  read against `e(a^4) = e(b^3) = 1`.
- **A one-point target.** Item 5 reduces `T` not MF to the absence of *one* scalar `-1` from `Lambda`, in the
  form of one projective statement about the half-turn centralizer.
  - Proving `-1 ∉ Lambda` is equivalent to the flagship.
  - Exhibiting `-1 ∈ Lambda` proves that `T` is MF.

  Item 5 does not help the torus-knot eigencorner lane, which is dead
  (`torus-knot-group-k34-has-central-eigencorners` is refuted). Here the eigencorners are *produced* from
  exact finite-order rotations, not extracted.
- **Relator-drop computations (artifacts; they change no status).**
  - `sl2_triangle.py`: no `SL_2(C)` lift of a rigid `Delta(4,3,5)` character satisfies `r_1` or `r_2`, even
    projectively. Both evaluate to non-central matrices on every lift.
  - `low_index.py` and `low_index_detail.py`: `Delta(4,3,5)/<<r_1>>` maps onto `A_5`, with `J -> 1`, and
    `Delta(4,3,5)/<<r_2>>` maps onto `A_6`. `T` has no proper subgroup of index `<= 7`.

    So each of `r_1` and `r_2` is independent of the other relators. But these witnesses are finite, so they
    carry only torsion `H_2`, and they give no non-torsion Dadarlat class that separates the relators.
