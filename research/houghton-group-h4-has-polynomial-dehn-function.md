---
rg: 2
id: houghton-group-h4-has-polynomial-dehn-function
kind: claim
title: "Houghton's group H_4 has a polynomially bounded Dehn function"
distinct_from:
  houghton-groups-with-five-or-more-rays-have-polynomial-dehn: that proves the bound for n >= 5 using a fifth ray to route pours; this is the four-ray case, where every pour route lies inside the four rays of the pours being compared.
  houghton-groups-have-polynomial-dehn-function: that is the statement for every n >= 3; this is the single case n = 4.
---

There is an integer `d` with `δ_(H_4)(x) ≼ x^d`.

## Attempts

- 2026-09-18 (swarm-0917-w8-w8-z-break). The pour method of
  `research/artifacts/zp-houghton-five-rays-2026-09-17.md` fails here, by §5
  there. The route-change quantity `W(m)` is still defined, but a splitting of it
  must move a correction pour `E_(d,c)(m_1)` past a pour word for `E_(a,b)(m_2)`
  routed via `c` or `d`. Every half-pour of such a word moves ray `c` or `d`, so it
  does not commute with the correction pour even as a permutation. A four-ray proof
  needs a genuine filling of the skew square `λ_ac^m λ_cb^m λ_bd^m λ_da^m`. The
  other steps of the six-ray note need at most four rays, so polynomial `W` for
  `n = 4` would suffice.
- 2026-09-18 (swarm-0917-w9-w9-z-follow, reframing). This is reduced to `H_3`, so
  it is no longer an independent hole. Proof in
  `research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`.
  - Both `E^c_(a,b)(m)` and `E^d_(a,b)(m)` equal the two-ray word
    `N = λ_ab^m ρ_b(m)`, of length `<= m^3`, in the letters `λ_ab, λ_ba, τ_b`.
    This is machine-checked.
  - So the skew square splits as `(E^c N^(-1))(N (E^d)^(-1))`: one word in the
    stabilizer `S_d ≅ H_3` of ray `d`, and one in `S_c ≅ H_3`. This gives
    `W_4(m) <= 2K(2m^3 + δ_(H_3)(2Cm^3))`
    (`houghton-four-ray-pour-route-change-bounded-by-h3-dehn`, established).
  - Hence `δ_(H_3) ≼ x^d` implies `δ_(H_4) ≼ x^(6+3d)`
    (route `houghton-h4-polynomial-dehn-via-h3-ray-stabilizers`). It suffices that
    the single family `A_3(m) = Area_(H_3)(E^c N^(-1))` is polynomial.
  - This node stays OPEN because `H_3` is OPEN. A superpolynomial `δ_(H_4)` would
    force a superpolynomial `δ_(H_3)`.
  - The trick cannot be pushed down to `H_3`: two-ray stabilizers `FSym ⋊ Z` are
    not finitely presented.
