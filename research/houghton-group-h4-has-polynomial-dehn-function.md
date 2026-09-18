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
