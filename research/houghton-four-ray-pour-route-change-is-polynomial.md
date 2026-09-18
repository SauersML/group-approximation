---
rg: 2
id: houghton-four-ray-pour-route-change-is-polynomial
kind: claim
title: "In H_4, changing the route ray of a pour of size m costs polynomial area"
artifacts:
  - research/artifacts/zp-houghton-pour-doubling-2026-09-18.md
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.py
  - experiments/houghton-three-ray-pours-2026-09-17/verify_pour_doubling.out
distinct_from:
  houghton-four-ray-pour-route-change-bounded-by-h3-dehn: that bounds W_4 by the Dehn function of H_3, and so is conditional as a polynomial bound; this is an unconditional polynomial bound on W_4.
  houghton-five-ray-pour-route-change-is-polynomial: that bounds W by m^(log_2 5) for n >= 5 using a fifth auxiliary ray; this is the four-ray case, with no auxiliary ray and an inexplicit exponent.
---

Let `n = 4` and work in the finite presentation `P` of `H_4` from
`research/artifacts/zp-houghton-pours-2026-09-17.md` §0. With
`E^c_(a,b)(m) = λ_ac^m λ_cb^m`, put

```text
W_4(m) = max { Area_P( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : {a,b,c,d} = {1,2,3,4} }.
```

There are constants `C_4` and `β` with `W_4(m) <= C_4 m^β` for all `m >= 1`.
