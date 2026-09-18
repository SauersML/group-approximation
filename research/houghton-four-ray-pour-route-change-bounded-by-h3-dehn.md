---
rg: 2
id: houghton-four-ray-pour-route-change-bounded-by-h3-dehn
kind: claim
title: "In H_4, changing the route ray of a pour of size m costs area at most O(m^3 + δ_(H_3)(O(m^3)))"
artifacts:
  - research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md
  - experiments/houghton-four-rays-2026-09-17/verify_two_ray_factorization.py
distinct_from:
  houghton-five-ray-pour-route-change-is-polynomial: that bounds W by m^(log_2 5) for n >= 5, splitting pours through a fifth ray; this is the four-ray case, bounded by the Dehn function of H_3 through ray stabilizers, with no auxiliary ray.
  houghton-group-h4-has-polynomial-dehn-function: that is the polynomial Dehn bound for H_4 itself; this is an unconditional comparison of the four-ray route-change area with δ_(H_3), and gives the H_4 bound only once H_3 is polynomial.
---

Let `n = 4` and work in the finite presentation `P` of `H_4` from
`research/artifacts/zp-houghton-pours-2026-09-17.md` §0. For distinct rays `a,b,c` put
`E^c_(a,b)(m) = λ_ac^m λ_cb^m`, and let

```text
W_4(m) = max { Area_P( E^c_(a,b)(m) · E^d_(a,b)(m)^(-1) ) : {a,b,c,d} = {1,2,3,4} }.
```

There are constants `K, C` (depending only on the presentations) with

```text
W_4(m) <= 2K ( 2m^3 + δ_(H_3)(2C m^3) )        for all m >= 2.
```

More sharply, `W_4(m) <= 2K(2m^3 + A_3(m))`, where `A_3(m)` is the `H_3`-area of the
single word `E^c_(a,b)(m) · N_(a,b)(m)^(-1)`, and `N_(a,b)(m) = λ_ab^m ρ_b(m)` is the
explicit two-ray word of length `<= m^3` in the letters `λ_ab, λ_ba, τ_b` given in
Lemma 1 of the artifact.

The mechanism: both `E^c` and `E^d` equal the two-ray element `N`. So the skew square
`E^c (E^d)^(-1)` is the product of `E^c N^(-1)`, a word in the stabilizer `S_d ≅ H_3`
of ray `d`, and `N (E^d)^(-1)`, a word in `S_c ≅ H_3`.
