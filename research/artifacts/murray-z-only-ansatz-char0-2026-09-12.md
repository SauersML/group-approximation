# Murray's z-only ansatz in characteristic 0: checks (2026-09-12)

Script: `research/artifacts/murray-z-only-ansatz-check.py`, run with Sage 10.7
(`sage -python`) on MSI, slurm job 584703 (partition `agsmall`).
Claim: `research/murray-z-only-ansatz-has-no-char0-units.md`.

## Mode `verify`

`u'u - 1` is computed in the affine model of the Promislow group (translations
`x, y, z = 2e1, 2e2, -2e3`; `a = ((1,-1,-1),(1,1,0))`, `b = ((-1,1,-1),(0,1,1))`).
The script first asserts the relators and `ba = x^-1 y z^-1 ab`. The `f_i` are
symbols `F_i`, the `f_i^*` are `G_i`, and a coefficient passing a coset
representative with third sign `-1` is mapped by `F <-> G`, `z -> z^-1`.

Output, verbatim:

```text
u'u - 1: 37 nonzero cells, 25 (coset, x^i y^j) rows  [0.1s]
ranks over Q(z): coefficients 12, Murray 12, together 12  [0.3s]
Murray's equations follow from u'u = 1: True; converse: True  [0.3s]
```

So over any field of characteristic 0, Murray's six equations (with their
`*`-images) are equivalent to `u'u = 1` for the ansatz.

Calibration. Theorem 3, `h = (1 - z^(1-2t))^(d-2)`, `f_1 = (z^t + z^(1-t)) h`,
`f_2 = z^w h`, `f_3 = z^w (1 + z^(2t-1)) h`, `f_4 = z^(w+t) h`,
`f_5 = z^w (z^t + z^(1-t)) h`, `f_6 = h`, `f_7 = z^(2t-1)`:

```text
Theorem 3 with h^(d-2), d = 3, over Finite Field of size 3, t = -1, w = 0: u'u = 1 is True
  ... all 8 cases (t in {-1,0,1,2}, w in {0,1}) True over F_3, F_5 and F_7 ...
Theorem 3 with h^(d-2), d = 3, over Rational Field, t = -1, w = 0: u'u = 1 is False
  ... all 8 cases False over Q ...
DONE
```

The positive-characteristic cases confirm the transcription of the ansatz and
of Gardam's inverse formula. The failures over `Q` are consistent with the
claim.

## Mode `solve`

Mode `solve D F` computes Groebner bases (Singular `slimgb`, 7200 s per case)
over `F` for `f_1, ..., f_7` supported in `z^-D .. z^D`. The variable `ci_j` is
the coefficient of `z^(j-D)` in `f_i`. Case `ci_j != 0` sets every earlier
coefficient of `f_1, ..., f_6` to 0 and adds `ci_j w = 1`, so the cases cover
every solution with some `f_i != 0`, `i <= 6`.

`D = 1` over `Q`, slurm job 588457, verbatim:

```text
D = 1 over Rational Field: 21 unknowns, 137 equations  [0.0s]
D = 1 over Rational Field: nonempty cases []  [4.2s]
DONE
```

Every case gives the unit ideal over `Q`. So no solution with all `f_i` in
`z^-1 .. z^1` and some `f_i != 0`, `i <= 6`, exists over any field of
characteristic 0, as the theorem says.

Calibration, `D = 1` over `F_3`, same job, verbatim except that the 32 printed
basis elements are cut to the 16 linear ones and the first four nonlinear ones:

```text
D = 1 over Finite Field of size 3: 21 unknowns, 137 equations  [0.1s]
// ** _ is no standard basis
case c1_0 != 0: nonempty, dim 0, GB size 32  [8.8s]
c7_1
c7_0
c6_2
c6_1 - c7_2
c6_0 + c7_2
c5_0 - c5_1 + c5_2
c4_2 - c5_2
c4_1 - c5_1 + c5_2
c4_0
c3_0 - c3_1 + c3_2
c2_2
c2_1 - c3_2
c2_0 - c3_1 + c3_2
c1_2 + w
c1_1
c1_0 - w
w^2 - 1
c7_2^2 - 1
c5_2*c7_2 + c3_2*w
c5_1*c7_2 + c3_1*w
...
D = 1 over Finite Field of size 3: nonempty cases [('c1_0', 32)]  [13.6s]
DONE
```

The Singular warning comes from `dim` applied to the `slimgb` output and does
not affect the result.

Theorem 3 with `d = 3`, `t = 1`, `w = 0` has `f_1 = f_3 = f_5 = z - z^-1`,
`f_2 = f_6 = 1 - z^-1`, `f_4 = z - 1` and `f_7 = z`, so `c1_0 = -1` and
`w = -1`. All 32 printed basis elements vanish at this point (checked by
hand). So the case split finds the known solutions in positive
characteristic.

`D = 2` over `F_3` and over `Q` (job 584703, 35 unknowns, 237 equations)
printed only their header lines. The job was cancelled after 49 minutes,
still on the first case. These runs are not part of the evidence.
