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

Mode `solve D F` computes Groebner bases over `F` for `f_1, ..., f_7` supported
in `z^-D .. z^D`, split into cases by the first nonzero coefficient of
`f_1, ..., f_6`. Runs: `D = 2` over `F_3` (calibration, where Theorem 3 with
`t = 0` must appear), and `D = 1` and `D = 2` over `Q`. They were still running
at the time of writing. This file will record their outcome.
