# Lifting Promislow-group units toward characteristic zero (lane hl-kaplansky-unit-lift, 2026-09-13)

Target: `rational-unit-conjecture-torsion-free` / `integral-unit-conjecture-torsion-free`
for the Promislow group `P = <a, b | (a^2)^b = a^-2, (b^2)^a = b^-2>`,
`x = a^2`, `y = b^2`, `z = (ab)^2`. All computation ran on MSI.

## 1. Sources (fetched on MSI into `/scratch.global/sauer354/hl-kaplansky-unit-lift/src/`)

- Gardam, arXiv:2102.11818 (`units.tex`), Section 3.1: the product formula in
  `K[P]` in terms of `K[x^±, y^±, z^±]`, with conjugation acting on the right
  (`x^a = x, y^a = y^-1, z^a = z^-1`; `x^b = x^-1, y^b = y, z^b = z^-1`;
  `x^ab = x^-1, y^ab = y^-1, z^ab = z`), and Lemma 1 (piecewise symmetric units,
  inverse `p' = x^-1 p^a, q' = -x^-1 q, r' = -y^-1 r, s' = z^-1 s^a`).
- Murray, arXiv:2106.02147 (`main.tex`):
  - second theorem: two units of `F_3[P]`, with
    `p = (1+x)(1+y)(z^-1 - z)`,
    `q = (1+x)(x^-1+y^-1)(1-z^-1) + (1+y^-1)(z-z^-1)`,
    `r = (1+y^-1)(x+y)(z-1) + (1+x)(z-z^-1)`,
    `s = -z + (1+x+x^-1+y+y^-1)(z^-1-1)`,
    and the variant with `q_x, r_y`;
  - third theorem: for a prime `d` and integers `t, w`, with
    `h = (1 - z^(1-2t))^(d-2)`,
    `p = (1+x)(1+y)(z^t+z^(1-t))h`,
    `q = z^w[(1+x)(x^-1+y^-1)+(1+y^-1)(1+z^(2t-1))]h`,
    `r = z^w[(1+y^-1)(x+y)z^t+(1+x)(z^t+z^(1-t))]h`,
    `s = z^(2t-1) + (4+x+x^-1+y+y^-1)h`,
    `p + qa + rb + sab` is a nontrivial unit of `F_d[P]`. The derivation uses the
    characteristic-`d` identity `(1+f)^d = 1 + f^d`.

## 2. Mod-`d^2` lifting on the unit's own support pair

`research/artifacts/hl-kaplansky-unit-lift/lift.py` builds each unit `alpha` with
integer coefficients, forms the inverse by Gardam's Lemma 1, checks
`alpha' alpha = 1 mod d` exactly, and sets `S = supp alpha`, `T = supp alpha'`.
A unit modulo `d^2` on `(S,T)` reducing to `(alpha, alpha')` exists iff
`E = (alpha' alpha - 1)/d` lies mod `d` in the image of
`L(delta, delta') = alpha' delta + delta' alpha` (`delta` on `S`, `delta'` on `T`).
Exact ranks over `F_d` (output `lift_results.json`):

| unit | d | |S| | |T| | equations | unknowns | rank L | rank [L|E] | tangent dim | lifts mod d^2 |
|---|---|---|---|---|---|---|---|---|---|
| Gardam (F_2, calibration) | 2 | 21 | 21 | 121 | 42 | 39 | 40 | 3 | **no** |
| Murray F_3 (a) | 3 | 39 | 39 | 219 | 78 | 76 | 76 | 2 | yes |
| Murray F_3 (b) | 3 | 39 | 39 | 219 | 78 | 76 | 76 | 2 | yes |
| Murray family d=3, t=0, w=0 | 3 | 39 | 39 | 219 | 78 | 76 | 76 | 2 | yes |
| Murray family d=3, t=1, w=0 | 3 | 39 | 39 | 219 | 78 | 76 | 76 | 2 | yes |
| Murray family d=5, t=0, w=0 | 5 | 73 | 73 | 415 | 146 | 140 | 140 | 6 | yes |
| Murray family d=5, t=1, w=0 | 5 | 73 | 73 | 415 | 146 | 140 | 140 | 6 | yes |
| Murray family d=7, t=0, w=0 | 7 | 103 | 103 | 611 | 206 | 200 | 200 | 6 | yes |
| Murray family d=7, t=1, w=0 | 7 | 103 | 103 | 611 | 206 | 200 | 200 | 6 | yes |

- **Calibration:** the Gardam row reproduces main's record that Gardam's
  `F_2` unit has no lift modulo 4 on its own pair
  (`gardam-support-pair-has-no-rational-units`).
- **Reading:** Murray's odd units do lift to units modulo `d^2` on their pairs,
  so the first-order obstruction that kills Gardam's unit does not fire for
  them. The tangent space has dimension 2 (d=3) or 6 (d=5,7), more than the
  one-dimensional scaling orbit, so these `F_d`-points are not smooth isolated
  points and Newton lifting is not automatic.
- By `support-pair-unit-scheme-is-finite-over-z`, the normalized unit scheme on
  a pair is finite over `Z`. So a mod-`d^2` lift does not by itself give a
  `Z_d`-point. The decisive test is the Groebner classification of Section 3.

## 3. Groebner classification of the Murray `F_3` support pairs (Slurm, Sage 10.7)

`pairgb.py` (in `/scratch.global/sauer354/hl-kaplansky-unit-lift/`) computes the
ideal of units on `(S,T)` with `eps(u) = 1`, its Krull dimension and vdim over
`GF(1000003)`, then saturates away every trivial unit on the pair. The Gardam
pair is the calibration: main's exact `Q` computation gives 16 nontrivial units.
Results are recorded below when the job returns.

## 4. Completed group rings (where lifting "always works")

If `A` is `p`-adically complete, every element whose image in `A/pA` is a unit is
a unit. The `p`-adic completion `Z_p<P>` of `Z_p[P]` (coefficients tending to `0`
`p`-adically) has `Z_p<P>/p = F_p[P]`. So every unit of `F_p[P]` (Gardam's,
Murray's) lifts to a unit of `Z_p<P>`, but the inverse and the lift have
infinite support in general. The unit conjecture over `Q_p` asks for a lift
with finite support. That is exactly the support-pair question of Sections 2–3.

## 5. Transfer between characteristics

`bounded-support-char-p-units-force-qbar-units` (Nullstellensatz plus reduction
of algebraic integers): nontrivial units on a fixed pair occur in finitely many
characteristics or in almost all, and almost all exactly when `Qbar` carries
one. Units over `Q` on a pair force `F_p`-units on that pair for almost all `p`.
Murray's supports grow with `d` (39, 73, 103), so the family as a whole gives
no characteristic-zero unit through this principle.
