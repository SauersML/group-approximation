---
rg: 2
id: square-spiral-z2-enumeration-passes-the-finite-window-gate
kind: claim
title: The square spiral enumeration of Z^2 passes the finite-window shell gate with window two
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that excludes window width zero for every one-ended input; this exhibits a width-two witness for the one-ended input Z^2, so the ascending gate is not an obstruction for Z^2.
  shell-ascending-gate-is-a-finite-window-inclusion: that is the general criterion; this is the first witness for an input that is not virtually cyclic.
  virtually-cyclic-inputs-have-fp-shell-stabilizers: that proves all three shell stabilizer clauses for virtually cyclic inputs; this proves only the ascending gate for Z^2, and `square-spiral-z2-near-shift-group-is-not-finitely-presented` shows the other clause fails for this enumeration.
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
  - research/artifacts/hl-bh-universal-2-2026-09-13/spiral_verify.py
  - research/artifacts/hl-bh-universal-2-2026-09-13/verify.json
---

**ESTABLISHED** by `square-spiral-z2-finite-window-gate-proof` (direct proof with an exact
finite verification; not independently reviewed; no novelty claimed).

## The enumeration

`P = Z^2`, `S = {e1, e2}`. The square spiral `nu` has `nu(0,0) = 0` and then traverses ring
`r = 1, 2, ...` (the points with `max(|x|,|y|) = r`) from `(r, -r+1)` up to `(r, r)`, left to
`(-r, r)`, down to `(-r, -r)`, and right to `(r, -r)`. Its successor map
`sigma = nu^-1 s nu` is the four-piece translation

    R  = {x > |y|}               :  sigma(p) = p + e2
    T  = {y >= |x|, x + y > 0}   :  sigma(p) = p - e1
    Lf = {-x >= |y|, y > x}      :  sigma(p) = p - e2
    B  = {-y >= |x|}             :  sigma(p) = p + e1

and these four sets partition `Z^2`.

## Statement

Let `L_h` be translation by `h`. Put `delta_j(h) = L_-h sigma^j L_h sigma^-j` and
`T_k(f) = L_k f L_-k`. Composition is right to left. Then, at all but finitely many points,

    sigma^-1 L_e1 sigma = L_e1 . delta_1(-e1) . T_(-e1)(delta_1(-e1)) . T_(-2e1)(delta_1(-e1)) . delta_2(e1),
    sigma^-1 L_e2 sigma = L_e2 . T_(1,-1)(delta_1(-e2)) . T_(0,-1)(delta_1(-e2)) . T_(-1,-1)(delta_1(-e2)) . delta_2(e2).

Transported to `N` by `nu`, these say that `s^-1 lambda_g s` lies in
`W_2 = <lambda(P), s lambda(P) s^-1, s^2 lambda(P) s^-2>` for both generators. By
`shell-ascending-gate-is-a-finite-window-inclusion`, the ascending gate of
`shell-germ-fp-is-an-ascending-hnn-gate` holds for this enumeration, with `eps = 1` and
`B = W_2`. As `one-ended-shell-inputs-admit-no-shift-normalizing-enumeration` requires,
`B` is strictly larger than `lambda(P)`.

## Mechanism

Away from the four diagonals, `sigma` is a single translation and commutes with every
`L_h`. Near a diagonal, each window conjugate `sigma^j L_h sigma^-j` equals `L_h` followed
by shifts by one diagonal step along finitely many diagonal lines. The shift pattern
depends only on the line offset (`x - y` in quadrants I and III, `x + y` in II and IV):

- **Offset characters.** Conjugating by `L_k` or by `sigma` moves every line offset by a
  fixed amount. For `L_k` it is `k1 - k2` on quadrants I and III and `k1 + k2` on II and IV.
  For `sigma` it is `-1, +1` on I, III and `-1, +1` on II, IV.
- **The window corrections.** The label-`j` correction vectors (recorded in `vectors.json`
  for `j = -1, 1, 2, 3`) satisfy `Q3 = -t^j Q1` and `Q4 = -u^(j+1) Q2` as Laurent
  polynomials in the offsets.
- **Where the two identities come from.** The label `-1` vector solves the resulting
  2 x 2 Laurent systems using labels 1 and 2 only.

## Not claimed

This says nothing about finite presentation of `R_nu`, `F_nu`, `Q` or `A_1`.

DERIVATION
square-spiral-z2-finite-window-gate-proof
