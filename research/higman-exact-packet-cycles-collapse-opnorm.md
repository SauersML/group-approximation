---
rg: 2
id: higman-exact-packet-cycles-collapse-opnorm
kind: claim
title: Cycles of four exact BS(1,2) packets with operator-norm small seams collapse to the identity
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that is the marked collapse for arbitrary approximate Higman tuples; this restricts it to tuples whose four relations hold exactly on consecutive occurrence pairs, and is equivalent to it given trivially padded BS(1,2) correction.
  three-higman-bs-seams-vanish-fourth-is-product-holonomy: that scalarizes the fourth seam for independently gauged copies of one packet in normalized HS; this quantifies over all exact packet cycles in operator norm.
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that is the normalized-HS reduction to such cycles; this is the operator-norm collapse statement for them.
---

**OPEN.**  `(CGC)`: for every `epsilon>0` there is `eta>0` such that for all
`M` and unitaries `C_i, Z_(i+1)` in `U(M)`, `i in Z/4`, with

```text
C_i Z_(i+1) C_i^* = Z_(i+1)^2,     ||Z_(i+1)-C_(i+1)|| <= eta,
```

one has `max_i ||C_i-1|| <= epsilon`.

By `higman-seam-gate-needs-only-padded-bs-correction` (items 1--2), the
marked Higman collapse `(HMF5)` implies `(CGC)`, and `(CGC)` together with
`bs12-trivially-padded-opnorm-correction` implies `(HMF5)`.  Every exact
packet has the normal form of
`three-higman-bs-seams-vanish-fourth-is-product-holonomy`: squaring orbits of
odd-order roots of unity, with the conjugator a cyclic shift with `U(k)`
wrap monodromy.  So `(CGC)` is a statement about four such normal forms with
small operator-norm occurrence seams.  The calibrations recorded on
`higman-four-cycle-intrinsic-mf-seed` apply verbatim: one small generator
collapses the cycle, the periodic clocks leave a fourth-return holonomy, and
numerical searches show no countermodel.

In the exact limit, item 3 of that claim shows that seams equal to `0` force
every `C_i=1`.

## Attempts

Recorded when the claim was created on 2026-09-18 (reframing).  This is a
partial result, not a proof.

- *Quantitative smallest-prime chain (works only for bounded orders).*  Let
  `o_i` be the order of `Z_i`.  It is finite and odd, by the spectral argument
  of item 3 applied to the exact packet `(C_(i-1),Z_i)`.  The seam gives
  `||C_i-Z_i|| <= eta`, so `||C_i^(o_i)-1|| <= o_i eta`.  The packet relation
  gives `C_i^(o_i) Z_(i+1) C_i^(-o_i) = Z_(i+1)^(2^(o_i))`, hence
  `||Z_(i+1)^(2^(o_i)) - Z_(i+1)|| <= 2 o_i eta`.  Both sides are functions of
  `Z_(i+1)`, whose eigenvalues are `o_(i+1)`-th roots of unity.  Distinct such
  roots are at distance `>= 2 sin(pi/o_(i+1)) >= 4/o_(i+1)`.  So if
  `o_i o_(i+1) eta < 2`, then `Z_(i+1)^(2^(o_i)) = Z_(i+1)` exactly, and
  `o_(i+1) | 2^(o_i)-1`.  If this holds for all four `i`, the prime chain of
  item 3 forces every `o_i=1`.  Then every `Z_i=1` and every `||C_i-1|| <= eta`.
  So `(CGC)` holds for all cycles with `max_i o_i o_(i+1) < 2/eta`.
- *Where it dies.*  The bound degrades with the order.  A dimension-uniform
  statement must handle fine clocks with `o_i >= eta^(-1/2)`, whose odd-order
  spectra are `eta`-dense in the circle.  There the error `o_i eta` of the
  approximate order `C_i^(o_i)` is not small, and divisibility is lost.  This is
  the operator-norm regime of the fourth-return holonomy calibration on
  `higman-four-cycle-intrinsic-mf-seed`.  Any proof of `(CGC)` needs an
  invariant that survives spectra with unbounded orders, not the exact order
  arithmetic.
