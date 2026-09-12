---
rg: 2
id: every-high-free-root-valuation-has-a-rank-one-e5-detector
kind: claim
title: Every free-root valuation above one has a polynomial-cost rank-one E5 detector
artifacts:
  - experiments/valuation_complete_e5_rank_one_pulse.py
distinct_from:
  dyadic-e5-hard-pulses-have-disjoint-degree-bands: that gives sparse unshifted pulses with gaps inside each band; this shifts one side of the Heisenberg frame so the unique top coefficient lands at an arbitrary prescribed valuation.
  free-root-first-detection-eigenvectors-localize-exactly: that says a valuation-r eigenvector lies in the rth Fourier boundary; this supplies a fixed group-word frame which evaluates to exactly one Pauli pair on that boundary.
  conditional-parent-absence-packet-exposes-relative-pauli: that names a relative pair using a finite conditional packet but cannot switch it on the child carrier; this reads the relative hard character by its free-root valuation without a nonlinear scalar switch.
---

For every integer `r>=2`, there are explicitly constructible paired-frame
words in two commuting copies of `E_5(F_2[x])` with the following property.
Transport only the source copy by a power of the four-root word `D` and hold
the coefficient copy fixed.  If their relative additive character has
valuation exactly `r`, the evaluated relative commutator form is

```text
e_13^*,                                                     (VCD1)
```

and hence has alternating rank two: exactly one Pauli factor.

The words have length `O(r^2)`.  More explicitly, choose the unique dyadic
`n` satisfying

```text
4n-2 <= r < 8n-2                                          (VCD2)
```

and put `t=r-(4n-2)`.  In both frames replace the two `p` roots
`e_02(1),e_12(1)` by `e_02(x^t),e_12(x^t)` while keeping the `q` roots
constant.  The relative pulse becomes

```text
x^t Delta_n.                                               (VCD3)
```

It has degree `r`, and its degree-`r` coefficient is uniquely `e_13^*`.
All other coefficients have smaller degree, so a valuation-`r` character
kills them.

Thus no high-valuation relative character can hide in the polynomial gaps of
one raw pulse.  The only exceptional valuations are zero and one, a fixed
finite packet which can be charged separately.  The detector cost is
polynomial, so it is compatible with the exponentially weighted Fanizza
recurrence.
