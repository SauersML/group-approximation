---
rg: 2
id: single-spike-split-or-charge-proof
kind: route
title: Compare actual coarea boundary with spike trace and balance three powers
target: single-spike-split-or-charge-has-fourth-root-modulus
requires:
  - one-anchor-odd-spike-has-a-cheap-reducing-cut
  - block-adaptive-sparse-reset-is-cheap
---

The chosen coarea threshold satisfies

```text
b<=2r/t.                                                 (SCP1)
```

In the split branch, cosine--sine block diagonalization costs at most a
universal multiple of the actual boundary `b`, hence at most `C eta m`.
The spectral projection `p` already commutes exactly with `Q_a,Q_i`, so
leave those two generators unchanged and the spectral cutoff survives.
Once every corrected generator commutes with `p`, the block-adaptive reset
estimate gives the additional `m/L` terms.

In the charge branch, `eta m<b`; combine this with `(SCP1)`:

```text
m<2r/(eta t)=2r^(1/4),
```

which is `(SSC5)`.  Equation `(OSC5)` gives
`(1-p)R(1-p)<=2t(1-p)`; functional calculus and `R=Y^2` give `(SSC6)`.

For general powers, these same three calculations give `(SSC7)`.  The
linear inequalities in the final paragraph of the claim prove the optimal
fourth-root exponent.

