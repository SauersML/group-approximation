---
rg: 2
id: spectral-cut-anchor-reset-pays-boundary-in-one-row
kind: claim
title: Resetting an anchor on its odd spectral cut pays boundary in only one row
distinct_from:
  block-adaptive-sparse-reset-is-cheap: that assumes a common reducing block and resets arbitrary coordinate sets; this resets one anchor on a possibly nonreducing cut which commutes only with that anchor.
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that changes every generator to make the cut reducing; this avoids that global correction and keeps the boundary under the complete-pair row normalization.
  localized-loewner-pays-spike-or-boundary: that charges the cut mass by localized row energy or boundary; this gives the actual one-coordinate modification fed by that dichotomy.
---

ESTABLISHED.  Let `A` be a reflection, let `p` be a projection commuting
with `A`, and define

```text
 A'=p+(1-p)A.                                            (SAR1)
```

Then `A'` is a reflection and

```text
 ||A-A'||_2^2<=4tau(p).                                 (SAR2)
```

For any reflection `B`, writing `q=1-p`,

```text
 ||[A',B]||_2
 <=||q[A,B]q||_2+2||[p,B]||_2.                          (SAR3)
```

Consequently, if `A=Q_a` is one shared coordinate and
`D(p)=L^(-1)sum_k||[p,Q_k]||_2^2`, then for every `theta>0`

```text
 (1/L)sum_k||[A',Q_k]||_2^2
 <=(1+theta)(1/L)sum_k||q[A,Q_k]q||_2^2
   +4(1+theta^(-1))D(p).                                (SAR4)
```

In the complete-pair energy this whole row has one further factor `1/L`.
Resetting all equality copies of coordinate `a` by the same formula keeps
equality exact.  Bounded face incidence and telescoping charge the induced
parity energy by `C tau(p)/L` plus the pre-existing face energy.

Apply this with `p` a spectral cut of `Y_(a,i)^2`.  Such a cut commutes
exactly with `Q_a`, so no cosine--sine correction of all `L` generators is
needed.  In the row-paid alternative of
`localized-loewner-pays-spike-or-boundary`, the reset displacement
`tau(p)/L` is charged without length loss.  The only new noncommutativity is
the boundary term `D(p)/L` in `(SAR4)`.

This is the correct greedy primitive.  It does not alone prove geometric
decay: successive nonreducing anchor resets can create new odd spectral
mass through their boundary terms.  A terminal stopping ledger must show
that the high-tail coarea charge for `D(p)/L` is not reused indefinitely.

Literal sign-mass reuse is excluded by
`odd-spectral-anchor-resets-have-monotone-sign-budget`: every positive
odd-square cut contains equal positive and negative anchor trace, and the
reset permanently deletes its negative half.  Remaining reuse can only
mean conversion of still-unused negative mass into boundary odd mass at too
many energy scales.
