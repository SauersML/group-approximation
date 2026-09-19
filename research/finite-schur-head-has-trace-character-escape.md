---
rg: 2
id: finite-schur-head-has-trace-character-escape
kind: claim
title: Every finite packet-headed Toeplitz window has an inner-invariant root-character escape
---

Use the odd finite splitting field `k` and the forbidden packet algebra

```text
A_f^-=P_fk[B_f]P_f.
```

For every `N>=1`, identify the finite Toeplitz head as

```text
F_N^-=M_N(A_f^-)
```

by `schur-toeplitz-head-is-matrix-amplified-forbidden-algebra`. There is a
nontrivial additive character

```text
chi_N:(F_N^-,+)->mu_p                                      (FTE1)
```

such that:

1. `chi_N(uau^-1)=chi_N(a)` for every unit `u in (F_N^-)x`;
2. for every site defect `e_i=x^iP_fy^i`, `0<=i<N`,
   `chi_N(e_i)!=1`; and
3. in particular, all conjugation, finite-packet covariance, and Reynolds
   identities internal to the complete forbidden head are exact on this
   character while every site mark remains visible.

Hence retaining the full selector packet before reset is necessary but not
sufficient for normalized-HS root-defect collapse. No finite Schur/Reynolds
authentication which acts only by inner conjugation on `F_N^-` can force a
first-hit decomposition of the additive root characters. The required
pre-reset cell must use a transverse Steinberg multiplication row, or another
operation not annihilated by the ordinary matrix trace, and must couple that
row to the one-sided head/tail boundary.

This strengthens `toeplitz-defect-idempotents-do-not-localize-root-characters`
on every finite head: the escaping character may be chosen invariant under
the entire head unit group, not merely nonzero on all orthogonal coefficient
idempotents.

