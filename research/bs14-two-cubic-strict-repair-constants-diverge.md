---
rg: 2
id: bs14-two-cubic-strict-repair-constants-diverge
kind: claim
title: Strict BS14 relative repair constants diverge already on the two cubic residuals
distinct_from:
  even-weil-fixed-line-compression: that constructs the rank-one compressed packets and proves strict separation; this extracts the quantitative lower bound on every strict relative repair modulus while holding the entire dihedral BS interface exact.
  sl2-half-explicit-strict-flexible-separation: that states global strict instability of the arithmetic group; this localizes the divergence to the two cubic equations over an exact BS(1,4) core.
  direct-sum-weil-compressions-have-quadratic-padding: that calibrates flexible missing-dimension density; this rules out strict orbitwise spectral matching and quantifies its level dependence.
---

For every prime `p=1 mod 4`, let

```text
d_p=(p-1)/2
```

and let `(X_p,R_p,S_p)` be the compressed even-Weil tuple from
`even-weil-fixed-line-compression`.  Define the **two-cubic defect**

```text
eta_p=max(||(X_p S_p^2)^3-1||_2,
          ||(X_p R_p S_p)^3-1||_2),                    (TCD1)
```

and its distance from the exact same-dimensional extension variety

```text
D_p=inf_(exact (Y,A,B) in U(d_p)^3)
       max(||X_p-Y||_2,||R_p-A||_2,||S_p-B||_2).       (TCD2)
```

There are universal constants `C,c>0` such that

```text
eta_p <= C/sqrt(p),       D_p >= c.                    (TCD3)
```

The important strengthening of the usual strict-instability statement is
that every other relative equation is exact:

```text
R_p S_p R_p^(-1)=S_p^4,
X_p^2=1,
X_p R_p X_p=R_p^(-1).                                  (TCD4)
```

Thus no error from core exactification, involution rounding, inverse-spectrum
matching, or return-phase pairing is available to charge.  The obstruction
is carried entirely by the simultaneous pair of cubic constraints.

Consequently there is no dimension-independent strict modulus
`f(t)->0` which repairs `(TCD1)` over exact BS cores.  More quantitatively,
if a level-`p` orbitwise theorem had a linear estimate

```text
D_p <= L_p eta_p,                                      (TCD5)
```

then necessarily

```text
L_p >= (c/C)sqrt(p).                                   (TCD6)
```

For a Holder estimate `D_p<=L_p eta_p^theta`, `theta>0`, one similarly has
`L_p >= c C^(-theta) p^(theta/2)`.  Hence exact packet classification,
finite-level compactness, or orbitwise spectral matching can only produce
constants diverging with the packet level.  They cannot be diagonalized into
the strict same-dimensional Iwahori endpoint.

Proof: `(TCD3)` and `(TCD4)` are precisely the polar-compression and
property-`(T;FD)` separation conclusions of
`even-weil-fixed-line-compression`; `(TCD6)` follows by division.  Notice
that the lower bound allows the exact comparison tuple in `(TCD2)` to move
the BS core as well.  It therefore rules out not only repair with fixed
`(R_p,S_p)` but every same-dimensional spectral rematching of the core.

This does not refute the flexible claim
`bs14-relative-involution-extension-stability`: adjoining the deleted fixed
line repairs the tuple exactly, with relative padding `Theta(1/p)`.  One
must not silently rewrite this as `Theta(eta_p^2)`: the recorded compression
proof establishes only the upper bound `eta_p<=C/sqrt(p)`.  It does not prove
the reverse bound `eta_p>=c'/sqrt(p)` for the maximum of the two particular
cubic residuals.  Rank one of the deleted excursion alone does not exclude
cancellation in those words.  Thus a genuinely sharp quadratic padding law
still needs one explicit Weil matrix-coefficient lemma showing that at least
one cubic sees the boundary mode at constant unnormalized Frobenius scale.
The only viable endpoint is a flexible global cross-packet reconciliation
theorem; a strict orbitwise theorem is impossible regardless of that missing
lower bound.

That lower bound is now established on the infinite progression
`p=5 mod 8` by
`even-weil-second-cubic-has-a-rank-six-determinant-gap`.  The second cubic
alone has determinant `-1` and residual rank at most six, hence norm at
least `2/sqrt(6d)`.  Thus the quadratic padding calibration is rigorous on
this subsequence.  `deleted-fixed-line-first-cubic-has-explicit-positive-spectrum`
supplies the determinant-neutral `p=1 mod 8` charge.  The remaining caveat is
no longer a prime residue class, but arbitrary packet mixtures not presented
in an authenticated orthogonal block decomposition.
