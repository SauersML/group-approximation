# STW XLVII: paper-folding refutation of the Cantor-diagonal criterion

## Primary source

Grigoris Kopsacheilis and Wilhelm Winter, *Paper-folding models for the CAR algebra*, [arXiv:2508.04837v2](https://arxiv.org/abs/2508.04837), revised 2026-07-24; published online in *Ergodic Theory and Dynamical Systems*, [doi:10.1017/etds.2026.10312](https://doi.org/10.1017/etds.2026.10312).  The arXiv comments identify v2 as the published version with minor changes.

## Exact theorem match

Theorem A, restated as Theorem 4.1, says:

```text
The CAR algebra M_(2^infinity) admits a Cantor-spectrum
C-star-diagonal which is not an AF diagonal.
```

The terminology is the same as in the Cairn root.  The paper defines a
C-star-diagonal as a Cartan pair having the unique extension property.  Its
ambient algebra is the CAR/UHF algebra `M_(2^infinity)`, hence an AF algebra.
Consequently the displayed example is exactly the negation of the universal
claim encoded by `stw99-problem-xlvii-af-cartan-criterion`.

| Cairn requirement | Source certificate |
| --- | --- |
| ambient algebra is AF | the ambient algebra is the CAR algebra `M_(2^infinity)`, a UHF algebra |
| `D` is a C-star-diagonal | Theorem A / Theorem 4.1 says C-star-diagonal; the source uses the unique-extension definition |
| spectrum of `D` is Cantor | Theorem A / Theorem 4.1 says Cantor spectrum |
| `D` is not an AF diagonal | Theorem A / Theorem 4.1 says this verbatim |
| universal XLVII claim fails | one such pair in an AF algebra is a counterexample |

The proof gives an additional internal certificate for non-AF-ness.  The
constructed pair contains an intermediate algebra with `K_1` isomorphic to
`Z`, hence non-AF, whereas every intermediate algebra over the standard AF
diagonal in the CAR algebra is AF by Archbold--Kumjian.  This separates the
new diagonal from every AF diagonal, not merely from one chosen presentation.

## Strengthening relevant to XLVIII

Theorem B, restated as Theorem 4.4, constructs for each
`n in {0,1,2,...,infinity}` a Cantor-spectrum diagonal in the CAR algebra of
diagonal dimension `n`, and explicitly concludes that these are pairwise
non-conjugate.  This is strong evidence of wildness for STW XLVIII, but it
does not establish the much stronger Cairn root asserting nonclassification
by countable structures.  That root remains open.

## Trust boundary

The imported result is a numbered theorem in arXiv v2 and the published
article, not withdrawn material.  Cairn does not reconstruct the paper-folding
subshift, crossed-product K-theory computation, or classification argument.
It uses only Theorems 4.1 and 4.4 and the standard fact that every UHF algebra
is AF.  This refutes Cairn's sharp universal encoding of XLVII; the original
STW prose asks more broadly for an intrinsic recognition criterion, so the
counterexample kills diagonality as the proposed criterion without claiming
to supply a complete replacement criterion.
