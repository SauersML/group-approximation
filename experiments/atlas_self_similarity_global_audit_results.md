# Global boundary audit of the exact block-eight phase

Date: 2026-08-11

`atlas_self_similarity_global_audit.py` embeds eight copies of the exact
8-dimensional construction into the honest 64-dimensional $A_8$ irrep and
evaluates every one of the 234 tensor-flip failures in the complete
radius-ten collision boundary.

| statistic | value |
|---|---:|
| boundary words | 234 |
| scalar words | 14 |
| identity words | 0 |
| nonidentity scalar words | 14 |
| maximum centrality defect | 1.7375382832 |
| RMS of per-word maximum defects | 1.4149416221 |

The fourteen scalar records have boundary indices

\[
11,23,27,28,29,33,34,84,161,171,172,181,182,183.  \tag{1}
\]

This is exactly the conjugacy/inversion class $\mathcal C_{11}$ from
`FALSE_SELF_SIMILARITY_PHASE_SEED.md`. Every value is $+iI$ or $-iI$; scalar
deviations are below $3.8\cdot10^{-15}$ and full-chart centrality defects are
below $5.4\cdot10^{-15}$. Thus the exact representative phase propagates
coherently to its entire free-product conjugacy class, as it must.

No word outside `(1)` is scalar even approximately at the same scale. The
next-smallest scalar deviation is $0.99835$. In particular, none of the 178
perfect-overlap-certified zero words maps to the identity in this model. The
ten worst boundary records all have centrality defect $1.7375382832$.

This cleanly separates two statements:

1. the one-relator central phase exists exactly in honest chart marginals;
2. this particular relative alignment does not kill the known generators of
   $[P,R]$ and therefore does not factor through $P/[P,R]$.

The next finite solver should retain the exact $\mathcal C_{11}$ phase while
forcing representatives of the 24 certified-zero classes to the identity.
Failure in dimension 64 would not prove that the central class vanishes, but
the resulting incompatibility pattern can guide either multiplicity coupling
or an exact multi-chart filling proof.
