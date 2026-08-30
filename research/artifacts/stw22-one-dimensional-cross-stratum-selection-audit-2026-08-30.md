# STW XXII: cross-stratum weighted selection in dimension one

## New unconditional range

For a trivial hyperfinite-factor field, weighted corner embeddings exist
continuously over every compact metrizable base of covering dimension at
most one.  This removes the fixed-support hypothesis: the support trace may
jump and the support projection need not be continuous.

The key uniform estimate is the principal-logarithm contraction

```text
path radius <= endpoint distance.
```

It follows by extending the relative polar isometry of two purifications
to a corner unitary and using the principal-logarithm path.  It proves
uniform local path connectedness of all weighted purification fibres with
support trace at most `s<tau(e)`, without any support continuity.  Together
with lower semicontinuity, closed fibres, and path connectedness, Michael's
one-dimensional selection theorem produces a global weighted section.

Orthogonal fixed corners then give arbitrarily many equivalent copies of
each sufficiently small spectral cut in a fibre gap.  Hence every bounded
positive trace on every gap vanishes, and all traces on the uniform tracial
completion of `C(X) tensor U` are the expected measure integrals.

## Exact higher-dimensional hinge

For `dim(X)=d>=2`, Michael's theorem asks for equi-`LC^(d-1)`, not merely
contractibility of each individual fixed-support Stiefel space.  The
weighted estimate above supplies the `LC^0` case.  A higher-dimensional
proof must continuously fill parameterized families while their low
spectral supports change rank.  Popa--Takesaki contractibility and the
Andruchow--Varela fixed-support bundles prove the pointwise/fixed-stratum
parts, but do not by themselves give the required uniform cross-stratum
fillings.  This is the precise remaining obstruction; the audit makes no
claim beyond dimension one.

Primary sources:

- E. Michael, *Continuous Selections II*, Ann. of Math. 64 (1956), 562--580,
  https://doi.org/10.2307/1969603.
- E. Andruchow and A. Varela, *States with equivalent supports*, J. Operator
  Theory 53 (2005), 35--48,
  https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-002.pdf.
- S. Popa and M. Takesaki, *The topological structure of the unitary and
  automorphism groups of a factor*, Comm. Math. Phys. 155 (1993), 93--101,
  https://doi.org/10.1007/BF02100051.
