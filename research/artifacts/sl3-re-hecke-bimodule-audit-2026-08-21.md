# SL3 RE/N Hecke-bimodule audit — 2026-08-21

## Result

The standard rigidity properties do not contradict Gao relative
embeddability for

```text
L(SL_3(Z)) subset L(SL_3(Z[1/2])).
```

The source inclusion is quasi-regular and explicitly nonmixing.  Every
dyadic group element commensurates the lattice, so its group unitary spans a
bifinite lattice-factor correspondence.  For the diagonal `h`, a weakly
null sequence inside `C cap h^-1 C h` remains norm one after conjugation by
`h`, giving an exact failure of Popa mixing.

Gao Proposition 2.2 removes the coefficient factor here: because
`N=L(SL_3(Z))` is Connes embeddable/QWEP, `RE/N` is equivalent to scalar
RE.  Thus a witness can be written

```text
M -> prod_omega A_k,       N -> D=prod_omega B_k,
```

with `A_k` finite QWEP, `B_k` hyperfinite, and a commuting square.
Distinct arithmetic double cosets then give mutually orthogonal bifinite
`N-N` correspondences in the ultraproduct target, with their exact Jones
dimensions.  The powers of `h` form an infinite orthogonal tower, satisfy
`E_D(U_(h^n))=0` for all `n!=0`, and have dimensions growing at least as
`2^(2n)`.

## Sharp remaining obstruction

The dyadic Haar unitary is not opposed to the quasi-normalizer: it is the
quasi-normalizer.  Property `(T)` is compatible with bifinite
correspondences, and co-density applies to exact finite quotients rather
than arbitrary Gao coordinates.  Thus none of these abstract invariants can
prove non-relative-embeddability.

The exact remaining theorem is coordinate-specific:

> An ultraproduct `prod A_k` with hyperfinite `B_k subset A_k` cannot
> contain, relative to `D=prod B_k`, the regular-trace arithmetic Hecke
> tower described above.

This is sharper than asking vaguely for mixing or rigidity.  A proof must
use the coordinate hyperfiniteness/QWEP structure together with the fusion
and dimension data of multiple Hecke sectors.  Crucially, the tower is
exact only after passage to the metric ultraproduct.  An exact decomposition
inside every coordinate `A_k` does not follow; obtaining a coherent lift is
the remaining theorem, not bookkeeping.  The source group factor itself
already realizes every purely tracial or correspondence-theoretic identity
of one sector.

## Placement inside Gao's general problem

The ambient factor `M` is itself QWEP: `SL_3(Z[1/2])` is a finitely
generated linear group in characteristic zero and hence residually finite.
Accordingly this scalar terminal is a concrete instance of Gao's Problem
6.1, which asks whether every inclusion into a finite QWEP algebra is
scalar relatively embeddable.  Proving the desired SL3 failure would answer
that problem negatively.  Conversely, a universal positive answer to
Gao's question would kill this arithmetic route.  This confirms that
ambient CE/QWEP alone cannot supply the missing obstruction.
