# Induction without subgroup-index loss

The new claim `moving-subgroup-schreier-correction-has-no-index-loss`
removes a normalization loss from the arithmetic stability program.
The previous induction argument fixed the subgroup and absorbed its index
into constants.  The new argument permits arbitrary moving finite-index
subgroups and measures only their actual Schreier edge discrepancy.

For an exact subgroup representation on `C^d`, gauges on the cosets, and
generatorwise root-mean-square edge error `beta`, it constructs an exact
ambient representation with

```text
relative added dimension <= 4 beta^2/kappa^2,
normalized-HS generator error <= (1+10/kappa) beta.
```

Neither bound contains the subgroup index.  No normal core is taken.

The decisive calculation is to normalize the range projection of the
induction isometry by its rank `d`, even though the induced space has
dimension `[G:N]d`.  A Kazhdan projection followed by the best spectral
projection at `1/2` gives

```text
||P-Q||_HS^2 <= 4 beta^2 d/kappa^2.
```

Keeping Hilbert-space orthogonality at this cutoff avoids the larger
triangle-inequality constant.  The projection rank discrepancy is bounded
by this squared norm.  An isometry into the invariant range, padded with
trivial representations when needed, then corrects the generator tuple.

The same construction gives the explicit ucp map
`Phi(g)=avg_t V_(t') pi(n(g,t)) V_t^*`.  Its generator correlation deficit
is exactly half the measured edge energy.  This is a positive-definite
matrix-valued function because it compresses a genuine induced
representation; no positivity of an approximate group representation is
assumed.

For a finite presentation, the edge bound is `B delta+L xi`, where `B`
and `L` are root-mean-square section areas and subgroup word lengths, and
`xi` is error relative to the exact subgroup representation.  Thus the
remaining obstruction is concrete: neither exact subgroup holonomy nor
small moving section error has been constructed for arbitrary lattice
microstates.  In particular `delta->0` does not imply `B delta+L xi->0`
when the subgroup and word choices vary.

The existing fixed-index correction route now consumes this quantitative
theorem.  This is an improvement of an analytic step, not a proof of
flexible HS stability of `SL_3(Z)`, and the nonhyperlinear-group root
remains OPEN.

The [Cairn replay](moving-schreier-cairn-replay-2026-09-04.json) ran on
MSI acn116 in 0.828 seconds.  Edited-source lint and graph compilation
against the existing cache, with nineteen source overlays, reported no
errors and three existing unrelated cycle warnings.  The new quantitative
route and its fixed-index specialization compile as COMPLETE.  Both lattice
stability and the nonhyperlinear-group root remain OPEN.  This validation
is neither a full source rebuild nor a proof-kernel check of the mathematics.
