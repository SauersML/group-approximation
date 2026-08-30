# STW XXII: diffuse two-sphere supercarrier audit

## Result

The degree-one diffuse Stiefel modulus bootstraps to a factor-uniform
degree-two modulus. For an `L^2`-continuous sphere `x:S^2->Nq` with
`sup||x||_2<=delta`, the inclusive high spectral projection

```text
h_z=1_[kappa,infinity)(|x(z)|)
```

has trace at most `delta^2/kappa^2`. Michael selection enlarges it
continuously to a constant-trace superprojection of trace at most twice
that number. The complement has operator residual at most `kappa`.

## Spectral-crossing check

At a base value `e_0>=h_0`, separate
`1_[0,kappa-theta](|x_0|)` from
`1_[kappa,infinity)(|x_z|)`. The Hilbert--Schmidt Sylvester estimate
controls their overlap by
`theta^(-1)|||x_z|-|x_0|||_2`. The remaining band
`(kappa-theta,kappa)` has trace tending to zero. The cutoff is inclusive,
so an atom at `kappa` already lies under `e_0`. A polar-completion
argument, including the polar-range distance estimate, then produces a
trace-preserving superprojection converging to `e_0`. This verifies lower
semicontinuity with no continuity assumption on either the hard spectral
projection or its trace.

## Topological check

The superprojection values are fixed-trace projection Grassmannians in
diffuse corners. Small projection loops lift, by controlled Michael
selection, to small unitary loops; the established diffuse Stiefel loop
modulus fills the lifts. Arbitrary loops lift by Farah--Vaccaro and contract
by Jekel. Hence the values are simply connected and equi-`LC^1`, exactly
the hypotheses for Michael selection over `S^2`.

After spectral localization, the frame differs from its centre only on the
selected carrier. Two Michael selections lift the carrier and its partial
isometry to unitary spheres in diffuse corners. Jekel may move those
unitaries without quantitative control: every projected frame throughout
the contraction still differs from the centre on the same carrier trace.
That trace supplies the uniform radius.

## Scope boundary

This proof uses that every nonzero stabilizer corner is a II1 factor, so
Jekel kills its fundamental group. Matrix stabilizers have a different
`pi_1` obstruction and are not covered. No statement about matrices,
finite direct sums, or all finite factors is inferred.

Primary sources checked: Farah--Vaccaro, Proc. Amer. Math. Soc. 154 (2026),
Theorem 1.1 and Claims 3.1--3.2; Jekel, Math. Ann. 393 (2025), Theorem A;
Michael, Ann. of Math. 64 (1956), Theorem 1.2; Gutev, Serdica Math. J. 44
(2018), Theorem 5.3; Takesaki, *Theory of Operator Algebras III*,
Lemmas XIV.2.1--2.
