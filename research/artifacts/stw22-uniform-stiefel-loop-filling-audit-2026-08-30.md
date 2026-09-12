# STW XXII: uniform filling of small strong-Stiefel loops

## The new estimate

For every initial projection `p` and target corner `e` in the hyperfinite
`II_1` factor, there is one universal small-loop filling modulus, independent
of both traces.  The earlier linear claim `42 delta` has been withdrawn: the
controlled Michael theorem gives the qualitative modulus required for
`(USF_1)`, but its proof does not preserve that linear constant.

The construction is quantitative at every stage:

1. the two-projection perturbation lemma and an orientation correction
   give a pointwise implementing unitary within `13 delta` of `1`;
2. the conjugator fibres are closed, lower semicontinuous, and uniformly
   equi-`LC^0`, with the explicit principal-log modulus
   `delta_0(eta)=eta/2`;
3. Gutev's controlled one-dimensional Michael theorem converts the constant
   approximate selection `e` into an exact loop lift arbitrarily close to
   `e`; and
4. the Popa--Takesaki contraction in the whole target corner fills the lifted
   loop without increasing its `2`-norm radius.

This proves the previously isolated property `(USF_1)`.  Combined with the
weighted spectral-transfer theorem, it supplies global metric-uniform
`LC^1` for all weighted purification fibres with strict corner slack.

## Source audit

- Takesaki's two-projection lemma provides the uniform close conjugating
  unitary.
- No quotient or orbit cross-section is used.  This is essential because the
  published Andruchow--Varela proof invokes the older Popa--Takesaki quotient
  section argument, and Ozawa's strongly-stable-subalgebra repair does not
  directly cover the stabilizer with its scalar type-I summand.
- Gutev's Theorem 5.3 is the exact controlled selection result used.  Its
  proof is self-contained and traces the construction to Michael's
  *Continuous Selections II*, Theorem 4.1.
- Popa--Takesaki's hyperfinite contraction supplies the nonexpanding
  disk contraction.  The contraction estimate itself is separate from the
  quotient-section issue.

Primary sources:

- M. Takesaki, *Theory of Operator Algebras III*, Springer, 2003, Lemma
  XIV.2.1.
- S. Popa and M. Takesaki, *The topological structure of the unitary and
  automorphism groups of a factor*, Comm. Math. Phys. 155 (1993), 93--101,
  https://doi.org/10.1007/BF02100051.
- V. Gutev, *Constructing selections stepwise over skeletons of nerves of
  covers*, Serdica Math. J. 44 (2018), 137--154, Theorem 5.3,
  https://www.math.bas.bg/serdica/2018/2018-137-154.pdf.
- E. Michael, *Continuous Selections II*, Ann. of Math. (2) 64 (1956),
  562--580, Theorem 4.1,
  https://doi.org/10.2307/1969603.
- I. Farah and A. Vaccaro, *Continuous Selection of Unitaries in II_1
  Factors*, Proc. Amer. Math. Soc. 154 (2026), 1609--1622,
  https://arxiv.org/abs/2501.01272.
