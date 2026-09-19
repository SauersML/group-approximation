# Matrix-order rigidity kills the localized compressor pair

Date: 2026-08-11

## 1. Outcome

The coefficient-mismatched inclusion used in
`FALSE_LOCALIZED_BS_PAIRED_SURVIVOR.md` is **not** infranormal.  More
generally, conjugating the full elementary group of a polynomial matrix
order into itself already forces equality of the underlying matrix order.
Over `Z[x]`, every such compressor is an ordinary polynomial change of
basis and therefore normalizes the elementary subgroup.

Let

`S=Z[x]`, `K=Q(x)`, `T=Z[1/q][x^(+-1)]`,                 `(MON1)`

where `q>=2`, and fix `r>=3`.  Put

`Gamma=E_r(S) < E=E_r(T)`.                              `(MON2)`

Recall that the compression semigroup is

`Comp_E(Gamma)={g in E : g Gamma g^(-1) <= Gamma}`.      `(MON3)`

We prove

`Comp_E(Gamma) <= N_E(Gamma)`.                          `(MON4)`

Since the normalizer is proper, the compression semigroup cannot generate
`E`.  Thus `Gamma<E` is not infranormal in the Kun--Thom sense.

This closes the remaining global gate in the localized
Baumslag--Solitar construction negatively.  The paired class there is a
valid local survivor, but that exact ambient pair cannot feed the
infranormal radical theorem.

## 2. A compressor preserves the full matrix order

Take `g in GL_r(K)` such that

`g E_r(S) g^(-1) <= E_r(S)`.                            `(MON5)`

For `i!=j`, the elementary matrix `1+e_ij` lies in `E_r(S)`.  Hence

`g(1+e_ij)g^(-1)=1+Ad_g(e_ij)`                          `(MON6)`

has entries in `S`, and therefore

`Ad_g(e_ij) in M_r(S)`.                                 `(MON7)`

For every `i`, choose `j!=i`.  Since `e_ii=e_ij e_ji`, equation `(MON7)`
also gives

`Ad_g(e_ii)=Ad_g(e_ij)Ad_g(e_ji) in M_r(S)`.            `(MON8)`

The matrix units form an `S`-basis of `M_r(S)`, so

`Ad_g(M_r(S)) <= M_r(S)`.                               `(MON9)`

Regard `Ad_g` as a linear endomorphism of the `r^2`-dimensional
`K`-vector space `M_r(K)`.  Left multiplication by `g` has determinant
`det(g)^r`, while right multiplication by `g^(-1)` has determinant
`det(g^(-1))^r`.  Consequently

`det(Ad_g)=1`.                                          `(MON10)`

By `(MON9)`, the matrix of `Ad_g` in the matrix-unit basis has entries in
`S`.  Equation `(MON10)` and the adjugate formula show that its inverse
also has entries in `S`.  Therefore `(MON9)` is equality:

`Ad_g(M_r(S))=M_r(S)`.                                  `(MON11)`

This determinant-one argument is important: a one-sided inclusion of
arbitrary lattices need not be equality, but an inner automorphism has
exactly unit determinant on the full matrix algebra.

## 3. Normalizer of the polynomial matrix order

We now prove the following elementary order-normalizer lemma.

**Lemma 1.**  If `g in GL_r(K)` satisfies `(MON11)`, then

`g=lambda u` with `lambda in K^x` and `u in GL_r(S)`.   `(MON12)`

**Proof.**  The ring `S=Z[x]` is a UFD.  For every irreducible `varpi` of
`S`, localize at the height-one prime `(varpi)`.  The local ring
`S_(varpi)` is a DVR.  Smith normal form gives

`g=P diag(varpi^(a_1),...,varpi^(a_r)) Q`,              `(MON13)`

where `P,Q in GL_r(S_(varpi))` and `a_i in Z`.  The factors `P,Q`
normalize the local matrix order.  Conjugation by the diagonal factor
sends `e_ij` to

`varpi^(a_i-a_j)e_ij`.                                  `(MON14)`

Equality of the matrix order in `(MON11)` forces both
`a_i-a_j>=0` and `a_j-a_i>=0`.  Thus

`a_1=...=a_r=:a_varpi`.                                 `(MON15)`

Only finitely many `a_varpi` are nonzero.  Since `S` is a UFD, choose
`lambda in K^x` with valuation `a_varpi` at every height-one prime.  Then
`u=lambda^(-1)g` and `u^(-1)` have nonnegative valuation entrywise at
every height-one prime.  A UFD is a Krull domain and

`S=intersection_varpi S_(varpi) inside K`.              `(MON16)`

It follows that both `u` and `u^(-1)` lie in `M_r(S)`, hence
`u in GL_r(S)`.  This proves `(MON12)`.  QED

Suppose now that `g in E_r(T)`.  Then `det(g)=1`.  From `(MON12)`,

`1=lambda^r det(u)`,                                    `(MON17)`

and `det(u)` is a unit of `S`, hence `det(u)=+-1`.  Thus `lambda^r=+-1`.
The only roots of unity in `Q(x)` are `+-1`, so `lambda=+-1`.  Therefore

`g in GL_r(S)`.                                         `(MON18)`

For `r>=3`, `E_r(S)` is normal in `GL_r(S)`.  Equations `(MON5)` and
`(MON18)` consequently imply

`g Gamma g^(-1)=Gamma`.                                 `(MON19)`

This proves `(MON4)`.

## 4. The normalizer is proper

Let

`h=e_12(x^(-1)) in E`.                                 `(MON20)`

Conjugating the polynomial elementary matrix `1+e_21` gives

`h(1+e_21)h^(-1)`
` =1+e_21+x^(-1)(e_11-e_22)-x^(-2)e_12`.               `(MON21)`

This matrix does not belong to `GL_r(S)`, hence not to `Gamma`.  Therefore

`h notin N_E(Gamma)`,                                  `(MON22)`

so `N_E(Gamma)` is a proper subgroup of `E`.

Every element of `Comp_E(Gamma)` lies in this proper normalizer by
`(MON4)`.  The subgroup generated by the compression semigroup is
therefore also contained in the normalizer and cannot equal `E`.  We have
proved:

**Theorem 2 (matrix-order compressor no-go).**

For every `q>=2` and `r>=3`,

`E_r(Z[x]) < E_r(Z[1/q][x^(+-1)])`                     `(MON23)`

is not infranormal.  In fact every compressor normalizes
`E_r(Z[x])`.

## 5. Consequences for the FALSE search

The obstruction is broader than the particular diagonal scaling used in
the localized Baumslag--Solitar subgroup.  Whenever the amalgamated group
contains **all** elementary roots of a full matrix order over a UFD, a
one-sided inner compression preserves the entire matrix order and cannot
introduce a genuinely new scalar denominator.

Hence the next host must break at least one premise of the no-go:

1. use a proper parabolic/root-semigroup subgroup rather than the full
   elementary matrix order;
2. use an endomorphism not realized by inner conjugation in the same
   matrix algebra;
3. use a nontrivial projective/invertible-ideal class over a coefficient
   ring with nonzero Picard group; or
4. transplant the paired Baumslag--Solitar cycle into an already-known
   infranormal pair without localizing the full coefficient order.

The first option threatens Kazhdan property, and the second often creates
an infinite cyclic quotient.  The third option is structurally new: the
order-normalizer argument then permits an invertible fractional ideal
instead of only a scalar principal lattice.  It is the cleanest algebraic
escape hatch exposed by the proof.
