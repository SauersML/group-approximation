# Fixed group-ring resolutions give uniform decoder comparisons

Date: 2026-08-11

## Purpose

`TRUE_CHAIN_COMPARISON_DECODER_TRANSFER.md` proves that integral cochain
comparisons transport harmonic carry decoders with loss equal to the product
of the two degree-map norms.  For a family of finite charts, this raises an
apparent new question: can those comparison norms grow with the chart?

For two **fixed** finite free resolutions over `Z[G]`, the answer is no.
Resolution comparison gives fixed group-ring matrices.  Every group element
acts by a permutation on every finite `G`-set, so the normalized `L2`
operator norm of each specialization is bounded by a fixed coefficient
`l1` Schur norm.

The well-rounded-retract/modular-symbol model has finite cell stabilizers and
is not integrally free.  After inverting the finite stabilizer orders it is a
fixed projective resolution, so the same uniform comparison holds there.
The only remaining comparison obstruction is therefore integral and
supported at the finitely many primes dividing those stabilizer orders.
This qualification is essential: clearing a fixed denominator does not by
itself produce an integral decoder.

## 1. Uniform norm of a group-ring matrix

Let `G` be a group and let

`a=sum_(g in G) n_g g in Z[G]`                                  `(FRI1)`

have finite support.  Put

`||a||_1=sum_g |n_g|`.                                           `(FRI2)`

For a finite `G`-set `X`, let `pi_X` be the permutation representation on
`ell^2(X)` with normalized counting norm.  Then

`||pi_X(a)||<=||a||_1`,                                          `(FRI3)`

because every `pi_X(g)` is unitary.

Now let `A=(a_ij)` be an `s x t` matrix over `Z[G]`.  Define

`R(A)=max_i sum_j ||a_ij||_1`,
`C(A)=max_j sum_i ||a_ij||_1`.                                  `(FRI4)`

**Lemma 1 (uniform Schur bound).**  On every finite `G`-set `X`,

`||pi_X(A):ell^2(X)^t->ell^2(X)^s||`
` <=sqrt(R(A) C(A)).`                                            `(FRI5)`

The same bound holds for every unitary representation of `G`.

**Proof.**  Put `b_ij=||a_ij||_1`.  Equation `(FRI3)` and the triangle
inequality reduce the block-operator estimate to the nonnegative scalar
matrix `(b_ij)`.  The ordinary Schur test bounds its `ell^2` norm by
`sqrt((max_i sum_j b_ij)(max_j sum_i b_ij))`, which is `(FRI5)`.  End proof.

The estimate is independent of `|X|`.  Normalizing the counting measure
does not change it because the same scalar rescales the source and target
copies of `ell^2(X)`.

## 2. Comparison of fixed free resolutions

Let `C_*` and `D_*` be free `Z[G]`-resolutions of `Z`, finitely generated in
degrees through `r+1`.  The comparison theorem for projective resolutions
gives chain maps

`f:C_*->D_*`, `g:D_*->C_*`                                      `(FRI6)`

lifting the identity of `Z`, and chain homotopies

`g f homotopic to id_C`, `f g homotopic to id_D`.                `(FRI7)`

In every fixed degree these maps are finite matrices over `Z[G]`.

For a finite `G`-set `X`, use the coefficient module `ell^2(X)` and form the
cochain complexes

`C_X^*=Hom_(Z[G])(C_*,R[X])`,
`D_X^*=Hom_(Z[G])(D_*,R[X])`.                                   `(FRI8)`

Precomposition reverses the arrows in `(FRI6)` and gives integral cochain
maps between `(FRI8)` which remain homotopy inverse.

**Theorem 2 (uniform free-resolution invariance).**  There is a constant

`B_r<infinity`                                                   `(FRI9)`

depending only on the two fixed resolutions and their degree-`r`
comparison matrices such that, for every finite `G`-set `X`,

`B_r^(-1) kappa(C_X)<=kappa(D_X)<=B_r kappa(C_X)`,               `(FRI10)`

and identically for the least integral-section norms `mu`.  One may take

`B_r=sqrt(R(f_r)C(f_r)R(g_r)C(g_r))`.                            `(FRI11)`

**Proof.**  Lemma 1 bounds the two specialized degree-`r` cochain maps by

`sqrt(R(f_r)C(f_r))`, `sqrt(R(g_r)C(g_r))`.                      `(FRI12)`

They are integral and cochain-homotopy inverse.  Apply Theorem 4 of
`TRUE_CHAIN_COMPARISON_DECODER_TRANSFER.md`; the product of the two bounds
in `(FRI12)` is `(FRI11)`.  End proof.

Thus uniform harmonic integral repair is independent, up to one explicit
constant, of the chosen fixed finite free resolution.  A large HAP
resolution may be replaced by a smaller fixed free model without paying a
chart-dependent norm.

## 3. Fixed complexes with finite stabilizers

The arithmetic cellular models used for `SL_3(Z)` are naturally proper
`G`-complexes.  Their cellular chain modules have the form

`Z[G/H]`                                                         `(FRI13)`

for finite cell stabilizers `H`, possibly with an orientation character.
Such a module need not be projective over `Z[G]`.

Let `mathcal H` be the finite collection of stabilizers occurring through
degree `r+1` and put

`M=lcm{|H|:H in mathcal H}`.                                    `(FRI14)`

Over `R=Z[1/M]`, the averaging idempotent

`e_H=|H|^(-1) sum_(h in H) h`                                   `(FRI15)`

splits the relevant induced module.  Hence every `R[G/H]` is projective as
an `R[G]`-module.  If the fixed cellular complex is exact in the required
degrees, it is a projective `R[G]`-resolution there.

**Theorem 3 (localized uniform comparison).**  Let `E_*` be a fixed proper
cellular `G`-complex with finitely many cell orbits and finite stabilizers
through degree `r+1`, and suppose its augmented cellular complex is exact in
those degrees.  Let `C_*` be a fixed free integral resolution.  After
tensoring with `Z[1/M]`, there are comparison maps in both directions and
homotopies whose matrices have coefficients in `Z[1/M][G]`.  Their
specializations to every finite `G`-set have operator norms bounded
uniformly in the set.

**Proof.**  The preceding averaging argument makes the cellular modules
projective over `Z[1/M][G]`.  The projective-resolution comparison theorem
constructs maps and homotopies through the required finite degrees.  These
are fixed finite matrices with finitely supported localized group-ring
entries.  Lemma 1 applies verbatim with the sum of the absolute rational
coefficients in place of `(FRI2)`.  End proof.

Theorem 3 removes all real-metric and chart-size growth from the comparison
problem.  It does **not** give the integral hypothesis of Theorem 2.

## 4. The exact integrality boundary

Clear denominators in the localized comparison maps.  Because only finitely
many fixed matrices occur, there is one integer `N`, all of whose prime
divisors divide `M`, such that

`F=Nf`, `G=Ng`                                                    `(FRI18)`

are integral in the required degrees.  On cohomology the localized maps are
inverse, so

`G F=N^2 id`, `F G=N^2 id`                                      `(FRI19)`

on the corresponding integral free lattices: the identities hold after
tensoring with `Q`, hence hold integrally between torsion-free groups.  It
follows directly that the kernel and cokernel of either cleared comparison
are killed by `N^2`.  For example, every cokernel class of `F` satisfies

`N^2[y]=[F(Gy)]=0`.                                              `(FRI20)`

Therefore the failure of the localized comparison to identify the two
integral harmonic lattices has the following exact form:

* it vanishes after tensoring with `Z[1/M]`;
* its kernel and cokernel are finite and supported only at primes dividing
  `M`; and
* its exponent divides `N^2`, a constant depending on the fixed comparison,
  not on the finite chart.

This bounded-primary statement is not yet a metric decoder.  A family of
finite-index lattice inclusions of bounded exponent can still have badly
shaped coset representatives when the rank grows.  One must either construct
integral comparison maps on the desired free cuspidal summand or control
these finitely many primary correction lattices directly.

For the projective `SL_3(Z)` computations this qualification matches the
data: the rational harmonic sector is clean, while characteristic two has
the exceptional jumps.  The comparison theorem says that arbitrary prime
growth is not hiding in the change of resolution; the unresolved comparison
is a fixed-stabilizer, bounded-primary integral problem.

## 5. Consequence for the selected carry program

The combined implication is now

`uniform decoder in one fixed integral free resolution`
` <=> uniform decoder in every fixed integral free resolution`,           `(FRI16)`

with explicit constants from `(FRI11)`.

For the compact modular-symbol/well-rounded model one has, unconditionally,

`uniform localized comparison to HAP`                             `(FRI17)`

and hence a uniform comparison of the real harmonic norms.  To upgrade
`(FRI17)` to integral carry repair, it remains to solve only the finite set
of stabilizer-primary lattice corrections.

At level `53`, an explicit integral comparison on the rank-two free cuspidal
summand would close this correction at that chart and allow the compact
Gram lattice to be transported by
`TRUE_CHAIN_COMPARISON_DECODER_TRANSFER.md`.  Across all prime levels, a
uniform integral correction theorem at the fixed stabilizer primes would
remove the comparison-map gate completely.  The remaining difficulty would
then be the compact model's own uniform integral section, not the HAP
resolution or its dimension.

The zero-th stabilizer-homology row now has one exact correction.  The first
degree-two orientation-torsion block is induced from `S_4`, the degree-one
block from an index-three `D_8`, and the cellular transfer is a permutation
isomorphism on signed `C_2` orbit summands for every finite coefficient
action.  Its inverse has norm one.  These zero-row summands can therefore be
cancelled uniformly.  This does not cancel the positive stabilizer-homology
rows in HAP's derived total complex; the remaining bounded-primary issue is
the residual filtered augmentation described in
`TRUE_HAP_DERIVED_TOTAL_AUDIT.md`.  See
`TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md` for the exact finite-group theorem.
