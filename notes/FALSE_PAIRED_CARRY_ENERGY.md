# Exact paired carry energy for radical phase microstates

Date: 2026-08-11

## 1. Purpose

The exact nonlinear repair identity in
`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` improves the FALSE-side
criterion in a way which is easy to miss.  The relator defect of the
canonical phase table is not merely bounded by the cycle-side radius
`rho_K(c)`.  It is an exact infimal convolution of the cycle and range
discriminant radii.  Consequently a filling code can have microscopic
average defect even when its cycle-side mean radius is macroscopic.

This note proves the exact formula and a subgroup-splitting criterion which
feeds directly into the radical filling code of
`FALSE_RADICAL_FILLING_DISCRIMINANT.md`.

## 2. Exact carry energy on the discriminant group

Let `Lambda=Z^m` with its Euclidean metric, let `W` be a rational subspace,
and put

`L=W intersect Lambda`, `K=W^perp intersect Lambda`.                 `(PCE1)`

Write

`gamma:D_K=K^#/K -> D_L=L^#/L`                                      `(PCE2)`

for the canonical unimodular gluing isomorphism.  For `c in D_K`, choose
any

`a_c in L^#`, `a_c+L=gamma(c)`,                                     `(PCE3)`

and define its ambient integral carry energy by

`delta(c)=dist(a_c,Lambda)`.                                        `(PCE4)`

This is well defined: two choices in `(PCE3)` differ by an element of
`L subset Lambda`.

Let `rho_L` and `rho_K` denote shortest-vector radii in discriminant
cosets.

**Theorem 1 (exact discriminant convolution).**  For every `c in D_K`,

`delta(c)^2=min_(d in D_K)`
`  (rho_L(gamma(c-d))^2+rho_K(d)^2)`.                                `(PCE5)`

In particular,

`delta(c)^2<=min(rho_L(gamma(c))^2,rho_K(c)^2)`.                     `(PCE6)`

**Proof.**  The exact paired-discriminant formula `(NDR14)` says

`dist(a_c,Lambda)^2=min_d`
`  (d_(gamma(d))(a_c)^2+rho_K(d)^2)`.                               `(PCE7)`

For fixed `d`, subtraction by `a_c` identifies the entire coset
`gamma(d)` with the coset `gamma(d-c)` up to sign.  Hence

`d_(gamma(d))(a_c)=rho_L(gamma(c-d))`.                              `(PCE8)`

Substitution gives `(PCE5)`.  Taking `d=0` and `d=c` gives `(PCE6)`.
End proof.

Thus the apparent dependence of the defect quantity `delta_A(c)` in
`(DPI19a)` on the ellipsoidal shortest representative is illusory: the
ambient carry defect is constant on the range discriminant coset and is
the intrinsic function `(PCE5)`.  The matrix `A` still governs the repair
distance through the ellipsoidal range norm, but not this canonical
relator defect.

**Example 2.**  Take `Lambda=Z^2` and

`W=R(1,2)`, `K=Z(2,-1)`, `L=Z(1,2)`.                              `(PCE8a)`

Both discriminant groups are `Z/5`.  If the cycle class is indexed by the
coefficient of `(2,-1)/5`, the gluing map is multiplication by `3` modulo
`5`.  Hence

`rho_K(t)^2=min_(r=t mod 5)|r|^2/5`,
`rho_L(gamma(t))^2=min_(r=3t mod 5)|r|^2/5`.                       `(PCE8b)`

For `c=2`, the cycle radius squared is `4/5`, whereas taking `d=0` in
`(PCE5)` gives

`delta(2)^2<=rho_L(gamma(2))^2=1/5`.                              `(PCE8c)`

Thus replacing `rho_K` by the exact carry energy is already a strict
improvement in the smallest nonsymmetric primitive line example.

## 3. Exact-energy character pruning

Retain the phase-relator and radical-word setup of
`FALSE_DISCRIMINANT_PHASE_INSTABILITY.md`.  Thus `A_n` is the integral
phase-relator matrix of a finite chart, `m_n` is its number of relator
coordinates, `C_n<=D_(K,n)` is a finite subgroup, and

`chi_(w,n):C_n -> (R/Z)^(N_n)`                                      `(PCE9)`

is the radical-word character.  Let `delta_n(c)` be `(PCE5)` for the
`n`-th chart.

**Theorem 2 (exact mean-carry FALSE criterion).**  Suppose that for one
fixed `alpha>0`, at least `alpha N_n` coordinate characters of `(PCE9)`
are nontrivial, and

`(1/|C_n|) sum_(c in C_n) delta_n(c)^2=o(m_n)`.                     `(PCE10)`

Then a hyperlinear nonsofic group exists.

**Proof.**  Character orthogonality gives

`(1/|C_n|) sum_(c in C_n) mu_(w,n)(c)^2>=2 alpha`,                  `(PCE11)`

where every marked energy lies in `[0,4]`.  Put

`eta_n=((1/(m_n|C_n|))sum_c delta_n(c)^2)^(1/4)`.                   `(PCE12)`

Then `eta_n->0`, and Markov's inequality shows that the proportion of
classes with

`delta_n(c)>eta_n sqrt(m_n)`                                       `(PCE13)`

is at most `eta_n^2`.  Removing them deletes only `o(|C_n|)` total
marked energy from `(PCE11)`.  Some remaining class has marked energy
bounded below while its exact normalized relator defect is at most
`eta_n`.  The marked discriminant criterion `(DPI24)--(DPI26)` produces a
tracial matrix-ultraproduct image which retains the nontrivial radical
word.  That image is hyperlinear and cannot be sofic.  End proof.

Condition `(PCE10)` is strictly weaker than `(DPI35a)`, because `(PCE6)`
gives

`delta_n(c)^2<=rho_(K,n)(c)^2`.                                    `(PCE14)`

It also gives the previously unavailable range-side criterion

`(1/|C_n|)sum_(c in C_n)rho_(L,n)(gamma_n(c))^2=o(m_n)`.            `(PCE15)`

The exact mean in `(PCE10)` has a still simpler finite form.  The canonical
embedding

`D_(L,n)->(R/Z)^(m_n)`                                               `(PCE15a)`

makes every ambient coordinate a character of `C_n`.  If `s_n` is the
number of nontrivial coordinate characters, Theorem 1 of
`FALSE_CARRY_MEAN_SUPPORT_FORMULA.md` gives

`(2/27)s_n<=avg_(c in C_n)delta_n(c)^2<=(1/8)s_n`.                  `(PCE15b)`

Consequently `(PCE10)` is equivalent to `s_n=o(m_n)`.  The orders of the
coordinate characters give the exact mean through `(CMS11)--(CMS12)`, but
even those orders are irrelevant to the asymptotic criterion.  Thus one may
verify the load-bearing defect hypothesis by a rational/Smith support pass,
without a discriminant CVP.

## 4. Splitting a filling code between the two lattices

The infimal convolution has a useful group-theoretic consequence.

**Theorem 3 (paired subgroup decomposition).**  Let `P,Q` be subgroups of
`D_K`, and set `C=P+Q`.  Then

`(1/|C|)sum_(c in C)delta(c)^2`
` <=(1/|P|)sum_(p in P)rho_K(p)^2`
`   +(1/|Q|)sum_(q in Q)rho_L(gamma(q))^2`.                         `(PCE16)`

**Proof.**  For `p in P` and `q in Q`, choose `d=p` in `(PCE5)` to get

`delta(p+q)^2<=rho_K(p)^2+rho_L(gamma(q))^2`.                      `(PCE17)`

The addition map `P times Q -> C` is onto and every fiber has cardinality
`|P intersect Q|`.  Therefore the pushforward of the uniform measure on
`P times Q` is uniform on `C`.  Average `(PCE17)`.  End proof.

**Corollary 4 (hybrid low-rank criterion).**  In Theorem 2 it is enough to
write `C_n=P_n+Q_n` so that

`avg_(p in P_n)rho_(K,n)(p)^2`
` +avg_(q in Q_n)rho_(L,n)(gamma_n(q))^2=o(m_n)`.                  `(PCE18)`

Neither summand has to control all of `C_n`.  A cheap cycle subgroup and a
cheap range subgroup may jointly cover the radical filling code.

For example, `(PCE18)` follows if `P_n` and `gamma_n(Q_n)` have fundamental
domains of radii `o(sqrt(m_n))` in `K_n^#` and `L_n^#`, respectively.  In
fixed rank these radii reduce to ordinary low-dimensional CVP estimates.
This is the precise FALSE-side use of the rank-two pullback

`Q^#/(H intersect Z^m) -> D_L`                                     `(PCE19)`

from the `p=53` calculation: the projective `SL_3(Z)` chart itself has no
radical word, but its two-variable rational-pullback and binary-quadratic
CVP method can certify the range-side term in `(PCE18)` for a genuine
radical presentation.

## 5. Combination with the finite nonisotropy certificate

For a regular presentation cover and radical filling code `C_(w,X)`, deck
transitivity turns one nonzero discriminant pairing into the character
hypothesis of Theorem 2.  The isotropic-size theorem `(RFD31)--(RFD34)`
gives the purely finite replacement

`|C_(w,X)|^2>|D_K|`.                                                `(PCE20)`

Combining the results yields the following exact endpoint.

**Corollary 5 (paired radical-filling certificate).**  Let `(X_n)` be
regular finite covers of a fixed finite presentation with a nontrivial
radical word `w`.  A hyperlinear nonsofic group exists if, eventually,

1. `|C_(w,X_n)|^2>|D_(K,n)|`; and
2. `C_(w,X_n)=P_n+Q_n` with the paired mean energy in `(PCE18)` equal to
   `o(m_n)`.

More directly, item 2 may be replaced by the exact single condition
`(PCE10)` and item 1 by one nonintegral entry of the discriminant Gram
matrix.

For the regular covers of one fixed presentation, this sufficient criterion
is in fact vacuous for a nonzero deck-invariant code.  Theorem 1 of
`FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md` shows that its carry support
contains a full deck orbit and hence has positive density; quantitatively,
if the base has `b_2` relator cells, then

`avg_C delta_n(c)^2>=(2/(27b_2))m_n`.                              `(PCE21)`

Thus neither `(PCE10)` nor the stronger paired bound `(PCE18)` can hold for
the radical filling code in that setting.  The live FALSE statistic is the
joint low-carry/high-word tail, not the uniform subgroup mean: one must use
a nonuniform selection correlated with word energy, allow a growing number
of coordinate orbits, or leave the regular-cover phase ansatz.

`FALSE_BERNOULLI_CARRY_INCIDENCE.md` gives a concrete nonuniform
replacement in the two-torsion sector.  A binary parametrization proves
FALSE when its maximum carry-row degree is negligible compared with the
marked-word row degree on a positive fraction of word coordinates.

There is now an additional sharp qualification in the bounded marked-frame
regime.  `FALSE_BOUNDED_FRAME_PAIRED_CARRY_COLLAPSE.md` proves that any
individual class with microscopic exact paired energy and macroscopic
marked energy contains a class with microscopic **cycle** radius and the
same asymptotic marked energy.  Thus `(PCE16)--(PCE18)` remain useful finite
search and averaging devices, but once they output a successful marked
class they do not give a genuinely new existential mechanism beyond the
cycle-side criterion.
