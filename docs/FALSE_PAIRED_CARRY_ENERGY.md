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

This leaves a genuinely smaller finite problem than the earlier
cycle-radius formulation.  The remaining search should not enumerate the
full cycle lattice.  It should compute the Smith image of the radical
filling code, split it into low-rank cycle-cheap and range-cheap pieces,
and solve the corresponding low-dimensional CVPs.
