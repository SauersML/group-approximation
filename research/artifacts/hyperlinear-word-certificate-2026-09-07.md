# The remaining certificate for a nonhyperlinear group

2026-09-07. **Status:** the equivalences and the certificate obstruction
below are proved. No instance with a nontrivial word and a valid
all-dimensions bound is supplied. There is no new existence theorem or
Lean verification claim.

## 1. Radical membership has an ordinary HS linear certificate

Let Gamma=<S|r_1,r_2,...>, where S is finite. The relator list may be finite
or countable and need not be computable. Fix a word w in F(S). Define

```text
e_v(U) = ||v(U)-I||_(2,d)^2 = 2-2 Re tr_d(v(U)).
```

Then the following are equivalent:

1. Every homomorphism from Gamma to a tracial matrix ultraproduct kills w.
2. There are a finite sublist R_0 of the defining relators and a positive
   integer N such that in every dimension d>=1 and for every U in U(d)^S,

   ```text
   e_w(U) <= N sum_(r in R_0) e_r(U).                 (CERT)
   ```

Condition 1 is membership of wbar in Rad_hyp(Gamma). For a finite
presentation one may take its entire relator list in condition 2. The
single finite list and N are independent of both dimension and accuracy.

**Forward direction.** Apply the established
`hyperlinear-radical-presentation-compactness` with word tolerance one.
It supplies a finite R_0 and eta>0 such that

```text
max_(r in R_0)||r(U)-I||_2 < eta  ==>  ||w(U)-I||_2 < 1.
```

By contraposition this is the fixed-gap hypothesis of
`fixed-hs-word-gap-is-linear-domination`. Hence

```text
e_w(U) <= (4/eta^2) max_(r in R_0) e_r(U)
       <= (4/eta^2) sum_(r in R_0) e_r(U).
```

Choose any positive integer N>=4/eta^2. The empty-list case uses the
zero maximum and zero sum; it simply forces e_w=0 everywhere.

**Reverse direction.** Represent a homomorphism into a metric
ultraproduct of the groups U(d_n) by unitary tuples U_n on S. For each
r in R_0, its HS defect tends to zero along the ultrafilter because r is
a relation of Gamma. The finite sum in (CERT) therefore tends to zero,
so the image of w is the identity. Equivalently, use unitary lifts in
the tracial matrix ultraproduct; singular-value polar completion supplies
such lifts. No passage from an arbitrary trace to matrix microstates is
being assumed.

This is a quantitative refinement of the existing compactness theorem,
not a new source of radical membership. It also explains the finite-prefix
result already in `hyperlinear-radical-is-finitely-witnessed`: the same
inequality proves radical membership in <S|R_0>.

## 2. When the certificate would solve the existence question

If wbar!=1 in Gamma, then its lift in G_0=<S|R_0> is nontrivial: the
quotient map G_0 -> Gamma sends that lift to wbar. A hyperlinear embedding
of G_0 would kill w by (CERT) and be injective, a contradiction. Thus
an actual finite R_0, nontrivial w, and proof of (CERT) would supply a
finitely presented nonhyperlinear group.

This separates two proof obligations:

* establish w!=1 in the presented group, for example by a justified
  normal-form argument or a faithful algebraic realization;
* prove (CERT) for **all** finite-dimensional unitary tuples, not merely
  all tuples up to a tested dimension or all exact finite representations.

An exact finite-dimensional representation detecting w would refute the
second obligation, since all its relators have zero energy. Therefore
nontriviality cannot be certified by such a representation for a successful
instance. An infinite-dimensional regular representation has no such issue.

For a finitely presented infinite simple G and a fixed wbar!=1, existence
of N in (CERT), with the full relator list, is equivalent to G being
nonhyperlinear. Indeed a nontrivial homomorphism from a simple group is
injective; if its target is a tracial matrix ultraproduct, that would make
G hyperlinear. This is the scalar-sensitive linear version of the existing
`fp-simple-nonhyperlinearity-is-one-word-domination` theorem. For a general
group, membership of a specified w in the radical is a stronger assertion
than nonhyperlinearity alone; simplicity must not be omitted from this
particular equivalence.

## 3. Why universal tracial SOS cannot prove a successful instance

Write the candidate inequality as the rational group-ring polynomial

```text
P_N = N sum_(r in R_0) (r-1)^*(r-1) - (w-1)^*(w-1)
      in Q[F(S)].                                    (POLY)
```

The assertion (CERT) is exactly `tr_d(P_N(U))>=0` for all finite
matrix tuples. Suppose w!=1 in G_0=<S|R_0>. Evaluate the same words in
the left regular representation lambda of G_0. In its finite tracial
von Neumann algebra L(G_0), every defining relator is exactly I and
tau(lambda(w))=tau(lambda(w)^*)=0. Thus

```text
tau(P_N(lambda(S))) = -tau((lambda(w)-1)^*(lambda(w)-1))
                   = -2.                             (REGULAR)
```

Consequently (POLY) cannot have a certificate formed solely from rules
valid in every tracial algebra. In particular it cannot be a sum of
Hermitian squares modulo cyclic commutators and the relator *-ideal.
Squares have nonnegative trace, commutators have zero trace, and the
relator ideal vanishes in lambda. This also rules out certificates for
P_N+epsilon*1 when 0<=epsilon<2.

The finite-moment version is equally concrete. On any finite word set W,

```text
M_(u,v) = tau(lambda(u)^*lambda(v))
        = 1 if u=v in G_0, and 0 otherwise
```

is a positive semidefinite Gram matrix: use the vectors delta_(ubar) in
ell^2(G_0). These moments satisfy every valid tracial, unitary, and
relator identity, while (REGULAR) remains negative whenever the required
words are included. Therefore a finite moment relaxation which is valid
for *all tracial states* cannot certify (CERT). This statement does not
rule out a method using additional, sound matrix-specific information.

This is the same regular-trace obstruction already used for the Jacobson
head in `left-regular-representation-defeats-tracial-sos-proof` and for
the eight-slice packet in
`universal-tracial-certificates-cannot-force-eight-slice-overlap`.
Here it is applied to the exact linear certificate now identified for the
ordinary HS word norm. It must not be interpreted as a refutation of the
matrix-only inequality itself: whether the regular trace is approximable
by matrices is precisely the issue.

## 4. Attempt and outcome

The attempted route was to turn the repository's fixed HS gap into a
linear energy inequality and then look for a rational cyclic SOS witness.
The first step succeeds with the explicit constant from the companion
amplification proof. The second cannot succeed using only universal
tracial positivity, by (REGULAR). It would certify a false inequality in
the canonical group trace.

The live remaining obligation for `saturated-group-hs-relator-defect-gap`
is a matrix-specific proof of its gap or equivalent global inequality.
The current operator-norm certificate does not provide one. A bounded
matrix search, or a dimension growth lower bound, also does not provide
one. No constant for that candidate is asserted here.

The finite replay now includes G=<x|x^2=1>, x represented by the
two-point swap: its relator energy is zero, marked-word energy is two,
and (POLY) has trace -2 for every N. The amplifier identities all pass
on this finite, hence hyperlinear, group. This negative control makes the
distinction between validating an amplifier and proving a group's gap
explicit and reproducible.
