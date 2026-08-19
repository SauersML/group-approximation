# The Iwahori matching problem reduces to simultaneous modular square roots

Date: 2026-08-12

## 1. Outcome

Dogon--Vigdorovich ask whether two finite-dimensional representations of
`SL_2(Z)` which almost agree on the two index-three Iwahori subgroups can be
perturbed, with flexible normalized-Hilbert--Schmidt padding, to
representations which agree exactly.  A positive answer gives a
nonhyperlinear finite central extension of `SL_2(Z[1/2])`.

This note proves two reductions.

First, the question is exactly a simultaneous square-root stability problem
for two unitaries.  Put

```text
u = [[1,1],[0,1]],       l = [[1,0],[1,1]],       z=-I.       (IMR1)
```

Then

```text
B_+=<u,l^2,z>,       B_-=<u^2,l,z>,                         (IMR2)
sigma(u)=u^2,        sigma(l^2)=l,       sigma(z)=z.         (IMR3)
```

If `alpha,beta:SL_2(Z)->U(d)` are the two vertex representations and

```text
X=beta(u),       Y=alpha(l),                                (IMR4)
```

then their Iwahori defect is precisely the defect of replacing the two
vertex pairs by

```text
(alpha(u),alpha(l)) ~ (X^2,Y),
(beta(u),beta(l))   ~ (X,Y^2),                              (IMR5)
```

together with agreement of the two central words.  Thus exact matching is
equivalent to perturbing `X,Y` so that both `(X^2,Y)` and `(X,Y^2)` are exact
`SL_2(Z)` representations and their copies of `z` coincide.

Second, the full matching question is true on every **fixed finite library
of vertex representation types**.  Consequently, a counterexample cannot
come from increasing only the multiplicities of finitely many irreducible
representations.  It must use infinitely many inequivalent irreducible
vertex representations.  In particular, the question has a positive answer
for pairs factoring through any two fixed finite quotients of `SL_2(Z)`.

This does not solve the unrestricted question.  It identifies the remaining
escape exactly as unbounded representation type, rather than multiplicity,
dimension padding, or central-sign mismatch.

The character-rigidity reduction below gives a stronger conclusion.  The
question is positive whenever the irreducible dimensions on even one vertex
are uniformly tight: for every `epsilon>0`, all but `epsilon d_n` dimensions
belong to irreducible summands of dimension at most some fixed
`D=D(epsilon)`.  Thus a counterexample must put positive normalized
dimension on irreducible summands whose dimensions escape every fixed bound,
on both vertices.  Merely moving through a continuous family of bounded
dimensional irreducibles cannot produce a counterexample.

## 2. The exact square-root formulation

Write

```text
K=SL_2(Z),       Lambda=K*K.                               (IMR6)
```

The standard presentation in the two unipotents is

```text
K=<u,l |
      u l^(-1) u = l^(-1) u l^(-1),
      (u l^(-1) u)^4=1>.                                  (IMR7)
```

The central involution is

```text
z=(u l^(-1)u)^2.                                          (IMR8)
```

Let `R(P,Q)` denote the two relations in `(IMR7)`, evaluated at a pair of
unitaries `P,Q`, and put

```text
Z(P,Q)=(P Q^(-1) P)^2.                                   (IMR9)
```

For two representations `alpha,beta:K->U(d)`, Dogon--Vigdorovich's local
defect on the displayed generators of `B_+` is

```text
max( ||alpha(u)-beta(u)^2||_2,
     ||alpha(l)^2-beta(l)||_2,
     ||alpha(z)-beta(z)||_2 ).                            (IMR10)
```

Indeed `(IMR10)` is just `(IMR2)--(IMR3)`.  With `X,Y` as in `(IMR4)`, the
first two terms say exactly `(IMR5)`.  Since `alpha` and `beta` are honest
representations, a finite telescoping estimate gives

```text
def R(X^2,Y) + def R(X,Y^2) = O(def(alpha,beta)),          (IMR11)
```

where the constant is absolute because the words in `(IMR7)` are fixed.
The third term in `(IMR10)` becomes

```text
||Z(X^2,Y)-Z(X,Y^2)||_2 = O(def(alpha,beta)).             (IMR12)
```

Conversely, suppose `X',Y'` satisfy

```text
R((X')^2,Y')=1,       R(X',(Y')^2)=1,
Z((X')^2,Y')=Z(X',(Y')^2).                               (IMR13)
```

Define

```text
alpha'(u)=(X')^2,    alpha'(l)=Y',
beta'(u)=X',         beta'(l)=(Y')^2.                    (IMR14)
```

The first line of `(IMR13)` makes these two honest `K`-representations.
The second line and `(IMR2)--(IMR3)` say that their Iwahori restrictions
agree exactly.  Hence they give a compatible representation of

```text
K *_(B_+ ~= B_-) K ~= SL_2(Z[1/2]).                      (IMR15)
```

Equations `(IMR10)--(IMR14)` prove the claimed equivalence, both in a
sequential formulation and in the usual epsilon--delta formulation.

The central line in `(IMR13)` must not be omitted.  The elements `u,l^2`
do not by themselves make the two copies of the central involution equal;
this is why `z` occurs in Dogon--Vigdorovich's generating set for `B_+`.

### 2.1 The edge group has no hidden coupled relation

Put

```text
e=u l^(-2).                                               (IMR13a)
```

A direct matrix calculation gives

```text
e^2=z,             l^2=e^(-1)u.                          (IMR13b)
```

Consequently

```text
B_+ = <u,e,z | z^2=1, [z,u]=[z,e]=1, e^2=z>
    ~= C_4 *_(C_2) (C_2 x Z).                            (IMR13c)
```

After restricting to either central sector `z=+1` or `z=-1`, multiply `e`
by a fixed scalar in the negative sector.  In both cases a representation of
`B_+` is then simply an arbitrary unitary together with an arbitrary
involution: the sector quotient is `Z*C_2`.  Thus the edge representation
variety itself contains no additional relation coupling its two generators.
All of the difficulty in the Iwahori problem comes from requiring that this
free edge datum extend simultaneously across the two index-three modular
vertices.  In particular, proving Hilbert--Schmidt stability of the edge
group alone cannot solve the compatibility problem.

## 3. Central signs cost only vanishing padding

The central coordinate is not the hard part of the problem.

**Lemma 1 (central-sign matching).**  Let `alpha_n,beta_n:K->U(d_n)` be
representations such that

```text
||alpha_n(z)-beta_n(z)||_2 ->0.                           (IMR16)
```

After adding `o(d_n)` one-dimensional summands to each representation and
conjugating one enlarged representation by a unitary which is `o(1)` from
the identity in normalized Hilbert--Schmidt norm, one may assume

```text
alpha_n(z)=beta_n(z).                                    (IMR17)
```

The perturbation tends to zero in the generalized metric `d_2`.

**Proof.**  Put

```text
p_n=(1-alpha_n(z))/2,       q_n=(1-beta_n(z))/2.          (IMR18)
```

These are the negative central projections.  For projections,

```text
|tr(p_n)-tr(q_n)| <= ||p_n-q_n||_2^2.                    (IMR19)
```

Thus their rank difference is `o(d_n)`.  The abelianization of `K` is
cyclic of order twelve, so `K` has one-dimensional characters on which `z`
acts by `+1`, and also characters on which it acts by `-1`.  If, for
example, `rank(p_n)<rank(q_n)`, add `rank(q_n)-rank(p_n)` negative characters
to `alpha_n` and the same number of positive characters to `beta_n`.
The enlarged spaces have the same dimension and the negative central
projections have equal rank.  The added relative dimension is `o(1)`, so
the generalized `d_2` cost tends to zero.

Equal-rank projections which are close in normalized Hilbert--Schmidt norm
are conjugate by a unitary close to the identity in the same norm (use the
principal-angle decomposition of the two projections).  Conjugating the
second enlarged representation gives `(IMR17)` at an additional `o(1)`
cost.  End proof.

After Lemma 1, both representations split over the same `+1` and `-1`
central subspaces.  The matching problem can therefore be treated
separately in the two central sectors and recombined by direct sum.

## 4. A fixed-type matching theorem

Let `V_1,...,V_r` and `W_1,...,W_s` be fixed finite lists of
finite-dimensional unitary representations of `K`.  Repetitions in the
lists are harmless, although it is convenient to take the listed
representations irreducible and pairwise inequivalent.

Call a representation **of `(V,W)`-type** if its first vertex is a direct
sum of copies of the `V_i` and its second vertex is a direct sum of copies
of the `W_j`.

**Theorem 2 (fixed-type Iwahori matching).**  Suppose

```text
alpha_n,beta_n:K->U(d_n)                                 (IMR20)
```

are `(V,W)`-type representations and their Iwahori defects tend to zero.
Then there are dimensions `D_n` with

```text
D_n/d_n ->1                                             (IMR21)
```

and compatible representations

```text
alpha'_n,beta'_n:K->U(D_n)                              (IMR22)
```

such that

```text
d_2(alpha_n,alpha'_n)+d_2(beta_n,beta'_n)->0.            (IMR23)
```

In particular, Dogon--Vigdorovich's question has a positive answer on every
fixed finite collection of vertex representation types.

### 4.1 The restriction matrix

Restrict the fixed `V_i` to `B_+`, and restrict `W_j` to `B_-` before
pulling back by `sigma`.  Only finitely many irreducible `B_+`
representations occur in these restrictions; list them as

```text
theta_1,...,theta_t.                                    (IMR24)
```

Let

```text
R_+ in M_(t,r)(N),       R_- in M_(t,s)(N)              (IMR25)
```

be the two restriction-multiplicity matrices.  If `m_n in N^r` and
`n_n in N^s` are the multiplicity vectors of `alpha_n,beta_n`, set

```text
A=[R_+  -R_-].                                          (IMR26)
```

Exact compatibility of the restrictions up to unitary equivalence is
precisely

```text
A(m_n,n_n)=0.                                           (IMR27)
```

The hypothesis that the concrete restrictions become close implies

```text
||A(m_n,n_n)||_1=o(d_n).                                (IMR28)
```

One way to see `(IMR28)` is to use the finite-dimensional left--right
representations on `Hom(theta_a,theta_b)`.  Because the finite list
`(IMR24)` is fixed, the Laplacians of these representations have a positive
minimum spectral gap away from their invariant subspaces.  Orthogonally
projecting the identity matrix onto the exact intertwiner space, with the
projection obtained by functional calculus of this fixed Laplacian, therefore
shows that two close restrictions have all their isotypic multiplicities
equal up to `o(d_n)`.  Equivalently, one can apply the finitely many central
isotypic projections associated with the fixed constituent list.

### 4.2 Integral correction in a fixed rational cone

We use the following elementary integer-cone lemma.

**Lemma 3.**  Fix an integral matrix `A`.  If `x_n in N^k` satisfies

```text
||A x_n||_1=o(||x_n||_1),                               (IMR29)
```

then there are `y_n in N^k cap ker(A)` such that

```text
||x_n-y_n||_1=o(||x_n||_1).                             (IMR30)
```

**Proof.**  The cone

```text
C=ker(A) cap R_+^k                                      (IMR31)
```

is rational polyhedral.  A fixed Hoffman error bound for the finite system
`Ax=0, x>=0` gives

```text
dist_1(x_n,C) <= C_A ||A x_n||_1.                       (IMR32)
```

By Gordan's lemma, `C` is generated as a real cone by finitely many integral
vectors.  Express a nearest point of `C` in these fixed generators and
round the nonnegative coefficients.  The rounding error is bounded by a
constant depending only on the fixed generators.  Equations
`(IMR29)--(IMR32)` give `(IMR30)`.  End proof.

Apply Lemma 3 to `(IMR26)--(IMR28)`.  We obtain corrected vertex
multiplicity vectors

```text
(m'_n,n'_n) in N^(r+s),       R_+m'_n=R_-n'_n,          (IMR33)
```

which differ from the original vectors by `o(d_n)`.  The dimensions of the
two corrected vertex representations are equal because the dimensions of
equal restricted representations are equal.  Call this common dimension
`D_n^0`.  Fixed dimensions of the representations in the libraries imply
`D_n^0/d_n->1`.  If `D_n^0<d_n`, add `d_n-D_n^0` copies of the compatible
trivial one-dimensional vertex pair to both sides.  Thus the final common
dimension `D_n` satisfies `D_n>=d_n` and `D_n/d_n->1`.

Build vertex representations with the multiplicities in `(IMR33)`, keeping
all common old summands and changing only `o(d_n)` dimensions.  They are
therefore `o(1)` from `alpha_n,beta_n` in generalized `d_2`.  Their
Iwahori restrictions are isomorphic by `(IMR33)` and remain `o(1)`-close as
concrete representations.

For completeness, the last alignment can be made by a near-identity
unitary.  Orthogonally project the identity onto the intertwiner space using
functional calculus of the fixed left--right Laplacian.  The resulting exact
intertwiner is `o(1)` from the identity in normalized Hilbert--Schmidt norm.
Polar decomposition gives a partial isometric intertwiner on a
`D_n-o(D_n)` dimensional subspace.  Since the two restrictions are
isomorphic with the same multiplicity of every irreducible constituent, the
kernel and cokernel carry isomorphic complementary subrepresentations.
Extend the partial isometry there to a unitary intertwiner.  The extension is
still `o(1)` from the identity.  Conjugating the second vertex representation
by this unitary makes the two restrictions exactly equal without changing
`(IMR23)`.

The universal property of the amalgam `(IMR15)` now gives the compatible
representations `(IMR22)`.  This proves Theorem 2.

## 5. Finite-quotient corollary and the exact remaining gate

**Corollary 4.**  Fix finite quotients `F_+,F_-` of `K`.  The Iwahori
matching question has a positive answer for pairs whose two vertex
representations factor through `F_+` and `F_-`, respectively.

**Proof.**  Take the finite libraries in Theorem 2 to be the irreducible
representations of the two fixed finite groups.  End proof.

The fixed-quotient hypothesis is essential to what has been proved here.
If the quotient or representation type varies, the finite list `(IMR24)`,
the spectral separation used in `(IMR28)`, and the integral restriction
matrix `(IMR26)` all vary.  Their constants can degenerate.

Thus every negative sequence must satisfy the following necessary
condition:

```text
the vertex irreducible support escapes every fixed finite subset of
the unitary dual of SL_2(Z).                              (IMR34)
```

Equivalently, multiplicity growth inside a bounded representation library
cannot defeat matching.  The remaining problem is to control the varying
restriction cones and the continuous free-product parameters of
`SL_2(Z)=C_4 *_(C_2) C_6` uniformly.  In the square-root formulation, this
is a uniform noncommutative shadowing problem for `(IMR11)--(IMR13)`.

That is the next load-bearing lemma; finite-index induction by itself is not
enough, because inducing the entire `d`-dimensional edge representation
would triple the dimension rather than add only `o(d)` dimensions.

## 6. Character rigidity leaves only the central-regular sector

There is a second, independent reduction coming directly from the
Dogon--Vigdorovich machinery.  It is stronger than merely saying that the
irreducible types must vary.

Let

```text
Gamma=SL_2(Z[1/2]),             Z(Gamma)={1,z}.           (IMR35)
```

An Iwahori pair with defect tending to zero is an asymptotic representation
of `Gamma`: use the two honest vertex representations on the two vertex
groups and the vanishing discrepancy on the amalgam generators.  After
passing to a subsequence, its normalized traces converge pointwise to a
trace `tau` of `Gamma`.

The character-rigidity theorem used by Dogon--Vigdorovich says that every
extreme trace of this `S`-arithmetic group is either finite dimensional or
is supported on the center.  The latter possibilities are the two
central-regular characters

```text
tau_chi(g)=0                    if g is not in Z(Gamma),
tau_chi(z)=chi(z),              chi(z) in {+1,-1}.        (IMR36)
```

Consequently the GNS algebra of an arbitrary limiting trace splits as

```text
M_tau = M_hyp  direct-sum  (central-regular factor summands), (IMR37)
```

where `M_hyp` is amenable (a direct integral of finite-dimensional factors).
The character criterion in the supplied manuscript implies that `Gamma` is
hyperfinitely Hilbert--Schmidt stable.  Hence the portion of the asymptotic
representation corresponding to `M_hyp` can already be perturbed to honest
representations.

To make this finite-level statement precise, lift the central projections
of `(IMR37)` to projections in the matrix ultraproduct.  They asymptotically
commute with the given matrices.  Standard polar correction turns the
compressions into asymptotic unitary representations on the corresponding
corners; the ranks add up to the original dimension up to `o(d_n)`.  Apply
hyperfinite Hilbert--Schmidt stability on the amenable corner and retain the
central-regular corners.  The cutdowns of the two vertex representations are
initially only asymptotic representations of `K`, but the known flexible
Hilbert--Schmidt stability of `SL_2(Z)` corrects them back to honest vertex
representations without changing the vanishing edge defect.  Direct sums and
`o(d_n)` padding then reassemble the original sequence.

This proves the following reduction.

**Proposition 5 (central-regular endpoint).**  To answer the
Dogon--Vigdorovich Iwahori question positively, it is enough to prove the
following statement for each `chi(z) in {+1,-1}`:

> If an Iwahori-pair asymptotic representation `pi_n` satisfies
> `tr(pi_n(g))/d_n -> tau_chi(g)` for every `g in Gamma`, then `pi_n` is
> flexibly Hilbert--Schmidt close to honest representations of `Gamma`.

Conversely, any negative answer admits, after discarding the hyperfinite
corner and passing to one of the two nonzero central summands, a negative
sequence of precisely this form.  Thus the unrestricted problem is not a
general finite-dimensional-character problem.  Its only genuinely
nonamenable obstruction is **regular-sector microstate repair with the two
modular vertex groups already represented exactly**.

Residual finiteness supplies honest finite-quotient representations whose
traces converge to `(IMR36)`, but trace agreement alone does not conjugate
two nonamenable matrix models.  The missing theorem is therefore a relative
microstate-uniqueness statement for the inclusion of the two modular
vertices in `Gamma`; ordinary character approximation is insufficient.

## 7. Bounded irreducible dimension cannot reach the regular endpoint

The preceding reduction also removes all bounded-dimensional continuous
families of modular representations.  This is stronger than the fixed
library theorem because the irreducible type may vary with `n` through an
arbitrary compact representation variety.

For a finite-dimensional representation `rho` of `K=SL_2(Z)`, let
`rho^(>D)` denote the direct sum of its irreducible summands of dimension
strictly greater than `D`, counted with multiplicity.

**Theorem 6 (dimension-tight Iwahori matching).**  Let
`alpha_n,beta_n:K->U(d_n)` be an Iwahori pair whose defect tends to zero.
Suppose that on at least one vertex, say `alpha_n`,

```text
for every epsilon>0 there is D such that
dim(alpha_n^(>D)) <= epsilon d_n for all large n.       (IMR38)
```

Then the pair is flexibly Hilbert--Schmidt close to compatible honest
representations.  Consequently any negative sequence satisfies, on each
vertex,

```text
there is epsilon_0>0 such that for every D,
limsup_n dim(alpha_n^(>D))/d_n >= epsilon_0,             (IMR39)
```

and the analogous assertion for `beta_n`.

### Proof

The two vertex representations and their vanishing edge discrepancy define
an asymptotic representation `pi_n` of
`Gamma=SL_2(Z[1/2])`.  Pass to a subsequence on which its normalized traces
converge to a trace `tau` of `Gamma`.

Condition `(IMR38)` implies that the restricted trace `tau|_K` is amenable.
To see this without a closure assumption on amenable traces, decompose each
`alpha_n` into irreducibles and put mass

```text
(multiplicity of V) dim(V)/d_n
```

on the normalized trace of each irreducible summand `V`.  Condition
`(IMR38)` makes these probability measures tight on the disjoint union of
the compact unitary representation varieties of dimensions `1,2,...`.
After passing to a subsequence they converge to a probability measure
supported on finite-dimensional representations, and

```text
tau|_K(g)=integral tr_V(g)/dim(V) dmu(V).               (IMR40)
```

The GNS algebra of `(IMR40)` is a direct integral of finite-dimensional
factors and is therefore amenable.

Now use the decomposition `(IMR37)`.  A central-regular summand of positive
weight restricts to `K` as a central-regular trace.  To avoid any issue from
the scalar central twist, restrict once more to a torsion-free finite-index
free subgroup `F<K`.  It misses `Z(K)\setminus{1}`, and the restricted trace
is the ordinary regular trace `delta_e` of `F`.  The group `F` is a
nonabelian free group, so `L(F)` is nonamenable.  Thus a positive
central-regular weight would put a nonamenable direct summand in the GNS
algebra of `tau|_F`, whereas `tau|_F` is a restriction of the amenable trace
`tau|_K` and is amenable.  This is impossible.  Therefore every
central-regular weight in `(IMR37)` is zero.

It follows that `M_tau` is amenable.  The hyperfinite
Hilbert--Schmidt-stability criterion quoted in Section 6 corrects the
asymptotic representation `pi_n`, along a further subsequence, to honest
representations of `Gamma` with flexible `o(d_n)` padding.  Restricting the
corrected representations to the two modular vertices gives the required
compatible pair.  Applying the argument to every subsequence upgrades
subsequential correction to correction of the original sequence.

If `(IMR39)` failed on one vertex, a diagonal choice of `D` would give
`(IMR38)` along a subsequence, contradicting negativity.  The same argument
applies to the other vertex.  End proof.

The remaining central-regular problem is therefore a genuinely
large-irreducible phenomenon.  Its matrix models cannot be assembled, up to
negligible rank, from bounded-dimensional modular blocks.  This is the
appropriate starting point for a uniform high-dimensional restriction
analysis of the index-three Iwahori subgroup.
