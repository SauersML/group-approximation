# STW Problem LXXXIV: local rank and locally finite factor audit (2026-08-30)

## Status boundary

Problem LXXXIV asks for a characterization of countable amenable groups whose
group C*-algebras have finite nuclear dimension.  The 2026 publication of
Eckhardt--Wu proves a uniform finite bound for finitely generated virtually
polycyclic groups of fixed Hirsch length and leaves their finite-Hirsch-length
conjecture open for general finitely generated elementary amenable groups.
The primary-catalogue search for this audit found no later paper claiming the
full characterization.

This packet does not claim that conjecture.  It adds two permanence mechanisms
and combines them into new exact and finite-dimensional classes.  It also
records an exact controlled locally-finite-by-abelian extension class and a
quantitative finite-lamp wreath class beyond local virtual polycyclicity.

## Lower mechanism: abelianization

The quotient `C*(G)->C*(G_ab)` forces

```text
dim_nuc(C*(G)) >= rank_Q(G_ab).
```

The equality `dim_nuc(C*(A))=rank_Q(A)` for countable abelian `A` follows from
Fourier transform, commutative nuclear dimension, and the Pontryagin formula
`dim(A_hat)=rank_Q(A)`.  Thus infinite-rank abelianization is an immediate
certificate of infinite nuclear dimension.

## Nonabelian quotient obstruction

Eckhardt--Wu's wreath-product dichotomy says that, for `K` virtually
polycyclic and `H` finitely generated virtually nilpotent, `C*(K wr H)` has
finite nuclear dimension exactly when one of `K,H` is finite.  Quotient
permanence of nuclear dimension therefore gives a larger negative class:

```text
G ->> K wr H,  K and H infinite  =>  dim_nuc(C*(G))=infinity.
```

This applies to arbitrary countable amenable extensions of the indicated
wreath products.  It is not subsumed by the abelianization bound.  For every
restricted wreath product one has

```text
(K wr H)_ab = K_ab direct_sum H_ab,
```

because the coinvariants of `direct_sum_H K_ab` under the regular shift are
`K_ab`.  Taking both factors to be the infinite dihedral group produces a
finitely generated amenable group `D_infinity wr D_infinity` with
abelianization `(Z/2)^4` and infinite nuclear dimension.  Thus even rational
rank zero does not protect an amenable group algebra from infinite nuclear
dimension.

## Upper mechanism: subgroup exhaustions

For an increasing exhaustion of an amenable group, reduced subgroup algebras
embed faithfully and have dense union.  Full and reduced algebras agree, so
the group algebra is their inductive limit.  A uniform nuclear-dimension bound
at the finite stages passes to the limit.

Applying the 2025 exact computation for finitely generated virtually abelian
groups yields

```text
h_loc(G)=r<infinity  =>  dim_nuc(C*(G))<=r
```

for countable locally virtually abelian `G`.  If the abelianization has rank
`r`, the lower mechanism closes this to equality.

Using instead Eckhardt--Wu's uniform bound for virtually polycyclic groups of
fixed Hirsch length gives a broader finiteness theorem.  Every countable
locally virtually polycyclic group whose finitely generated subgroups have
uniformly bounded Hirsch length has group C*-algebra of finite nuclear
dimension.  The resulting bound depends only on that uniform local Hirsch
length.

## Finite-lamp wreath products over local nilpotent bases

Eckhardt--Wu's Theorem 5.14 gives the quantitative finite-stage estimate

```text
dim_nuc(C*(K wr V)) <= 2 * 9^d(V)
```

for finite `K` and finitely generated virtually nilpotent `V`, where `d(V)`
is polynomial-growth degree.  The Bass--Guivarc'h formula writes that degree
as `sum i*a_i` for the lower-central homogeneous ranks, while Hirsch length
is `sum a_i`.  The nilpotency class is at most the Hirsch length, so
`d(V)<=h(V)^2`.

Now let `H` be countable locally virtually nilpotent with all local Hirsch
lengths at most `r`.  An increasing finitely generated exhaustion `H_n` gives

```text
K wr H = union_n (K wr H_n).
```

The equality is literal: every wreath element has finite lamp support and one
acting coordinate.  Thus all stage dimensions are at most `2*9^(r^2)`, and
the subgroup-algebra inductive-limit theorem gives the same bound for
`C*(K wr H)`.  This combines an imported finite-stage theorem and growth
formula with a new uniformization and wreath-exhaustion argument.

For `H=Q`, the local Hirsch bound is one.  Hence `(Z/2) wr Q` has nuclear
dimension at most `18`.  It contains `(Z/2) wr Z`, so it is not locally
virtually polycyclic; this positive class is not subsumed by the earlier
polycyclic exhaustion node.

## Exact locally finite factor theorem

If `L` is countable locally finite, then `C*(L)` is AF.  For every countable
amenable `H`,

```text
C*(L times H)=C*(L) tensor C*(H).
```

The zero-dimensional tensor estimate gives the upper bound by
`dim_nuc(C*(H))`, while the augmentation character of `L` gives a quotient
back onto `C*(H)`.  Therefore adjoining `L` changes no nuclear dimension.
In particular,

```text
dim_nuc(C*(L times A))=rank_Q(A)
```

for every countable abelian `A`, including infinite rank.  Taking `L` to be an
infinite direct sum of nonabelian finite groups produces non-virtually-abelian
examples with arbitrarily complicated finite subgroup structure.

## Kernel-finite locally-finite-by-abelian extensions

Consider an exact sequence

```text
1 -> L -> G -> A -> 1
```

with `L` countable locally finite and `A` countable abelian.  If every
finitely generated subgroup `H` of `G` has finite intersection with `L`, then
each `H` is finite-by-finitely-generated-abelian, hence virtually abelian,
and its Hirsch length is at most `rank_Q(A)`.  The quotient also shows that
`rank_Q(G_ab)=rank_Q(A)`.  The local virtually abelian upper mechanism and
the abelianization lower mechanism therefore give the exact formula

```text
dim_nuc(C*(G))=rank_Q(A),
```

including infinite rank.  This argument permits nonsplit extensions.

For `G=L rtimes A`, a checkable sufficient condition is that the subgroup
generated by the orbit of each finite subset of `L` under each finitely
generated subgroup of `A` is finite.  For example, let `Z` rotate disjoint
finite coordinate blocks of unbounded lengths in `direct_sum Z/2`.  The
resulting semidirect product is not virtually abelian and has nuclear
dimension exactly one.

The imported analytic input remains the 2025 exact computation for finitely
generated virtually abelian groups and upper semicontinuity of nuclear
dimension under inductive limits.  The new input is the finite-kernel
reduction at every finitely generated stage, the quotient-rank identification,
and the finite-orbit-hull semidirect criterion.  No general crossed-product
dimension estimate is used.

## Trust boundary

No statement here handles arbitrary locally-finite-by-abelian extensions or
general finite-Hirsch-length elementary amenable groups.  The controlled
extension theorem requires finite kernel intersection at every finitely
generated stage.  The finite-lamp theorem covers regular wreath shifts over
uniformly locally virtually nilpotent acting groups, but not arbitrary
locally finite kernels or actions.  The direct-factor proof uses the
augmentation quotient and therefore does not extend formally to an arbitrary
semidirect product.  The directed-union theorem needs a uniform stage bound;
it cannot turn unbounded finite-stage dimensions into a finite limit.  The
wreath-product negative result is a one-way obstruction: no claim is made
that groups without one of the displayed wreath quotients have finite nuclear
dimension.
