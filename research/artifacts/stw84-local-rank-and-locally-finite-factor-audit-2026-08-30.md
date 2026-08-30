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
and combines them into new exact and finite-dimensional classes.

## Lower mechanism: abelianization

The quotient `C*(G)->C*(G_ab)` forces

```text
dim_nuc(C*(G)) >= rank_Q(G_ab).
```

The equality `dim_nuc(C*(A))=rank_Q(A)` for countable abelian `A` follows from
Fourier transform, commutative nuclear dimension, and the Pontryagin formula
`dim(A_hat)=rank_Q(A)`.  Thus infinite-rank abelianization is an immediate
certificate of infinite nuclear dimension.

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

## Trust boundary

No statement here handles nonsplit locally-finite-by-abelian extensions or
general finite-Hirsch-length elementary amenable groups.  The direct-factor
proof uses the augmentation quotient and therefore does not extend formally
to a semidirect product.  The directed-union theorem needs a uniform stage
bound; it cannot turn unbounded finite-stage dimensions into a finite limit.
