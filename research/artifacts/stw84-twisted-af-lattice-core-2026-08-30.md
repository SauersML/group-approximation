# Audit: unrestricted locally-finite-by-abelian reduction

Date: 2026-08-30

## Unconditional conclusions

For `1->L->G->A->1` with `L` locally finite and `A` finite-rank abelian:

1. The inverse image of `tor(A)` is locally finite.
2. Rank zero therefore forces `G` itself to be locally finite and
   `dim_nuc(C*(G))=0`, without any kernel-finite assumption.
3. After absorbing torsion, `G` is an increasing union of extensions of one
   fixed locally finite group by free lattices of rank at most `rank_Q(A)`.
4. Every such stage algebra is a group-unitary twisted crossed product of
   the AF algebra `C*(K)` by that lattice.
5. In rank one the twist disappears at every cyclic stage, reducing the
   problem to arbitrary automorphisms of countable locally finite groups.
6. In the cyclic semidirect case, kernel-finiteness is equivalent to an
   exhaustion of the kernel by finite invariant subgroups.  Thus the exact
   residual group-theoretic obstruction is failure of invariant finite
   exhaustion, not a hidden cocycle.

## Checks

- Extension closure of local finiteness is used only when both kernel and
  quotient are locally finite.  For a finitely generated subgroup, its
  kernel has finite index and is therefore finitely generated; local
  finiteness then makes it finite.
- A finitely generated subgroup of a torsion-free abelian group is free
  abelian, and its rank is bounded by the ambient rational rank.
- The Busby--Smith cocycle lies in the group `K`, not merely in an abstract
  multiplier algebra, and its two identities are exactly associativity in
  the extension.
- An extension by `Z` splits by lifting one generator.  No analogous claim
  is made for `Z^q`, `q>=2`.
- The lower bound uses only that the image of the locally finite kernel in
  the abelianization is torsion; kernel-finiteness is irrelevant.

## Sharp obstruction

The two-generated group

```text
Alt_fin(Z) rtimes_shift Z
```

is the smallest concrete stress test found.  Its locally finite kernel is
the normal closure of one 3-cycle, but shifted copies overlap and do not
commute.  The kernel is infinite simple, so it has no nontrivial direct-sum
lamp decomposition.  This rules out both finite-kernel exhaustion and the
homogeneous tensor-coordinate proof used for permutation wreath products.

Analytically, the missing theorem is a factor-uniform nuclear-dimension
bound for group-origin automorphisms of group AF algebras.  Existing
homeomorphism bounds concern commutative coefficient algebras, and the
permutation-wreath proof uses a special tensor decomposition.  Neither
applies to this example.  No claim of finite nuclear dimension in positive
rank is made here.
