---
rg: 2
id: fournier-facio-bounded-block-near-witness-impossible
kind: claim
title: A Fournier--Facio witness cannot have uniformly bounded charged blocks even modulo null mixing
invalidates:
  - fournier-facio-finite-band-block-near-witness
distinct_from:
  fournier-facio-charge-null-monomial-perturbations-impossible: That treats one-dimensional blocks and arbitrary charge-null perturbations; this permits genuine positive-charge mixing inside every block but bounds the block dimensions uniformly.
  fournier-facio-monomial-near-witness-impossible: That forgets scalar phases immediately; here fixed base blocks may carry arbitrary matrix-valued unitary cocycles whose diagonal coefficients can cancel.
  fournier-facio-compression-coset-charge-impossible: That uses a coarse factor over the compression cosets; this uses an arbitrary common block system and no map to `G/Gamma`.
---

**ESTABLISHED BOUNDED-DELOCALIZATION FENCE.**  Let `G` be the explicit
torsion-free Fournier--Facio group.  A Kahl--Schneider charged-basis witness
cannot, even after perturbations which vanish in the charged column
seminorm, have the following form.

Partition its orthonormal basis into finite blocks

```text
X=disjoint_union_(y in Y) X_y,          1<=|X_y|<=m,  (FBB1)
```

for one fixed `m`.  For every `g`, suppose there is a block-monomial unitary
`B_g` which maps `ell^2(X_y)` unitarily onto
`ell^2(X_(alpha_g y))` and satisfies

```text
phi_mu((pi(g)-B_g)^*(pi(g)-B_g))=0.                  (FBB2)
```

The internal block maps may be arbitrary elements of `U(|X_y|)`, may depend
on `g` and `y`, and need not satisfy a cocycle law exactly.

Charge-null removal first makes `B` itself an invariant essentially free
near representation.  Its block permutations `alpha_g` preserve the pushed
charge on `Y` and obey the group law charge-almost everywhere.  They must
also be essentially free.  Indeed, if `alpha_g` fixed positive block charge,
compactness of the finitely many groups `U(d)`, `d<=m`, gives a uniform
integer `N=N(m)` such that on every fixed block some power
`1<=n<=N` of its internal unitary is close to the identity.  A finite charge
pigeonhole then gives one `n` and positive charge on which `B_(g^n)` has a
large diagonal coefficient.  Since `G` is torsion-free, `g^n!=1`,
contradicting essential freeness.

Thus `alpha` would be an essentially free measure-preserving near action,
making `G` sofic, contrary to its established nonsoficity.

Consequently a positive non-Cartan witness cannot merely replace
phase-permutation fibers by matrix fibers of one fixed size.  Modulo the
charge-null ideal, it must either have unbounded block dimension on positive
charge or use genuinely overlapping delocalization which preserves no
common finite-block system.

Proof: `fournier-facio-bounded-block-near-no-go-proof`.
