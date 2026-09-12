---
rg: 2
id: stw95-c0-block-tensor-purity-proof
kind: route
title: Distribute the minimal tensor product over central c0 blocks and assemble purity
target: stw95-central-block-closure-of-tensor-pure-seeds
requires:
  - stw95-one-zstable-factor-forces-pure-product
  - stw95-purity-passes-to-sequential-inductive-limits
  - stw95-cu-z-tensor-counterexample
  - complete-selflessness-tensor-permanence
  - robert-tracial-selfless-regularity
  - thiel-stable-rank-one-ranks-close-purity-with-comparison
artifacts:
  - research/artifacts/stw95-central-block-tensor-purity-audit-2026-08-30.md
---

First note that a finite direct sum of pure C-star algebras is pure.  Indeed,
its Cuntz semigroup is the finite direct sum of the component Cuntz
semigroups, and both almost unperforation and almost divisibility hold
coordinatewise.  A countable `c_0`-sum is the sequential inductive limit of
its finite partial sums under the corner inclusions.  Therefore
`stw95-purity-passes-to-sequential-inductive-limits` shows that a finite or
countable `c_0`-sum of pure algebras is pure.

Every block `A_i` and `B_j` is pure: this is assumed for a copy of `P`, and
follows from Z-stability for every other block.  Hence `A` and `B` are pure.

For each pair `(i,j)`, the block product `A_i tensor_min B_j` is pure.  If
both blocks are copies of `P`, this is the seed hypothesis.  Otherwise at
least one block is Z-stable, so
`stw95-one-zstable-factor-forces-pure-product` makes the product Z-stable and
hence pure.  Minimal tensor products distribute over `c_0`-direct sums,
without an exactness hypothesis:

```text
(direct_sum_i A_i) tensor_min (direct_sum_j B_j)
  ~= direct_sum_((i,j) in I times J) (A_i tensor_min B_j).       (CB1)
```

For completeness, (CB1) follows first for algebraic finite-support tensors;
faithful direct-sum representations show that the spatial norm on each
finite central rectangle is the maximum of the block norms, and completion
is precisely the `c_0`-sum on the right.  The right side of (CB1) is a finite
or countable `c_0`-sum of pure blocks, so the first paragraph proves that it
is pure.

For the concrete seed put `P=C*_r(F_2)`.  The established node
`stw95-cu-z-tensor-counterexample` records

```text
Cu(P)=Cu(Z).
```

Here is the promised derivation of the other seed hypothesis.  The reduced
free-group algebra is exact and selfless, so tensor selflessness makes
`P tensor_min P` selfless.  Robert's tracial selfless theorem then gives
stable rank one, strict comparison, and a unique normalized quasitrace.
The imported stable-rank-one rank theorem realizes every lower
semicontinuous affine rank.  Together with strict comparison, rank
realization gives almost divisibility; strict comparison also gives almost
unperforation.  Thus `P tensor_min P` is pure.
The extra compact classes detected by `stw95-cu-z-tensor-counterexample`
show only that its Cuntz semigroup is not `Cu(Z)`; they do not obstruct
purity.  Thus `P` meets both seed hypotheses.

Finally let `N` be unital, separable, and nonexact and put `R=N tensor_min Z`.
Associativity and `Z tensor_min Z ~= Z` make `R` Z-stable.  It remains
nonexact: `N` embeds as `N tensor 1_Z`, while exactness passes to C-star
subalgebras.  Hence `A=P direct_sum R` is nonexact.  It is nonsimple and is
pure by the direct-sum argument.  It is not Z-stable, since Z-stability
passes to quotients and its quotient `P` is not Z-stable: the unique trace
on `P` has the full, non-McDuff GNS factor `L(F_2)`, whereas a Z-stable
tracial C-star algebra has McDuff tracial GNS closure.  Applying (CB1) to the
two-block decomposition proves that `A tensor_min A` is pure.

**Trust boundary.**  The proof uses only Cuntz-semigroup direct sums,
sequential permanence of purity, distribution of the minimal tensor product
over `c_0`-sums, the one-Z-stable-factor theorem, and the already established
free-group seed.  It does not use an abstract-to-concrete Cu tensor
isomorphism for the assembled factors and does not touch the compact-witness
counterexample corridor.
