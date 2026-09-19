---
rg: 2
id: stw84-almost-free-permutation-limit-proof
kind: route
title: Regroup finite-stabilizer fibers into free Bernoulli shifts and exhaust all lamps
target: stw84-almost-free-permutation-wreath-bound
requires:
  - stw84-directed-union-uniform-bound
artifacts:
  - research/artifacts/stw84-almost-free-permutation-wreath-2026-08-30.md
---

We first prove the finite-stage estimate needed here.  Let `F` be finite,
let `V` be a finitely generated abelian group of rational rank `q`, and let
`V` act on a countable set `T` with finite point stabilizers.  Put
`D=C*(F)` and write

`D=direct_sum_(i=1)^m M_(n_i)`.

The canonical finite-support tensor identification and the permutation
action give

`C*(F^(direct_sum T) rtimes V)=D^(tensor T) rtimes V`.    `(APW2a)`

The central spectrum of the coefficient algebra is the zero-dimensional
compact space

`Omega={1,...,m}^T`.

For `x in Omega`, its fiber is

`D_x=tensor_(t in T) M_(n_(x(t)))`.                       `(APW2)`

Apply Eckhardt--Wu, arXiv:2408.07223, Theorem 5.1 and their estimates
`(5.1)` to this `V-Omega-C*`-algebra.  It remains only to bound, uniformly
in `x` and `N<=V_x`, the nuclear dimension of `D_x rtimes N`.

Choose a torsion-free normal subgroup `K` of finite index in `V`, and put
`K_N=N intersection K`.  Since every point stabilizer in `T` is finite,
the torsion-free group `K_N` acts freely on `T`.  Choose representatives
`R` for its orbits.  Since `x` is `N`-invariant, it is constant on every
`K_N`-orbit, and regrouping the factors in `(APW2)` gives a
`K_N`-equivariant isomorphism

`D_x = B^(tensor K_N)`,

where

`B=tensor_(t in R) M_(n_(x(t)))`.

The algebra `B` is either scalar, a non-scalar full matrix algebra, or a UHF
algebra.  The scalar possibility must be separated.

If `B=C`, then `(APW2)` itself is scalar, the `N`-action is trivial, and

`D_x rtimes N=C*(N)`.

Since `N` is finitely generated abelian,

`dim_nuc(C*(N))=rank_Q(N)<=q`.                            `(APW3s)`

If `B!=C`, then `B` is simple and monotracial with nuclear dimension zero.
When `K_N` is nontrivial, Eckhardt--Wu's Bernoulli-shift argument (their
Example 4.9) shows that `B^(tensor K_N) rtimes K_N` is simple, monotracial,
and has nuclear dimension at most one: torsion-freeness makes every
nonidentity shift strongly outer.  If `K_N` is trivial, the same starting
algebra is just the matrix or UHF algebra `B`.

Continue in the case `B!=C`.  The quotient `N/K_N` is finite.  The standard
iterated-crossed-product description expresses `D_x rtimes N` as a twisted
finite-group crossed product of `D_x rtimes K_N`.  Eckhardt--Wu Lemma 5.13
makes it a finite direct sum of simple algebras.  If the first crossed
product is finite
dimensional, so is the result.  Otherwise it is `Z`-stable, and Sato's
finite-group permanence together with the nuclear-dimension-one theorem
for simple `Z`-stable nuclear algebras gives

`dim_nuc(D_x rtimes N)<=1`.                              `(APW3n)`

Combining `(APW3s)` and `(APW3n)`, the stabilizer-fiber parameter in
Eckhardt--Wu Theorem 5.1 is at most `max{1,q}`.  Since `Omega` is
zero-dimensional and the polynomial-growth degree of `V` is `q`, their
estimates `(5.1)` give

`dim_nuc(C*(F^(direct_sum T) rtimes V))+1
 <= 9^q * (max{1,q}+1)`.                                `(APW4)`

For `q>=1`, the right side is `(q+1)9^q`.  For `q=0`, the group in
`(APW2a)` is locally finite, so its group algebra has nuclear dimension
zero; this is sharper than `(APW4)`.

We now pass to the countable groups in the claim.  Choose increasing finite
subgroups `L_n` exhausting `L`, increasing finitely generated subgroups
`A_n` exhausting `A`, and an enumeration `S={s_1,s_2,...}`.  Let

`S_n=A_n {s_1,...,s_n}`

and

`G_n=(direct_sum_(S_n) L_n) rtimes A_n`.

After enlarging indices if necessary, these are increasing subgroups and
their union is `G`: every group element uses one actor, finitely many lamp
sites, and finitely many lamp values.  Stabilizers for `A_n` on `S_n` remain
finite.  Every finitely generated abelian `A_n` has polynomial-growth degree

`q_n=rank_Q(A_n)<=r`.

For `r>=1`, equation `(APW4)` therefore bounds every
`dim_nuc(C*(G_n))` by `(r+1)9^r-1`; stages of rank zero have dimension zero.
The group `G` is amenable, and
`stw84-directed-union-uniform-bound` passes this estimate to `C*(G)`, proving
`(APW1)`.

If `r=0`, the abelian group `A` is locally finite.  The base is locally
finite, and an extension of a locally finite group by a locally finite group
is locally finite.  Hence `C*(G)` is AF and has nuclear dimension zero.

In the displayed example, translation by the infinite-order generator on
each `A/<e_n>`-orbit produces infinitely many distinct conjugates of one
nontrivial lamp.  They generate an infinite subgroup of the lamp kernel
inside a two-generated subgroup, which verifies failure of the kernel-finite
hypothesis.
