---
rg: 2
id: radial-simplex-excludes-partitioned-involution-targets
kind: claim
title: Radial simplex relations exclude A5 and all partitioned-involution targets
distinct_from:
  radial-simplex-has-no-nonabelian-finite-solvable-quotient: that excludes solvable finite images by a minimal-normal-module argument; this excludes a nonsolvable family, including A5, by decomposing coordinates among elementary-abelian involution carriers.
  radial-parallelograms-kill-simplex-class-two: that kills central commutator layers internal to the radial group; this directly constrains homomorphisms into groups whose involutions have disjoint elementary-abelian carriers.
---

Assume `n>=3` and that the canonical radial-only presentation `(RGA2)`
satisfies `(RGA4)`, so its binary radial-check kernel on `K^*` is exactly
the punctured affine simplex code

```text
C={x |-> a+ell(x): a in F_2, ell in K}.                 (PIT1)
```

Call a finite group `T` a **partitioned-involution target** if there is a
family `{E_t}` of elementary abelian 2-subgroups such that every nonidentity
involution of `T` lies in exactly one `E_t`, and two commuting nonidentity
involutions lie in the same `E_t`.  Then every homomorphism

```text
phi:Gamma_rad -> T                                      (PIT2)
```

has elementary abelian image.  In particular, `Gamma_rad` has no quotient
isomorphic to `A5`, or more generally to `PSL_2(2^r)` for any `r>=2`.

Indeed, color a coordinate `x` by `t` when `phi(q_x)` is a nonidentity
element of `E_t`.  Pairwise commutativity in each radial four-set implies
that all its nonidentity entries have one color.  For each color, retain its
entries and replace all other entries by zero.  The product relation in
each four-set says that the resulting `E_t`-valued word satisfies every
radial parity check.  By `(PIT1)`, it is an affine map

```text
F_t:K -> E_t,        F_t(x)=a_t+L_t(x),                 (PIT3)
```

restricted to `K^*`.  The supports of the nonzero maps `F_t` are pairwise
disjoint on `K^*`.

Two nonzero affine maps with disjoint supports on `K^*` force an extremal
case: both have rank one, their zero sets are complementary affine
hyperplanes, and their supports partition all of `K`.  Thus there can be at
most two nonempty colors.  If there are two, each map is one fixed
nonidentity involution times the indicator of one of two complementary
affine half-spaces.  Every coordinate of every radial four-set is then
nonidentity.  Local commutativity forces each four-set to lie wholly in one
half-space.  In particular its pair `{x,alpha x}` is monochromatic for every
`x in K^*`.  Since `alpha` generates `K^*`, the half-space indicator is
constant on `K^*`, contradicting that it has weight `2^(n-1)-1` or
`2^(n-1)`.

Hence only one color occurs and every coordinate image lies in one `E_t`.
The image in `(PIT2)` is elementary abelian.

For `T=PSL_2(2^r)`, every involution is a nontrivial unipotent and fixes a
unique point of the projective line.  The involutions fixing one point,
together with the identity, form its elementary abelian root subgroup of
order `2^r`; the centralizer of any nontrivial member is exactly that root
subgroup.  These root subgroups give the required partition.  The case
`r=2` is `PSL_2(4)=A5`.

Thus an exact nonabelian finite simple quotient, if one exists, must have
genuinely interacting involution carriers; the smallest candidate `A5` is
not merely absent in bounded searches but is ruled out uniformly.
