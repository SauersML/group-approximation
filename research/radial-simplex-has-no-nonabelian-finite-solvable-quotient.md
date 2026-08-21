---
rg: 2
id: radial-simplex-has-no-nonabelian-finite-solvable-quotient
kind: claim
title: The exact radial simplex group has no nonabelian finite solvable quotient
distinct_from:
  radial-parallelograms-kill-simplex-class-two: that proves every nilpotent quotient is abelian; this excludes all finite solvable quotients, including odd-primary self-reproducing commutator cores.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that analyzes finite central-sign predicate packets; this is an intrinsic theorem about the radial homogeneous solution group.
---

Assume the canonical radial-only presentation `(RGA2)` satisfies `(RGA4)`,
or more generally start with any homogeneous radial presentation whose
classical kernel is exactly the punctured affine simplex code.  Then every
finite solvable quotient of `Gamma_rad` is abelian.

Suppose otherwise and pass to a minimal nonabelian finite solvable quotient
`G`.  Every proper quotient of `G` is abelian.  A minimal normal subgroup
`A` is therefore

```text
A=G',
A=(F_p)^d,
H=G/A is an elementary abelian 2-group.               (RSQ1)
```

The `H`-module `A` is irreducible.  If `p=2`, every simple module of the
2-group `H` in characteristic two is trivial.  Thus `A` is central and `G`
has class at most two, contradicting
`radial-parallelograms-kill-simplex-class-two`.

Let `p` be odd.  Schur--Zassenhaus splits `G=A semidirect H`, and every
irreducible `F_p`-representation of the elementary abelian 2-group `H` is
one-dimensional.  Hence `H` acts on `A=F_p` through a sign character

```text
chi:H->{+1,-1}.                                       (RSQ2)
```

Write the image of the coordinate involution `q_x` as `(v_x,h_x)`.  The
involution equation gives

```text
chi(h_x)=+1 => v_x=0.                                 (RSQ3)
```

If two coordinates in one radial context both have sign `-1`, commutativity
of their lifts gives `v_x=v_y`.  The negative sign set is the support of the
affine codeword obtained by pulling `chi` back along the abelianization.
By `affine-sign-support-is-radially-connected`, all its `v_x` are one scalar
`v`.

Choose `c=v/2 in F_p`.  Conjugating the complement `H` by the translation
`c` changes its lift over `h` by `(1-chi(h))c`: this is zero on the positive
sign and equals `v` on the negative sign.  Equations `(RSQ2)--(RSQ3)` show
that **every** coordinate generator lies in this one conjugate complement.
They therefore generate an abelian group, contradicting the choice of `G`.

Consequently any finite nonabelian quotient of the radial simplex group is
nonsolvable and has a nonabelian finite simple composition factor.  In a
minimal such quotient the derived subgroup is a direct power of a
nonabelian finite simple group and the quotient by it is elementary abelian
2.  This explains, without computation, the absence of nonabelian `S_3` and
`S_4` models.  The separate claim
`radial-simplex-excludes-partitioned-involution-targets` now also rules out
simple quotients `PSL_2(2^r)`, including the smallest candidate `A5`.  Any
remaining semisimple core must have genuinely interacting involution
carriers.
