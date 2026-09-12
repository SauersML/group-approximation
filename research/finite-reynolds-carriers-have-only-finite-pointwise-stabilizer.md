---
rg: 2
id: finite-reynolds-carriers-have-only-finite-pointwise-stabilizer
kind: claim
title: A finite Reynolds carrier has only a finite pointwise stabilizer
distinct_from:
  left-rank-amplification-is-not-a-fixed-sector: That distinguishes an invariant positive-density left ideal from a pointwise-fixed adjoint sector in matrices; this gives the algebraic finite-support stabilizer theorem and an explicit proper self-copy Reynolds shadow.
  finite-inclusion-is-free-self-compressor-quotient: That realizes arbitrary finite parent/child quotient shadows of a proper free self-copy; this proves why a signed Reynolds projection from such a shadow still cannot be the required pointwise-fixed payload carrier without conditional kernel annihilation.
  shared-bcs-carrier-localizes-free-compressor-quotient: That asks for matrix-only payload localization of a quotient action; this rules out replacing that localization by ordinary finite-subgroup membership or normalizer relations.
---

**ESTABLISHED FIXEDNESS DICHOTOMY.**  Let `G` be a group and let
`0!=z in C[G]` have finite support.  Its pointwise left stabilizer

```text
Stab_L(z)={g in G: lambda(g)z=z}                       (FRC1)
```

is finite.  Indeed `g supp(z)=supp(z)`, and the induced action of
`Stab_L(z)` on the finite set `supp(z)` is faithful: left multiplication on
`G` is free, so an element fixing one support point is the identity.

For a finite subgroup `K<G` and a one-dimensional character `chi`, put

```text
e_(K,chi)=|K|^(-1) sum_(k in K) conjugate(chi(k)) k.   (FRC2)
```

The sharper calculation is

```text
lambda(g)e_(K,chi)=e_(K,chi)
 iff g in K and chi(g)=1.                              (FRC3)
```

The support of the left side is `gK`, so equality first forces `g in K`;
the usual character-idempotent identity then gives the second clause.
Products and finite sums of signed Reynolds atoms are still finite-support
group-algebra elements, so `(FRC1)` applies to every finite packet/selector
projection used by the shared BCS front end.

Consequently, if `H` is infinite and `alpha:H->H` is injective, no nonzero
finite Reynolds projection can be pointwise fixed by `alpha(H)` in the
canonical regular representation.  A finite list of ordinary group
relations has only two direct ways to interact with such a projection:

1. putting the child generators in its finite character kernel, which makes
   the generated child image finite and is incompatible with an injective
   infinite self-copy; or
2. making the child normalize the finite packet and its character, which
   gives only

   ```text
   lambda(alpha(h)) e lambda(alpha(h))^*=e.             (FRC4)
   ```

Clause `(FRC4)` says that the physical projection and its positive-rank left
ideal are invariant.  It does not say that the adjoint action is the identity
on that left ideal.  Thus it falls exactly under
`left-rank-amplification-is-not-a-fixed-sector`.

The distinction already occurs in the smallest proper self-copy.  Let

```text
H=F(x,y),             alpha(x)=x^2, alpha(y)=y^2,
P=<r,s | r^2=s^2=[r,s]=1> ~= C_2^2.                   (FRC5)
```

Let `x` exchange `r` and `s`, and let `y` centralize `P`.  Then `H` embeds in
`P rtimes H`, `alpha` is injective and proper, and `alpha(H)` centralizes
`P`.  If `e` is the character atom with signs `chi(r)=-1,chi(s)=+1`, then

```text
Ad(alpha(H))(e)=e,
e'=Ad(x)(e) is orthogonal to e.                        (FRC6)
```

The ascending HNN extension

```text
<P rtimes H,t | t x t^(-1)=x^2, t y t^(-1)=y^2>      (FRC7)
```

is a finite ordinary presentation and contains the base by Britton's lemma.
It therefore supplies a completely explicit signed-Reynolds **quotient
shadow** of the desired parent/child motion.  On the regular `P` packet,

```text
tau(e)=1/4,             ||e-e'||_2^2=1/2.              (FRC8)
```

If `A` is a shared-BCS forbidden selector atom commuting with this packet,
then `F=Ae` is child-normalized and

```text
F Ad(x)(F)=0,           ||F-Ad(x)(F)||_2^2=2tau(F).    (FRC9)
```

In the exact perfect tracial BCS model `A=0`, so `(FRC9)` is vacuous.  This
shows that finite generation, a proper self-copy, signed Reynolds atoms, and
a full parent displacement are all algebraically available.

What is not available is the load-bearing pointwise fixed sector.  The
conjugation module `C[P]` in `(FRC6)` has fixed finite dimension.  In a large
packet-covariant representation, Schur decomposition has the form

```text
rho(h)=pi(theta(h)) tensor W(h).                       (FRC10)
```

Although the packet factor of `alpha(H)` is trivial, the multiplicity action
`W(alpha(H))` is arbitrary.  The child-fixed adjoint part is therefore
`C[P] tensor Comm(W(alpha(H)))`, whose normalized density can vanish.  The
HNN relation forces the complete parent and child actions to be conjugate and
allows precisely this multiplicity compensation.

To make the payload product `Ae` pointwise fixed one must impose, for finite
generators `s` of `H`, the corner equations

```text
(alpha(s)-1)Ae=0.                                      (FRC11)
```

These are additive, payload-conditional coefficient relations, not ordinary
finite-subgroup membership or normalizer relations.  They are exactly the
conditional kernel-annihilation face in
`shared-bcs-carrier-localizes-free-compressor-quotient`.  If imposed
globally, `(FRC1)--(FRC3)` collapse the infinite child or erase the carrier;
if only packet covariance is imposed, `(FRC10)` retains the multiplicity
gauge.  Hence signed Reynolds character projections plus a finite generating
set do not bypass the nonlinear localization gate.

DERIVATION
finite-support-stabilizer-and-free-square-shadow-proof
