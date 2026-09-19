---
rg: 2
id: finite-residual-universal-linear-reflection-proof
kind: route
title: Identify the finite quotients and apply Grothendieck's representation theorem
target: finite-residual-quotients-are-universal-linear-reflections
requires:
  - grothendieck-profinite-representation-equivalence
---

Assume first that `N <= R_fin(Gamma)`.  Every homomorphism from `Gamma` to a
finite group kills `N`, hence factors uniquely through `q`.  Conversely every
finite quotient of `Gamma/N` pulls back along `q`.  The two groups therefore
have the same cofiltered system of finite quotients, with the same transition
maps, so `q` induces an isomorphism of profinite completions.

Grothendieck's theorem applies to homomorphisms of finitely generated groups;
it does not require the groups themselves to be residually finite.  It says
that an isomorphism on profinite completions is equivalent, for every nonzero
commutative ring `A`, to the equivalence `(ULR1)` on finitely presented
`A`-modules with action.  This proves `(1)=>(2)=>(3)`.

Conversely, suppose `(ULR1)` holds.  Let `f:Gamma->F` be a finite quotient.
The left regular permutation action embeds `F` in `GL_{|F|}(Z)`, giving an
object of `Rep_Z^fp(Gamma)`.  Essential surjectivity says that this action
factors through `Gamma/N`; hence `N<=ker(f)`.  Intersecting over all finite
quotients gives `N<=R_fin(Gamma)`.  This proves `(3)=>(1)`.

Since `q` is surjective, restriction is fully faithful without any theorem:
a linear map is `Gamma`-equivariant exactly when it is `Gamma/N`-equivariant.
The equivalence therefore acts as the identity on underlying modules and
intertwiners.  Its compatibility with scalar extension, sums, tensor products,
and exact sequences is literal.

Taking `N=R_fin(Gamma)` proves that every finitely presented linear action
kills the finite residual.  The reverse containment in `(ULR2)` follows from
the integral regular permutation representation of each finite quotient.
