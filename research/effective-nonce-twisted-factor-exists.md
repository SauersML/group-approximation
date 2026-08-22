---
rg: 2
id: effective-nonce-twisted-factor-exists
kind: claim
title: An effective finitely generated non-CE twisted group factor exists
distinct_from:
  non-ce-twisted-group-factor-exists: that claim permits an arbitrary countable projective quotient and arbitrary noneffective scalar kernel; this claim requires a finite generating set and recursively enumerable kernel so Higman embedding applies.
---

There are a finite-rank free group `F`, a recursively enumerable normally
generated subgroup `N normal F`, and a scalar multiplier `omega` on `F/N`
such that `L_omega(F/N)` is not Connes embeddable.

`effective-twisted-factor-existence-is-fp-nonhyperlinearity`
shows that this is equivalent to the existence of a finitely presented
nonhyperlinear group.  Thus the effective gate is not a weaker intermediate
compiler target.  Its r.e.-kernel condition is precisely the Higman-level
effectivity content of the final problem; the multiplier itself need not be
computable because the forward relation-centralizing group `F/[F,N]` depends
only on `N`.

## Attempts

- Recognize the CDI/Manzoor factor from finitely many projective-word
  generators.  A projective basis is not known, and even after finding one
  the scalar-word kernel must be recursively enumerable rather than merely
  well-defined inside the factor.
- Compile the fixed non-CE BCS trace into a finite projective presentation.
  Existing phase packets leave exact forbidden selector sectors and so do not
  transfer the finite-dimensional energy gap.
- It would already suffice to find a finite-index projective core rather
  than a projective basis for the whole BCS factor, by
  `finite-index-projective-core-yields-central-witness`.
  The explicit context and fixed packet algebras do not provide one: they
  are finite-dimensional and therefore have infinite Jones index in the
  non-CE factor.  The native global BCS generators still force affine
  context support.  No current MIP-star/BCS construction supplies the
  missing diffuse finite-index projective core.
- The primary-source audit
  `primary-nonce-sources-miss-finite-index-core` finds no hidden instance of
  that weaker target.  MIP-star and BCS give correlation/star-algebra data;
  the IRS construction gives only inclusions into relation factors; and the
  CDI endpoint is a crossed product by an infinite group with an
  operator-valued cocycle and infinite-index native cores.  Any positive
  result therefore needs a new subfactor extraction theorem, not a rereading
  of the published decompositions.
- Merely use computability of the BCS character and centralize its scalar GNS
  kernel.  `computable-projective-kernel-has-reversed-enumerability` proves
  that computable coefficients enumerate the **complement** of that kernel;
  an r.e. scalar kernel would already be decidable.  More decisively, even a
  decidable scalar kernel does not retain the bad trace: mixing the BCS trace
  with the regular trace makes the scalar kernel equal to the ordinary RACG
  relator kernel while the selected canonical sector remains the CE regular
  RACG factor.  A recursive diagonal or free-label scheme must therefore
  prove a new non-CE retention theorem inside the projective-regular generated
  algebra, not merely in its ambient tensor product.
