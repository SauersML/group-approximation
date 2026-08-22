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

`effective-twisted-factor-existence-is-equivalent-to-fp-nonhyperlinearity`
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
