---
rg: 2
id: maslov-generator-complete-order-model-is-llp-strength
kind: claim
title: A liftable complete-order model of the Maslov generator system is already full-LLP strength
artifacts:
  - research/artifacts/maslov-generator-operator-system-lp-sources-2026-08-22.md
distinct_from:
  braid-prefix-label-space-has-no-ucp-expectation: that rules out one linear label-averaging projection on the six-prefix braid Gram space; this applies to every liftable complete-order model of the entire canonical generator system.
  fixed-chevalley-prefix-grams-give-only-tracial-positivity: that locates the failure at growing matrix levels; this explains why standard finite-dimensional coproduct, null-quotient, and retract constructions cannot bypass that failure.
  sp4-mod3-twisted-fibres-have-llp: that is the still-open full-algebra property; this proves that the proposed generic finite operator-system models would already imply it, not that LLP holds.
---

**ESTABLISHED.** Let

```text
A_alpha=C^*(Sp_4(Z);alpha),
S_alpha=span{1,u_s,u_s^*:s in Sigma} subset A_alpha,     (MCO1)
```

where `Sigma` is any finite root/Weyl generating set and `alpha` is either
nontrivial mod-three Deligne multiplier.

1. `S_alpha` contains enough unitaries in `A_alpha`; in particular
   `C_e^*(S_alpha)=A_alpha`.
2. If `S_alpha` has the operator-system lifting property, then `A_alpha` has
   LLP.
3. Consequently, each of the following proposed finite complete-order models
   is already a proof of the stronger open claim
   `sp4-mod3-twisted-fibres-have-llp`:

   - a complete-order realization of `S_alpha` as a null-subspace quotient of
     a finite-dimensional lifting-property system;
   - a realization as a ucp retract of such a system; or
   - a chordal/coproduct construction which supplies either of those two
     structures.

There is also an unconditional envelope obstruction to the most direct root
model.  Let `T` be a coproduct of rank-one cyclic/root operator systems, or a
clique-tree amalgam of such systems whose clique envelopes have compatible
characters.  Then `C_e^*(T)` is the corresponding unital (amalgamated) free
product and has a character.  The nontrivial Maslov fibre `A_alpha` has no
character.  Therefore

```text
T is not completely order isomorphic to S_alpha.          (MCO2)
```

Thus neither the free root coproduct nor a character-compatible chordal
completion captures the canonical generator matrix order.  A quotient can
capture it only through a genuinely non-null/nonretract kernel unless one
also proves full LLP.  That non-null positive kernel is exactly where the
mixed Chevalley/Maslov information resides.

This does not refute the tracially restricted lifting target.  It separates
that target sharply from standard operator-system LP technology: a successful
proof must exploit that the quotient is the tracial matrix ultraproduct and
that the map is a star homomorphism.  Any construction valid for arbitrary
ucp maps into arbitrary C-star quotients has crossed back to full LLP.

