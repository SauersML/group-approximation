---
rg: 2
id: central-character-rigid-sector-forbids-relator-quotients
kind: claim
title: A unique faithful central-character sector admits no nontrivial tracial group-relator quotient
distinct_from:
  finite-normal-signed-bcs-quotient-collapses-to-twisted-factor: that identifies the GNS factor of an arbitrary tracial C-star quotient; this additionally proves that a quotient obtained by imposing group relations has trivial group kernel.
  character-rigid-signed-bcs-quotient: that asks for a generating representation in a non-CE BCS algebra; this gives the exact projective-faithfulness and presentation-quotient constraints on such a representation.
---

Let `Gamma` be a countable group, let `C <= Z(Gamma)` be finite, and let
`eta:C -> T` be a faithful character.  Put

```text
p_eta=|C|^(-1) sum_(c in C) overline(eta(c)) c,
A_eta=p_eta C*(Gamma),
tau_eta(p_eta g)=eta(g) tau_eta(p_eta)  for g in C,
                    =0                for g notin C,       (UCR1)
```

where the displayed formula is understood after normalizing the corner
trace.  Suppose `tau_eta` is the unique tracial state of `A_eta`.

If `Phi:A_eta -> B` is a unital surjective `*`-homomorphism and `B` has a
tracial state, define

```text
u_g=Phi(p_eta g) in U(B).                                (UCR2)
```

Then:

1. every trace `sigma` on `B` satisfies `sigma Phi=tau_eta`;
2. the projective kernel of `g |-> u_g` is exactly `C`;
3. the ordinary kernel of `g |-> u_g` is contained in `ker eta={1}`.

In particular, suppose the quotient is obtained by adding group relators:
there is a normal subgroup `N normal Gamma` such that every `n in N` is sent
to the corner unit.  Then `N={1}`.  Thus no nontrivial finite or infinite
list of added group relations can install the quotient while retaining a
tracial faithful-`eta` sector.

This does not forbid an analytic C-star quotient.  It says precisely what
such a quotient must be: its ideal is contained in the GNS kernel of
`tau_eta`, its generating group representation is faithful modulo the
already selected center, and its tracial GNS algebra is the original twisted
regular factor.  Consequently a successful non-CE BCS quotient of this kind
has not converted a presentation quotient into a witness; it has directly
proved that the already present twisted regular factor is non-CE.

The proof is `central-sector-relator-kernel-proof`.

### Explicit Deligne application

For the Deligne triple cover `E_3` of `Sp_4(Z)`, the center is cyclic of
order six.  Fix the extension `eta` of a nontrivial character of the
order-three covering kernel which is faithful on this order-six center.
By `deligne-maslov-sector-traces-are-central-regular`, the full
`eta`-sector has a unique trace; finite-dimensional representations in the
nontrivial covering sector are absent.  Hence the theorem applies to this
explicit finitely presented character-rigid group.

This makes `E_3` the cleanest known source corner for the quotient route,
but also fences the naive compiler: adding BCS word relations to the group
presentation either adds no relation at all or destroys every tracial state
of the faithful marked sector.  The only remaining map is a genuinely
analytic surjection

```text
p_eta C*(E_3) -> B                                      (UCR3)
```

whose kernel lies in the full-to-reduced GNS kernel.  Constructing `(UCR3)`
is already equivalent, at von Neumann level, to proving the corresponding
Deligne twisted regular factor non-Connes-embeddable.

