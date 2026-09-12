---
rg: 2
id: tensor-separated-holonomy-controller-is-circular
kind: claim
title: A tensor-separated noncommuting holonomy controller merely outsources hyperlinearity
distinct_from:
  one-holonomy-word-controllers-are-free-or-torsion: that completely classifies one common cyclic holonomy; this treats arbitrarily many noncommuting holonomies when they occupy an independent tensor factor.
  exact-fd-wandering-reflection-promotion-can-remain-sofic: that gives one sterile sofic actuator counterexample; this proves the general microstate tensor-completion statement for every hyperlinear holonomy group.
  fixed-holonomy-on-overlap-pays-relator-energy: that charges a fixed nontrivial finite factor which cannot be removed by multiplicity; here the entire controller lies in the free multiplicity factor and therefore has no fixed finite charge.
---

**ESTABLISHED CONDITIONAL NO-GO.**  Let a proposed finite verifier controller
have a selected losing carrier `E` and suppose that, after its fixed packet is
exactified, every controller letter restricts in the tensor-separated form

```text
u_l|_E = F_l tensor pi(h_l),                             (TSH1)
```

where the `F_l` belong to one fixed finite packet and the `h_l` belong to a
fixed finitely presented holonomy group `H`.  Assume the controller relators
on `E` are precisely fixed packet identities tensored with relators of `H`.

If `H` is hyperlinear, this controller has arbitrarily accurate finite matrix
completions at **every** positive value of `tau(E)`.  Indeed, amplify the base
verifier model and tensor the losing multiplicity space with canonical-trace
microstates of `H`.  Normalized Hilbert--Schmidt defects of the controller are
exactly the corresponding defects of the `H` microstate, while tensor
amplification leaves `tau(E)` unchanged.  Mixed finite word moments factor as
the fixed packet trace times the canonical moments of `H`.

Consequently no inequality

```text
c tau(E) <= sum_(rho in R_controller) ||rho-1||_2^2       (TSH2)
```

with `c>0` can follow from a tensor-separated hyperlinear controller.

If `H` is nonhyperlinear and embeds as the asserted holonomy subgroup, then
the controller has already imported a nonhyperlinear group and no longer
constitutes a construction of one from the BCS verifier.  Hence allowing
several noncommuting return gauges does not by itself escape the one-holonomy
no-go: the gauges must be coupled non-tensorially to the verifier payload or
to a carrier which depends on their action.

