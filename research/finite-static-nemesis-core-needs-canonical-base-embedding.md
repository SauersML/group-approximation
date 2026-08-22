---
rg: 2
id: finite-static-nemesis-core-needs-canonical-base-embedding
kind: claim
title: A finite static nemesis core works exactly after preserving the canonical base profile
distinct_from:
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that extracts a finite subcover of canonical base types; this records the extra hypothesis needed to apply that cover to canonical microstates of the final finite extension.
  finite-nemesis-subcover-has-a-uniform-existential-residual-gap: that supplies the finite family and uniform residual eta; this turns it into a finitely presented nonhyperlinear group only under canonical base-profile preservation.
  common-completion-amalgamates-compatible-bespoke-gadgets: that gives one exact representation retaining the mark; this shows why such a representation alone does not preserve the canonical base type.
---

Let `Gamma_0` be finitely presented, let `p in Q[Gamma_0]` have positive
canonical `L^2` norm, and fix `alpha<||p||_(2,tau_Gamma0)`.  Suppose finite
gadgets `E_1,...,E_r` have the uniform optimized residual gap `(FER3)` on the
separated canonical type space `K_alpha`.  Form the finitely presented group

```text
Gamma=<Gamma_0, auxiliaries of E_1,...,E_r |
                         all gadget relations>.        (FSC1)
```

If the natural map `Gamma_0->Gamma` is injective, then `Gamma` is
nonhyperlinear.  More generally it suffices that the canonical trace of
`Gamma` restrict to the canonical trace of `Gamma_0` on the finite windows
used by the residual theorem and that `p` retain norm at least `alpha`.

Indeed, canonical microstates of a hypothetical hyperlinear `Gamma` restrict
to canonical microstates of `Gamma_0`, while their auxiliary coordinates solve
all `E_j`.  This contradicts `(FER3)`.  Thus, conditional on an exhaustive
library and base embedding, compactness really does replace the infinite
self-aware library by one finite static core.  The construction is
non-effective: the selected indices, trace window, and tolerances need not be
computable.

## The missing quantifier in common-completion arguments

One exact representation of `(FSC1)` with `p!=0` does **not** imply the needed
base embedding or canonical-profile preservation.  For example, start with

```text
Gamma_0=F(a,b),          p=a-1,
```

and adjoin the relation `b=1`.  The quotient has representations with
`p!=0`, but its canonical trace restricts with `tau(b)=1`, whereas
`tau_Gamma0(b)=0`.  A finite cover proved only for canonical `F(a,b)` types
does not apply to this quotient profile.

Therefore the correct static-core hypotheses are:

```text
exhaustive robust finite subcover
+ simultaneous exact marked completion
+ canonical base-profile preservation.                (FSC2)
```

The second term ensures nontriviality of the mark; it does not imply the
third.  Britton embeddings, amalgam normal forms, or an explicit trace-profile
theorem can provide the third, but arbitrary auxiliary relators cannot.

The base must also already be finitely presented, or be passed through a
separate faithful finite-presentation compiler.  A finite subcover chooses
only finitely many **extension gadgets**; it does not choose finitely many base
relators defining the same canonical type space.  Truncating a recursively
presented base enlarges its type space and can introduce separated canonical
types which the original subcover never attacked.

## Capacity-prefix fence

A finite capacity prefix does not provide `(FSC2)` for free.  If its exact
relations put `M` pairwise orthogonal copies of one authenticated projection
`q` into the left regular algebra, then

```text
M tau_Gamma(q)<=1.                                    (FSC3)
```

Choosing fixed `M>1/tau_Gamma(q)` collapses `q` already in the group algebra,
so no exact marked completion can keep it nonzero.  Allowing approximate
finite matrices only adds a fixed-prefix error term and does not change the
zero-defect regular obstruction.  Distinct depth carriers avoid collapse only
by letting their canonical masses tend to zero, exactly the existing
capacity-prefix firewall.
