---
rg: 2
id: state-support-corner-exactifies-near-representation
kind: claim
title: The bidual support corner exactifies every invariant free near-state
distinct_from:
  normal-state-free-near-representation-forces-factorization: that puts the support projection inside B(H), so the genuine corner remains a Hilbert subrepresentation carrying an invariant normal state on all its bounded operators; this works in B(H)** for an arbitrary state and does not preserve that amenability conclusion.
  singular-near-defects-vanish-on-canonical-genuine-sector: that constructs the regular cyclic GNS sector and observes that defect vectors vanish there; this identifies the intrinsic support corner in the bidual and proves that the whole compressed group law is exact.
  invariant-free-near-state-is-amenable-regular-cover: that exactifies after quotienting the generated C-star algebra by its tracial null ideal; this exactifies by a support projection before taking that quotient and identifies why the result does not imply factorization or hyperlinearity.
---

**ESTABLISHED.**  Let `pi:G->U(H)` and a state `phi` on `B(H)` satisfy the
state-form near-representation conditions

```text
phi o Ad(pi(g))=phi,
phi((pi(gh)-pi(g)pi(h))^*(pi(gh)-pi(g)pi(h)))=0.          (BSC1)
```

Let `M=B(H)**`, let `phi_bar` be the canonical normal extension of `phi` to
`M`, and let `s in M` be its support projection.  Then

```text
pi(g)s=s pi(g),
rho(g):=pi(g)s in U(sMs),
rho(gh)=rho(g)rho(h).                                    (BSC2)
```

Thus every invariant near-state becomes a genuine unitary representation in
its bidual support corner.  The normal state `phi_s=phi_bar|_(sMs)` is
faithful and `rho(G)`-central.  If the near-state is free,

```text
phi(pi(g))=delta_(g,e),                                  (BSC3)
```

then `phi_s(rho(g))=delta_(g,e)` and

```text
W^*(rho(G)) ~= L(G)                                      (BSC4)
```

trace preservingly.  Moreover this copy is not merely a subalgebra.  Since
`W^*(rho(G))` lies in the centralizer of the faithful normal state `phi_s`,
Takesaki's theorem supplies a `phi_s`-preserving normal conditional
expectation

```text
E:sMs -> W^*(rho(G)) ~= L(G).                            (BSC5)
```

For a purely singular state the projection `s` lies in the singular summand
of `B(H)**`; in particular it need not belong to `B(H)`.  Consequently
`(BSC2)` is not a genuine subrepresentation on a closed subspace of the
original `H`.  More importantly, the `rho(G)`-central state on `sMs` need not
extend to a `rho(G)`-central state on all of `B(K)` for a Hilbert-space
realization `sMs subset B(K)`.  Such an extension is precisely the missing
amenability/factorization input.  The support-corner exactification therefore
does not imply that `G` is hyperlinear.

For the binary Leavitt unit group this pins down the singular-near frontier:
any hypothetical Kahl--Schneider witness already contains a genuine regular
copy of `L(G)` in a singular bidual corner.  A contradiction must show that
this particular corner, or its inclusion, has an amenability or matricial
property unavailable to an arbitrary singular summand.  Even expectedness
is automatic; the missing input would have to make the singular support
corner injective, matricially approximable in a trace-compatible way, or
otherwise constrain that expectation.  Merely propagating the group law to
the support cannot be the missing theorem.

Proof: `state-support-corner-exactification-proof`.

DERIVATION
state-support-corner-exactification-proof
