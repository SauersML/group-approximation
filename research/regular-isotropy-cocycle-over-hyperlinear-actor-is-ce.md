---
rg: 2
id: regular-isotropy-cocycle-over-hyperlinear-actor-is-ce
kind: claim
title: Exact isotropy cancellation over a hyperlinear actor generates only a CE algebra
distinct_from:
  relation-cocycles-preserve-full-group-rectangles: that treats cocycles descending to the principal relation and proves they cannot cancel fixed-point traces; this allows arbitrary transformation-group isotropy holonomy and identifies what exact cancellation can generate.
  full-group-subgroup-trace-generation-dichotomy: that treats undecorated full-group unitaries; this includes arbitrary finite-rank measurable cocycle decorations.
  free-actor-extensions-cannot-host-nonce-relation: that rules out containing the source relation factor in a transformation crossed product by the native free actor; this works inside the relation algebra itself and applies to every hyperlinear actor.
---

Let `Gamma` act pmp on `(X,mu)`, let `R` be its orbit relation, and write
`u_g in L(R)` for the normalizer associated to the transformation of `g`.
Fix `n>=1` and a normalized measurable cocycle

```text
b in Z^1(Gamma acting on X,U(n)),
b_(gh)(x)=b_g(x)b_h(g^(-1)x).
```

Put

```text
v_g=b_g(u_g tensor 1_n) in M_n(L(R)),
N_b=W*(v_g:g in Gamma).                                (HIC1)
```

If the isotropy holonomy cancels every nonidentity fixed-point coefficient,

```text
(tr_n tensor tau_R)(v_g)=0       for every g!=e,         (HIC2)
```

then the assignment `lambda_g |-> v_g` extends to a trace-preserving
isomorphism

```text
L(Gamma) isomorphic_to N_b.                              (HIC3)
```

Consequently, if `Gamma` is hyperlinear, `N_b` is Connes embeddable and
cannot contain a trace-preserving copy of any non-Connes-embeddable tracial
algebra. In particular it cannot generate `M_n(L(R))), or retain the fixed
non-CE relation factor inside its generated algebra.

Thus an isotropy-sensitive cocycle does not create extra payload after exact
trace cancellation: it only gives a new concrete realization of the actor's
group factor. The native virtually-free actor, and every other actor already
known to be hyperlinear, are closed for this ansatz. If the actor's
hyperlinearity is unknown, proving `(HIC2)` together with non-CE payload
retention is already a direct proof that this actor is nonhyperlinear; it is
not a cheaper trace-promotion step.

Infinite isotropy alone is not an obstruction to `(HIC2)`. For the trivial
action of `Z` on `(T,Haar)`, the scalar cocycle `b_k(z)=z^k` gives
`v_k=z^k`, has regular trace, and generates `L^infinity(T)=L(Z)`. This CE
calibration shows why a valid no-go must use payload retention or a
restriction on the holonomy, not merely the size of the stabilizers.
