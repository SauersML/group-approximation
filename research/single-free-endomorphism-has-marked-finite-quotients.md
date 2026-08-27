---
rg: 2
id: single-free-endomorphism-has-marked-finite-quotients
kind: claim
title: Every single free-group endomorphism has compatible marked finite quotients
distinct_from:
  abelian-matrix-hnns-have-marked-finite-quotients: that gives an elementary simultaneous congruence construction for finitely many finite-rank abelian endomorphisms; this uses residual finiteness of an arbitrary one-ended free-group mapping torus, including endomorphisms singular on abelianization.
  graph-endomorphism-phase-hnn-embeds-formanek-procesi: that embeds a particular graph HNN in a residually finite automorphism group; this treats the ordinary ascending mapping torus of every injective endomorphism of a finite-rank free group.
  hnn-mark-collapse-requires-profinite-edge-incompatibility: that states the abstract compatible-quotient screening criterion; this supplies the compatible marked quotient for the whole single-free-endomorphism class.
---

ESTABLISHED.  Let `F_n` be a finite-rank free group, let
`phi:F_n->F_n` be injective, and form

```text
T_phi=<F_n,t | t g t^(-1)=phi(g), g in F_n>.            (SFE1)
```

Borisov--Sapir prove that `(SFE1)` is residually finite for every free-group
endomorphism; see *Polynomial maps over finite fields and residual finiteness
of mapping tori of group endomorphisms*, Theorem 1.2,
arXiv:math/0309121.

Consequently, for every `1!=y in F_n`, there is a finite quotient

```text
q:T_phi -> Q,                 q(y)!=1.                  (SFE2)
```

Put `H=q(F_n)`.  The HNN relation gives

```text
q(t) H q(t)^(-1)=q(phi(F_n))<=H.                        (SFE3)
```

The left side of `(SFE3)` has the same finite cardinality as `H`, so equality
holds.  Thus `phi` descends to the automorphism

```text
h |-> q(t)h q(t)^(-1)                                  (SFE4)
```

of the finite marked quotient `H`, and `(SFE2)` retains `y`.

Therefore no single genuinely nonabelian free-group proper endomorphism can
supply the profinitely incompatible type recurrence sought after
`kazhdan-type-blocks-pack-a-square-function`.  This includes injective
endomorphisms whose map on `H_1(F_n;Z)` is singular, which are not covered by
the elementary pro-`p` determinant argument.  A surviving free-group
endomorphism actuator must use at least two branches whose compatibility is
not contained in one ordinary mapping torus.
