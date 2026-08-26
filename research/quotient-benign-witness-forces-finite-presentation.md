---
rg: 2
id: quotient-benign-witness-forces-finite-presentation
kind: claim
title: A quotient-compatible benign witness forces the quotient to be finitely presented
artifacts:
  - research/artifacts/quotient-benign-rope-synchronization-2026-08-25.md
distinct_from:
  quotient-benign-rope-synchronizes-finite-quotients: that is the valid conditional finite-swap construction; this is the obstruction showing its quotient-compatible hypothesis cannot hold on the delayed positive branch.
  positive-rope-profinite-edge-synchronization: that synchronization claim may still have a different proof; this rules out only the route through a homomorphism from the benign overgroup killing its cutting subgroup.
---

Let `N` be normal in a finitely generated group `F`, let `Q=F/N`, and suppose
there are

```text
K finitely presented,          e:F->K injective,
L<=K finitely generated,       e(F) intersect L=e(N),
sigma:K->Q,                    sigma e=q,       L<=ker(sigma).  (QBF1)
```

Then `Q` is a retract of the finitely presented group

```text
P=K/normalClosure_K(L),                                      (QBF2)
```

and consequently `Q` is finitely presented.

In particular, no positive delayed FIN/INF scaffold whose limit group `Q`
is not finitely presented can have the quotient-compatible witness requested
by `positive-scaffold-has-quotient-compatible-rf-witness`.  This refutes that
claim and invalidates the corresponding route to rope synchronization.
