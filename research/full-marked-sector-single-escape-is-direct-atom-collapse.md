---
rg: 2
id: full-marked-sector-single-escape-is-direct-atom-collapse
kind: claim
title: The full marked-sector instance of one-piece escape is already direct forbidden-atom collapse
distinct_from:
  single-selected-atom-hs-escape: That asks for the overlap inequality on every reducing carrier; this computes its full-sector instance and shows it is not a geometric escape statement.
  finite-depth-adaptive-selected-atom-escape-tree: That asks only about proper carriers reached from the Pauli seed; this explains why that bounded tree is a genuinely weaker placement target.
  maximal-forbidden-atom-has-a-named-positive-half: That supplies the positive selected mass; this shows the universal escape inequality would kill it immediately without any carrier iteration.
---

**ESTABLISHED SCOPE AUDIT.**  In the setup of
`single-selected-atom-hs-escape`, take the permitted reducing carrier

```text
Q=Q_-=(1-J)/2.
```

Every actuator word in that claim preserves the marked sector, so for every
selected `A_*<=Q_-`,

```text
D_*=U_(i_*) A_* U_(i_*)^* <=Q_-,
tau(Q_- D_*)=tau(D_*)=tau(A_*).                        (FSC1)
```

Consequently `(SAE1)` at this carrier is exactly

```text
eta tau(A_*)<=C sqrt(E).                               (FSC2)
```

It is not an escape inequality: it is a direct dimension-independent
forbidden-atom vanishing estimate.  Combining `(FSC2)` with `(MFA2)` gives

```text
eta beta/(2M) tau(Q_-)<=C' sqrt(E).                    (FSC3)
```

Canonical separation of the marked involution keeps `tau(Q_-)` bounded
below, so `(FSC3)` alone excludes arbitrarily accurate marked matrix models.
Thus proving the all-carriers claim already proves the desired endpoint at
its full-sector instance; no iterative hull growth is used.

This is not a refutation.  The exact perfect tracial completion has every
forbidden atom zero, so `(FSC2)` is vacuous there.  Rather, it classifies the
strength of the target: `single-selected-atom-hs-escape` cannot be justified
as a purely geometric fact about a `J`-preserving unitary.  Its proof would
have to contain the same payload-sensitive matrix-only obstruction sought by
the final theorem.  The bounded reachable-carrier target avoids demanding
this direct collapse and remains the smaller placement problem.
