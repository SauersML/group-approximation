---
rg: 2
id: atlas-entropy-and-cmi-stop-at-face-emptiness
kind: claim
title: Atlas covering entropy and finite CMI stop at the original CE-face emptiness problem
distinct_from:
  cstar-one-bounded-entropy-is-canonical-trace-blind: that concerns the supremum over every trace on a full C-star algebra; this fixes the regular two-A8 trace face and shows that even trace-specific covering entropy has no exclusion threshold short of emptiness.
  atlas-radius-nine-packet-gram-sos-is-tracial: that fences fixed packet Gram and conditional-expectation positivity; this treats asymptotic microstate covering, orbital entropy and finite-dimensional information inequalities on the exact six-relator face.
  no-spherical-leak-in-matrix-ultraproducts: that records a 1-bounded-entropy fence for an arithmetic Hecke commutant; this gives the corresponding concrete fence for the Atlas relative-unitary microstate spaces.
  atlas-relators-keep-high-order-return-under-mixing: that gives an exact weak-mixing factor correlation countermodel; this explains why entropy and conditional mutual information cannot use those correlations to detect matrix-ultraproduct emptiness.
  atlas-six-relator-hyperlinear-escape-test: that identifies nonemptiness of the CE regular trace face with a nontrivial hyperlinear quotient; this proves the proposed entropy threshold is exactly that nonemptiness question, not a weaker invariant.
---

**ESTABLISHED FENCE.**  Put `n_k=20160k` and, for fixed `a>0`, define the
regular Atlas relative-unitary microstate space

```text
Omega_k(eta,a)={U in U(n_k): B_k(U)<=eta^2 and A_k(U)>=a},   (AEC1)
```

where `B_k` is the sum of the six squared relator defects and `A_k` is the
five-row energy from `atlas-five-row-lift-failure-dichotomy`.

Assume the normalized blow-up branch and the large finite-simple branch of
`atlas-hyperlinear-enemy-is-map-or-large-simple` have both been excluded.
Then the following are equivalent:

1. the diffuse MAP Atlas enemy exists;
2. for some `a>0` there are `eta_m->0`, `k_m->infinity`, and
   `U_m in Omega_(k_m)(eta_m,a)`;
3. the six-relator regular CE face is nonempty.

Now fix any covering radius `delta>0` and let

```text
N_delta(Omega_k(eta,a))
```

be the raw normalized-HS covering number, with value zero for the empty set.
Whenever the space is nonempty this integer is at least one, so

```text
n_k^(-2) log N_delta(Omega_k(eta,a)) >= 0.             (AEC2)
```

Consequently a raw-covering argument excludes the enemy only by proving
that the relevant `Omega_k(eta,a)` are empty at a fixed positive defect
threshold.  With the convention `log 0=-infinity`, a genuinely negative raw
covering exponent is exactly eventual emptiness, hence exactly the desired
six-relator CE-face gap.  Bounds saying the exponent is finite, zero, or
subquadratic do not help.

Standard 1-bounded and orbital/free entropies subtract conjugacy, gauge, or
ambient-volume baselines.  Their values can be nonpositive, and volume-based
free entropies can be `-infinity`, for nonempty but very thin microstate
families.  Thus no sign implication gives emptiness without an additional
theorem.  Such a theorem specialized to `(AEC1)` would already be the missing
uniform phase-lift assertion.  The
double-commutant gauge of the two regular `A8` charts further shows why raw
orbit volume is representation redundancy rather than a separating payload.

Finite-dimensional conditional mutual information gives no alternative.
Any CMI formed from finitely many chart matrix units, relator-word registers,
and finite ancillary systems obeys strong subadditivity and data processing
in every finite-dimensional state.  The same inequalities hold for the
corresponding finite-dimensional restrictions of an arbitrary tracial von
Neumann algebra.  In particular the exact Leavitt factor model satisfies
them while all six relators vanish and `tau(h_5)>0`.  Thus a standard CMI
inequality cannot distinguish the CE matrix-ultraproduct face from that
tracial countermodel.  A proposed information proof would need an extra
matrix-only integrality or coordinate-rounding step; CMI itself supplies
none.

This fence does not rule out a new entropy invariant with an independently
proved emptiness theorem.  It says precisely what that theorem must add:
ordinary entropy decay or finite information inequalities are insufficient;
one must obtain a dimension-independent **zero-versus-nonzero** statement
for `(AEC1)`.

## Attempts

- **Raw covering decay.**  This dies at `(AEC2)`: before the microstate face
  is empty, its raw covering number is a positive integer and its normalized
  logarithm cannot be negative.
- **Orbital or 1-bounded entropy sign.**  After subtracting the chart gauge or
  an ambient-volume baseline, nonpositive entropy is compatible with a thin
  nonempty face; no known sign theorem upgrades it to emptiness.
- **Conditional mutual information.**  Strong subadditivity and data
  processing also hold in the exact positive-energy Leavitt tracial model, so
  the standard inequalities are not CE-specific.
