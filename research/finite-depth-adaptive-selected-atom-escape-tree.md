---
rg: 2
id: finite-depth-adaptive-selected-atom-escape-tree
kind: claim
title: A fixed finite adaptive tree makes one selected BCS atom leave its current carrier
artifacts:
  - research/artifacts/finite-adaptive-hs-escape-audit-2026-08-24.md
distinct_from:
  single-selected-atom-hs-escape: That asks one fixed menu to work for every reducing carrier and hence supports indefinite iteration; this asks only for the finitely many carriers generated along one bounded decision tree.
  branching-plus-first-hit-exits-forces-hs-floor: That requires a uniform first-hit ladder and a simultaneous exit ledger; this permits the maximal forbidden type to be chosen adaptively and stops after one fixed depth.
  shared-bcs-active-recombination-after-schur-returns: That transports and recombines all forbidden types; this transports only the maximal named Reynolds atom at each node.
---

**OPEN FINITE PAYLOAD-CONDITIONED FACE.**  Fix the robust shared BCS with
`M` forbidden types and constant `beta`, together with the Pauli seed
`(SEC1)--(SEC2)`.  Construct one finite ordinary-group extension,
one integer `N`, and words

```text
U_(sigma,i),       sigma in {1,...,M}^{<N},  1<=i<=M,
```

with the following property.  For an accurate normalized-HS matrix model,
define `Q_empty=Q_-(1+B)/2`.  At a node `sigma`, let `i(sigma)` be a
maximal forbidden type on `Q_sigma`, let
`A_sigma=Q_sigma P_(i(sigma))` be its whole named Reynolds atom, and let
`Q_(sigma i)` be the reducing hull of

```text
Q_sigma join U_(sigma,i) A_sigma U_(sigma,i)^*.
```

Only on the actually reached carrier require

```text
tau(Q_sigma U_(sigma,i) A_sigma U_(sigma,i)^* Q_sigma)
 <=(1-eta)tau(A_sigma)+C sqrt(E)                       (FAT1)
```

for one `eta>0`, uniformly over the finitely many nodes.  All words preserve
`Q_-`, and the presentation must retain an exact finite-tracial model with
`J=-1`; there every forbidden atom is zero, so every conditional escape
requirement is vacuous.

It is enough to choose `N` once so that

```text
(1+eta beta/M)^N/4>1/2.                               (FAT2)
```

Canonical separation of the nontrivial involution gives
`tau(Q_-)->1/2`; the Pauli `B`-half then gives `tau(Q_empty)->1/4` in the
ambient normalized trace.  Every actuator preserves `Q_-`, so every reached
carrier has asymptotic trace at most `1/2`; this is the right side of
`(FAT2)`.  Equivalently it is enough that
`(1+eta beta/M)^N>2`.  The Clifford
half-selector is unnecessary: `(MFA1a)` already names the maximal atom as
an index-two Reynolds surplus and retains the stronger constant `beta/M`.
Thus neither an infinite address register, a reusable escape word, nor a
modulus uniform in depth is required.  What remains is finite but genuinely
payload-conditioned: the target placement must depend on the original
shared-context atom, not on an independent tensor address.

This claim is strictly weaker than `single-selected-atom-hs-escape`.
Different nodes may use unrelated words and unrelated finite packets, and
no assertion is made for reducing carriers that do not arise in this finite
decision tree.

In particular it does not assert the full-sector instance `Q=Q_-`.
`full-marked-sector-single-escape-is-direct-atom-collapse` proves that this
instance is already a direct forbidden-atom vanishing theorem, not a local
placement lemma.  Starting from the proper Pauli half and asking only about
reached carriers is therefore a substantive weakening, not bookkeeping.

## Attempts

A tensor-independent address packet cannot supply `(FAT1)`: disjoint address
cylinders only partition the payload trace, so their total authenticated mass
never exceeds the original carrier.  This is the exact capacity obstruction
in `independent-address-capacity-cannot-drive-selected-atom-growth`.  The
remaining attack must couple the transport to the selected shared-context
atom itself, for example through a common source Gram projection whose failed
covariance is charged to the fixed BCS residual menu.  Establishing that
payload-conditioned row at the finitely many reached nodes is deferred.

Replacing the adaptive maximum by an orthogonal finite role register is
exactly neutral.  `role-multiplexing-is-minimax-max-selection`
shows that `sum_i R_iP_i` is a genuine projection even for noncommuting
cross-context atoms, but its optimal representation-uniform trace is
`M^(-1)sum_i tau(P_i)`.  Thus it pays precisely the factor already paid by
the maximal-type choice and still needs the same payload-conditioned
outside-carrier placement.  In particular no arbitrary-list SELECT
controller is required for bookkeeping, but avoiding SELECT does not close
`(FAT1)`.

Generic mixing cannot supply it either.
`isotropic-mixing-has-only-logistic-carrier-growth` proves that `(FAT1)`
forces a hole of size at least `eta tau(A_sigma)-O(sqrt(E))` in every reached
carrier. Even exact depolarization only gives escape fraction
`1-tau(Q_sigma)/tau(Q_-)`, producing logistic growth toward capacity rather
than a fixed-factor overshoot. A valid actuator must therefore consume the
forbidden-character semantics, not merely mix a projection of the same rank.

There is also a strictly shorter sufficient route which does not establish
this claim: `finite-bad-character-packing-extension` asks for enough static
orthogonal conjugates of the maximal root character idempotent.
`simultaneous-character-packing-removes-max-loss` shows that more than
`2M/beta` copies of one maximal type already contradict the marked-sector
capacity, with no adaptive hulls; simultaneous packing of all types sharpens
the threshold to `2/beta`.
