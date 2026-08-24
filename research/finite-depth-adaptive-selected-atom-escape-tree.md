---
rg: 2
id: finite-depth-adaptive-selected-atom-escape-tree
kind: claim
title: A fixed finite adaptive tree makes one selected BCS atom leave its current carrier
distinct_from:
  single-selected-atom-hs-escape: That asks one fixed menu to work for every reducing carrier and hence supports indefinite iteration; this asks only for the finitely many carriers generated along one bounded decision tree.
  branching-plus-first-hit-exits-forces-hs-floor: That requires a uniform first-hit ladder and a simultaneous exit ledger; this permits the maximal forbidden type to be chosen adaptively and stops after one fixed depth.
  shared-bcs-active-recombination-after-schur-returns: That transports and recombines all forbidden types; this transports only the maximal named half at each node.
---

**OPEN FINITE PAYLOAD-CONDITIONED FACE.**  Fix the robust shared BCS with
`M` forbidden types and constant `beta`, its one-bit selector menu, and the
Pauli seed `(SEC1)--(SEC2)`.  Construct one finite ordinary-group extension,
one integer `N`, and words

```text
U_(sigma,i),       sigma in {1,...,M}^{<N},  1<=i<=M,
```

with the following property.  For an accurate normalized-HS matrix model,
define `Q_empty=Q_-(1+B)/2`.  At a node `sigma`, let `i(sigma)` be a
maximal forbidden type on `Q_sigma`, let `A_sigma` be its named selected
half, and let `Q_(sigma i)` be the reducing hull of

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
(1+eta beta/(2M))^N/4>1.                              (FAT2)
```

Canonical separation of the nontrivial involution gives
`tau(Q_-)->1/2`; the Pauli `B`-half then gives `tau(Q_empty)->1/4` in the
ambient normalized trace.  This is the factor in `(FAT2)`.
Thus neither an infinite address register, a reusable escape word, nor a
modulus uniform in depth is required.  What remains is finite but genuinely
payload-conditioned: the target placement must depend on the original
shared-context atom, not on an independent tensor address.

This claim is strictly weaker than `single-selected-atom-hs-escape`.
Different nodes may use unrelated words and unrelated finite packets, and
no assertion is made for reducing carriers that do not arise in this finite
decision tree.

## Attempts

A tensor-independent address packet cannot supply `(FAT1)`: disjoint address
cylinders only partition the payload trace, so their total authenticated mass
never exceeds the original carrier.  This is the exact capacity obstruction
in `independent-address-capacity-cannot-drive-selected-atom-growth`.  The
remaining attack must couple the transport to the selected shared-context
atom itself, for example through a common source Gram projection whose failed
covariance is charged to the fixed BCS residual menu.  Establishing that
payload-conditioned row at the finitely many reached nodes is deferred.
