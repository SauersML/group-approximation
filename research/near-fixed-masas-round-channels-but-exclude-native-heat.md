---
rg: 2
id: near-fixed-masas-round-channels-but-exclude-native-heat
kind: claim
title: Nearly fixed maximal abelian algebras permit channel rounding but cannot carry native Kazhdan heat
distinct_from:
  schur-near-idempotents-round-dimension-uniformly: That rounds an exact self-adjoint Schur channel; this repairs a channel with small averaged maximal-abelian energy to that class and gives a uniform obstruction for native heat.
  finite-leavitt-core-averages-stay-far-from-kazhdan-heat: That separates averages over fixed finite coefficient cores; this separates every basis-dependent Schur channel using one fixed noncommuting pair.
artifacts:
  - research/artifacts/masa-channel-rounding-and-native-heat-separation-2026-09-08.md
---

Use normalized matrix trace. Let `P:M_d->M_d` be self-adjoint,
bistochastic and completely positive, and let `D` be a maximal abelian
subalgebra. Set

```text
a=integral_(u in U(D)) (1-Re tr(u*P(u))) du,
epsilon=||P^2-P||_(infinity->2),       gamma=2 sqrt(2a).
```

There is a self-adjoint bistochastic Schur channel `S` in the basis
of `D` with `||P-S||_(infinity->2)<=gamma`. Consequently there is
a unital block-diagonal algebra `B` containing `D` such that

```text
||P-E_B||_(infinity->2) <= gamma+min(1,4 sqrt(epsilon+3gamma)).
```

The hypothesis on `a` does not follow from near idempotence. In fact,
for admissible canonical Kazhdan heat maps `P_n` of the native
nonabelian group `L`,

```text
liminf_n inf_(all Schur channels S in all bases)
    ||P_n-S||_(infinity->2) >= 1/4,

liminf_n inf_(all maximal abelian D)
    integral_(u in U(D)) (1-Re tr(u*P_n(u))) du >= 1/16.
```

Here heat times tend to infinity and their product with the fixed
SOS relation error tends to zero. The artifact proves a more general
finite-matrix bound using the commutator of any two generator words.
In particular, the first lower bound also applies to conditional
expectations onto algebras containing an ambient maximal abelian
subalgebra.

Thus the positive Schur rounding theorem cannot be applied to native
heat by finding a nearly fixed ambient maximal abelian algebra. The
general rounding problem allows represented matrix algebras with
nontrivial multiplicities and remains open. Neither hyperlinearity nor
a dimension-uniform matrix-relator gap is decided.

DERIVATION
kraus-projection-and-haar-commutators-control-masa-rounding
