---
rg: 2
id: support-packet-covariant-wedderburn-detector
kind: claim
title: A seven-dimensional packet coefficient is allowed-flat but has forbidden Wedderburn holonomy
artifacts:
  - experiments/schur_packet_tensor_fusion_search.py
  - experiments/schur_packet_wedderburn_holonomy_opt.py
  - experiments/support_packet_wedderburn_tag_capacity.py
  - experiments/support_packet_wedderburn_tag_capacity_4.json
  - experiments/run_support_packet_capacity.sbatch
  - research/artifacts/support-packet-covariant-wedderburn-detector-2026-08-20.md
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that compares the commutants of the nested packet groups in one representation; this compares diagonal tensor coefficients related by one explicit packet automorphism and is exactly flat on all allowed selector sectors.
  commuting-automorphism-cocycle-forces-multiplicity: that extracts a fixed divisibility condition from a projective square; this gives an amplification-stable distance between nonisomorphic commutant algebras.
  full-center-hnn-transport-cancels-schur-multiplicity: that proves ordinary full-center Pauli restriction loses the ambient rank jump; this retains it through the full packet fusion ring and detects it as Wedderburn block shape.
  support-packet-literal-tensor-covariance-is-blind: that proves no pair of finite tensor coefficients can make the tensor representations themselves allowed-equivalent and forbidden-distinct; this detector survives precisely because it compares their commutant algebras instead.
  support-packet-paired-word-frame-exposes-forbidden-rank: that replaces the detector's changing abstract commutant summand by four explicit paired packet words and identifies its unique reverse-character escape.
---

Let `B_sub` be the order-128 fixed support packet with central basis
`(J,z_e,z_f)` and commutators

```text
[p_1,q_1]=J,       [p_1,q_2]=J z_e,
[p_2,q_1]=z_f,     [p_2,q_2]=1.                     (CWD1)
```

There is an involutive automorphism `alpha` given by

```text
alpha(J)=z_e, alpha(z_e)=J, alpha(z_f)=z_f,
alpha(p_i)=p_i,
alpha(q_1)=q_1 q_2, alpha(q_2)=q_2.                 (CWD2)
```

Write `T_k` for the unique four-dimensional packet simple with central
character `k` when `k` is `011` or `101`, and write `1` for the trivial
simple.  Put

```text
V_+ = 1^3 directSum T_011,
V_- = 1^3 directSum T_101.                           (CWD3)
```

Both coefficients have dimension seven, and `V_-` is the pullback of `V_+`
by `alpha`.

For every irreducible packet `S` in the `J=-1` allowed central sectors
`100,110,111`, the commutant algebras

```text
End_B(S tensor V_+),       End_B(S tensor V_-)       (CWD4)
```

are unitarily conjugate.  Their Wedderburn signatures `(multiplicity,
simple dimension)` are

```text
k=100 or 111:  (1,2)^4, (3,2),
k=110:         (2,4), (3,2).                         (CWD5)
```

On the forbidden simple `S=T_101`, however,

```text
End_B(T_101 tensor V_+)  = M_(2m)^4 directSum M_(3m),
End_B(T_101 tensor V_-)  = M_m^16    directSum M_(3m) (CWD6)
```

after amplification by multiplicity `m`.  The corresponding packet simples
have dimensions `(2,2,2,2,4)` on the plus side and `(1^16,4)` on the minus
side.  In particular the two algebras have the same vector-space dimension
`25m^2`, but are not isomorphic: their centers have dimensions five and
seventeen.

More quantitatively, let `R_+,R_-` be their Reynolds projections on the
adjoint space of dimension `(28m)^2`.  For every unitary `W` on the underlying
`28m`-dimensional Hilbert space,

```text
||R_+-Ad_W R_- Ad_W^*||_(HS,(28m)^2)^2 >= 1/49.      (CWD7)
```

Thus this cell is simultaneously:

- exactly flat on every allowed selector sector;
- related by one fixed packet automorphism, so it has a group-covariance
  interface; and
- separated by a universal adjoint-HS constant on the forbidden sector,
  even after arbitrary multiplicity amplification.

It is the first explicit finite covariance coefficient in the Schur--Clifford
route that passes the equal-Hilbert-capacity and allowed-sector falsification
tests.

An exhaustive exact audit of all `101270` four-summand coefficient multisets
finds `905` equivalence classes after fixing coefficient dimension and all
twelve allowed-source Wedderburn signatures. Of these, `697` have one
forbidden signature and `208` have two; none has more than two. Thus the
four-summand ansatz carries exactly one non-character forbidden tag at best.
The pair `(CWD3)` realizes this sharp capacity, but no four-summand coefficient
family can encode a three-way selector while remaining completely
allowed-flat.

The changing sixteen-dimensional summand is not merely existential.
`support-packet-paired-word-frame-exposes-forbidden-rank` gives four fixed
paired Pauli words spanning `M_2^4` on the plus forbidden sector and `C^16` on
the minus forbidden sector.  Its exhaustive symbolic audit shows that every
finite edge-group identification exports `101` to the single reverse
character `011`.  Thus the remaining compressor problem is orientation of a
named four-word frame, not selection of an arbitrary Reynolds projection.
