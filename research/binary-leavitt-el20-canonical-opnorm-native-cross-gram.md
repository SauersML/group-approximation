---
rg: 2
id: binary-leavitt-el20-canonical-opnorm-native-cross-gram
kind: claim
title: The two native binary transports overlap in every operator-norm canonical microstate of EL20
distinct_from:
  binary-leavitt-el20-arbitrary-profile-native-cross-gram: that quantifies over every reblocked surviving corona profile, including concentrated finite-packet multiplicity vectors; this is its specialization to operator-norm models whose trace tends to delta_e, which by surviving-mf-mark-diracizes-to-canonical-opnorm-profile is still sufficient for the EL20 MF endpoint.
  binary-leavitt-native-two-scale-cross-gram-positive: that is a canonical-trace normalized-HS claim for Steinberg microstates and would also close the non-hyperlinear lane; this keeps the canonical trace but assumes operator-norm defects, so it is weaker and does not imply non-hyperlinearity.
  canonical-cross-gram-does-not-close-arbitrary-mf-active-profile: that firewall blocks applying a canonical theorem to an arbitrary original corona model; this claim is only ever applied to the Diracized replacement model, whose profile is canonical by proof.
---

**OPEN CANONICAL OPERATOR-NORM CROSS-GRAM CLAIM.**  Let
`R=L_(F_2)(1,2)` and `G=EL_20(R)`.  Let

```text
W_n : G -> U(d_n)
```

be operator-norm asymptotic unitary representations with

```text
tr W_n(g) -> delta_e(g)       for every g in G.                 (CAP0)
```

Exactify, in the same dimension and operator norm, the fixed depth-one and
next-refinement Pauli packets.  They are literal finite subgroups of `G`, so
by `(DCP2)` of `surviving-mf-mark-diracizes-to-canonical-opnorm-profile` they
carry Plancherel multiplicities.  Form the two **actual** native transports

```text
S_1,S_2 : P_source H_n -> P_target H_n
```

with selector ratios `1/2 -> 1/4` and `1/4 -> 1/8` (not unrelated rectangular
completions).  Prove that there is a fixed `gamma>0` such that

```text
tr_n(S_1^*S_2S_2^*S_1) >= gamma tr_n(P_source) - o(1),          (CAP1)
```

and that the two mixed source-Pauli commutators of the relative polar gauge
tend to zero in normalized HS norm on the resulting overlap corner.

The companion floor `tr_n(P_source)>=c` is automatic: `tr_n(P_source)`
converges to the canonical packet value.  The marked involution
`z=e_13(s_1t_1)` has negative carrier of normalized trace `1/2+o(1)`, so no
active-core reblocking is needed.

## Relations

- `(EAP1)` for all surviving profiles implies `(CAP1)`, since `W_n` is a
  surviving operator-norm model.
- The EL20 analogue of the normalized-HS canonical claim `(NCG1)` implies
  `(CAP1)`, since operator-norm defects dominate normalized-HS defects and
  `(CAP0)` is the canonical trace.
- `(CAP1)`, together with the established compiler lemmas, gives
  `Rad_MF(EL_20(R))=EL_20(R)`; see
  `el20-canonical-opnorm-cross-gram-gives-full-mf-radical`.
- A proof of `(CAP1)` may use canonical packet moments such as the regular
  center-chain atom `tau(e_chi)=1/64` and the Hecke support fractions derived
  from it.  It may also use operator-norm exactification.  It may not use
  Property `(T)`, Kazhdan projections, or literature theorems.

## Attempts

- **Import the canonical center-chain Hecke fractions.**  This attempt passes
  the quantifier check that failed for the arbitrary-profile claims.  It
  still stops at occurrence typing:
  `fixed-center-chain-hecke-occurrence-is-regularly-impossible` and
  `endpoint-whiteheads-are-center-chain-hecke-spectators` are realized in
  regular packet models.  The canonical profile supplies the correct scalar
  Gram, not the native occurrence.
- **Remaining obstruction.**  This is the fixed-Hecke-frame gauge lock of
  `growing-multicut-el20-order-seven-inheritance`, specialized to canonical
  models.  Fences built from non-Plancherel finite-packet profiles do not
  apply unless their packet's regular representation reproduces them.
- **Regular calibration (swarm-0917, calibration).**  The conclusion
  `(CAP1)` together with its gauge clause is false in every exact tracial
  model: `lambda` on `L(G)` and every tracial ultraproduct of models.  With
  exact rows and positive overlap mass, `(TSG6)` forces `epsilon_g>=2/3`, so
  the gauge lock cannot hold.  Every approximate model passes to such an
  exact model.  So this claim holds only vacuously and is equivalent to
  `(EMF1)` itself; see
  `native-cross-gram-conclusions-fail-in-every-tracial-model`.  The only
  alternative is that the recorded compiler has a step that is not valid in
  finite von Neumann algebras.  Any direct estimate of mass plus lock dies at
  the lock clause.
