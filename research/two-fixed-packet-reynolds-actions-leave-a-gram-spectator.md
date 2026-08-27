---
rg: 2
id: two-fixed-packet-reynolds-actions-leave-a-gram-spectator
kind: claim
title: Two fixed packet Reynolds actions leave an arbitrary Gram spectator
artifacts:
  - research/artifacts/fanizza-two-packet-reynolds-localization-firewall-2026-08-21.md
distinct_from:
  common-corner-mutual-bicommutant-extraction: that asks for a fixed label packet and a scalable word-generated reservoir algebra to become mutual commutants; this proves why replacing the scalable side by any second fixed packet cannot work.
  full-packet-bicommutant-synchronization: that asks to control every unitary in the full coordinate commutant; this shows finite packet Reynolds tests never expose all those unitaries under unbounded amplification.
  local-steinberg-heisenberg-packets-are-coefficient-rank-blind: that varies coefficient rank inside one characteristic-two root packet; this leaves arbitrary complex Gram projections in the spectator of two characteristic-zero packets.
---

Let `A_0,B_0 subset End(V)` be any two fixed finite semisimple packet
algebras.  On `V tensor C^N`, amplify both by the identity.  Every fixed
internal and mixed packet relation is preserved, but every projection

```text
q_N=I_V tensor Q_N
```

commutes with both packets and is fixed by all of their conjugation Reynolds
operators.  Its trace `rank(Q_N)/N` is arbitrary, while it is outside the
joint packet algebra unless `Q_N` is scalar.

For a concrete distinct pair on `C^2 tensor C^2`, take
`A_0=M_2 tensor I_2` and `B_0=W A_0 W^*` with
`W=CZ times SWAP`.  Their Pauli generators can be taken as
`X_1,Z_1` and `Z_1X_2,Z_2`; they do not commute and jointly generate `M_4`.
After tensoring with `C^N`, their common commutant is nevertheless
`I_4 tensor M_N`, so every `I_4 tensor Q_N` survives.

Reynolds averaging over a packet lands in its commutant, not its
bicommutant.  To project into `M_r tensor I_N`, the second packet must
generate the full `I_r tensor M_N`, which no fixed finite-dimensional
semisimple algebra can do for unbounded `N`.  Therefore Fanizza Gram
localization requires a scalable second algebra or a mixed word that is
sensitive to the spectator gauge, not merely a second fixed packet.
