---
rg: 2
id: support-packet-paired-word-frame-exposes-forbidden-rank
kind: claim
title: Four paired packet words name the forbidden commutant rank jump
artifacts:
  - experiments/schur_packet_paired_commutant_frame.py
distinct_from:
  support-packet-covariant-wedderburn-detector: that detects the jump by the abstract shape of the full tensor-product commutant; this supplies fixed group words whose image spans the changing sixteen-dimensional part.
  support-packet-literal-tensor-covariance-is-blind: that rules out conjugating the diagonal tensor representations; this works in their centralizers and identifies the exact reverse character through which an edge-group return can escape.
  full-center-hnn-transport-cancels-schur-multiplicity: that uses one Pauli pair and the whole selector center; these frames use four paired Pauli words and retain only a three-dimensional commutator center.
---

Take source and coefficient copies of the order-128 support packet and write
their noncentral coordinates in the order `(p_1,p_2,q_1,q_2)`.  Pair the four
source generators with the following coefficient words:

```text
F_+:  p_1 | p_1 p_2,   p_2 | p_2,   q_1 | q_1 q_2,   q_2 | q_2,
F_-:  p_1 | p_1,       p_2 | p_2,   q_1 | q_1,       q_2 | q_2.          (PWF1)
```

Evaluate the source packet at central character `k`, the plus coefficient at
`011`, and the minus coefficient at `101`.  The alternating commutator ranks
of the two four-generator frames are

```text
source k        100   110   111   101
rank F_+(k)       2     4     2     2
rank F_-(k)       2     4     2     0.                (PWF2)
```

Thus all three allowed `J=-1` sectors have identical frame-algebra type, while
the forbidden sector contains exactly one extra Pauli rank on the plus side.
On `T_101 tensor T_011`, the sixteen paired Pauli words span the
`M_2^4` part of the diagonal-packet commutant.  On
`T_101 tensor T_101`, they span the abelian `C^16` part.  This names, by fixed
group words, precisely the part of the seven-dimensional Wedderburn detector
that was previously available only as a Reynolds range.

Symbolically, before evaluating central characters, both frames have
three-dimensional commutator image and the same three-dimensional relation
kernel in `wedge^2(F_2^4)`.  They therefore define isomorphic order-128
class-two edge groups.  Exactly 32 changes of the four noncentral generators
induce such isomorphisms, producing eight central-character transport
patterns.  Every one transports the plus forbidden source character

```text
101  --->  011.                                          (PWF3)
```

Hence the sole finite-edge escape is explicit: it exports forbidden mass to
the reverse `J=+1` reservoir.  A successful one-sided compressor no longer has
to discover or select an arbitrary commutant projection; it has to orient
these four named words and exclude the single reverse reservoir `(PWF3)`.
