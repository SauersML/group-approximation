---
rg: 2
id: row2-quarter-source-opnorm-two-fence
kind: claim
title: An irreducible actor reservoir gives the row-two quarter-source attachment operator-norm defect two
artifacts:
  - research/row2-quarter-source-opnorm-fence-proof.md
distinct_from:
  recentered-order-seven-heads-have-actor-holonomy: that retains a regular finite actor gauge on the invariant five-pair carrier; this passes to a nontrivial irreducible actor constituent and computes the sharp operator-norm obstruction to a quarter-source conjugacy.
  quarter-whiteheads-lack-unequal-source-conjugacy: that audits the named ordinary covariance rows and finds no quarter source for the second Whitehead; this gives a zero-defect finite packet in which even an arbitrary analytic quarter source cannot be conjugated to the authenticated second Whitehead on a nonzero reducing carrier.
  prefix-order-seven-pair-retains-gl7-mark: that gives an ungauged finite occurrence model and shows the fixed word table is consistent; this gives a different exact finite model with irreducible nontrivial actor holonomy and a quantitative norm-two row defect.
---

**ESTABLISHED ROW-TWO OPERATOR-NORM FENCE.**  Use the recentered five-pair
Pauli packet and finite actor group `G` from
`recentered-order-seven-heads-have-actor-holonomy`.  Its second native
Whitehead is a nonidentity involution `j=J_2 in G`.  Choose an irreducible
complex unitary representation `sigma` of `G` for which

```text
sigma(j) != 1.                                           (R2F1)
```

Such a constituent exists because the left regular representation is
faithful.  On

```text
H=(C^2)^(tensor 5) tensor V_sigma                       (R2F2)
```

represent the Pauli group in its Schrodinger representation and every
actor `g in G` by its canonical label implementer tensored with `sigma(g)`.
Set both recentering involutions to `-1`.  All five-pair covariance rows,
all multiplication rows, the native braid, and both order-seven heads are
then exact.  In particular

```text
J_2=S_2 tensor D,       D=sigma(j),       D^2=1,        (R2F3)
```

where `S_2` swaps two of the five Pauli qubits.  Its negative label rank is
`8` in label dimension `32`, hence its label fraction is exactly `1/4`.

Write `m=dim(V_sigma)` and let `k>0` be the negative rank of `D`; positivity
of `k` follows from `(R2F1)` and `D^2=1`.  The negative rank of the actual
authenticated word in `(R2F3)` is

```text
rank_-(J_2)=8(m-k)+24k=8m+16k,                         (R2F4)
```

strictly larger than the quarter-source rank `8m`.  Consequently, for
every reflection `R` on `H` with `rank_-(R)=8m` and every unitary `U`,

```text
|| U R U^* - J_2 ||=2.                                 (R2F5)
```

Indeed the two negative spectral projections have different ranks, so
their operator-norm distance is one; reflections differ by twice their
negative projections.

There is no smaller nonzero reducing escape.  The five-pair Pauli algebra
is `M_32(C) tensor 1`, so every projection reducing it is `1 tensor p`.
Reduction by all actors forces `p` into `sigma(G)'`, which is scalar by
irreducibility.  Thus the complete displayed packet has only the reducing
carriers `0` and `H`.

The same conclusion is robust under fixed-packet operator-norm
exactification.  Once the approximate involutions and matrix units are
rounded, any proposed row-two conjugacy with defect strictly below
`2-o(1)` would give two exact projections at distance strictly below one
and hence equal rank, contradicting `(R2F4)`.  Therefore the current
recentered Pauli, prefix, braid, and order-seven relations do not force a
quarter-source conjugacy to the authenticated `J_2` on any nonzero reducing
carrier.  They also do not force the original eighth-label selector row:
the reservoir actor `D` remains an independently authenticated part of the
same exact word occurrence.

This is a scoped representation of the displayed finite semidirect packet,
not a representation of the full binary Leavitt elementary or Steinberg
group.  It rules out deriving the row-two attachment from that packet
alone; a new mixed occurrence must kill the `v_2` actor holonomy or compare
it with an independently ungauged occurrence.  No Property T, Kazhdan
input, trace hypothesis, literature theorem, or local computation is used.

DERIVATION
row2-quarter-source-opnorm-fence-proof

