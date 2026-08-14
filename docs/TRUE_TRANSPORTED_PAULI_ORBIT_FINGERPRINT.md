# The transported Pauli orbit retains a raw-coordinate fingerprint

Date: 2026-08-13

## Outcome

The transported order-32 Pauli packet does not preserve the raw coefficient
algebra, but averaging over its orbit does not erase the raw coefficient
label either.  It produces a canonical mixed-packet fingerprint with a fixed
spectral gap.

Let

```text
A_0 = span{F_(--),F_(-+),F_(+-),F_(++)}
```

be the raw four-character coefficient space on the `d=-1` carrier, and let
`P'` be the comb transport of the order-32 Pauli packet.  Exact enumeration
gives

```text
|P'| = 32,
|Stab_(P')(A_0)| = 2.                                (POF1)
```

Both stabilizer elements fix all four cuts pointwise.  In particular a
single raw cut `F=F_(--)` has a 16-element orbit

```text
O={u F u^(-1):u in P'}.                              (POF2)
```

The overlap row of `F` with this orbit is

```text
1 copy of 1/8,
8 copies of 3/128,
7 copies of 5/128.                                  (POF3)
```

Transitivity makes every Gram row a permutation of `(POF3)`.  Thus, for

```text
T=sum_(G in O) G,       M=T/16,
```

one has

```text
tau(T)=2,                 tau(T^2)=75/8.             (POF4)
```

The sum is neither `2*1` nor `4*q`, and it does not commute with any of the
four raw cuts.  Its four raw overlaps are

```text
tau(T F_(--)) = 75/128,
tau(T F_(-+)) = 31/128,
tau(T F_(+-)) = 15/128,
tau(T F_(++)) = 15/128.                              (POF5)
```

Consequently the Hilbert--Schmidt expectation of the normalized orbit
average onto `A_0` is

```text
E_(A_0)(M)
 = (75/256) F_(--)
 + (31/256) F_(-+)
 + (15/256) (F_(+-)+F_(++)).                         (POF6)
```

The top cut is uniquely separated from the middle cut by

```text
75/256-31/256=11/64.                                (POF7)
```

It is therefore recovered without choosing a basis or a permutation:

```text
F_(--)
 = (4096/165)
   (E_(A_0)(M)-(31/256)q)
   (E_(A_0)(M)-(15/256)q).                           (POF8)
```

Identity `(POF8)` is formalized for three orthogonal idempotents in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean` as
`recover_top_cut_from_pauli_orbit_fingerprint`.

## What this closes and what it opens

The transported finite packet is not a coefficient normalizer, so separate
finite-subgroup exactification still does not prove that a transported cut
belongs to `A_0`.  The squared residual of the unnormalized orbit sum from
`A_0` is in fact

```text
dist_2(T,A_0)^2=3041/512.                            (POF9)
```

Thus `(POF6)` is not a hidden algebra-containment result.

What is new is a robust gauge label.  If a simultaneous finite-coordinate
reconstruction supplies the raw expectation and the transported Pauli
average, the fixed polynomial `(POF8)` canonically selects the same raw
character cut with a gap `11/64`.  This removes the residual permutation
ambiguity from that reconstruction.  It does **not** supply the missing
simultaneous reconstruction itself.

The shortest mixed audit also identifies where genuinely nonfinite behavior
first enters.  For the five transported generators
`X'_0,X'_1,Z'_0,Z'_1,R'`, the commutators with raw have detected orders

```text
2, none through exponent 128, 2, 2, 2.              (POF10)
```

Here “none through exponent 128” is only the exact bounded statement; it is
not yet a proof of infinite order.  The exceptional word

```text
h=[X'_1,raw]
```

is now the smallest explicit cross-chart direction to analyze.  The next
test is whether its powers give a recoverable multiplication module or only
another transverse orbit inside the regular representation.

## Reproducible certificate

`experiments/atlas_double_pauli_comb_blocks.py` performs the exact bounded
binary Leavitt-prefix and rational group-algebra calculation.  Its checked
output is `experiments/atlas-double-pauli-comb-blocks.json`.  The one-core MSI
run uses the existing warm source tree and completes in roughly half a
minute; no local code is run.

`experiments/atlas_raw_comb_mixed_relations.py` independently enumerates the
radius-three ball of the abstract free product of two raw order-512 packets
and hashes its exact Leavitt images.  It confirms that transported generators
partially normalize the raw Pauli coordinates but all five escape on the raw
compressor.  The checked summary is
`experiments/atlas-raw-comb-mixed-relations.json`.
