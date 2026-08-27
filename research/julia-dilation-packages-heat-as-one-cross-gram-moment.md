---
rg: 2
id: julia-dilation-packages-heat-as-one-cross-gram-moment
kind: claim
title: The Julia dilation packages the Fanizza heat amplitude as one projection overlap
distinct_from:
  fanizza-heat-return-is-one-cyclic-amplitude-product: that starts from the positive amplitude square as the returned target; this realizes that target as one explicit 2 by 2 projection cross-Gram corner.
  support-only-toeplitz-return-cannot-see-heat-decay: that rules out support rank as a proxy for amplitude; this shows the exact additional overlap moment which retains the amplitude.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that uses an overlap near full mass to align two packet transports; this overlap is small on NONHALT instances and is the quantity to be charged.
---

Let `B` be a contraction in a unital C-star algebra and put

```text
D_B=(1-B^*B)^(1/2),
D_(B*)=(1-BB^*)^(1/2),
U_B=[ B       D_(B*) ;
      D_B     -B^*   ],
E  =[ 1 0 ; 0 0 ].                                    (JHG1)
```

The defect intertwining identity `B D_B=D_(B*) B` makes `U_B` unitary.
With `Q_B=U_B^* E U_B`, both `E` and `Q_B` are projections of normalized
matrix trace `1/2`, and

```text
E Q_B E=[ B^*B 0 ; 0 0 ].                             (JHG2)
```

For the accelerated Fanizza filter `B=B_t=D_Rp_t(H_m)`, every NONHALT
representation therefore satisfies

```text
(tau tensor tr_2)(E Q_(B_t))
 = (1/2) tau(B_t^*B_t)
 <= C_m/(8t^2).                                       (JHG3)
```

On the perfect HALT quotient, `B_t=D_R`; hence the same overlap is the
nonzero `D_R` carrier in the upper block.  Countable amplification causes no
problem.

Thus the heat-filter return can be stated using only two projections and one
cross-Gram scalar.  A finite-matrix-only cell must return the fixed marked
projection `P` to the small corner `E Q_(B_t) E`, equivalently produce

```text
YX approximately P,
XY approximately E Q_(B_t) E.                         (JHG4)
```

The Julia unitary supplies the right-hand target exactly.  It does not
supply `X,Y` or the scalar comparison to `P`.

The rank ledger explains the remaining difficulty.  `E` and `Q_B` both
have rank exactly half the amplified dimension for every `B`, including
`B=0`.  Their graph/range multiplicities therefore contain no heat
information; only their overlap `(JHG2)` does.  A 3 by 3 dilation cannot
improve this: unitary conjugacy preserves every carrier rank and merely
redistributes the same cross-Gram moments among more blocks.
