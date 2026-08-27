# Two left arrows suffice for the spectral Leavitt endgame

Date: 2026-08-14

## 1. Outcome

The positive-density spectral route does not require a common reducing cut
for all four decoded Leavitt contractions.  It requires one-sided leakage
control only for the two contractions which occur on the left of the three
terminal products.

Let `P` be a projection in a finite tracial matrix algebra and let
`R0,S0,R1,S1` be contractions.  The exact identities

```text
P Ri P Sj P-P
 =P(Ri Sj-I)P-P Ri(1-P)SjP,                         (TLS1)

P Ri P Sj P
 =P(Ri Sj)P-P Ri(1-P)SjP                           (TLS2)
```

show that the only carrier escape term is

```text
P Ri(1-P),                 i=0,1.                   (TLS3)
```

No commutator or leakage hypothesis on `S0,S1` is needed.

There is a symmetric improvement.  The leakage term in `(TLS1)` satisfies

```text
||P Ri(1-P)SjP||_2
 <=min { ||P Ri(1-P)||_2, ||(1-P)SjP||_2 }.          (TLS3a)
```

Thus one may control either endpoint of each of the three product edges

```text
(R0,S0),          (R1,S1),          (R0,S1).         (TLS3b)
```

Any vertex cover of this three-edge graph is sufficient.  Its minimum size
is two.  Besides `{R0,R1}`, the especially natural choice is

```text
{R0,S1}.                                             (TLS3c)
```

This is exactly the crossed pair in the finite paired-quotient proof: the
`00` diagonal makes `R0` injective, the `11` diagonal makes `S1` injective,
and the `01` relation is the crossed zero.

## 2. Quantitative corner contradiction

Write `alpha=tau(P)>0`, and set

```text
eta=max {
  ||P(R0 S0-I)P||_2,
  ||P(R1 S1-I)P||_2,
  ||P(R0 S1)P||_2 },

lambda=max {
  ||P R0(1-P)||_2,
  ||P R1(1-P)||_2 }.                                (TLS4)
```

Regard `PMP` as a matrix algebra with identity `P` and normalized corner
trace.  The four compressions

```text
Rhat_i=P Ri P,             Shat_j=P Sj P             (TLS5)
```

are contractions.  Equations `(TLS1)--(TLS2)` and the Hilbert--Schmidt ideal
inequality imply that each of the three corner-normalized Leavitt defects is
at most

```text
(eta+lambda)/sqrt(alpha).                            (TLS6)
```

The sharp multiplicative Leavitt floor therefore gives

```text
eta+lambda >=sqrt(alpha)(2-sqrt(3)).                 (TLS7)
```

For the spectral cut already obtained from the trace-flat Pauli block,

```text
alpha>=1/120,
```

so every finite matrix coordinate satisfies the fixed ambient floor

```text
eta+lambda >=(2-sqrt(3))/sqrt(120).                  (TLS8)
```

This is the complete analytic contradiction after carrier selection.

For the crossed-pair choice `(TLS3c)`, replace `lambda` in `(TLS4)` by

```text
lambda_cross=max {
  ||P R0(1-P)||_2,
  ||(1-P)S1P||_2 }.                                  (TLS8a)
```

The same proof and the same constants `(TLS6)--(TLS8)` apply.  The `00` and
`01` edges are charged to `R0`; the `11` edge is charged to `S1`.

## 3. Combine with transition synchronization

Let `W=GF` be the trace-flat transition block and `H=W*W=FGF`.  Spectral
coarea chooses `P=1_[t,infinity)(H)` of trace at least `1/120`.  To make
`lambda` tend to zero, it is enough to prove

```text
||[H,R0]||_2 ->0,             ||[H,R1]||_2 ->0.      (TLS9)
```

The transition identities from
`TRUE_TRANSITION_INTERTWINING_CONTROLS_SPECTRAL_LEAKAGE.md` reduce `(TLS9)`
further.  For suitable target arrows `R0',R1'`, it suffices to have

```text
||W Ri-Ri' W||_2 ->0,
||W* Ri'-Ri W*||_2 ->0,              i=0,1.          (TLS10)
```

Indeed,

```text
[W*W,Ri]
 =W*(W Ri-Ri'W)+(W*Ri'-RiW*)W.                       (TLS11)
```

Thus the previous four-arrow synchronization target was stronger than
necessary.  The live spectral decoder needs:

1. the three ambient product relations in `(TLS4)`;
2. forward and reverse transition synchronization for only `R0,R1`; and
3. the already proved trace-flat moments of `W`.

Everything after those inputs is dimension-free and quantitative.

Alternatively, synchronize the crossed pair `R0,S1`.  This is likely the
better interface with the radical-quotient construction because those are
the two maps whose injectivity/surjectivity drives the finite obstruction.
Coarea controls both orientations of each cut leakage, so no additional
argument is needed to use `(TLS8a)`.

For the reduced pairing packet, the right-factor cover `{L0,L1}` is better
still.  Its two diagonal defects `Ri* W Li-W` automatically control
`[W*W,Li]` for contraction arrows by mass saturation.  Hence the two
required coarea commutators are already among the three terminal pairing
hypotheses.  See
`TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md`.

## 4. What remains unproved

This note does not extract `(TLS10)` from the atlas microstate.  The target
arrows and their common finite-multiplicity coordinate system must still be
recovered from the cross-chart multiplication-module relations.  They cannot
be chosen by an arbitrary gauge separately for each block.

The exact finite Pauli countermodels remain a valid warning: local Weyl
relations and trace-flat block masses alone do not imply `(TLS10)`.  The new
result only shows that, once the multiplication module supplies two
two-sided transition laws, no further four-arrow invariance theorem is
needed.

## 5. Formalization status

The algebraic compression formulas `(TLS1)--(TLS2)` are transcribed without
placeholders as `compressed_product_sub_carrier_identity` and
`compressed_cross_product_identity` in
`GroupApproximation/Sofic/LeavittTraceFloor.lean`.  The sharp terminal floor
is already formalized there.  The normalization and ideal-norm combination
in `(TLS6)--(TLS8)` remains a paper proof.  Per instruction, no local build
was run.
