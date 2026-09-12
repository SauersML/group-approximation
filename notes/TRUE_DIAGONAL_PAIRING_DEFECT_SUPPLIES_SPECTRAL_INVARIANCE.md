# Diagonal pairing defects supply spectral invariance

Date: 2026-08-14

## 1. Outcome

The reduced-Fourier spectral route does not need a separate invariance
hypothesis.  A diagonal pairing defect already forces the corresponding
transition intertwining, even when the recovered arrows are only
contractions.

Let `W,R,L` be contractions in a finite tracial matrix algebra and put

```text
D=R* W L-W,                 H=W* W,
eta=||D||_2.                                          (DPI1)
```

Then

```text
||W L-R W||_2 <=eta+sqrt(2 eta),
||W* R-L W*||_2 <=eta+sqrt(2 eta),                   (DPI2)
```

and consequently

```text
||[H,L]||_2 <=2 eta+2 sqrt(2 eta).                   (DPI3)
```

The estimate is dimension-free.  In particular, `eta->0` implies
`||[W*W,L]||_2->0` without any unitary or global near-bijectivity assumption.

## 2. Mass-saturation proof

Set

```text
X=W L,                 Y=R* X.                       (DPI4)
```

Because `W,R,L` are contractions,

```text
||Y||_2 <=||X||_2 <=||W||_2 <=1.                    (DPI5)
```

The defect says `||Y-W||_2=eta`, so the reverse triangle inequality gives

```text
||Y||_2 >=max(0,||W||_2-eta).                        (DPI6)
```

Let `Q=1-R R*`.  It is a positive contraction.  Direct trace expansion
gives

```text
||X||_2^2-||Y||_2^2=tau(X* Q X),                    (DPI7)
```

while `Q^2<=Q` gives

```text
||QX||_2^2<=tau(X* Q X).                             (DPI8)
```

Equations `(DPI5)--(DPI7)` imply

```text
||X||_2^2-||Y||_2^2<=2 eta.                          (DPI9)
```

For `eta<=||W||_2`, this is
`||W||_2^2-(||W||_2-eta)^2<=2 eta`; for
`eta>||W||_2`, it follows from
`||X||_2^2<=||W||_2^2<eta^2<=2 eta`, since the distance
of two contractions is at most `2`.

The exact algebraic decomposition is

```text
W L-R W
 =R(R* W L-W)+(1-R R*)W L.                          (DPI10)
```

The first summand has norm at most `eta`, and `(DPI8)--(DPI9)` bound the
second by `sqrt(2 eta)`.  This proves the first half of `(DPI2)`.

Taking adjoints turns `D` into

```text
D*=L* W* R-W*.                                       (DPI11)
```

Apply the same argument with `(W*,L,R)` replaced by `(W*,R,L)`.  This proves
the second half of `(DPI2)`.  Finally use the exact two-sided identity

```text
[W*W,L]
 =W*(W L-R W)+(W*R-LW*)W                            (DPI12)
```

to obtain `(DPI3)`.

## 3. Apply both diagonal pairing relations

The reduced pairing packet asks for contractions satisfying

```text
R0* W L0 = W,
R1* W L1 = W,
R0* W L1 = 0                                        (DPI13)
```

asymptotically in normalized Hilbert--Schmidt norm.  Apply `(DPI3)` to the
first two defects.  It gives

```text
||[W*W,L0]||_2 ->0,
||[W*W,L1]||_2 ->0.                                  (DPI14)
```

These are exactly the two commutators needed by spectral coarea.  In the
vertex-cover language of
`TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md`, choose the
right-factor cover `{L0,L1}`.  Every terminal product edge has one of these
right endpoints, so no commutator estimate for `R0` or `R1` is needed.

## 4. Quantitative coarea consequence

For the trace-flat Pauli transition, `H=W*W` has the already proved moments.
Coarea on `[1/32,1/16]` selects one cut

```text
P=1_[t,infinity)(H),          tau(P)>=1/120           (DPI15)
```

whose `L0,L1` leakage tends to zero.  More explicitly, if

```text
eta_i=||Ri* W Li-W||_2,
```

then

```text
sum_(i=0)^1 ||[P,Li]||_2^2
 <=64 sum_(i=0)^1 (eta_i+sqrt(2 eta_i)).              (DPI16)
```

On `P`, the singular values of `W` are at least `1/sqrt(32)`.  Hence the
retained transition has inverse bound at most `4 sqrt(2)`, while `(DPI16)`
supplies the right-factor leakage needed to pass all three relations in
`(DPI13)` to the common corner.  The ambient Leavitt floor from
`TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md` then supplies the
fixed contradiction.

Thus positive density, conditioning, and invariance all follow from the
trace-flat moments and the same two diagonal defects already present in the
decoder.  There is no independent spectral-synchronization hypothesis.

## 5. What remains

This does not extract `(DPI13)` from an abstract group microstate.  The live
theorem is now exactly common-coordinate recovery of one trace-flat pairing
block and the four contraction arrows with the two diagonal and one crossed
defect tending to zero.  That is the finite-multiplicity/radical-quotient
decoder itself.

The exact finite Pauli countermodel still blocks any attempt to infer these
coefficient contractions from local Weyl signs alone.  The raw/comb
cross-chart multiplication module must resolve the extension fibers.  The
advance here is that, once the three common-coordinate defects are obtained,
there is no further singular-value-invariance lemma to prove.

## 6. Formalization status

The exact decomposition `(DPI10)` is transcribed without placeholders as
`pairing_defect_transition_decomposition`, the two-sided identity `(DPI12)`
as `hsNormSq_transitionGram_commutator_le_two_sided`, and the unitary special
case as `hsNormSq_pairing_defect_controls_sourceGram_commutator` in
`GroupApproximation/Sofic/LeavittTraceFloor.lean`.  Its scalar squared-mass
arithmetic is transcribed as `contraction_sq_mass_loss_le_two`, and
`hsNormSq_pairing_transition_le_of_range_deficiency` propagates any proved
range-deficiency bound through `(DPI10)`.  The matrix positivity bridge
`(DPI7)--(DPI8)` is now transcribed as
`hsNormSq_range_deficiency_le_mass_loss`: it proves

```text
||(1-RR*)X||_2^2 <= ||X||_2^2-||R*X||_2^2
```

for every contraction `R`, by applying trace positivity to
`Q-Q^2=R(1-R*R)R*`.  The remaining formal work is to combine this matrix
lemma with the already transcribed scalar saturation bound and its adjoint
copy, yielding the full contraction form of `(DPI2)--(DPI3)` as one exported
theorem.  This is source-level formalization pending a kernel build; per
instruction, no local build was run.
