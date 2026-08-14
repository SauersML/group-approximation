# Perfect binary pairings have a dimension-free transport error floor

Date: 2026-08-13

## 1. Outcome

The finite paired-radical endpoint admits a direct robust formulation which
does not require constructing a complex Fourier unitary, deleting its
constant mode, or separately proving that four pullback operators are
contractions.

Let `V,W` be nonzero finite binary vector spaces of the same cardinality
`N`, and let

```text
b : V times W -> F2
```

be a perfect bilinear pairing.  For maps `R : V -> V` and `L : W -> W`, put

```text
eps(R,L) = Pr[b(Rv,Lw) != b(v,w)],
zeroErr(R,L) = Pr[b(Rv,Lw) != 0],                  (RPF1)
```

where `(v,w)` is uniform on `V times W`.

For arbitrary maps `R0,R1,L0,L1`, one has

```text
zeroErr(R0,L1) + 4 eps(R0,L0) + 4 eps(R1,L1)
  >= (N-1)/(2N).                                    (RPF2)
```

Consequently

```text
max(zeroErr(R0,L1),eps(R0,L0),eps(R1,L1))
  >= (N-1)/(18N)
  >= 1/36.                                           (RPF3)
```

This is a dimension-independent robust form of the exact finite theorem in
`TRUE_FINITE_PAIRED_QUOTIENT_OBSTRUCTION.md`.

## 2. Approximate diagonal transport is close to a permutation

Fix `R,L` and write `eps=eps(R,L)`.  For each `v`, let `E(v)` be the number
of labels `w` on which

```text
b(Rv,Lw) != b(v,w).
```

Consider a fiber `F` of `R` with cardinality `s>=2`.  For distinct
`v,v'` in `F`, the two predicted rows are identical, while perfectness of
`b` says that the target rows `b(v,-)` and `b(v',-)` disagree at exactly
`N/2` labels.  Therefore

```text
E(v)+E(v') >= N/2.                                  (RPF4)
```

Sum `(RPF4)` over all unordered pairs in `F`.  Each `E(v)` occurs `s-1`
times, so

```text
sum_(v in F) E(v) >= sN/4.                          (RPF5)
```

Summing over the nonsingleton fibers gives

```text
N-card(im R) <= 4 eps N.                            (RPF6)
```

Choose one representative in every fiber of `R` and biject the remaining
inputs with the missing outputs.  This produces a permutation `Rbar` which
differs from `R` on at most `4 eps N` points.  Applying the column version of
the same argument produces a permutation `Lbar` with the same bound.

Applied to the two diagonal relations, this gives

```text
Pr[R0 != R0bar] <= 4 eps(R0,L0),
Pr[L1 != L1bar] <= 4 eps(R1,L1).                    (RPF7)
```

No operator norm, singular-value truncation, or condition-number estimate is
used.

## 3. The crossed-zero table cannot survive the repair

For permutations `R0bar,L1bar`, the table

```text
b(R0bar v,L1bar w)
```

is just a row-and-column permutation of the original perfect pairing table.
The zero vector contributes no ones, and every one of the other `N-1` rows
contains exactly `N/2` ones.  Its one-density is therefore

```text
(N-1)/(2N).                                         (RPF8)
```

Changing the left map on a fraction `deltaV` of inputs and the right map on
a fraction `deltaW` changes at most `deltaV+deltaW` of the whole table.
Equations `(RPF7)--(RPF8)` give `(RPF2)`, and `(RPF3)` follows because the
three coefficients in `(RPF2)` sum to nine.

## 4. Convex extension to unitary block-mass kernels

The same floor holds without choosing deterministic maps.  Let

```text
KR0,KR1 : V times V -> [0,1],
KL0,KL1 : W times W -> [0,1]
```

be doubly stochastic kernels, and define the three errors by independently
sampling the target labels from the corresponding kernels.  For example,

```text
eps00 = Pr[b(x,y) != b(v,w)],
x ~ KR0(v,-), y ~ KL0(w,-).                         (RPF9)
```

Every finite doubly stochastic matrix is a convex combination of permutation
matrices.  Choose independent Birkhoff decompositions of the four kernels.
For every resulting quadruple of permutations, `(RPF2)` holds.  Averaging
over the four decompositions gives the identical inequality

```text
eps01 + 4 eps00 + 4 eps11 >= (N-1)/(2N).            (RPF10)
```

This convex form is the one naturally produced by matrix microstates.  If
two atomic decompositions of a finite Hilbert space have `N` atoms of a
common rank `m`, the normalized squared Hilbert--Schmidt masses of the blocks
of any unitary form a doubly stochastic `N by N` matrix: row and column sums
are one because both families of atomic projections sum to the identity.
No choice of bases inside the atoms and no rounding to a single permutation
is required.

## 5. Gain for the hyperlinear program

The previous robust-radical gate asked for a normalized complex Fourier
unitary, near-bijective arrows, removal of two trivial modes, invariance of
the reduced sectors, and three contraction estimates.  The Hamming theorem
shows that all of that is unnecessary once a finite perfect-pairing label
model with uniform counting measure has been extracted.

The strictly smaller live theorem is now:

> From one canonical regular-margin normalized-HS atlas microstate, extract
> finite binary label spaces with a perfect pairing and four bistochastic
> block-mass kernels for which the two diagonal mismatch rates and the
> crossed-zero rate tend to zero.

The fixed floor `1/36` then gives the contradiction directly.  Partial maps
are harmless: extend them arbitrarily on their bad sets, which only adds the
bad-set density to the three errors.

This still does not prove nonhyperlinearity.  The unresolved step is the
common-coordinate extraction of the paired labels and kernels.  What has been
removed is the separate Fourier-flatness, near-bijectivity, and trivial-mode
analysis after that extraction.

The existing four-cut raw coefficient packet does not itself instantiate
this theorem.  Its comb transition table is exactly Fourier-flat: after
conditioning on the transported carrier, every raw label sends mass `1/4`
to every transported label.  Thus it is maximally nondeterministic and does
not satisfy either diagonal error hypothesis.  The required perfect-pairing
kernels must come from the deeper multiplication/radical quotient, not from
the ambient `C2^2` coefficient cuts alone.
