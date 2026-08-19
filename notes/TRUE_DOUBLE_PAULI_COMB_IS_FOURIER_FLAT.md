# The comb is Fourier-flat on the raw double-Pauli coefficient

Date: 2026-08-13

## Outcome

The raw-invariant coefficient `C2^2` from
`TRUE_RAW_DOUBLE_PAULI_COEFFICIENT_PACKET.md` has an exact, positive-density
comb transition table.  It is not Hall-deficient: every one of its sixteen
raw-to-comb character blocks is nonzero, and all sixteen have exactly the same
canonical tracial mass.  Here "Fourier-flat" means trace-flat; it does not
mean that the individual blocks are scaled isometries.

Work in the trace-half carrier

```text
q=(1-d)/2
```

and let `B0,B1` be the two commuting raw-fixed coefficient involutions.  For
`epsilon=(epsilon0,epsilon1)` in `{+1,-1}^2`, define the four character cuts

```text
F_epsilon = q (1+epsilon0 B0)(1+epsilon1 B1)/4.
```

They are pairwise orthogonal, sum to `q`, and have canonical group trace

```text
tau(F_epsilon)=1/8.                                 (FFC1)
```

Let `U` denote the comb compressor and put

```text
G_eta=U* F_eta U.
```

Exact rational group-algebra arithmetic over the binary Leavitt-prefix model
gives, for every pair of characters,

```text
tau(F_epsilon G_eta)=1/64.                          (FFC2)
```

Thus the full `4 x 4` transition table is constant.  Summing `(FFC2)` gives

```text
tau(q U* q U)=1/4,                                  (FFC3)
```

the independent value for two trace-half carriers.

For projections `F,G`,

```text
||F G||_2^2=tau(FG).
```

Consequently every comb coefficient block has squared Hilbert--Schmidt mass
`1/64` (norm `1/8`).  The generic projection identity is kernel-checked as
`hsNormSq_projection_product_eq_re_normTrace` in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean`.

## Why this persists in hyperlinear microstates

Each `F_epsilon` is a fixed rational polynomial in finitely many marked group
unitaries.  Equation `(FFC2)` is therefore a finite group-algebra trace
identity, not a statement about a chosen representation or coordinate gauge.
In any trace-preserving matrix microstate sequence, the corresponding
polynomial traces converge to `1/64`.  After the standard exactification of
the finite involution packet, all sixteen coefficient blocks retain fixed
positive normalized rank/mass.  There is no vanishing-density escape.

This supplies the positive-density half of the proposed coefficient-pairing
argument.  In the terminology of the radical-quotient program, the comb is
trace-Fourier-flat across the four raw coefficient characters.

There is an exact limitation.  Already for the `(-1,-1)` character on both
sides, the stronger mutually-unbiased identities fail:

```text
F G F != (1/8) F,            G F G != (1/8) G.       (FFC3a)
```

Thus `(FFC2)` controls total Hilbert--Schmidt mass but not the singular-value
distribution of a block.  It does not by itself supply the reduced Fourier
unitary in `(RPC128)` or a uniform condition-number bound.  The finite
multiplicity extraction must still produce that operator-level structure (or
use a spectral truncation with invariant leakage control).

## The falsification and the remaining theorem

The same audit proves that no coefficient-character support block vanishes:

```text
F_epsilon G_eta != 0            for all epsilon,eta. (FFC4)
```

Moreover none of the four raw character sectors kills the leakage

```text
(1-E) (U* Q U),
```

where `E` and `Q` are the trace-`1/8` initial and trace-`1/4` carrier cuts of
`PauliBranchTransfer`.  Therefore neither a Hall-zero graph nor a direct
character-sector refinement proves the missing containment `U*QU <= E`.

The remaining matrix-specific target is now asymmetric and quantitative:

> Pass from the Fourier-flat ambient blocks to the finite multiplicity module
> recovered from coefficient multiplication.  Prove that one orientation of
> a selected block is asymptotically forbidden there, while `(FFC2)` forces
> the reverse block to retain squared mass at least `1/64-o(1)`.

Finite-dimensional unitary projection balance then contradicts the mismatch.
The important advance is that the total positive lower bound no longer has to be
guessed, reconstructed from rank, or protected from dilution: it is the exact
canonical trace `1/64`.  What remains is the one-sided module-support
vanishing theorem together with operator-level control of the retained
singular-value sector.

## Reproducible certificate

`experiments/atlas_double_pauli_comb_blocks.py` implements a bounded rational
group-algebra audit with canonical prefix-expansion keys.  Its checked output
is `experiments/atlas-double-pauli-comb-blocks.json`.  The exact computation
finishes in seconds on one MSI core; the first naïve equality-scan version was
stopped and replaced rather than allowed to run indefinitely.  No local code
or build was run.
