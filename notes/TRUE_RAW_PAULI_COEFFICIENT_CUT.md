# The raw involution is a trace-half projection in the Pauli coefficient factor

Date: 2026-08-13

## 1. Exact finite subgroup

Let

\[
 p_0=s_0t_0
\]

and, inside the rank-four elementary group over the binary Leavitt algebra,
put

\[
 X=x_{12}(p_0),\qquad Y=x_{23}(p_0),\qquad Z=x_{13}(p_0).
 \tag{RPCut1}
\]

Because `p_0^2=p_0`, the Steinberg relation gives

\[
 [X,Y]=Z.
 \tag{RPCut2}
\]

Exact all-depth Leavitt arithmetic verifies that

\[
 H_0=\langle X,Y\rangle
\]

has order eight, with element-order histogram

```text
order 1: 1
order 2: 5
order 4: 2.
```

Thus `H_0` is the order-eight dihedral Heisenberg group, and `Z` is its
central commutator.

Let `r` be the raw involution.  The already formalized identity

\[
 [r,\alpha(\mathrm{Core})]=1
 \tag{RPCut3}
\]

implies that `r` centralizes `H_0`.  The exact matrix audit additionally
checks

\[
 r\notin H_0,\qquad r^2=1,
 \]

and hence

\[
 \boxed{\langle H_0,r\rangle\cong H_0\times C_2.}
 \tag{RPCut4}
\]

The generated group has order `16`, with the expected direct-product order
histogram `1,11,4` in orders `1,2,4`.

## 2. Pauli coefficient placement

Let a trace-preserving hyperlinear model be exactified on the fixed finite
subgroup in `(RPCut4)`.  On the `Z=-1` central sector, the unique
noncommutative irreducible representation of `H_0` is the two-dimensional
Pauli representation.  Therefore the sector has the canonical form

\[
 e_Z\mathcal H\cong\mathbb C^2\otimes\mathcal K,
 \tag{RPCut5}
\]

with `H_0` acting on the first factor.  Since `r` centralizes all of `H_0`,
Schur's lemma gives

\[
 r|_{e_Z\mathcal H}=I_2\otimes\widehat r.
 \tag{RPCut6}
\]

Consequently

\[
 e_Z{1-r\over2}
 =I_2\otimes {1-\widehat r\over2}
 \tag{RPCut7}
\]

is not merely an ambient spectral projection: it lies in the finite
multiplicity/coefficient factor after the fixed Pauli block is removed.

## 3. Exact trace

Restriction of the canonical group trace to the embedded finite group
`H_0 times C_2` is its regular character.  Therefore

\[
 \tau(e_Z)=\frac12,
 \qquad
 \tau\left(e_Z{1-r\over2}\right)=\frac14.
 \tag{RPCut8}
\]

After normalizing the trace on the `Z=-1` sector, the coefficient cut

\[
 \widehat e={1-\widehat r\over2}
\]

satisfies

\[
 \boxed{\tau_{\mathcal K}(\widehat e)=\frac12.}
 \tag{RPCut9}
\]

This crosses one of the main gates in the one-cut program.  The raw carrier
now has all three required properties:

1. it is an honest complex projection;
2. it belongs to a canonical finite root-character multiplicity corner; and
3. it has a dimension-independent normalized trace, exactly `1/2`.

## 4. What remains

The result does not yet produce asymmetric leakage.  One must compress the
comb or hard/comb transport to the same Pauli coefficient factor and prove
that, relative to `hat e`, one direction has vanishing mass while the other
retains positive mass.  The finite trace identity

\[
 \|(1-\widehat e)W\widehat e\|_2
 =\|\widehat eW(1-\widehat e)\|_2
\]

would then give the contradiction.

The next calculation is therefore sharply bounded: compute the Pauli block
matrix of the scalarized comb and of the first hard pair relative to
`H_0`, retaining `hat e` as a coefficient projection.  Unlike the invalid
`p_001` XOR formula, no Leavitt star is being identified with group inverse.

## 5. Replay and formal support

The exact finite-group audit is

```text
experiments/atlas_raw_compressed_heisenberg.py
```

with output

```text
experiments/atlas-raw-compressed-heisenberg.json
```

The identities `r^2=1`, `r!=1`, and `(RPCut3)` are kernel-checked in
`GroupApproximation/Leavitt/RawSwapCompressors.lean`.  The general complex
negative-cut and joint-cut calculations are kernel-checked in
`GroupApproximation/Sofic/ExactInvolutionCut.lean` as

```text
jointExactInvolutionNegativeCut_isOrthogonalProjection
normTrace_jointExactInvolutionNegativeCut
```

The second theorem proves the `1/4` trace in `(RPCut8)` from the three
regular-character equations `tau(Z)=tau(r)=tau(Zr)=0`.
