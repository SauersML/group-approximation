# The full Fourier space has a quantum unitary gap

Date: 2026-08-14

## 1. Outcome

The paired-quotient endpoint does not need classical response maps once the
two coefficient transports act unitarily on one common finite packet.
Working on the **full** Fourier space gives a shorter obstruction than the
previous reduced-mode/contraction argument.

Let `V,W` be nonzero finite sets of the same cardinality `N`, let

```text
F : l2(W) tensor K -> l2(V) tensor K
```

be unitary, and let `R,L` be unitaries on the target and source spaces.  Put

```text
T=R* F L.                                             (QFG1)
```

Then `T` is unitary.  If the crossed coefficient relation identifies `T`
with the constant Fourier kernel

```text
K_N=N^(-1/2) J_N tensor 1_K,                          (QFG2)
```

there is an immediate contradiction for `N>1`: `K_N` has rank only one in
the label coordinate and is not unitary.

More importantly, this has a dimension-free normalized-Hilbert--Schmidt
version.  For every finite tracial coefficient algebra `C` and every
unitary `T in M_N(C)`,

```text
||T-K_N||_2^2 >= 2-2/sqrt(N).                         (QFG3)
```

Thus for `N>=2`,

```text
||T-K_N||_2^2 >= 2-sqrt(2).                           (QFG4)
```

The coefficient dimension and the matrix-coordinate dimension do not enter
the constant.

## 2. Proof of the gap

Let `p=N^(-1)J_N tensor 1` be the constant-label projection.  Then

```text
K_N=sqrt(N) p,
tau(p)=1/N,
||K_N||_2=1.                                         (QFG5)
```

For a unitary `T`, traciality gives

```text
tau(T* p)=tau(p T* p).                                (QFG6)
```

The compression `p T* p` is a contraction in the corner `pM_N(C)p`.
Therefore

```text
|tau(T* p)|<=tau(p)=1/N,                              (QFG7)
```

and hence

```text
|tau(T* K_N)|<=1/sqrt(N).                             (QFG8)
```

Expanding the squared `L2` distance gives

```text
||T-K_N||_2^2
 =||T||_2^2+||K_N||_2^2-2 Re tau(T* K_N)
 >=2-2/sqrt(N).                                      (QFG9)
```

This proof is operator-valued.  It does not assume that the entries of `T`
commute, are projections, or arise from a classical permutation.

## 3. Application to a perfect binary pairing

Let `V,W` be finite `F_2`-spaces with a perfect pairing `b`.  The normalized
Fourier operator is

```text
(F_b)_(v,w)=N^(-1/2)(-1)^(b(v,w)).                   (QFG10)
```

It is unitary.  For bijective classical transports `r,l`, the matrix of the
transported pairing is

```text
P_r* F_b P_l.
```

If `b(rv,lw)=0` for every `v,w`, this matrix is exactly `K_N`.  Equations
`(QFG3)--(QFG4)` show that the same conclusion is impossible for arbitrary
operator-valued unitary transports as soon as the crossed relation controls
the complete Fourier operator in normalized `L2`.

The robust statement needed by the atlas is therefore only

```text
||R_n* F_(b,n) L_n-K_(N_n)||_2 -> 0,                 (QFG11)
```

with `R_n,L_n,F_(b,n)` unitary on one common finite packet and `N_n>=2`.
This contradicts `(QFG4)` directly.

## 4. What this removes

The earlier endpoint in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md` deleted the constant
source mode and the target delta mass, then sought contractions satisfying

```text
R_0* U L_0 ~= U,
R_1* U L_1 ~= U,
R_0* U L_1 ~= 0.
```

That route needed both diagonal identities to prove near-bijectivity,
invariance of the reduced modes, and the multiplicative `2-sqrt(3)`
contraction gap.  On the full Fourier space the crossed kernel should not be
discarded: its failure to be unitary is already the obstruction.

Once `(QFG11)` is available, none of the following is needed at the final
analytic step:

1. commuting magic-unitary coefficients;
2. a whole-map PVM or a common classical latent map;
3. multiplication-table quantum classicalization;
4. the two diagonal transport identities;
5. deletion or approximate invariance of the two trivial Fourier modes; or
6. the `2-sqrt(3)` contraction packet.

The recent multiplicative-unitary classicalization results remain correct
fallback endpoints.  They are strictly stronger than what `(QFG11)` asks
for.

## 5. The exact remaining atlas gate

The shortcut does **not** say that the current local Pauli relations already
imply `(QFG11)`.  The order-32 Pauli countermodel proves they do not.  What it
lacks is one common coefficient packet on which:

1. the raw and transported character decompositions have matched finite
   multiplicity;
2. the pairing Fourier operator is defined between those decompositions;
3. the two relevant group words have negligible leakage from the packet, so
   their compressions can be replaced by unitaries; and
4. the cross-root Steinberg relation controls the **complete** operator in
   `(QFG11)`, rather than only separate block-mass marginals.

This is a coherent operator statement, but it is weaker than classicalizing
the coefficient maps.  In particular, phases and noncommuting multiplicity
blocks are harmless: they are absorbed into the arbitrary unitary `T` in
`(QFG3)`.

The live endpoint is now:

> **Full-space Fourier packet gate.**  Recover a positive-trace common
> finite coefficient packet for the two atlas charts, with equal label
> multiplicities and negligible transport leakage, on which the crossed
> coefficient relation implies `(QFG11)`.

The analytic contradiction after this recovery is one line and has the
fixed squared gap `2-sqrt(2)`.

## 6. Relation to the magic-unitary idea

A magic transition matrix would certainly supply a unitary operator-valued
matrix, so the gap applies to it.  But projection entries and row/column
commutativity are irrelevant to `(QFG3)`.  The right target is therefore not
"extract a quantum permutation" unless the atlas naturally supplies one.
It is simply "extract the complete unitary block transport on a common
Fourier packet."  This avoids replacing one classicalization problem by a
quantum-permutation extraction problem.
