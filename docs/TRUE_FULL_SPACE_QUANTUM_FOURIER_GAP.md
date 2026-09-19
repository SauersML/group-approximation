# The full Fourier space has a quantum contraction gap

Date: 2026-08-14

## 1. Outcome

The paired-quotient endpoint does not need classical response maps.  In
fact, the two coefficient transports need not act unitarily on the recovered
packet.  Operator-norm contractions already have a fixed distance from the
crossed constant kernel.  Working on the **full** Fourier space therefore
gives a shorter obstruction than the previous reduced-mode/contraction
argument.

Let `V,W` be nonzero finite sets of the same cardinality `N`, let

```text
F : l2(W) tensor K -> l2(V) tensor K
```

be unitary, and let `R,L` be contractions on the target and source spaces.
Put

```text
T=R* F L.                                             (QFG1)
```

Then `T` is a contraction.  If the crossed coefficient relation identifies
`T` with the constant Fourier kernel

```text
K_N=N^(-1/2) J_N tensor 1_K,                          (QFG2)
```

there is an immediate contradiction for `N>1`: `K_N` has operator norm
`sqrt(N)`, while `T` has operator norm at most one.

More importantly, this operator-norm mismatch has a dimension-free
normalized-Hilbert--Schmidt version.  For every finite tracial coefficient
algebra `C` and every contraction `T in M_N(C)`,

```text
||T-K_N||_2^2 >= (1-1/sqrt(N))^2.                     (QFG3)
```

Thus for `N>=2`,

```text
||T-K_N||_2^2 >= 3/2-sqrt(2).                         (QFG4)
```

The coefficient dimension and the matrix-coordinate dimension do not enter
the constant.  If `T` is unitary, the sharper bound

```text
||T-K_N||_2^2 >= 2-2/sqrt(N) >= 2-sqrt(2)             (QFG4a)
```

also holds, but it is not needed.

## 2. Proof of the gap

Let `p=N^(-1)J_N tensor 1` be the constant-label projection.  Then

```text
K_N=sqrt(N) p,
tau(p)=1/N,
||K_N||_2=1.                                         (QFG5)
```

Let `T` be a contraction.  Right multiplication by `p` is the orthogonal
projection in tracial `L2`, so

```text
||T-K_N||_2 >= ||(T-K_N)p||_2.                        (QFG6)
```

Moreover,

```text
||Tp||_2<=||T||_infinity ||p||_2<=1/sqrt(N),          (QFG7)
```

whereas `||sqrt(N)p||_2=1`.  The reverse triangle inequality
therefore gives

```text
||(T-K_N)p||_2>=1-1/sqrt(N).                          (QFG8)
```

Squaring proves `(QFG3)`, and monotonicity in `N>=2` proves `(QFG4)`.

For completeness, if `T` is unitary, traciality and compression to `p` give
`|tau(T* p)|<=tau(p)=1/N`, hence
`|tau(T* K_N)|<=1/sqrt(N)`.  Expanding the squared distance then gives

```text
||T-K_N||_2^2
 =||T||_2^2+||K_N||_2^2-2 Re tau(T* K_N)
 >=2-2/sqrt(N).                                      (QFG9)
```

This proof is operator-valued.  It does not assume that the entries of `T`
commute, are projections, or arise from a classical permutation.  The
contraction version does not even use a trace-overlap estimate.

The estimate is also immune to one common multiplicity holonomy.  If
`C in M` is unitary and

```text
K_(N,C)=N^(-1/2)J_N tensor C,                         (QFG9a)
```

then right multiplication by `1 tensor C*` sends `K_(N,C)` to `K_N` and
sends every contraction to a contraction.  Hence `(QFG3)--(QFG4)` hold
unchanged with `K_(N,C)` in place of `K_N`.  Stone--von Neumann
factorizations of the form `S_fixed tensor C` therefore introduce no gauge
loss at this endpoint.  What would be insufficient is a different
coefficient operator in every matrix entry; aligning those entries is part
of complete cross-operator control.

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
operator-valued contraction transports as soon as the crossed relation
controls the complete Fourier operator in normalized `L2`.

The robust statement needed by the atlas is therefore only

```text
||R_n* F_(b,n) L_n-K_(N_n)||_2 -> 0,                 (QFG11)
```

with `R_n,L_n` contractions, `F_(b,n)` unitary on one common finite packet,
and `N_n>=2`.  This contradicts `(QFG4)` directly.  Compressions of ambient
group unitaries are automatically contractions, so no polar repair is part
of this endpoint.

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
discarded: its singular value `sqrt(N)` is already incompatible with a
contraction.

Once `(QFG11)` is available, none of the following is needed at the final
analytic step:

1. commuting magic-unitary coefficients;
2. a whole-map PVM or a common classical latent map;
3. multiplication-table quantum classicalization;
4. the two diagonal transport identities;
5. deletion or approximate invariance of the two trivial Fourier modes; or
6. polar repair, near-bijectivity, or the `2-sqrt(3)` contraction packet.

The recent multiplicative-unitary classicalization results remain correct
fallback endpoints.  They are strictly stronger than what `(QFG11)` asks
for.

For the existing two-qubit Pauli packet the label space is already
`C_2^2`, so `N=4`.  On that fixed packet `(QFG3)` reads

```text
||T-K_4||_2^2>=1/4,                                  (QFG11a)
```

and the unitary version reads `||T-K_4||_2^2>=1`.  Thus a successful atlas
application need not pass to growing radical-quotient rank.  It may instead
use the forced four-label Pauli Fourier factor and prove one complete
crossed-operator identity on its multiplicity space.  The present raw/comb
trace-flat calculation controls only the sixteen block masses, not their
common coefficient operator, so it does not yet establish `(QFG11a)`.
Those exact masses are nevertheless already large enough: common-block
coherence would force the common coefficient to have `L2` norm
`1/sqrt(2)>1/2`, and the variable-coefficient contraction gap would finish.
See `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md`.

## 5. The exact remaining atlas gate

The shortcut does **not** say that the current local Pauli relations already
imply `(QFG11)`.  The order-32 Pauli countermodel proves they do not.  What it
lacks is one common coefficient packet on which:

1. the raw and transported character decompositions admit one common finite
   coefficient packet;
2. the pairing Fourier operator is defined between those decompositions;
3. the compressions of the two relevant group words define the contraction
   factors in `(QFG11)`; and
4. the cross-root Steinberg relation controls the **complete compressed
   operator** in
   `(QFG11)`, rather than only separate block-mass marginals.

This is a coherent operator statement, but it is weaker than classicalizing
the coefficient maps.  In particular, phases and noncommuting multiplicity
blocks are harmless: they are absorbed into the arbitrary contraction `T`
in `(QFG3)`.

The live endpoint is now:

> **Full-space Fourier packet gate.**  Recover a positive-trace common
> finite coefficient packet for the two atlas charts, with a flat pairing
> Fourier operator, on which the crossed coefficient relation implies the
> complete compressed-operator estimate `(QFG11)`.

The analytic contradiction after this recovery is one line and has the
fixed squared gap `3/2-sqrt(2)`.  Leakage need not be shown to vanish
separately; any effect it has must only be included in the error in
`(QFG11)`.

## 6. Relation to the magic-unitary idea

A magic transition matrix would certainly supply a unitary operator-valued
matrix, so the sharper gap applies to it.  But projection entries and
row/column commutativity are irrelevant to `(QFG3)`.  The right target is
therefore not "extract a quantum permutation" unless the atlas naturally
supplies one.  It is simply "extract the complete contracted block transport
on a common Fourier packet."  This avoids replacing one classicalization problem by a
quantum-permutation extraction problem or a polar-decomposition problem.
