# The raw branch packet is an exact `D8 times D8` Pauli cell

Date: 2026-08-13

## 1. Two commuting Pauli factors

Let

\[
 H_0=\langle x_{12}(p_0),x_{23}(p_0)\rangle\cong D_8
\]

be the compressed root Heisenberg group, with central commutator
`z_0=x_13(p_0)`.  Put `z_1=x_13(p_1)` and let `r` be the raw involution.
Exact all-depth Leavitt arithmetic gives

\[
 \langle r,z_1\rangle\cong D_8.
 \tag{RBPC1}
\]

Every element of this second `D8` commutes with every element of `H_0`, and
the two factors have trivial intersection.  Hence

\[
 \boxed{
 \langle x_{12}(p_0),x_{23}(p_0),r,z_1\rangle
 \cong D_8\times D_8.}
 \tag{RBPC2}
\]

The order is `64`, with element-order histogram

```text
order 1:  1
order 2: 35
order 4: 28.
```

On the two negative central sectors this produces a fixed
`M_2(C) tensor M_2(C)` packet.  The raw negative cut is a rank-one Pauli
projection in the second matrix factor.  This refines the earlier statement
that it merely belongs to an unspecified multiplicity algebra.

## 2. The hard cylinder signs

Lift the characteristic-two cylinder idempotents through one central root:

\[
 z_{11}=x_{13}(p_{11}),\qquad
 z_{001}=x_{13}(p_{001}).
 \tag{RBPC3}
\]

The additive formulas for the two idempotents are now represented by group
multiplication in the elementary-abelian root subgroup, so their negative
spectral cuts are honest complex projections.  The exact subgroup is

\[
 \boxed{\langle r,z_{11},z_{001}\rangle\cong D_8\times C_2.}
 \tag{RBPC4}
\]

More precisely, `r` commutes with `z_001`, while `r` and `z_11` generate
the `D8`.  Let

\[
 c_{11}=[r,z_{11}].
\]

On the `c_11=-1` sector, `r` and `z_11` are anticommuting Pauli signs.
Restricting also to `z_001=-1`, regular trace gives

\[
 \tau(c_{11}=-1,z_{001}=-1)=\frac14,
 \tag{RBPC5}
\]

and either `z_11` half has trace `1/8`.

## 3. The exact near-miss

Within `(RBPC5)`, multiplication by `r` flips the `z_11` sign and preserves
the `z_001` sign.  Thus the two raw candidate arrows have the same
trace-`1/8` initial half and orthogonal trace-`1/8` ranges.  However those
ranges fill the larger trace-`1/4` carrier:

\[
 2\cdot\frac18=\frac14.
 \tag{RBPC6}
\]

There is no finite-trace contradiction.  To recover the properly infinite
Leavitt packet, one must additionally prove that both ranges lie under the
original parent projection, not merely under the larger Pauli carrier.

This isolates the final algebraic operation:

\[
 p_{\rm child}p_{\rm parent}=p_{\rm child}
 \quad\Longrightarrow\quad
 E_{\rm child}\le E_{\rm parent}
 \tag{RBPC7}
\]

inside the finite coefficient disintegration.  Equation `(RBPC7)` is false
for ambient negative root-sign projections: regular root characters make
the signs independent.  It must be extracted from cross-root Steinberg
commutators, where coefficient multiplication is visible.  This is exactly
why the left regular representation in `L(Q)` realizes `(RBPC4)--(RBPC6)`
without contradiction.

## 4. Where the hard pair leaves the finite cell

Let `K=D8 times D8` be `(RBPC2)`.  For the first class-11 hard prefix `q`
and next letter `l`, exact intersection calculations give

\[
 |K\cap qKq^{-1}|=1,
 \qquad
 |K\cap lKl^{-1}|=2.
 \tag{RBPC8}
\]

Thus ordinary finite-subgroup restriction/branching loses essentially all
of the child data at the first hard prefix.  The hard packet is genuinely
the point where coefficient multiplication, rather than a larger finite
Clifford normalizer, must be recovered.

## 5. Replay

The exact audit is

```text
experiments/atlas_raw_branch_pauli_cell.py
```

with output

```text
experiments/atlas-raw-branch-pauli-cell.json
```

It uses one CPU core and exact prefix arithmetic; there are no numerical
tolerances.

The matrix-level Pauli calibration is independently kernel-checked in
`GroupApproximation/Sofic/ExactInvolutionCut.lean` as

```text
exactInvolutionNegativeCut_conj_of_anticommute
exactInvolutionNegativeCut_mul_conj_eq_zero
exactInvolutionNegativeCut_add_conj_eq_one
```

The last theorem is the formal version of `(RBPC6)`: the two Pauli halves
fill their carrier exactly.
