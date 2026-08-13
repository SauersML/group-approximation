# Endpoint audit for the induced Weyl seam criterion

Date: 2026-08-11

## 1. Outcome

The sparse Weyl seam reduces an induced transition block to the scalar
upper bound

\[
F_M(L)=C_1\frac{R^2L^2}{M^2}+C_2\frac{A}{L},
\qquad 1\leq L\leq M,                               \tag{IWA1}
\]

where `R` is the RMS coefficient coordinate, `A` is the mean absolute
stable-letter coordinate, and for `M=p^k` the seam width `L` must be a
power of `p`.

The single condition

\[
RA=o(M)                                               \tag{IWA2}
\]

is not sufficient when either moment can approach zero.  The exact
asymptotic criterion for the bound `(IWA1)` to vanish is

\[
\boxed{
R=o(M),\qquad A=o(M),\qquad RA=o(M).
}                                                     \tag{IWA3}
\]

This correction matters for Shapiro bundles because both moments are
averages over a growing finite set; a nonzero integer coordinate on a
vanishing fraction of fibers need not give a uniform positive lower bound
on either moment.

## 2. Why the product condition alone fails

Take `A=0` and `R=M/2`.  Then `RA/M=0`, but `(IWA1)` is minimized at
`L=1` and its first term is `C_1/4`.  Dually, take `R=0` and `A=M/2`.
Then the product again vanishes identically, but the second term is minimized
at `L=M` and equals `C_2/2`.

Thus endpoint cases are not automatically better.  Each endpoint needs its
own sublinearity condition.

## 3. Exact asymptotic theorem

**Theorem 1 (three-condition seam criterion).**  Let `M_j=p^(k_j)` tend to
infinity and let `R_j,A_j>=0`.  There exist divisors

\[
L_j\in\{1,p,\ldots ,M_j\}
\]

such that

\[
\frac{R_j^2L_j^2}{M_j^2}+\frac{A_j}{L_j}\longrightarrow0              \tag{IWA4}
\]

if and only if `(IWA3)` holds.

### Proof: necessity

Suppose `(IWA4)` holds.  Since `L_j>=1` and `L_j<=M_j`,

\[
\frac{R_j}{M_j}
\leq
\frac{R_jL_j}{M_j}
\longrightarrow0,
\qquad
\frac{A_j}{M_j}
\leq
\frac{A_j}{L_j}
\longrightarrow0.                                  \tag{IWA5}
\]

Moreover,

\[
\frac{R_jA_j}{M_j}
=
\left(\frac{R_jL_j}{M_j}\right)
\left(\frac{A_j}{L_j}\right)
\longrightarrow0.                                  \tag{IWA6}
\]

This proves all three conditions.

### Proof: sufficiency

When `R_j,A_j>0`, the continuous minimizer is

\[
L_{*,j}=\left(\frac{A_jM_j^2}{R_j^2}\right)^{1/3}.  \tag{IWA7}
\]

If `1<=L_{*,j}<=M_j`, choose a `p`-power within a factor `p` of it.  Then

\[
F_{M_j}(L_j)
\leq C_p\left(\frac{R_jA_j}{M_j}\right)^{2/3}
\longrightarrow0.                                  \tag{IWA8}
\]

If `L_{*,j}<1`, choose `L_j=1`.  The defining inequality for this case gives

\[
A_j<\frac{R_j^2}{M_j^2},
\]

so both terms tend to zero because `R_j=o(M_j)`.  If `L_{*,j}>M_j`, choose
`L_j=M_j`.  Then

\[
R_j^2<\frac{A_j}{M_j},
\]

so both terms tend to zero because `A_j=o(M_j)`.  The cases `R_j=0` and
`A_j=0` are the same two endpoint arguments.  This proves sufficiency.
\(\square\)

The constants `C_1,C_2>0` do not affect the statement; they only change the
bounded rounding factor in `(IWA8)`.

## 4. Simultaneous finite-generator form

For finitely many fixed generators `s`, one seam width must work for all of
them.  Put

\[
R_{*,k}=\max_s R_{s,k},
\qquad
A_{*,k}=\max_s A_{s,k}.                              \tag{IWA9}
\]

The safe simultaneous sufficient criterion is

\[
\boxed{
R_{*,k}=o(M_k),qquad
A_{*,k}=o(M_k),qquad
R_{*,k}A_{*,k}=o(M_k).
}                                                     \tag{IWA10}
\]

Using only the individual products `R_(s,k)A_(s,k)` is also insufficient:
different generators can approach opposite endpoints and demand
incompatible seam widths.

If both maximal moments are bounded below away from zero, the product
condition implies the other two conditions.  That special interior regime
is the only setting in which the single-product formulation is complete.

## 5. Computational consequence

The next MSI screen must record all three normalized statistics

\[
R_*/M,qquad A_*/M,qquad R_*A_*/M,                  \tag{IWA11}
\]

after each Schreier-gauge optimization.  Reporting only the product can
mistake a one-coordinate boundary concentration for a successful global
seam.  A candidate tower passes the scalar screen only if all three columns
tend to zero while the marked Bockstein phase remains nontrivial.

This endpoint correction does not weaken the local theorem in
`FALSE_CLOCK_POSITIVE_WEYL_SEAM.md`, where the tested coordinates are
uniformly bounded.  It sharpens the unresolved induced/global problem.
