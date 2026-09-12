# Spectral coarea turns block commutators into one common invariant cut

Date: 2026-08-14

## 1. Outcome

The spectral fallback in `TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` does not
need a pre-existing eigenvalue gap.  A finite-dimensional coarea identity
chooses the threshold separately at each matrix coordinate and produces one
positive-density spectral cut which is simultaneously almost invariant
under every member of a fixed finite arrow family.

Let `M_d(C)` have normalized trace, let `0<=H<=1`, and let

```text
P_t=1_[t,infinity)(H),        0<=t<=1.                (SCI1)
```

For every matrix `A`,

```text
integral_0^1 ||[P_t,A]||_2^2 dt
  =sum_(i,j)^normalized |lambda_i-lambda_j||A_ij|^2
  <=||[H,A]||_2 ||A||_2.                             (SCI2)
```

Here `lambda_i` are the eigenvalues of `H` and the entries of `A` are taken
in an eigenbasis of `H`.  The equality follows because

```text
integral_0^1
 |1_(lambda_i>=t)-1_(lambda_j>=t)|^2 dt
 =|lambda_i-lambda_j|.                                (SCI3)
```

The inequality is Cauchy--Schwarz:

```text
sum |lambda_i-lambda_j||A_ij|^2
 <=(sum |lambda_i-lambda_j|^2|A_ij|^2)^(1/2)
    (sum |A_ij|^2)^(1/2).                             (SCI4)
```

Both sums use normalized matrix counting, so the two factors in `(SCI4)`
are exactly `||[H,A]||_2` and `||A||_2`.  In particular, if `A` is a
contraction, the right side of `(SCI2)` is at most `||[H,A]||_2`.

## 2. A common threshold for finitely many arrows

Let `A_1,...,A_m` be contractions.  Restrict `(SCI2)` to an interval
`[a,b] subseteq [0,1]`, sum over `k`, and average in `t`.  There is one
`t in [a,b]` such that

```text
sum_k ||[P_t,A_k]||_2^2
 <=(b-a)^(-1) sum_k ||[H,A_k]||_2.                   (SCI5)
```

The same threshold works for the entire fixed family.  Since

```text
||[P,A]||_2^2
 =||(1-P)AP||_2^2+||PA(1-P)||_2^2,                  (SCI6)
```

equation `(SCI5)` controls leakage in both directions.  The threshold may
depend on the matrix coordinate; no limiting spectral projection or literal
group word is asserted.

## 3. Application to the trace-flat Pauli block

For one raw/comb coefficient block the existing exact moments give

```text
H=FGF,        0<=H<=1,
tau(F)=1/8,  tau(H)=1/64.                             (SCI7)
```

`TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` proves

```text
tau(1_[1/16,infinity)(H))>=1/120.                    (SCI8)
```

Apply `(SCI5)` on

```text
[a,b]=[1/32,1/16].                                   (SCI9)
```

Every selected `t` satisfies `t<=1/16`, so monotonicity and `(SCI8)` give

```text
tau(P_t)>=1/120.                                     (SCI10)
```

The interval has length `1/32`.  Hence, for the four coefficient arrows,

```text
sum_(k=1)^4 ||[P_t,A_k]||_2^2
 <=32 sum_(k=1)^4 ||[H,A_k]||_2.                     (SCI11)
```

On `P_t`, the transition block has singular values at least

```text
sqrt(t)>=1/sqrt(32)=1/(4 sqrt(2)).                   (SCI12)
```

Thus the retained sector simultaneously has:

1. ambient trace at least `1/120`;
2. a dimension-free inverse bound `4 sqrt(2)`; and
3. vanishing two-sided leakage for all four arrows whenever their
   commutators with `H` vanish.

No minimum eigenvalue spacing is needed.

## 4. New smallest spectral gate

The previous spectral endpoint asked directly for approximate invariance of
a selected spectral projection.  Equations `(SCI5)--(SCI12)` reduce it to
the operator-polynomial estimates

```text
||[FGF,A_k]||_2 -> 0,        k=1,...,4.               (SCI13)
```

This is a better interface with the atlas relations.  `F`, `G`, and the
candidate arrows are obtained from the root-character and raw/comb packets;
their commutators can be expanded and bounded by covariance and
multiplication defects before any spectral calculus is performed.

The note does not claim `(SCI13)`.  The exact finite Pauli countermodel shows
that local Weyl relations alone cannot imply it.  A successful proof must
use the cross-chart multiplication-module relations.  Once `(SCI13)` is
proved, however, spectral selection, positive density, conditioning, and
simultaneous arrow leakage are no longer separate gates.

There is a further reduction.  If `T=GF`, so that `H=T* T=FGF`, and the
source and target arrows satisfy

```text
||T A_k-B_k T||_2 -> 0,
```

then the elementary Gram estimate

```text
||[T* T,A_k]||_2 <=2||T A_k-B_k T||_2
```

implies `(SCI13)`.  See
`TRUE_TRANSITION_INTERTWINING_CONTROLS_SPECTRAL_LEAKAGE.md`.  Thus the
smallest spectral gate is now the four natural source--target transition
intertwinings, not a separately postulated commutator estimate.

## 5. Formalization status

The trace and threshold arithmetic `(SCI7)--(SCI8)` is kernel-represented by
`one_div_120_le_of_trace_flat_spectral_split` in
`GroupApproximation/Sofic/DoublePauliCoefficient.lean`.  The coarea identity
is proved above by diagonalizing one finite Hermitian matrix and applying
finite-sum Cauchy--Schwarz.  It has not yet been transcribed into Lean, and
no build or computation was run.
