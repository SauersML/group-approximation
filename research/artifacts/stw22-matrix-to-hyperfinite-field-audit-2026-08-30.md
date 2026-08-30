# STW XXII: growing matrix fibres converging to a hyperfinite fibre

## Question tested

Can the trace-continuity theorem be proved for a genuinely changing-fibre
tracial completion, rather than another presentation of a trivial or
locally trivial `R`-bundle?

## Model and completion

Choose a dense increasing full-matrix chain `F_n` in an
infinite-dimensional UHF algebra `U`.  The algebra

```text
A={a_infinity in U, a_n in F_n: ||a_n-a_infinity|| -> 0}
```

is a separable nuclear extension of `U` by `direct-sum_n^c0 F_n`.  Its
extreme traces are the evaluations on the convergent sequence.  Completing
uniformly in their `2`-norm gives the bounded sections with `a_infinity in
R`, `a_n in F_n`, and `||a_n-a_infinity||_2 -> 0`.

The completion is not a locally trivial `R`-bundle: every isolated fibre is
the finite factor `F_n`, while the limit fibre is the hyperfinite `II_1`
factor.  Therefore Evington--Pennig's theorem that locally trivial
`R`-bundles are globally trivial does not identify this class with the
existing trivial-field theorem.

## Fibre-gap calculation

All isolated norm/`2`-norm fibre gaps vanish.  At infinity the gap is

```text
{(a_n) in product F_n: ||a_n||_2 -> 0}
 / {(a_n):||a_n|| -> 0}.
```

It is nonzero because rank-one projections have norm one and `2`-norm
tending to zero as the matrix dimensions grow.  It has no nonzero bounded
positive trace: after a fixed spectral cutoff, the support ranks are an
arbitrarily small fraction of the matrix dimensions, so the cut has
arbitrarily many orthogonal unitarily equivalent copies.  Boundedness of a
trace forces its value on the cut to vanish; norm approximation removes the
cutoff.

## Consequence and scope

The exact norm-fibre-gap criterion proves that every trace on the completion
is the integral of its canonical matrix/hyperfinite fibre traces and hence
is uniformly `2`-norm continuous.  This is an unconditional positive class
with an infinite Bauer boundary, nonconstant fibre type, and a genuinely
nonzero fibre gap.

The argument uses the isolated-coordinate geometry of the convergent
sequence.  It does not solve arbitrary non-locally-trivial hyperfinite
fields, infinite-dimensional bases, or non-Bauer trace simplices.
