---
rg: 2
title: STW LXXXII finite-spectrum spectral-repair no-go audit (2026-08-30)
kind: artifact
---

# Result

Positive finite-spectrum quasicentral cuts cannot automatically replace the
projectional hypothesis in the noncomplemented multiplier-support theorem.
There is a proper essential stable-AF generated ideal `L=closure(ApA)` with
finite-spectrum positive cuts commuting exactly with `p`, but the enlarged
ideal `L+C p` is not quasidiagonal in `A+C p`.

# Concrete model

For the Toeplitz algebra `T=C*(S)`, its defect projection `e=1-SS^*`, and
`H=ell^2(N_0)`, take

```text
A=T tensor K(H),
p=e tensor 1_(B(H)),
L=K(H) tensor K(H).
```

The generated ideal is proper and essential, so it is noncomplemented.  It
is stable AF and hence has real rank zero.

Diagonal tapers `a_n`, equal to one on an initial block and decreasing to
zero in `1/n` steps, satisfy `norm([a_n,S])<=1/n`.  With initial finite-rank
projections `Q_n`, the contractions

```text
h_n=a_n tensor Q_n
```

are a finite-spectrum positive quasicentral approximate unit for `L` and
commute exactly with `p`.  Moreover `p+(1-p)h_n` is a finite-spectrum
positive quasicentral approximate unit for the actual extension ideal
`L+C p` in `A+C p`.

# Spectral-cut audit

Every nonzero positive-threshold spectral projection of `h_n` is
`P tensor Q_n` for a finite initial-coordinate projection `P`.  Against the
fixed element `S tensor e`, its commutator has norm exactly one.  Thus the
spectral cutoff amplifies commutators from at most `1/n` to one.  Individual
finite spectra and their individual gaps provide no uniform repair estimate;
the gap must quantitatively dominate the incoming commutator error.

# Intrinsic obstruction audit

For `K=A+C p` and `J=L+C p`, the residual quotient is
`C(T) tensor K(H)`.  Naturality carries the stabilized Toeplitz index
generator from `K_0(L)` into `K_0(J)`.  The latter image is nonzero because
the six-term sequence for

```text
0 -> L -> J -> C -> 0
```

makes `K_0(L)->K_0(J)` injective.  Therefore the residual extension has a
nonzero index boundary and is not quasidiagonal.  No different choice of
projectional cuts can evade the explicit commutator obstruction.

# Scope

This is a proof-strategy no-go, not a counterexample to the nuclear-
dimension maximum formula.  It shows sharply why real rank zero, positive
finite-spectrum quasicentral approximate units, exact `p`-commutation, and
stagewise spectral gaps do not suffice for the previous spectral-repair
argument.  A further positive theorem must either impose quantitative gap
control or absorb a genuinely nonquasidiagonal transition band.
