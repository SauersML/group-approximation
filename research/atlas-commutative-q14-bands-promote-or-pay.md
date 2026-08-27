---
rg: 2
id: atlas-commutative-q14-bands-promote-or-pay
kind: claim
title: Every one-parameter commutative q14 band either pays rank or promotes to an exact Atlas zero
distinct_from:
  atlas-q14-irreducible-field-bands-pay-quarter-rank: that gives a sharp full-rank block on growing irreducible companions; this handles arbitrary reducible and nonsemisimple matrices C by a Laurent gcd and finite-algebra correction.
  atlas-fixed-formal-toeplitz-microstates-promote: that treats one fixed power-series symbol on growing truncations; this treats arbitrary matrix substitutions into the diagonal Laurent chart T(C).
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: that decomposes circulants by Fourier modes; this needs no cyclic or semisimple hypothesis on C.
---

ESTABLISHED.  For every invertible binary matrix `C`, use the q14-exact
diagonal chart

```text
T(C)=diag(C,I,I,I).                                   (CBP1)
```

Let `p_1(t),...,p_N(t) in F2[t,t^(-1)]` be all scalar block entries of the
twelve packet and collision residuals on `(CBP1)`.  They are a fixed finite
list, not all zero.  Let

```text
g(t)=gcd(p_1,...,p_N)                                 (CBP2)
```

in the Laurent PID, normalized up to a monomial unit.

Then exactly one of the following mechanisms applies.

1. If `g=1`, a finite Laurent Bezout identity gives a constant `L` such that

   ```text
   dim C <= L sum_i rank p_i(C).                      (CBP3)
   ```

   Hence some Atlas residual has a uniform positive normalized-rank floor.

2. If `g` is nonconstant and a sequence `C_n in GL_(m_n)(F2)` satisfies

   ```text
   rank p_i(C_n)/m_n ->0  for every i,                (CBP4)
   ```

   then, after a flexible `o(m_n)` rank and dimension correction, `C_n` is
   replaced by an invertible `C'_n` satisfying

   ```text
   g(C'_n)=0.                                         (CBP5)
   ```

   Every packet and collision residual vanishes exactly at `T(C'_n)`, and
   q14 remains exact.  Thus `(CBP4)` promotes to an exact finite-dimensional
   augmented Atlas zero and hence to the established finite-quotient escape.

Therefore no one-parameter commutative diagonal q14 band can realize a
genuinely unstable wandering countermodel.  The remaining independent
stratum must use at least two noncommuting parameters or coefficient data not
captured by one Laurent functional calculus.

### Proof

The Laurent form of the residual entries is
`atlas-q14-irreducible-field-bands-pay-quarter-rank`.  They are not all zero,
because specialization at `t=1` would otherwise give a forbidden classical
packet-and-collision alignment.

If `g=1`, choose a finite Bezout identity

```text
1=sum_i a_i(t)p_i(t).                                 (CBP6)
```

Evaluation and rank subadditivity prove `(CBP3)` (with `L` absorbing repeated
entries or, sharply, with the displayed finite sum itself).

If `g` is nonconstant, choose its polynomial representative with nonzero
constant term; this is possible because `t` is a unit.  Laurent Bezout gives

```text
g=sum_i a_i p_i,                                      (CBP7)
```

so `(CBP4)` implies `rank g(C_n)=o(m_n)`.  The algebra

```text
A_g=F2[t,t^(-1)]/(g)                                  (CBP8)
```

is finite-dimensional over `F2`.  By finite-dimensional-algebra normalized
rank stability from `atlas-rank-stability-literature-fence`, the approximate
`A_g` modules defined by `C_n` flexibly correct to exact modules `C'_n` at
`o(m_n)` rank cost.  The image of `t` remains invertible and satisfies
`g(C'_n)=0`.  Since every `p_i` is divisible by `g`, all residual entries
vanish at `C'_n`.  Fixed-word rank Lipschitzness transfers the correction,
and `atlas-exact-matrix-zero-set-is-a-finite-quotient-test` supplies the
finite-quotient conclusion.
