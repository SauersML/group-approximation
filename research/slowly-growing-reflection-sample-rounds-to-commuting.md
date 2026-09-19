---
rg: 2
id: slowly-growing-reflection-sample-rounds-to-commuting
kind: claim
title: A sufficiently slow growing sample of almost commuting reflections rounds jointly
distinct_from:
  bounded-type-noncentral-code-sectors-round-uniformly: that fixes matrix block size and lets the number of reflections grow; this fixes each sample cardinality, allows arbitrary matrix dimension, and then diagonalizes the cardinality growth
  joint-pinching-costs-linear-generator-gap: that quantifies pinching relative to a commuting tuple; this constructs the sampled commuting tuple itself
---

Let `epsilon_n->0`.  Suppose that for every `n` one has a finite family of
reflections whose maximum pair commutator defect is at most `epsilon_n`.
There is a sequence `t_n->infinity`, chosen sufficiently slowly, such that
every selected `t_n`-tuple can be replaced on the same Hilbert space by
commuting reflections `(T_(n,s))` with

```text
sum_(s=1)^t_n ||Q_(n,s)-T_(n,s)||_2^2 ->0.              (SGR1)
```

For each fixed `t`, this follows by induction.  Having corrected the first
`t-1` reflections, pinch the last reflection by their joint PVM and take
its polar sign.  `joint-pinching-costs-linear-generator-gap` and finite
telescoping give a same-dimension modulus `omega_t(delta)->0`.  Choose
thresholds `delta_t>0` so that the total squared correction is below `1/t`
whenever the raw maximum commutator is below `delta_t`.  Let `t_n` increase
only after `epsilon_n<delta_t`.  This proves `(SGR1)` without a modulus
uniform in `t`.

## Attempts

Taking `t_n` at a prescribed logarithmic rate is not justified because the
fixed-family moduli may deteriorate arbitrarily with `t`.  The weighted hash
tail may be sent to zero along an arbitrarily slow `t_n->infinity`, so the
diagonal schedule is sufficient and avoids asserting nonexistent uniform
finite-family constants.
