---
rg: 2
id: cyclic-energy-excess-recognizer-is-essential
kind: claim
title: Exact finite-dimensional excess cannot supply reverse-Kleene energy soundness
distinct_from:
  cyclic-energy-reverse-kleene-ceiling-diagonal: that uses an exact excess recognizer to derive a ceiling at the fixed point; this proves that its NONHALT hypothesis cannot itself provide an unconditional excess witness and that the recognizer is essential for r.e. presentations.
  threshold-free-reverse-kleene-higman-diagonal: that searches a formal proof that a group-algebra mark vanishes; this concerns semidecision of a strict supremum over exact finite-dimensional representations.
  dimension-matched-kleene-microstate-diagonal: that searches approximate canonical models at a chosen dimension; this rules out an exact-model substitute before any approximation rate is considered.
---

Let a total computable finite-presentation energy compiler satisfy the HALT
clause

```text
e halts => beta_e<=b_e.
```

It cannot also satisfy

```text
e nonhalts => beta_e>b_e.                                (EER1)
```

Indeed, `beta_e>b_e` is uniformly recursively enumerable by exact real
quantifier elimination over the matrix dimension. Thus `(EER1)` together
with the HALT clause would enumerate `coHALT`; equivalently the reverse-Kleene
fixed point would be forced both to halt and not halt.

Therefore residual finiteness, a finite quotient, profinite regular models,
or any unconditional exact representation carrying energy above `b_e`
cannot prove the NONHALT side of the cyclic-energy diagonal. That side must
consume a hypothetical canonical microstate and be allowed to become vacuous
when the compiled group is nonhyperlinear.

For uniformly r.e. presentations, the explicit excess-recognizer hypothesis
is essential. There is a uniform family of finite (hence hyperlinear) groups
with the semantic HALT/NONHALT energy behavior but for which recognizing
`beta_e>b_e` is exactly `coHALT`.
