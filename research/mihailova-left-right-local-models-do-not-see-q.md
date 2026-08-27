---
rg: 2
id: mihailova-left-right-local-models-do-not-see-q
kind: claim
title: Finite local metric models of the Mihailova left-right action carry no information about Q
distinct_from:
  mihailova-nonseparable-coset-stabilizer: that constructs the nonseparable fiber product and proves failure of residual finite action models; this shows that a weaker but tempting finite metric model exists universally despite that failure.
  gkp-sofic-action-toolkit: that concerns positive-density Hamming orbit charts defining a sofic set action; this concerns local finite metric actions and proves they cannot replace the Hamming chart condition.
  glebsky-weak-soficity-is-metric-free: that characterizes group approximation by arbitrary finite invariant metrics; this concerns an isometric action of a residually finite free-product actor and does not approximate the quotient group law.
---

Let `pi:F_m->Q` be any epimorphism, equip `Q` with the discrete `0/1` metric,
and let

```text
F_m x F_m curvearrowright Q,
(u,v).q=pi(u) q pi(v)^(-1).                            (MLM1)
```

For every finite actor window, finite subset of `Q`, and `epsilon>0`, `(MLM1)`
has an `epsilon`-accurate local model inside a finite metric space carrying an
exact isometric action of `F_m x F_m`.

This holds for **every** `Q`, including the fixed finitely presented nonsofic
quotient used by `mihailova-nonseparable-coset-stabilizer`.  Consequently:

- finite local isometric orbit models do not imply soficity, residual
  finiteness, or any other nontrivial finite-approximation property of `Q`;
- they do not contradict nonseparability of the Mihailova stabilizer, because
  residual finite set-action models require exact finite Schreier charts;
- any proof that the combined Mihailova action is sofic must use the extra
  positive-density Hamming chart coherence in the Gao--Kunnawalkam
  Elayavalli--Patchell definition.  Replacing those charts by arbitrary finite
  metric orbit patches is vacuous.

There is a sharp stronger boundary.  The unitary left-right representation
of `F_m x F_m` on `ell^2(Q)` is weakly contained in finite-dimensional
unitary representations if and only if `Q` is hyperlinear.  Thus extracting
that finite-dimensional coefficient approximation from Hamming action charts
would yield a genuine approximation property of `Q`; Alekseev--Thom's local
metric models explicitly do not supply this extraction.
