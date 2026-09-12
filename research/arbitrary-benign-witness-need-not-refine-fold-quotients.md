---
rg: 2
id: arbitrary-benign-witness-need-not-refine-fold-quotients
kind: claim
title: An arbitrary benign witness need not have fold-refining finite quotients
artifacts:
  - GroupApproximation/Higman/Benign.lean
  - research/benign-witness-finite-quotients-refine-the-fold.md
distinct_from:
  positive-rope-profinite-edge-synchronization: that asks for a specially constructed positive rope with cofinal synchronized finite quotients; this gives a counterexample to the assertion that benign-witness axioms alone provide even the relative fold quotients.
  higman-half-row-has-regular-mf-benign-witness: that is an analytic regular-MF property of one selected witness; this is a profinite counterexample and does not say that every useful witness fails regular MF.
  mf-safe-asymmetric-hnn-replacement: that has other established tensor-synchronization routes; this only kills the universal profinite shortcut through an arbitrary benign witness.
---

There are a finite-rank free group `F`, a normal subgroup `N` with `F/N`
residually finite, and a valid finitely presented benign witness

```text
F -> K,                L<=K,             L cap F=N
```

for which neither conclusion `(BW1)(i)` nor `(BW1)(ii)` of
`benign-witness-finite-quotients-refine-the-fold` holds.

Take Higman's group

```text
H=<a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>,
F=<a,c> ~= F_2,                 K=H,       N=L={1}.
```

Then `K` is finitely presented, the displayed `F` embeds in `K`, `L` is
finitely generated, `L cap F=N`, and `F/N` is residually finite.  Thus these
data satisfy the exact benign-witness hypotheses.  Nevertheless every
finite quotient of `K` is trivial.  For

```text
Gamma=<K,v | [v,L]=1>=H*<v>,
S=<F,vFv^(-1)> ~= F*F,
```

all finite quotients of `Gamma` kill both displayed copies of `F`.

This refutes the universal formulation only.  It does not exclude a
separately engineered benign witness carrying the relative profinite
compatibility required by the positive compiler.

