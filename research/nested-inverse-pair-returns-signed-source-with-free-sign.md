---
rg: 2
id: nested-inverse-pair-returns-signed-source-with-free-sign
kind: claim
title: A nested inverse-pair cell returns the actual reverse root to the signed source but retains a chart sign
invalidates:
  - nested-inverse-pair-reverse-root-is-ungauged-el20-bridge
artifacts:
  - experiments/reverse_root_nested_inverse_pair_return_audit.py
distinct_from:
  actual-mixed-complement-returns-reverse-root: that identifies the corrected complementary output `x_97(1)` and stops because this root does not normalize the signed source; this gives its first literal non-Boolean return to that source.
  signed-hecke-normalizer-has-eight-external-root-returns: that realizes each external normalizer by an isolated inverse-pair commutator; this occurrence starts with the actual mixed-braid reverse root and nests the positive inverse-pair output with it.
---

**ESTABLISHED POSITIVE RETURN AND SCOPED GAUGE FENCE.**  Let the corrected
complementary mixed-braid output be

```text
a=x_97(1).
```

Use actor coordinate `5` and the literal non-Boolean inverse pair

```text
u=x_75(t_0),             v=x_56(s_0).
```

The Steinberg commutator law and `t_0s_0=1` give

```text
h=[u,v]=x_76(1).                                      (RNR1)
```

The arrow `6->7` is one of the seven positive signed generators in
`L_0`, so `rho(h)Q=Q`.  A second ordinary commutator gives

```text
n=[a,h]=x_96(1).                                      (RNR2)
```

The arrow `6->9` is one of the eight external constant-root normalizers
in `(ERN2)`.  Consequently

```text
nQn^*=Q.                                              (RNR3)
```

Thus the word

```text
[x_97(1),[x_75(t_0),x_56(s_0)]]
```

is the first bounded continuation of the corrected reverse-root occurrence
which contains uncancelled `t_0,s_0` letters and returns with exact full
signed-source Gram.  It is not part of the earlier one-cell/two-root
census: it is a nested three-coordinate commutator whose inner coefficient
product becomes one only after the two nonnormal letters occur.

The return is nevertheless not ungauged.  There is an exact two-chart
occurrence model on

```text
H=(C^2)_chart tensor (C^2)_reservoir,
Q=|0><0| tensor 1.
```

Let `A=X_chart tensor 1`.  Let `U,V` be the identity on the zero chart and
the Pauli pair `X,Z` on the one chart.  Then

```text
H_0=[U,V]=diag(1,-1)_chart tensor 1,
N_0=[A,H_0]=-1_H.                                    (RNR4)
```

In particular

```text
H_0Q=Q,               N_0Q=-Q.                       (RNR5)
```

Tensoring this chart factor with the finite constant-label occurrence
changes the returned external-normalizer action by the nontrivial
reservoir sign while preserving `(RNR1)--(RNR3)`.  Hence the nested
identity authenticates source and range Gram, but it does not authenticate
the `tensor 1` clause of `(ESB2)`.  An additional same-carrier relation
involving the literal native Whitehead/order-seven gauge is still required.

This is deliberately a fence only on the nested inverse-pair continuation.
It does not exclude a longer word which couples `u` or `v` to a native
opposite-root occurrence before the inner commutator collapses.

No Property `(T)`, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
reverse-root-nested-inverse-pair-return-proof
