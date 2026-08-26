---
rg: 2
id: external-weyl-dressed-native-pair-is-root-valued
kind: claim
title: One external Weyl dressing makes the native relative word root-valued but moves its Pauli chart
artifacts:
  - research/external-weyl-native-relative-word-proof.md
distinct_from:
  native-local-occurrence-closure-fixes-mark: that proves every relative word in the current native local occurrence closure fixes the mark; this adjoins the smallest constant Weyl outside that closure and computes the resulting disjoint root exactly.
  root-valued-overlap-does-not-undress-external-selector: that gives an abstract finite analytic packet in which a root mover survives as a scalar sign; this uses the literal binary-Leavitt native Whiteheads and identifies the exact Pauli chart moved by the concrete Weyl dressing.
  root-valued-relative-transport-forces-cross-gram: that proves the scalar Gram floor for authenticated full-word restrictions; this supplies such a root-valued pair of literal full words but proves that the dressed member is not yet the prescribed native selector occurrence on the original Pauli chart.
---

Retain

```text
z=x_13(q),       C=x_42(q),       F=P_zP_C,
W_1=J_1,         W_2=J_2
```

from the same-center native packet, and put

```text
h=w_14(1)w_23(1).                                     (EWN1)
```

The two constant Weyl factors commute and their permutation exchanges the
ordered root positions `(1,3)` and `(4,2)`.  In characteristic two there is
no sign, so

```text
h z h^(-1)=C,             h C h^(-1)=z.               (EWN2)
```

Both native Whiteheads centralize `z` and `C`.  Therefore `h` and `W_i`
all preserve the common projection `F`, and the two literal full words

```text
g_1=W_1,                 g_2=hW_2                     (EWN3)
```

have relative word

```text
u=g_1^(-1)g_2=W_1hW_2,
u z u^(-1)=C=x_42(q).                                  (EWN4)
```

Thus `(EWN3)` is the minimal concrete root-valued dressing of the native
adjacent pair.  Since `{4,2}` is disjoint from `{1,3}` and `q!=0`, it meets
the scalar hypothesis of `root-valued-relative-transport-forces-cross-gram`.
Indeed both words reduce `F`, so their restrictions already have full
cross-Gram on that common carrier.

This does **not** authenticate `(NCG1a)` for the two actual unequal selector
occurrences.  On the same-center arms

```text
A_m=x_(4,k_m)(a_m),             B_m=x_(k_m,2)(b_m),
```

the same Weyl acts by

```text
hA_mh^(-1)=x_(1,k_m)(a_m),
hB_mh^(-1)=x_(k_m,3)(b_m).                             (EWN5)
```

Hence it transports the complete three-pair Pauli chart from endpoints
`(4,2)` to a different chart with endpoints `(1,3)`.  The word `hW_2` is
not an endomorphism of the named source/target Pauli packet and its relative
polar is not covered by the two established mixed-Pauli commutator rows.
Calling `h` a fixed relabeling would assume exactly the missing
same-occurrence identification.

The finite obstruction to removing this discrepancy is sharp:
`root-valued-overlap-does-not-undress-external-selector` admits maximal
marked/root overlap and maximal cross-Gram while the external mover remains
`-1` on every positive subcorner.  Therefore polar cutting cannot turn
`hW_2` back into `W_2`.  A successful continuation must authenticate an
ordinary bridge identifying the moved Pauli chart in `(EWN5)` with the
actual second selector chart, while preserving its unequal `1/8` label
meaning.  That bridge, not the scalar root overlap, is the remaining datum.

No Property `(T)`, Kazhdan input, canonical trace, literature theorem,
local computation, or Lean compilation is used.

DERIVATION
external-weyl-native-relative-word-proof

