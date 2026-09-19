---
rg: 2
id: cross-row-native-diamond-cube-retains-common-c2-gauge
kind: claim
title: The cross-row native-arm commutator cube retains one common C2 gauge
artifacts:
  - research/cross-row-native-diamond-c2-fence-proof.md
invalidates:
  - cross-row-native-diamond-cube-locks-moving-gauge
distinct_from:
  first-native-diamond-extension-of-cross-return-has-gl7-c2-model: that leaves a free C2 on one native Whitehead after one rowwise diamond; this couples both rowwise diamonds by their first literal cross commutators and includes the shared Whitehead braid and B2/B3 sign flips.
  endpoint-odd-actor-retains-native-factor-gauge: that dresses one native factorization while retaining the endpoint actor; this exhibits the simultaneous two-row dressing which also survives the coefficient-sensitive cross cube.
  endpoint-whitehead-star-braid-synchronizes-native-gauges: that proves the native gauges are conjugate and removes an isolated one-row sign; this proves the synchronized common sign is still invisible when both Hecke factors are dressed with it.
---

**ESTABLISHED TWO-ROW GAUGE FENCE.**  Retain the two native-arm diamonds
`(RND2)--(RND5)`, the exact cross-row commutators

```text
[C'_1,D_2]=[x_98(t_00),x_87(s_00)]=x_97(1),
[D'_1,C_2]=[x_86(s_00),x_28(t_00)]=x_26(1),          (CDC1)
```

the braid between `J_1,J_2`, both order-seven heads

```text
T_1=J_1B_2A_1,                 T_2=J_2B_3A_2,        (CDC2)
```

and the B2/B3 full-Hecke sign-flip rows.  This complete displayed relation
table admits a nontrivial common central involution `c` under

```text
J_1 |-> J_1c,       J_2 |-> J_2c,
B_2 |-> B_2c,       B_3 |-> B_3c,                    (CDC3)
```

with every other named occurrence fixed.

Indeed the `J_i` conjugation rows contain `J_i` twice, so their two copies
of `c` cancel.  Every commutator containing `B_2` or `B_3` also contains
that letter with total even incidence, so the central factor cancels before
the returned arm is formed.  In particular all four arms in `(CDC1)` are
unchanged.  The sign-flip conjugacies and involution relations are likewise
unchanged.

The two dressed factors in each head cancel:

```text
(J_ic)(B_(i+1)c)A_i=J_iB_(i+1)A_i=T_i.               (CDC4)
```

Thus the seventh-power anchors see no `c`.  The `J_1--J_2` Coxeter braid
is also preserved because both sides have three Whitehead occurrences and
hence the same central factor `c`.  It identifies the two dressings but
does not kill their common value.

Taking `c` to be the nonidentity element of `C_2` gives an exact finite
gauge-layer model of every named row with a surviving common multiplicity
involution.  Consequently the first cross-row coefficient cube does not
authenticate an ungauged bridge and does not prove `(ESB2)`.

This is an occurrence-interface fence, not a representation of the full
EL20 presentation.  A new relation can exclude it, but that relation must
have odd incidence in one exposed member of a paired factorization, or
must type one of those members on a common reducing carrier.  Further
commutator naturality rows alone remain even in the dressing and cannot do
so.

No Property T, Kazhdan input, trace assumption, computation, literature
theorem, or Lean compilation is used.

DERIVATION
cross-row-native-diamond-c2-fence-proof
