---
rg: 2
id: unbalanced-torus-free-lamp-spectator-gap-proof
kind: route
title: The torus defect is the denominator coordinate that controls the first lamp cross-Gram
target: unbalanced-torus-blocks-spectator-free-lamp-models
requires:
  - two-torus-closures-detect-denominator-multiplicity
---

The exact product evaluation in
`two-torus-closures-detect-denominator-multiplicity` gives

```text
ev_(X,H)(R_tor)=V^(-1) tensor I_K.
```

Therefore

```text
eta=||V^(-1)-I||_2=||V-I||_2.                          (SFG1)
```

The arithmetic tensor factor cancels from the conjugate letter:

```text
T_1=H^*TH=V^*LV tensor I_K.                            (SFG2)
```

For unitaries `L,V`, a two-term telescope gives

```text
||V^*LV-L||_2
 <=||V^*L(V-I)||_2+||(V^*-I)L||_2
 <=2||V-I||_2.                                         (SFG3)
```

Using the normalized trace and Cauchy--Schwarz,

```text
|1-tr(T^*T_1)|
 =|tr_M(L^*(L-V^*LV))|
 <=||L-V^*LV||_2
 <=2 eta.                                               (SFG4)
```

The reverse triangle inequality in `(SFG4)` is `(SFL2)` and immediately
implies `(SFL3)`.

Finally, in the central HNN group the stable letter `t` commutes with `C`
and `h` is not in `C`.  Thus `t` and `h^(-1)t h` are distinct members of
the quasiregular stable-letter frame; amalgamated freeness (or Britton
normal form) gives the cross-Gram `(SFL4)`.  This proves the claim.
