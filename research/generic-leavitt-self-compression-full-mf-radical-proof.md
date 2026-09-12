---
rg: 2
id: generic-leavitt-self-compression-full-mf-radical-proof
kind: route
title: Combine the generic Whitehead compressor with a full complementary root
target: generic-leavitt-self-compression-full-mf-radical
requires:
  - normal-kazhdan-defect-non-mf
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelWhitehead.lean
  - GroupApproximation/Leavitt/HilbertHotelSaturation.lean
---

The binary Leavitt relations give an explicit Whitehead unit in `E_16(R)`.
On a chosen four-coordinate corner, its conjugation is the nonunital corner
endomorphism

```text
a |-> s_0 a t_0.
```

Embed this configuration in `E_n(R)`.  A disjoint elementary root centralizes
the source `E_4(R)`.  After conjugation by the Whitehead unit, its commutator
with one source root is

```text
e_02(q),       q=s_1 t_1.
```

The relation `t_1 q s_1=1` makes `q` full.  For every `a in R`, two Steinberg
commutators give

```text
[e_dx(a t_1),e_xy(q)] = e_dy(a t_1 q),
[e_dy(a t_1 q),e_yz(s_1)] = e_dz(a).
```

Thus the normal closure of the compression defect contains one complete root
subgroup.  Weyl conjugation moves it to every root position, so the defect
normally generates `E_n(R)`.

Property `(T)` of `E_4(R)` supplies the compression source hypothesis.
Property `(T)` of the ambient `E_n(R)` makes the whole normally generated
defect a normal Kazhdan subgroup.  The normal-Kazhdan compression theorem
therefore places every element of `E_n(R)` in its MF radical.
