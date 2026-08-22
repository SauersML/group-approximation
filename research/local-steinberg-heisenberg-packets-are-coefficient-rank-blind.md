---
rg: 2
id: local-steinberg-heisenberg-packets-are-coefficient-rank-blind
kind: claim
title: Local Steinberg--Heisenberg selector packets are blind to coefficient rank
artifacts:
  - research/artifacts/fanizza-root-heisenberg-rank-blindness-2026-08-21.md
distinct_from:
  char-p-weyl-blocks-local-commutator-decoder: that uses the characteristic-p identity [D,M]=1 to refute additive-commutator decoding; this varies the rank of an idempotent while keeping the entire local D8 root packet identical.
  hecke-dilations-do-not-lock-capacity-gram: that compares Steinberg and finite monomial names for one Hecke unitary; this gives an explicit family of exact root packets with arbitrary hidden source rank.
  toeplitz-defect-roots-form-independent-heisenberg-cells: that constructs many independent Heisenberg cells from orthogonal idempotents; this proves one such cell does not reveal the coefficient size of its idempotent.
---

For `R_n=M_n(F_2)` and every nonzero idempotent `e_r` of rank `r`, the
three roots

```text
x_12(e_r),       x_23(e_r),       x_13(e_r)
```

generate the same abstract order-eight Heisenberg/D8 group.  In the left
regular representation of `E_3(R_n)`, restriction to this subgroup is a
multiple of its regular representation, independently of `r`.

Hence the complete local Heisenberg packet, any fixed abstract selector
automorphism table internal to that packet, same-root additivity on
`F_2e_r`, and the multiplication triangle using `e_r^2=e_r` have identical
finite-dimensional unitary data for every

```text
r/n in {1/n,...,1}.
```

Local Steinberg/root additivity and a fixed finite Heisenberg selector packet
therefore cannot authenticate the complex source Gram or distinguish a full
coefficient carrier from a proper one.  Such authentication requires a
larger rank-exposing coefficient chart plus a same-reservoir trace-reflection
theorem, or an extensive matrix-dependent family of coefficient atoms.
