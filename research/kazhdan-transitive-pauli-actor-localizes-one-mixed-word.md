---
rg: 2
id: kazhdan-transitive-pauli-actor-localizes-one-mixed-word
kind: claim
title: A uniformly gapped transitive Pauli actor localizes a Gram from one mixed word
artifacts:
  - research/artifacts/dual-prefix-kazhdan-reynolds-localization-2026-08-21.md
distinct_from:
  common-corner-mutual-bicommutant-extraction: that asks to exactify two word-generated algebras as mutual commutants; this gives a direct conditional expectation estimate when the scalable side is a Pauli algebra with a transitive gapped actor.
  kazhdan-type-blocks-pack-a-square-function: that packs transitions among inequivalent representation types; this is the Weyl martingale square function inside one growing irreducible Pauli type.
  leavitt-prefix-renormalization-is-noncontractive: that proves the bare prefix maps do not contract additive-root defect; this identifies the extra actor gap which makes one prototype commutator control every Weyl coordinate.
  finite-clifford-symplectic-section-obstruction: that rules out a genuine symplectic section of the finite Clifford extension in the relevant binary ranks; this estimate uses only projective lifts because central phases disappear under conjugation.
---

Let `P_N` be a Pauli group and let `K_N` act transitively on its nonzero Weyl
vectors.  If a fixed generating set for `K_N` has conjugation-module gap
`kappa>0`, uniformly in `N`, then for every matrix `T`

```text
dist_2(T,P_N')
 <= ||[T,W_0]||_2/sqrt(2)
    +(1+sqrt(2))/sqrt(kappa)
      (avg_s ||[T,U_s]||_2^2)^(1/2),
```

where `W_0` is any one nonzero Weyl word.

The proof combines actor averaging with the exact Reynolds square function

```text
avg_v ||[T,W_v]||_2^2=2||T-E_(P_N)(T)||_2^2.
```

Thus one mixed prototype word localizes a decoded Gram into the fixed label
factor with constants independent of Pauli rank and matrix dimension.  For
the dual-prefix Leavitt tower, the missing datum is exactly a finitely
word-exposed actor with this uniform gap; the bare two Morita branches do not
provide it.
