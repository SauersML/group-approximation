---
rg: 2
id: regular-coherent-coefficients-kill-leavitt-tensor-k-theory
kind: claim
title: Tensoring with L_2 kills K_n for n >= 1 of every regular coherent coefficient ring
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that needs the coefficient ring regular supercoherent, i.e. all polynomial rings over it regular coherent, and gives every degree; this needs only regular coherence of the ring itself and gives the degrees n >= 1.
---

**ESTABLISHED (literature import; the source is a remark).** Let `R` be a unital
ring that is regular coherent on both sides, in the sense of
Ara--Brustenga--Cortiñas Section 7: coherent, and every finitely presented module
has finite projective dimension. Then

```text
K_n(R ⊗_Z L_Z(1,2)) = 0   for every n >= 1.
```

Over a field `k`, `R ⊗_k L_k(1,2) = L_R(E)` for every `k`-algebra `R`. In
particular `K_1(R ⊗ L) = K_2(R ⊗ L) = 0`.

**Consumers.**
- The `K`-theory condition of `decidable-group-algebras-have-fp-central-simple-hosts`,
  and the trivial-kernel case of `simple-inputs-have-fp-elementary-leavitt-tensor-hosts`,
  hold whenever the host `B` is regular coherent. Supercoherence is not needed.
- With `leavitt-tensor-powers-are-left-coherent` and
  `leavitt-tensor-global-dimension-bound`, it settles the tensor-power claims.
  See routes `leavitt-tensor-powers-k-theory-via-coherence` and
  `prime-field-leavitt-powers-k-theory-via-coherence`.

**Trust surface.** Remark 7.8 is stated without a separate proof. The citation
route records its wording.
