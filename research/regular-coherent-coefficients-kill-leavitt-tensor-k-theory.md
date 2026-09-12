---
rg: 2
id: regular-coherent-coefficients-kill-leavitt-tensor-k-theory
kind: claim
title: Tensoring with L_2 kills K_n for n >= 1 of every regular coherent coefficient ring
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that needs the coefficient ring regular supercoherent, i.e. all polynomial rings over it regular coherent, and gives every degree; this needs only regular coherence of the ring itself and gives the degrees n >= 1.
---

**ESTABLISHED (literature import, checked against the source proofs for
`n >= 1`).** Let `R` be a unital ring that is regular coherent on both sides,
in the sense of Ara--Brustenga--Cortiñas Section 7: coherent, and every finitely
presented module has finite projective dimension. Then

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

## Trust surface

- **What the route rests on.** ABC Theorem 5.10, Notation 3.4.1, the proof of
  Proposition 7.1, and the `n >= 1` case of the proof of Lemma 7.2. The
  statement does not rest on Remark 7.8 alone.
- **Unread primary.** ABC's reference [30, Theorem 4]: Waldhausen, *Algebraic
  K-theory of generalized free products I*, Ann. of Math. 108 (1978). ABC cite
  it for the vanishing of twisted Nil groups of a regular coherent ring in
  degrees `n >= 1`.
- **Remark 7.8 is ambiguous; the proof settles it.** The remark says the
  sequence "terminates at K_0(L_k(E))" under regular coherence alone. Lane
  `bh-leavitt-path-steinberg` flagged a reading on which the positive degrees
  would be conjectural. The proof of Lemma 7.2 rules that reading out:
  - its `n >= 1` case needs only that the ring is regular coherent;
  - supercoherence enters only in the downward induction to degrees `n <= 0`,
    through `R[t, t^-1]`.

  So the conjectural part of the remark is the continuation into negative
  degrees. The citation route gives the degree-by-degree check.
