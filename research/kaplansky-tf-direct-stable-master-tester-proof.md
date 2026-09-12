---
rg: 2
id: kaplansky-tf-direct-stable-master-tester-proof
kind: route
title: Transfer finite inverse witnesses through torsion-free stages
target: kaplansky-torsion-free-direct-stable-master-tester
requires:
  - two-generator-fp-torsion-free-universal-whitehead-container
  - torsion-free-directed-colimit-recursively-presented
---

Choose the group `E` from
[[two-generator-fp-torsion-free-universal-whitehead-container]] and fix a
field `k`.

Both finiteness properties pass from `k[E]` to subgroup group rings. If
`K <= E`, then `k[K] -> k[E]` is a unital injection. Thus direct finiteness
passes immediately. If `k[E]` is stably finite, then for every `n >= 1` the
unital injection

```text
M_n(k[K]) -> M_n(k[E])
```

shows that `M_n(k[K])` is directly finite, so `k[K]` is stably finite.

Let `G` be an arbitrary torsion-free group. By
[[torsion-free-directed-colimit-recursively-presented]], write

```text
G = colim_i K_i
```

with every `K_i` finitely generated, recursively presented, and torsion-free;
the structure maps need not be injective. Every `K_i` embeds in `E`, although
the embeddings need not be coherent. Hence every `k[K_i]` has whichever of
the two finiteness properties is assumed for `k[E]`.

The group-ring functor preserves directed colimits, and for each fixed `n`
so does `M_n`. Suppose that matrices `A,B in M_n(k[G])` satisfy

```text
AB=I_n,              BA!=I_n.
```

Lift their finitely many entries to one stage. After passing to a later stage,
the equality `AB=I_n` holds there. The element `BA-I_n` remains nonzero at
that stage, because its image in the colimit is nonzero. This contradicts
direct finiteness of the corresponding matrix ring. Taking `n=1` proves the
direct-finiteness transfer; allowing every `n` proves the stable-finiteness
transfer. The reverse implications use only that `E` itself is torsion-free.

For coefficient fields, Ceccherini-Silberstein, Coornaert, and Phung,
*First-order model theory and Kaplansky's stable finiteness conjecture for
surjunctive groups*, Groups Geometry and Dynamics 19 (2025), 495--503,
doi:10.4171/GGD/885, prove the needed fixed-group statements without any
surjunctivity hypothesis: Lemma 3.3 transfers stable finiteness from every
finite field to every field, and Remark 4.3 gives the analogous transfer for
direct finiteness. Apply these statements to `E`, then apply the fixed-field
tester equivalences above. The converses are immediate.

Finally, let `F` be a finite field of degree `r` over its prime field
`F_p`. The regular representation gives a unital injection

```text
F[E] -> M_r(F_p[E]),
```

and hence, for every `n`,

```text
M_n(F[E]) -> M_(nr)(F_p[E]).
```

Thus stable finiteness of `F_p[E]` implies stable finiteness of `F[E]`,
proving the prime-field reduction.

There is deliberately no direct-to-stable collapse here. Dykema and
Juschenko, *On stable finiteness of group rings*, Algebra and Discrete
Mathematics 19 (2015), 44--47, Theorem 2.2, use

```text
k[G] stably finite
  <=>
k[G x H] directly finite for every finite group H.
```

For nontrivial finite `H`, the group `G x H` has torsion. Consequently,
direct finiteness over all torsion-free groups does not supply the hypothesis
of that theorem. QED
