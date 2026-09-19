---
rg: 2
id: four-cap-three-actuator-destroys-all-fd-packet-evaluations
kind: claim
title: A Thompson-simple third actuator destroys every finite four-cap packet evaluation
distinct_from:
  four-cap-two-chart-mixer-has-finite-clifford-evaluator: that claim constructs the marked two-chart cell and finds a finite Clifford evaluator; this claim amalgamates a finite-dimensionally invisible simple-group involution along its D8 cross-chart seed.
  packet-retraction-evaluates-hecke-collision-atlas: that claim excludes groups admitting a retraction onto the packet; the present group excludes every finite-dimensional packet-preserving evaluation, whether or not it arises from a retraction.
  thompson-v-not-lef: that claim records finite presentation, infinitude and simplicity of Thompson V; this claim uses those facts to build a central marked actuator around an involution of V.
---

**ESTABLISHED.**  Use the notation of
`four-cap-two-chart-mixer-has-finite-clifford-evaluator`.  In particular,
`Gamma_2` contains the finite packet

```text
K=E times <z_1,z_2>,
q=(1-J)/2 in C[E] subset C[K],                          (TCA1)
```

and the subgroup

```text
D=<z_2,b,J>,              b=t z_2 t,                    (TCA2)
```

is a copy of `D_8`: `z_2,b,J` are involutions, `J` is central, and
`[z_2,b]=J`.  Faithfulness of the explicit Pauli--Hadamard evaluator on
this subgroup proves that no additional relation collapses `D`.

Let `V` be Thompson's finitely presented infinite simple group and choose a
standard prefix-swap involution `u in V`.  Every finite-dimensional unitary
representation of `V` is trivial.  Indeed a nontrivial representation has
trivial kernel by simplicity, hence embeds the finitely generated group `V`
in a linear group.  Malcev residual finiteness would then make `V`
residually finite, impossible for an infinite simple group.

Introduce a new central involution `J` and a D8 reflection `s` by

```text
Lambda=(V times <J>) *_(<u,J>) <u,s,J>,                 (TCA3)
```

where the right factor is

```text
D_8=<u,s,J | u^2=s^2=J^2=1,
                  J central, [u,s]=J>.                 (TCA4)
```

Finally identify the two displayed D8 subgroups:

```text
Gamma_3=Gamma_2 *_D Lambda,
z_2=u,                  b=s,                  J=J.       (TCA5)
```

Normal-form theorems for free products with amalgamation prove that every
vertex group embeds.  Consequently `K` embeds in `Gamma_3`, `q!=0`, and the
common `J` remains nontrivial.  It is central because it is central in both
vertex groups.  All first- and second-chart cap projections therefore
survive algebraically in the nonzero packet corner of `C[Gamma_3]`.

On the other hand, every finite-dimensional unitary representation

```text
pi:Gamma_3 -> U(d)                                      (TCA6)
```

kills `J`.  Its restriction to `V` is trivial and therefore kills `u`;
applying `(TCA4)` gives

```text
pi(J)=pi([u,s])=I.                                      (TCA7)
```

Thus `pi(q)=0`.  There is no finite-dimensional evaluation which is
faithful on the packet, retains the marked corner, or merely keeps one
four-cap atom nonzero.

All groups in `(TCA3)--(TCA5)` are finitely presented: the vertex groups
are finitely presented and the amalgamated groups are finite.  This closes
the **exact** packet-evaluator problem with one simple-group third actuator.
It does not give normalized-HS soundness.  A robust version would require a
dimension-independent theorem forcing the chosen Thompson involution close
to the identity in approximate representations.  No such theorem is
asserted here, and there is no affine-Leavitt decoder dependency.
