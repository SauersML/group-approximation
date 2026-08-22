---
rg: 2
id: four-cap-three-actuator-destroys-all-fd-packet-evaluations
kind: claim
title: An affine-Leavitt third actuator destroys every finite four-cap packet evaluation
distinct_from:
  four-cap-two-chart-mixer-has-finite-clifford-evaluator: that claim constructs the marked two-chart cell and finds a finite Clifford evaluator; this claim amalgamates a third additive actuator along its D8 cross-chart seed and proves that no finite-dimensional representation can retain the packet sign.
  affine-leavitt-steinberg-mark-is-fd-invisible: that claim kills one active Steinberg root in every finite-dimensional representation; this claim converts that root into the common central involution of the four-cap packet while preserving the entire finite packet by amalgam normal forms.
  packet-retraction-evaluates-hecke-collision-atlas: that claim excludes groups admitting a retraction onto the packet; the present group excludes every finite-dimensional packet-preserving evaluation, whether or not it arises from a retraction.
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

Specialize `affine-leavitt-steinberg-mark-is-fd-invisible` to the finite
field `F_2`.  Write

```text
Gamma_A=St_5(R_A),             w=x_12(A).                (TCA3)
```

Then `Gamma_A` is finitely presented, `w` is a nontrivial involution, and
every finite-dimensional unitary representation of `Gamma_A` sends `w` to
the identity.

Introduce a new central involution `J` and a D8 reflection `s` by

```text
Lambda=(Gamma_A times <J>) *_(<w,J>) <w,s,J>,            (TCA4)
```

where the right factor is

```text
D_8=<w,s,J | w^2=s^2=J^2=1,
                  J central, [w,s]=J>.                  (TCA5)
```

Finally identify the two displayed D8 subgroups:

```text
Gamma_3=Gamma_2 *_D Lambda,
z_2=w,                  b=s,                  J=J.       (TCA6)
```

Normal-form theorems for free products with amalgamation prove that every
vertex group embeds.  Consequently `K` embeds in `Gamma_3`, `q!=0`, and the
common `J` remains nontrivial.  It is central because it is central in both
vertex groups.  All first- and second-chart cap projections therefore
survive algebraically in the nonzero packet corner of `C[Gamma_3]`.

On the other hand, every finite-dimensional unitary representation

```text
pi:Gamma_3 -> U(d)                                      (TCA7)
```

kills `J`.  Its restriction to `Gamma_A` kills `w`; applying `(TCA5)` then
gives

```text
pi(J)=pi([w,s])=I.                                      (TCA8)
```

Thus `pi(q)=0`.  There is no finite-dimensional evaluation which is
faithful on the packet, retains the marked corner, or merely keeps one
four-cap atom nonzero.

All groups in `(TCA4)--(TCA6)` are finitely presented: the vertex groups
are finitely presented and the amalgamated groups are finite.  This closes
the **exact** packet-evaluator problem with one additive third actuator.  It
does not give normalized-HS soundness.  Making `(TCA8)` robust is exactly the
open root-to-coefficient interface
`affine-leavitt-steinberg-hs-coefficient-decoder`.
