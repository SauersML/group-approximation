---
rg: 2
id: weak-bass-two-generator-tester-proof
kind: route
title: Preserve the two Bass traces through subgroup and finite-support colimit steps
target: weak-bass-fixed-two-generator-torsion-free-tester
requires:
  - two-generator-fp-torsion-free-universal-whitehead-container
  - torsion-free-directed-colimit-recursively-presented
---

Choose `E` from
[[two-generator-fp-torsion-free-universal-whitehead-container]].

First, the weak Bass property passes to subgroups. If `H <= E` and an element
of `K_0(Z[H])` is represented as a difference of idempotent matrices, its
image in `K_0(Z[E])` is represented by the same matrices, now viewed over
`Z[E]`. Injectivity of `H -> E` preserves the coefficient of the identity,
while augmentation is preserved by every group homomorphism. Therefore

```text
kappa_E(i_*x)=kappa_H(x),
epsilon_E(i_*x)=epsilon_H(x).
```

Thus `epsilon_E=kappa_E` implies `epsilon_H=kappa_H`.

Now let `G` be any torsion-free group and use
[[torsion-free-directed-colimit-recursively-presented]] to write

```text
G = colim_i K_i,
```

where every `K_i` is finitely generated, recursively presented, and
torsion-free, while the structure maps may be noninjective. Every `K_i`
embeds in `E`, so every `K_i` satisfies the weak Bass conjecture if `E`
does.

Take `x in K_0(Z[G])` and represent it as a difference of two idempotent
matrices `p` and `q`. Their finitely many entries lift to one `Z[K_i]`.
After passing to a later stage `K_j`, the two idempotent equations hold, so
the lifted matrices define an element `x_j in K_0(Z[K_j])` mapping to `x`.

Put

```text
t_j = tr(p_j)-tr(q_j) in Z[K_j].
```

Its support is finite. For every support element `s` whose image in `G` is
the identity, equality with the identity in the directed colimit is already
witnessed at some later stage. Pass to one common stage `K_l` at which all
such support elements have become the identity. A support element whose image
in `G` is nontrivial cannot become the identity at `K_l`. Consequently

```text
coefficient_1(t_l) = coefficient_1(t),
augmentation(t_l)  = augmentation(t),
```

where `t` is the image of `t_j` in `Z[G]`. Since `K_l` satisfies weak
Bass,

```text
kappa_G(x)
 = kappa_K_l(x_l)
 = epsilon_K_l(x_l)
 = epsilon_G(x).
```

Hence every torsion-free `G` satisfies weak Bass. The converse follows
because `E` itself is torsion-free.

Berrick, Chatterji, and Mislin, *Homotopy idempotents on manifolds and
Bass' conjectures*, Geometry and Topology Monographs 10 (2007), 41--62,
doi:10.2140/gtm.2007.10.41, Section 2, record precisely that the
Hattori--Stallings and augmentation traces are natural for all group
homomorphisms while the Kaplansky trace is natural for monomorphisms.
Their Lemma 6.3 gives the related finite-presentation lifting argument for
both Bass conjectures.

The proof above is deliberately restricted to weak Bass. For the classical
Bass conjecture, distinct conjugacy classes of a subgroup can fuse in the
ambient group, so the subgroup step does not provide the required
componentwise Hattori--Stallings information. QED
