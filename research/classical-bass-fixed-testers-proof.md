---
rg: 2
id: classical-bass-fixed-testers-proof
kind: route
title: Preserve every finite Hattori--Stallings support component
target: classical-bass-fixed-two-generator-testers
requires:
  - two-generator-frattini-universal-containers
  - torsion-free-directed-colimit-recursively-presented
---

Berrick, Chatterji, and Mislin, *Homotopy idempotents on manifolds and
Bass' conjectures*, Geometry and Topology Monographs 10 (2007), 41--62,
doi:10.2140/gtm.2007.10.41, Section 2, identify

```text
HH_0(Z[G]) = direct_sum_[g in Conj(G)] Z[g]
```

and record that the Hattori--Stallings trace is natural for every group
homomorphism. Their Lemma 6.3 is the corresponding finite-presentation
lifting argument.

## 1. Frattini inheritance

Let `i:K->H` be a Frattini embedding. Naturality gives a square

```text
K_0(Z[K])  --HS_K-->  HH_0(Z[K])
    |                     |
    v                     v
K_0(Z[H])  --HS_H-->  HH_0(Z[H]).
```

The right vertical map sends the basis vector `[k]` to `[i(k)]`. It is
injective: injectivity of `i` separates the identity, and the Frattini
condition says that two `K`-classes cannot fuse in `H`. Hence classical
Bass for `H` implies classical Bass for `K`.

This is exactly where an arbitrary subgroup embedding would be insufficient:
distinct nonidentity conjugacy classes could fuse and their coefficients
could cancel. Every embedding used here is Frattini by
[[two-generator-frattini-universal-containers]].

## 2. Arbitrary directed colimits, including noninjective maps

Let

```text
G=colim_i G_i
```

be a directed colimit with arbitrary structure maps, and suppose every
`G_i` satisfies classical Bass. Take `x in K_0(Z[G])` and write it as a
difference of classes represented by two finite idempotent matrices `p,q`.
Their entries lift to one stage. The finitely many equations `p^2=p` and
`q^2=q` hold at some later stage `G_j`, so they define
`x_j in K_0(Z[G_j])` mapping to `x`.

Put

```text
z_j=tr(p_j)-tr(q_j) in Z[G_j]
```

and let `S` be its finite support. Partition `S` by declaring

```text
s ~ t  <=>  their images are conjugate in G.
```

For every equivalent pair, choose a conjugator in `G`. That conjugator is
represented at some stage, and its conjugacy equation is an equality in the
colimit, hence is witnessed at a later stage. There are only finitely many
pairs in `S`, so one common stage `G_k` realizes every conjugacy that
occurs in the final group. Two elements in different final classes cannot
become conjugate at any stage, since such a conjugacy would persist to
`G`. Consequently the partition of the image of `S` into
`G_k`-conjugacy classes is exactly its final partition. Equalities among
support elements merely add coefficients inside one of these same blocks.

It follows that every coefficient of `HS_G(x)` is already the coefficient
of the corresponding class of `HS_G_k(x_k)`. If the final class is
nonidentity, its representative cannot have become the identity at
`G_k`. Thus a nonzero nonidentity component at the colimit would give one
at a stage, contradicting classical Bass for `G_k`. Classical Bass is
therefore closed under arbitrary directed colimits.

## 3. Apply the two universal lanes

Every group is a directed colimit of finitely presented groups: use finite
sets of generators from the target together with finite sets of relations
that hold there. If `U` satisfies classical Bass, then every finitely
presented group does by its Frattini embedding into `U` and Section 1.
Section 2 gives classical Bass for every group. The converse applies the
global statement to `U`.

Now let `E` satisfy classical Bass and let `G` be torsion-free. By
[[torsion-free-directed-colimit-recursively-presented]], write

```text
G=colim_i K_i
```

with every `K_i` finitely generated, recursively presented, and
torsion-free; the maps need not be injective. Each `K_i` Frattini embeds
in `E`, so Section 1 gives classical Bass for every `K_i`, and Section
2 gives it for `G`. The converse applies the torsion-free global statement
to `E`. QED
