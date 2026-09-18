---
rg: 2
id: equivariant-scaling-hnn-vertex-groups-are-linear
kind: claim
title: If an elementary-abelian-by-H group admits an H-equivariant finite-index scaling whose ascending HNN extension acts faithfully on its tree, the group is linear over F_p((x))
distinct_from:
  finite-index-edge-hnn-embeds-in-fp-simple-group: that is the Bux--Llosa Isenrich--Wu embedding theorem for faithful finite-index HNN extensions of finitely presented groups; this identifies which vertex groups one natural shape of such an extension can have, and finds only linear ones.
  virtually-endomorphic-self-similar-actions-have-finite-image: that kills self-similar actions whose sections agree virtually with endomorphisms; this is about faithful ascending HNN extensions, where endomorphisms of finite-index image are allowed and faithfulness is a different condition, and it concludes linearity instead of finite image.
  kms-configuration-modules-avoid-abelian-lamp-bases: that excludes placing the Kharlampovich--Myasnikov--Sapir configuration modules in abelian lamps of a wreath product; this excludes equivariant scalings of the same modules as a source of faithful finite-index HNN extensions.
artifacts:
  - research/artifacts/gq-bh-bh-free-02-complexity-root-notes.md
---

**ESTABLISHED** by `equivariant-scaling-hnn-vertex-groups-are-linear-proof`
(lane proof, elementary, not independently reviewed; no novelty claimed).

## Statement

Let `p` be a prime and `A = M ⋊ H`, where `M` is a normal elementary abelian
`p`-subgroup, written additively as an `F_p[H]`-module. Let `λ: M -> M` be an
injective `F_p[H]`-module endomorphism with `M/λM` finite. Then

```text
phi : A -> A,   phi(m h) = λ(m) h        (m in M, h in H)                (SC)
```

is an injective endomorphism whose image has index `|M/λM|`. Put
`K = A*_phi = < A, t | t a t^-1 = phi(a) (a in A) >`.

1. **Faithfulness.** `K` acts faithfully on its Bass--Serre tree if and only if
   `∩_{n>=0} λ^n M = 0` and `H` acts faithfully on `M`.
2. **Linearity.** In that case, with `d = dim_{F_p} M/λM`, there are `r <= d` and
   an embedding `A -> GL_(r+1)(F_p((x)))`. So `A` is linear over a field of
   characteristic `p`.

Finite presentation of `A` is not used. It enters only when (1) is fed into
`finite-index-edge-hnn-embeds-in-fp-simple-group`.

## What it kills

**The scaling shape of the Bux--Llosa Isenrich--Wu route to
`fp-simple-groups-with-arbitrarily-complex-word-problem`.**
- The idea: put a finitely presented residually finite group `A` with a hard word
  problem as the vertex group of a faithful HNN extension with finite-index edges.
  Then `finite-index-edge-hnn-embeds-in-fp-simple-group` gives a finitely presented
  simple host, and the host inherits the hardness by the length-linear substitution
  of `arbitrarily-complex-fp-simple-via-hard-self-similar-groups`, step 3.
- The only such hard inputs in the graph are the Kharlampovich--Myasnikov--Sapir
  groups (`kms-arbitrarily-hard-fp-rf-groups`). They are split extensions
  `T ⋊ H` with `T` elementary abelian of exponent `p` (arXiv:1204.6506, §4.1,
  read from the TeX in `gq/src/kms/`). The first map to try fixes the top `H` and
  scales the configuration module `T`, which is exactly (SC).
- By (2), any `A` of this shape with a faithful extension is linear, so its
  finitely generated subgroups share the classical low-complexity bound for
  linear groups (Lipton--Zalcstein in characteristic 0, Simon in characteristic
  `p`; cited, not re-read here). It also already satisfies Boone--Higman
  (`finitely-generated-linear-groups-satisfy-boone-higman`).
- So a hard group admits no map of the form (SC) with faithful HNN extension. A
  finite-index route to the complexity root must use a `phi` that moves the top
  group `H`.

## Calibration

- **Lamplighter.** `A = F_p[z^±] ⋊ <z>`, `λ` = multiplication by `z - 1`. Here
  `M/λM = F_p`, `∩ (z-1)^n F_p[z^±] = 0` (Krull), and `<z>` acts faithfully.
  So `K` is faithful. Indeed sending a lamp configuration `f(z)` to `f(1+x)` and
  `z` to multiplication by `1 + x` embeds `A` in the affine group
  `F_p((x)) ⋊ F_p((x))^×`, consistent with (2).
- **A non-faithful case.** `λ = id` on `M = F_p[z^±]`: then `phi = id`,
  `K = A × <t>`, the tree is a line, and `A` (in particular
  `M = ∩ λ^n M`) lies in the kernel, as (1) predicts.
- **Boundary.** The statement needs `λ` to be `H`-equivariant, i.e. `phi` is the
  identity on `H`. A semilinear `phi(m h) = λ(m) ψ(h)` with `ψ` a nontrivial
  endomorphism of `H` is not covered; neither is a non-ascending HNN extension
  with two proper finite-index edges.

DERIVATION
equivariant-scaling-hnn-vertex-groups-are-linear-proof
