---
rg: 2
id: gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings
kind: claim
title: For each prime p, GL_n(Q) acts faithfully on the vertices of the Bruhat-Tits building of PGL_(n+1)(Q_p), and PGL_2(Q) and Aff(Q) act faithfully on the (p+1)-regular tree
distinct_from:
  sl-n-q-is-colimit-of-lattice-stabilizers: that presents SL_n(Q) through lattice stabilizers over the restricted product of all primes; this is the faithfulness of the action at one prime and its consequence for host classes.
  divisible-elements-act-elliptically-on-trees: that constrains every tree action of an overgroup; this exhibits the permitted parabolic case.
---

**ESTABLISHED** through `gl-n-q-acts-faithfully-on-p-adic-bruhat-tits-buildings-proof`.
Not independently reviewed. Elementary; no priority is claimed.

## Statement

Fix a prime `p` and `n >= 1`. Let `X_p` be the set of homothety classes `[L]` of
`Z_p`-lattices `L` in `Q_p^(n+1)`, the vertex set of the Bruhat–Tits building of
`PGL_(n+1)(Q_p)`. For `n = 1` it is the vertex set of the `(p+1)`-regular tree
`T_(p+1)` (Serre, *Trees*, Ch. II §1.1).

1. `X_p` is countable, and `PGL_(n+1)(Q_p)` acts faithfully on it.
2. `g -> [diag(g, 1)]` embeds `GL_n(Q)` in `PGL_(n+1)(Q) <= PGL_(n+1)(Q_p)`. So
   `GL_n(Q)` acts faithfully on `X_p`, as do `PGL_(n+1)(Q)` and `Aff(Q)`,
   `PGL_2(Q)` (for `n = 1`, via `x -> ax + b` as `[[a, b], [0, 1]]`) on `T_(p+1)`.
3. The vertex stabilizers of these countable groups lie in compact open subgroups
   of `PGL_(n+1)(Q_p)`, so they are residually finite. By
   `divisible-elements-act-elliptically-on-trees` (part 3) the unipotent
   `(Q,+) = {[[1, b], [0, 1]]}` fixes exactly one end of `T_(p+1)`, the line
   `Q_p e_1`, and no vertex.
4. `PGL_(n+1)(Q)` is transitive on `X_p`, has infinitely many orbits on pairs of
   vertices, and its vertex stabilizers are not finitely generated. So this action
   is not of type (A).

## What it says about hosts

- **The tree clause of O1 is sharp.** O1 excludes faithful actions on locally
  finite *rooted* trees. Here `PGL_2(Q)` and `Aff(Q)` act faithfully on a locally
  finite *unrooted* tree. So `Aut(T_(p+1))`, and every group of almost
  automorphisms of `T_(p+1)` containing it, is not excluded as an ambient group.
  `no-q-in-tree-product-actions-with-finite-stabilizers` excludes their discrete
  subgroups.
- **One prime carries all divisibility.** `Q <= Q_p`. Divisibility by primes
  `q != p` happens inside the compact vertex stabilizers (`Z_(p) <= Z_p`).
  Divisibility by `p` comes from the end, as an ascending union of vertex
  stabilizers. So a family-E host does not need varying branching over all
  primes: one `p`-adic tree or building already carries `GL_n(Q)` faithfully.
- The obstacle is to find a *finitely presented* (or f.g. then f.p.) countable
  group acting on `T_(p+1)` or on the building that contains this copy of
  `GL_n(Q)`. By `divisible-elements-act-elliptically-on-trees` its vertex
  stabilizers must be infinite. If they are residually finite, the root groups
  stay parabolic.
