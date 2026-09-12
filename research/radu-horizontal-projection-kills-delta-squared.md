---
rg: 2
id: radu-horizontal-projection-kills-delta-squared
kind: claim
title: In Radu's BMW lattice (xz)^2 acts trivially on the horizontal tree, so the mark lies in a free normal kernel
invalidates:
  - radu-bmw-lattice-sofic-via-horizontal-factor
distinct_from:
  radu-mark-is-controlled-by-one-commutator: that bounds the mark by one commutator in every almost action; this locates the mark and that commutator inside the kernel of the horizontal tree action.
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that imports the lattice, its presentation and the embedding; this computes the action of its vertical group on the horizontal tree.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
  - research/artifacts/titz-witzel-radu-projections.py
  - research/artifacts/titz-witzel-radu-projections-output-2026-09-11.txt
---

**ESTABLISHED.**  Let `Gamma_R` act on `T_h x T_v` as in
`radu-bmw-lattice-embeds-in-titz-witzel-kernel`.  Here `T_h = Gamma_R/V` is
the tree of reduced words in `a,b,c`, and `V = <x,y,z>` is the stabilizer of
its root.  On `T_h`:

* `y` is the global substitution `b <-> c`;
* `x` swaps `a <-> b` exactly in the odd `c`-blocks of a word;
* `z` swaps `a <-> b` exactly in the even `c`-blocks.

So `xz` acts as the global substitution `a <-> b`, and `(xz)^2` acts
trivially:

```text
(xz)^2 in Lambda_v := ker(Gamma_R -> Aut(T_h)).                          (HK1)
```

`Lambda_v` is a free normal subgroup of `Gamma_R` inside `V`, and it contains
the mark `(xz)^4`, `u = y(xz)^2y`, and the commutator `[u, xz]`.

Consequently, an almost action of `Gamma_R` obtained by pulling back an
action of the horizontal tree group `Gamma_R/Lambda_v` sends the mark to the
identity.  This holds however large or congruence-like that quotient's
finite models are.

Computed through level 10 (artifact Section 4): the level quotients of
`V/Lambda_v` have orders `6, 48, 192, 1536, ..., 6291456`, and the relation
`(xyz)^3` holds there.

DERIVATION
radu-horizontal-projection-kills-delta-squared-proof
