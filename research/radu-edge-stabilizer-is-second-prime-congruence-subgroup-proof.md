---
rg: 2
id: radu-edge-stabilizer-is-second-prime-congruence-subgroup-proof
kind: route
title: Count indices in the vertex stabilizer of the second tree and match the two index-two kernels with the outer permutation signs
target: radu-edge-stabilizer-is-second-prime-congruence-subgroup
requires:
  - radu-xz-slab-is-second-tree-edge-stabilizer
  - radu-horizontal-sign-is-local-action-on-second-tree
  - radu-horizontal-quotient-is-arithmetic-lattice
artifacts:
  - research/artifacts/radu-second-tree-slab-output-2026-09-13.txt
---

The derivation is written in the body of the target, under **Proof**. It uses:
* the vertex stabilizer `S_3` of `W` at `p` and its transitivity on the star
  (`radu-horizontal-quotient-is-arithmetic-lattice`, item 1);
* the facts that `a, b, c` fix `p, q` and that `x` inverts `e'`
  (`radu-xz-slab-is-second-tree-edge-stabilizer`, item 1);
* the permutations of `a, b, c, xz` on the outer vertices of `e'`, from the landed output file;
* the star computation of `radu-horizontal-sign-is-local-action-on-second-tree`, which serves as a
  consistency check.

The argument itself is two index counts, `[Fix_Q(p) : C] = 6` and `[Fix_Q(p) : E] = 3`. Each
index-two kernel is then identified from one element, `xz` for `sign_q` and `c` for `sign_p`.

∎
