---
rg: 2
id: deligne-triple-cover-via-lattice-non-hyperlinear
kind: route
title: Exclude the full parameter circle by non-hyperlinearity of Deligne's lattice through P_op inside E_CE, and the finite branch by period arithmetic
target: deligne-triple-cover-exact-mf-radical
requires:
  - deligne-universal-cover-lattice-is-not-hyperlinear
  - deligne-norm-parameter-group-embeds-in-ce-subgroup
  - deligne-finite-parameter-group-has-period-prime-to-three
  - deligne-sep7-all-cover-mf-radical-classification
---

The argument has three steps.
1. The first prerequisite says that `Gamma~` is not hyperlinear. By (NCE3) of
   `deligne-norm-parameter-group-embeds-in-ce-subgroup`, `E_CE` is then finite, and so is `P_op <= E_CE`. So
   `P_op = (1/m)Z/Z` for one even `m`.
2. The third prerequisite gives `3 not | m`. So neither `1/3` nor `2/3` lies in `P_op`.
3. The annihilator formula of `deligne-sep7-all-cover-mf-radical-classification`, at covering degree three, makes
   `Rad_MF(E_3)` the whole order-three kernel.

Steps 2 and 3 are those of `deligne-triple-cover-via-deligne-lattice-non-mf`.

**Difference from `deligne-triple-cover-via-deligne-lattice-non-mf`.** That route excludes the full circle by
operator-norm non-MF of the lattice. This route excludes it by the tracial statement. That statement is implied by
weak ucp-stability of `Sp_4(Z)`, and by the LLP of `C^*(Sp_4(Z))`. It asks less than non-hyperlinearity of `E_3`,
because the order of `E_CE` may be divisible by `3`. The operator-norm period prerequisite then removes the prime
`3` on the norm side only.

**Each prerequisite can fail on its own.**
- The first fails iff `E_CE = R/Z`, that is, iff there is one irrational CE twist of `Sp_4(Z)`. That alternative
  forces LLP failure of `C^*(Sp_4(Z))`.
- The third fails through an MF model of `E_6` with `P_op` still finite. That is compatible with finite `E_CE`,
  provided `6` divides `|E_CE|`.
