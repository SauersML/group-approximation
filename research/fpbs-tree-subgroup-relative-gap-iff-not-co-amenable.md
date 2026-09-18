---
rg: 2
id: fpbs-tree-subgroup-relative-gap-iff-not-co-amenable
kind: claim
title: On the free-group tree every infinite subgroup with a nonamenable Schreier graph has a relative threshold gap, and spectral radius one kills the gap
distinct_from:
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that computes p_c(N;T) and chi^N_p exactly for normal N, and its threshold argument uses normality (cyclically reduced conjugates); this proves the gap criterion for every infinite subgroup, normal or not, with the Schreier graph in place of the quotient Cayley graph, and does not compute the threshold beyond the bound p_c(H;T) >= R_H.
  fpbs-relative-gap-along-any-subgroup-separates: that turns a relative gap along any subgroup into p_c < p_u on any Cayley graph; this decides, on trees, exactly which subgroups have a relative gap, and uses that claim only for the implication from infinite susceptibility to no gap.
artifacts:
  - experiments/fpbs-schreier-kesten-2026-09-17/verify_schreier_cogrowth_identity.py
  - experiments/fpbs-schreier-kesten-2026-09-17/output.txt
---

**ESTABLISHED.**

**Setting.**
- Let `d >= 2`, `q = 2d - 1`, `S` the free basis of `F_d` and its inverses, and
  `T = Cay(F_d,S)`, the `(q+1)`-regular tree, with `p_c(T) = 1/q`.
- Let `H <= F_d` be any infinite subgroup, normal or not. Let
  `X = Sch(H\F_d, S)` be the Schreier graph on right cosets, with arcs
  `Hg -> Hgs`. It is a `(q+1)`-regular symmetric multigraph.
- Let `p_m` be the `m`-step return probability of simple random walk on `X` to
  the coset `H`, and `rho_H = limsup_m p_m^(1/m)`.
- Let `f_n(H)` be the number of elements of `H` of word length `n`, and `R_H`
  the radius of convergence of `F_H(s) = sum_n f_n(H) s^n`. Since `H` is
  infinite, `1/q <= R_H <= 1`.
- Write `z(s) = s/(1 + q s^2)`, `phi(s) = (1 - s^2)/(1 + q s^2)`,
  `W_m = (q+1)^m p_m`, and `chi^H_p = E_p|K_o ∩ H|`.

Then:

1. **Susceptibility identity.** `chi^H_p = F_H(p)` for all `p in [0,1]`, and
   near `s = 0` the following holds as an identity of convergent series:

   ```text
   F_H(s) = phi(s) * sum_m W_m z(s)^m .
   ```

2. **Gap criterion.** `p_c(T) < p_c(H;T)` iff `rho_H < 1`. More precisely:
   - if `rho_H < 1`, then `R_H > 1/q` and `p_c(H;T) >= R_H > 1/q`;
   - if `rho_H = 1`, then `R_H = 1/q`, `chi^H_p = infinity` for every
     `p > 1/q`, and `p_c(H;T) = 1/q`.
3. **Co-amenability suffices.** If `H` is not co-amenable in `F_d`, that is,
   there is no `F_d`-invariant mean on `ℓ^∞(H\F_d)`, then `rho_H < 1`, and so
   `p_c(T) < p_c(H;T)`.

For normal `H` the Schreier graph is the Cayley graph of `F_d/H`, and item 2
recovers item 4 of `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`.
The converse of item 3 (co-amenable implies `rho_H = 1`) is the standard
Følner–Kesten equivalence for Schreier graphs (Eymard, *Moyennes invariantes et
représentations unitaires*, LNM 300, 1972; Woess, *Random Walks on Infinite
Graphs and Groups*, Ch. 10). It is not used here and is not claimed as
established. With it, the gap holds on `T` exactly for the subgroups that are
not co-amenable.

Novelty. Item 1 is Grigorchuk's cogrowth identity (1980), which is known for
arbitrary subgroups. Items 2 and 3 read it as a percolation statement for
non-normal subgroups. That reading was not found in the local graph, and no
literature search beyond it was made.

**Proof.** `fpbs-tree-subgroup-relative-gap-iff-not-co-amenable-proof`.
