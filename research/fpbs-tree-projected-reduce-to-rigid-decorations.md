---
rg: 2
id: fpbs-tree-projected-reduce-to-rigid-decorations
kind: route
title: Split tree-projected Cayley graphs by the twist and by coincidences of oriented decoration shapes
target: fpbs-tree-projected-cayley-graphs-strict-thresholds
requires:
  - fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular
  - fpbs-tree-projected-reversible-letter-nonunimodular
  - fpbs-tree-projected-letter-exchange-nonunimodular
  - fpbs-tree-projected-rigid-decorations-strict-thresholds
artifacts:
  - research/artifacts/fpbs-twisted-cyclic-by-free-nonunimodular-2026-09-16.md
---

Let `Gamma`, `H`, `B` and `S` be as in the target.

1. **Normal form.** Section 1 of the artifact shows that `F_n` is free, so the
   extension splits and `Gamma ≅ Z ⋊_chi F_n`, with `chi : F_n -> {±1}` the action
   on `H`. `H` is central iff `chi = 1`. The isomorphism is the identity on `F_n`
   modulo `H`, so the image of `S` still projects into `{1} ∪ B ∪ B^(-1)`.
   Isomorphic Cayley graphs have the same `p_c` and `p_u`.
2. **Twisted case.** If `chi ≠ 1`, then `H` is not central, and
   `fpbs-tree-projected-twisted-cyclic-by-free-nonunimodular` gives
   `p_c < p_u`.
3. **Direct product.** If `chi = 1`, then `Gamma ≅ F_n x Z` via
   `z^m sigma(g) -> (g,m)`. `S` becomes a finite symmetric generating set with
   `pi(S) ⊆ {1} ∪ B ∪ B^(-1)`. Put `D_s = {k : (s,k) in S}`, so that
   `(s,k)^(-1) = (s^(-1),-k)` and the heights over `s^(-1)` are `-D_s`. Compare the
   `2n` oriented shapes `D_s`, `-D_s` (`s in B`) up to translation.
   * **Some shape is a translate of its own reflection.** If `-D_s = D_s + c'`, then
     `c - D_s = D_s` with `c = -c'`, and
     `fpbs-tree-projected-reversible-letter-nonunimodular` applies.
   * **Two shapes of different letters coincide.** Let `s ≠ t`.
     * If `D_t = D_s + c`, or equivalently `-D_t = -D_s + c'`,
       `fpbs-tree-projected-letter-exchange-nonunimodular` applies.
     * If `-D_t = D_s + c'`, then `D_t = c - D_s` with `c = -c'`, and the same claim
       applies.
     * If `D_t = -D_s + c'`, then `D_t = c' - D_s`, and the same claim applies.
   * **No coincidence.** The decorations are rigid, and
     `fpbs-tree-projected-rigid-decorations-strict-thresholds` applies.

   These cases are exhaustive. Two distinct oriented shapes either belong to one
   letter, which is the first case, or to two letters, which is the second.
4. **Conclusion.** In every case `p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`.

Three of the four required claims are established. Only rigid decorations over
`F_n x Z` remain, so this route makes
`fpbs-tree-projected-rigid-decorations-strict-thresholds` the exact open part of
the target.
