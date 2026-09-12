---
rg: 2
id: private-origin-rows-force-permutation-encoders
kind: claim
title: If the origin cells of decoder rows are glued only forward along an order avoiding the origin row, every forward-sufficient encoder is a symbol permutation
distinct_from:
  two-by-two-single-coincidence-strict-cores-classified: that classifies strict rules on 2x2 tables with one coincidence at the Boolean level; this shows for tables of any size that relays whose origin cells are private, or glued only forward along an order, carry no information, so the encoder reads only its origin cell.
  copy-codes-make-one-sided-table-identities-strict: that exhibits strict copy codes for cells glued to the origin; this assumes the marked class is the origin alone and proves forward sufficiency then forces a symbolwise permutation encoder.
  triangular-forward-tables-force-surjectivity: that proves bijectivity through freeness of the table group of a triangular partition; this proves it from the rules, on partitions whose table group may be anything, including every mixed-bigon square presentation.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `private-origin-rows-permutation-proof`.

Let `D = (A, S, M, nu, mu)` be a design and `E` a marked partition of `S x M` whose
marked class is `{(1_S, 1_M)}`. Call `(s, 1_M)` the **origin cell** of row `s`.
Suppose the rows `S \ {1_S}` can be ordered `s_1, ..., s_k` so that, for every `i`,
the class of `(s_i, 1_M)` contains no cell of row `1_S`, no other cell of row `s_i`,
and otherwise only cells of rows `s_j` with `j > i`. In particular this holds when
every origin cell `(s, 1_M)` with `s != 1_S` is a singleton class.

**Theorem.** If `(nu, mu)` is forward sufficient on `E`, then `mu = psi o pi_(1_M)` for a
permutation `psi` of `A`. So over every group and every realization whose forward
table dominates `E`, the encoder is the symbolwise permutation `x -> psi o x`, and no
such realization is strict.

**At a group realization.** The marked class is the origin iff `S ∩ M^(-1) = {1}`. The
origin cell of `s` is private iff `s` is no product `s' m'` other than `s . 1`.

**Consequence for square tables.** The partitions of
`mixed-bigon-difference-graphs-present-vh-square-complexes` use only non-identity memory
labels, so their marked class is the origin and every origin cell is private. No rule
pair with a non-permutation encoder is forward sufficient on them. A square table that
can carry a strict pair needs anchoring cells `(s, 1_M) ~ (s', m')` whose gluing reaches
row `1_S` or closes a cycle, so some decoder addresses must be memory products. The
shift–shear designs do this through the marked cells `(v_r^(-1), v_r)`.

Proof: Section 7 of the artifact.
