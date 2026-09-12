---
rg: 2
id: boolean-core-is-uniform-single-demand-network-coding
kind: claim
title: Strict rule pairs for fixed tables are uniform single-demand network codes that fail on the transposed network
distinct_from:
  surjunctivity-is-axiomatized-by-rectangle-clauses: that proves a group is nonsurjunctive exactly when it realizes strict data; this recasts the strict-data condition itself as a network-coding problem and proves Boolean filters for discrete forward tables and one-relay shapes.
  strict-automata-live-on-canonical-table-groups: that fixes a rule pair and finds the only groups it needs; this fixes the pair of tables and studies which rule pairs, over which alphabets, are strict.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `boolean-core-network-coding-proof`.

Fix label sets `S` and `M` with distinguished labels `1`, a forward table `T_f` on `S x M`, and a
reverse table `T_r` on `M x S`.

**Network form.** `N(T_f)` has:
- one source per `T_f`-class;
- one relay per `s` in `S`, applying a shared rule `mu` to the tuple of classes in row `s`;
- one sink applying `nu` to the relay outputs, which must return the source of the class of `(1,1)`.

The transposed network `N^t(T_r)` has relays `m` in `M` applying `nu` to the classes of the
reverse row `m`, and a sink applying `mu`.

Then `Dec(T_f)` holds iff `(mu, nu)` solves `N(T_f)`, and `Enc(T_r)` holds iff `(nu, mu)` solves
`N^t(T_r)`. So strict data are the uniform codes that solve the forward network and fail the
transposed one. Linear codes over a finite field are exactly the one-sided inverse identities at
table level.

**Boolean filters, over every alphabet.**
- **Discrete forward table.** If no two forward cells are identified, every solution is
  `mu = f o pi_1`, `nu = f^-1 o pi_1` for a permutation `f`. It satisfies `Enc` on every reverse
  table, so a strict core needs a forward coincidence.
- **One relay or one column.** If `S = {1}` or `M = {1}`, and `T_r` contains the transpose of
  `T_f`, every solution of `N(T_f)` solves `N^t(T_r)`.

Proofs: Sections 1 and 3 of the artifact.
