---
rg: 2
id: q-masa-to-fresh-packet-morita-bridge
kind: claim
title: Turn the flip-free q-MASA character vector into one fresh packet multiplicity vector
distinct_from:
  raw-radical-branch-morita-reset: that starts from four rank-drop radical characters; this starts from the complete q-MASA character supports of the two rank-up Schur children.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out asking a subgroup isomorphism alone to change multiplicity; this asks for a one-sided corner or projective incidence after the exact type vector has been transported.
---

For each of the finitely many levels required by
`constant-depth-schur-lift-of-doubling-tape`, construct a fixed ordinary-group
cell coupling the flip-free endpoint `K_f` to a fresh Schur packet so that:

1. the complete weighted `K_f` character vector is compared with the fresh
   input packet multiplicity vector with normalized discrepancy at most
   `C sqrt(E)`;
2. the two disjoint supports selected by `(QMR3)` contribute their **sum** to
   the next marked multiplicity, retaining the factor-two active restriction;
3. every complementary `K_f` character either enters an explicitly tracked
   next type or is charged to the finite BCS violation/certificate energy;
4. only `K_f` is placed in the next packet commutant, so `(QMR2)` prevents any
   old selector generator from commuting automatically with the fresh
   context; and
5. the exact marked infinite-dimensional BCS representation extends across
   the finite chain.

The cell must be one-sided.  It may transport the child vector before a
balancing flip is adjoined, but its returned packet cannot contain the flip
which exchanges the two supports.

## Attempts

- **Ordinary HNN identification. Dead.**  It preserves each `K_f` character
  multiplicity and cannot perform the required matrix-scale conversion.
- **Direct product or selector amalgam. Dead.**  Commuting the fresh packet
  only with `K_f` does avoid selector globalization, but
  `q-masa-selector-bridge-is-scale-conservation` shows that its apparent
  multiplicity gain is exactly the inverse change in simple dimension.
  Common-scale marked multiplicity is conserved.  Divisibility and arbitrary
  correlation with fresh selector types create further leakage, never the
  required fixed-scale contraction.
- **Finite restriction-matrix search. Active.**  Because the depth and all
  packets are fixed, enumerate the exact `K_f` restriction matrices, adjoin
  candidate proper-corner incidences, and solve for a positive functional
  which contracts the marked branch sum while assigning nonnegative cost to
  every complementary type.  A feasible rational certificate is a complete
  local proof; an infeasibility dual is a theorem-grade stationary-flow
  obstruction.
- **Transverse Pauli completion. Dead when the child line varies.**  Adding
  partners to rebuild a fixed spin factor seems to repair the scale loss, but
  `selector-free-transverse-completion-has-fixed-radical` gives a dichotomy.
  If the endpoint still forgets the old selector center, its commutator form
  and radical are selector-independent; if it follows the corrected lines
  `Q_x`, its commutators regenerate nontrivial old selector words.  The live
  search must therefore leave the class-two subgroup category.
