---
rg: 2
id: open-cells-arithmetical-complexity-of-group-properties
kind: claim
root: true
title: Fill the open cells of the arithmetical complexity ledger of group properties
distinct_from:
  arithmetical-complexity-table-of-group-properties: that is the established ledger; this is the root collecting the cells it leaves open, each with its known bounds and the reason the standard route is blocked.
  sofic-safe-finite-presentation-compiler: that is one of the cells; this is the list.
---

OPEN (root).  Each item is a precise question left open by
[[arithmetical-complexity-table-of-group-properties]]; establishing any of
them fills one cell.

1. **`SOFIC_fp` `Pi^0_2`-complete?**  Known: `Pi^0_2 \ Pi^0_1`.  Needs
   [[sofic-safe-finite-presentation-compiler]]; blocked by soficity of
   centralizing HNN extensions over non-amenable, non-profinitely-closed
   Mikhailova-type subgroups.
2. **`HYP_fp` `Pi^0_2`-complete iff a non-hyperlinear group exists?**  Needs
   [[mf-compiler-positive-branch-is-hyperlinear]]: is the regular trace of
   the MF compiler's positive branch quasidiagonal?
3. **`RF_fp` `Pi^0_2`-complete?**  Known: `Pi^0_2 \ Pi^0_1`.  This is the
   residually finite Higman problem; every finitely presented ambient of
   an r.e. relator set encodes the enumeration through non-closed
   subgroups.
4. **`AMENABLE_fp` `Pi^0_2`-complete?**  Known: `Pi^0_2 \ Pi^0_1`
   ([[amenability-of-finite-presentations-is-pi2-complete]]).  Higman-type
   compilers introduce free subgroups; a mechanism inside finitely
   presented amenable groups with unsolvable word problem is needed.
5. **`FP_rec2` `Sigma^0_3`-complete?**  Known: `Sigma^0_2`-hard, `Sigma^0_3`
   ([[finite-presentability-two-generator-recursive-is-sigma2-hard]]).
   Shift-invariant relator families cannot encode cofiniteness, since
   relations propagate along the shift; on enumerated syntax the answer is
   `Sigma^0_3`-complete ([[enumerated-presentation-finite-generation-levels]]).
6. **Does some group fail weak soficity / linear soficity?**  Each answer
   flips a completeness dichotomy
   ([[weak-soficity-recognition-has-a-pi2-upper-bound]],
   [[linear-soficity-recognition-has-a-pi2-upper-bound]]).
7. **`METABELIAN_fp`, `CONTAINS-F2_fp` exact levels** (`Pi^0_2`, `Sigma^0_2`
   upper bounds; first-level hardness only).
