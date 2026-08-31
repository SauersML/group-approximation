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

OPEN (root). Each item is a precise question left open by
[[arithmetical-complexity-table-of-group-properties]]; establishing any of
them fills one cell.

0. **Common gate.** By
   [[finite-presentation-rice-criterion-via-the-fixed-positive-rope]] every
   hereditary cell below is the single question "does the MF compiler's
   positive rope have the property". The rope is MF and torsion-free
   ([[mf-compiler-positive-branch-is-torsion-free]], which closes the
   torsion-free cell), is not amenable and is not residually finite, so for
   cells 3 and 4 this route is provably unavailable.

1. **`SOFIC_fp` `Pi^0_2`-complete?** Known: `Pi^0_2 \ Pi^0_1`. Needs
   [[sofic-safe-finite-presentation-compiler]]; blocked by soficity of
   centralizing HNN extensions over non-amenable, non-profinitely-closed
   Mikhailova-type subgroups.
2. **`HYP_fp` `Pi^0_2`-complete iff a non-hyperlinear group exists?**
   Needs [[mf-compiler-positive-branch-is-hyperlinear]]: is the regular trace
   of the MF compiler's positive branch quasidiagonal?
3. **`RF_fp` `Pi^0_2`-complete?** Known: `Pi^0_2 \ Pi^0_1`. This is
   the residually finite Higman problem; every finitely presented ambient of
   an r.e. relator set encodes the enumeration through non-closed subgroups.
4. **`AMENABLE_fp` `Pi^0_2`-complete?** Known:
   `Pi^0_2 \ Pi^0_1`
   ([[amenability-of-finite-presentations-is-pi2-complete]]). Higman-type
   compilers introduce free subgroups; a mechanism inside finitely presented
   amenable groups with unsolvable word problem is needed.
5. **`FP_rec2` `Sigma^0_3`-complete?** Known: `Sigma^0_2`-hard,
   `Sigma^0_3`
   ([[finite-presentability-two-generator-recursive-is-sigma2-hard]]).
   Shift-invariant relator families cannot encode cofiniteness, since
   relations propagate along the shift; on enumerated syntax the answer is
   `Sigma^0_3`-complete
   ([[enumerated-presentation-finite-generation-levels]]).
6. **Is the fixed universal test group weakly sofic / linear sofic?** Let
   `V` be the fixed two-generator finitely presented group of
   [[universal-local-approximation-fixed-two-generator-test-group]]. By
   [[fixed-finite-relator-quotient-tests-local-permanence]],

   ```text
   V is weakly sofic
     <=> every group is weakly sofic
     <=> weak soficity is closed under arbitrary quotients,

   V is linear sofic over F
     <=> every group is linear sofic over F
     <=> F-linear soficity is closed under arbitrary quotients
                                                    (for each field F).
   ```

   Thus each universe-wide existence and quotient-permanence question is
   decided by one prescribed group `V`. For every computable field `F`,
   the two answers still flip the completeness dichotomies in
   [[weak-soficity-recognition-has-a-pi2-upper-bound]] and
   [[linear-soficity-recognition-has-a-pi2-upper-bound]]. No displayed horn
   is decided here.
7. **`METABELIAN_fp`, `CONTAINS-F2_fp` exact levels**
   (`Pi^0_2`, `Sigma^0_2` upper bounds; first-level hardness only).

## Attempts

The obvious attack on every finite-presentation cell is a property-safe
Higman compiler: cells 1--4 record where it dies (non-amenable non-closed
edges; an abstract trace; the residually finite Higman problem; free
subgroups in every HNN tower). For cell 5 the obvious attack, an r.e. edge
set complemented to force cofiniteness, dies because complements of r.e.
edge sets give non-recursively-presented groups and shift-invariant relator
families collapse under the shift. Cell 6 is no longer an unconstrained
search over groups: the fixed quotient tester reduces universality and
quotient permanence exactly to the two approximation calculations above on
the same prescribed group `V`. No claim is made that either calculation is
known. Cell 7 is deferred: its positive branch would have to be metabelian,
respectively free-subgroup-free, on a finitely presented switch, which is
the same obstruction as cell 4.
