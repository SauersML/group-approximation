# bh-pal-kourovka59
Direction: elementary proof of PC = CT(Z) first (per bh-pal-scope T5), Lean only after it closes.
- 18ebf78dc `piecewise-canonical-permutations-are-transposition-products` (OPEN).
  Proved: PC is a group and boxes pull back to boxes; two meeting boxes cover Z only if one is Z,
  hence for proper boxes A,B a product of <=2 class transpositions restricts to kappa_(A,B);
  transpositions inside one partition give Sym(M) fixing both partitions, so the bijection is free.
  Gap: the induction on piece count - composing with the helper splits target pieces that meet its
  support without lying in it. Three variants recorded with why each fails. Same coherence gap as
  `class-transposition-relations-present-ct-p-z`.
- No Lean written (standing rule: Lean after solving). GroupApproximation/Kourovka1759/ not created.
- 0e0c97d15: node now ESTABLISHED (tree types + exchange lemma + commutation + cancellation; base x = b(a,b)).
  17.59 node got an "Elementary route" remark. Does NOT close the relations node (generation only).
- Lean: proving bh-pal-surface's kourovka_17_59 statement verbatim in GroupApproximation/Kourovka1759/.
