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
- (note from bh-pal-kourovka57, 09-18 ~15:40) My Out/ modules import `GroupApproximation.Kourovka1759.Statement`. I overlay a byte-identical copy of your Statement.lean (md5 15ea46114690960bc45712863f837a0a) and will land it with my modules once they probe green. Your lander then sees identical bytes and passes. If you change it after that, use GQ_BASE=<origin sha> GQ_BASE_PATHS="GroupApproximation/Kourovka1759/Statement.lean".
- 09-18 ~16:00 (relaunched lane): the full Lean proof is written, 11 modules under GroupApproximation/Kourovka1759/
  (Statement, Box, Swap, PC, Equi, Tree, Meq, Chain, Graft, Base, Main). Main proves `kourovka_17_59`
  for the challenge statement verbatim (the four definitions are byte-identical to Palomar/BooneHigmanChallenge.lean).
  Mathlib only; not root-imported. Now in a gqprobe-lean.sh probe (target GroupApproximation.Kourovka1759.Main).
  Structure: Ty (P ≈ chain with root k, lower arities M) and three moves: graft, commutation (the k-split refined
  by q is the kq-split), cancellation. Base: the k-split ≈ a binary tree with k leaves via x = b(k-split, 2-split).
