# Kourovka 20.47: state (bh-k2047, 2026-09-19)

**Problem** (Le Boudec, Matte Bon; wording as recorded in aae1608cbe): Is every faithful, minimal,
strongly proximal action of F_n on a compact space topologically free? **Status: OPEN.**

## What is known, and who gets credit

- **Extremely proximal actions are topologically free.** For minimal actions this is due to
  Le Boudec, arXiv:1802.04736v4, Lemma 4.3 (read at source): under (EP), "if the action … is not
  topologically free, then it is micro-supported". F_n has no pair of nontrivial elements with
  disjoint supports, which rules out micro-support.
- **Node** `kourovka-20-47-extreme-proximality-forces-topological-freeness` (4f865cbe62, 82e540dfe3;
  lane proof, unreviewed) extends this to:
  - any torsion-free group with cyclic centralizers;
  - actions that need not be minimal.
- **Cases therefore excluded as counterexamples:**
  - minimal general-type tree-boundary actions;
  - minimal circle actions, conditional on the Ghys–Margulis structure theorem (recalled, not
    re-read);
  - minimal sets of dendrite actions, conditional on the Duchesne–Monod extreme-proximality
    theorem (secondary quote only);
  - convergence boundaries, since each nontrivial element there has at most two fixed points.

## Shape a counterexample must have

Suppose F_n acts faithfully, minimally and strongly proximally on X, and some g ≠ 1 fixes an open
set U pointwise. Let K = supp g.

1. **Not extremely proximal:** K meets every translate hK.
2. **Singletons out of reach:** the Vietoris orbit closure of K contains no singleton.
3. **Measures still move:** measures on K can be pushed into U, by strong proximality.
4. **Intersecting supports:** any two nontrivial elements have intersecting supports. So every
   rigid stabilizer of a proper open set is trivial, and the action is as far from micro-supported
   as possible.
5. **Non-amenable URS:** the stabilizer URS is nontrivial, and by Kennedy's C*-simplicity criterion
   it must be non-amenable, since F_n is C*-simple.
6. **Where it must live:** a space built for the purpose, most likely a Cantor-type space, that is
   not a tree boundary, a circle, a dendrite or a convergence boundary.

## Open leads, none started

- **Relative to a factor:** a boundary that is strongly proximal relative to a topologically free
  factor, with fibers where elements can fix open sets without having disjoint supports.
- **URS side:** a non-amenable URS of F_n realized as the stabilizer URS of some boundary, for
  example one built from Glasner–Weiss-type URS constructions. Its members would need open-set
  fixators.
