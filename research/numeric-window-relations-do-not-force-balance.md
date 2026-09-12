---
rg: 2
id: numeric-window-relations-do-not-force-balance
kind: claim
title: Window fiber counts used only as numbers force a uniform site law exactly when the decoder memory group is amenable
invalidates: [balance-from-numeric-window-relations]
distinct_from:
  decoder-window-fiber-bound-loses-exactly-the-boundary: that proves the decoder fiber bound and its boundary loss for one automaton; this shows no argument from that bound, translation invariance, integral finitely dependent counts and a zero removes the loss, since unbalanced measures satisfy all of them over every nonamenable decoder memory.
  finite-left-inverse-identity-does-not-force-balance: that is a fact about the end-fixing tree, an index set that is not a group acting on itself, where translation totals fail; this keeps translation invariance on a genuine group and still exhibits imbalance, so the missing input is not relation (a) as a number.
  amenable-decoder-memory-forces-surjectivity: that derives surjectivity from the pointwise decoder identity when the decoder memory group is amenable; this shows the numerical shadow of the identity already gives a uniform site law there and gives nothing once that group is nonamenable.
artifacts:
  - research/artifacts/numeric-window-relations-no-go-2026-09-12.md
---

**ESTABLISHED** by `numeric-window-relations-do-not-force-balance-proof` (artifact Sections 1–3).

Let `G` be a group, `A` an alphabet with `q` symbols, `mu` the uniform product measure, and `M`, `N` finite
sets containing `e`. For finite `E` put `int_N E = {g : gN is contained in E}`. A probability measure `nu`
on `A^G` satisfies the *numerical window relations* for `(M, N)` if:

- **(R1)** `nu` is shift-invariant;
- **(R2)** `q^|EM| nu[p]_E` is an integer for all finite `E` and `p in A^E`, and the restrictions of `nu` to `U` and `U'`
  are independent whenever `UM` and `U'M` are disjoint;
- **(R3)** `nu[p]_E <= q^(-|int_N E|)` for all finite `E` and `p`;
- **(R4)** some cylinder is `nu`-null.

The image of `mu` under a strict automaton with memory `M` and left-inverse memory `N` satisfies them.

1. **Amenable decoder memory.** If `N` generates an amenable subgroup, R1 and R3 force a uniform one-site law.
2. **Nonamenable decoder memory, large alphabets.**
   - If `N` generates a nonamenable subgroup, there is `theta_N < 1` with `|int_N E| <= theta_N |E|` for every
     finite `E`.
   - Take `q >= 3` with `q^(1 - theta_N) >= 2`, and the merge rule `f(a_2) = a_1` (every other symbol fixed).
     The iid image of `mu` under `f` satisfies R1–R4 for every `M`, and its site law is not uniform.
3. **Binary alphabet.** Take `q = 2`. Let `c` have infinite order, and let `N` contain the radius-2 ball of a
   free pair `a, b`. The image of `mu` under the AND rule `x(g) x(gc)` satisfies R1–R4 for `M = {e, c}`, with
   site law `(3/4, 1/4)`.

**Consequence.** In cases 2 and 3 no argument from R1–R4 proves a uniform site law, so none proves balance
at any window. The goal quantifies over every alphabet, so a numerical proof would have to work at the
alphabet sizes of case 2.

This covers the following manipulations of window counts:
- mass transport along the decoder graph;
- averaging over translates or invariant random windows;
- cofinal window families;
- telescoping `tau`, `sigma`, `tau` at the level of counts.

What remains is an input that is not a numerical window relation.
- **The uniform Gibbs specification of the image in base `q`**
  (`research/artifacts/gottschalk-injective-image-uniform-gibbs-bridge-2026-09-08.md`). The merge measure
  fails it: conditioned on the outside, its law at a site is not uniform on the `q - 1` allowed symbols.
- **The pointwise decoder identity `sigma o tau = id`.** Without the group law this coexists with imbalance,
  by the end-fixing tree.

Either input would have to be used together with the group law.
