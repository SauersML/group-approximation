---
rg: 2
id: one-haagerup-factor-kills-bader-shalom-universality
kind: claim
title: A Bader-Shalom lattice with one Haagerup factor contains no infinite finitely generated simple Kazhdan group, so a universal family of such lattices needs two non-Haagerup factors
distinct_from:
  decidable-simple-groups-embed-in-bader-shalom-lattices: that is the open universality statement P1; this is an established obstruction to it, upgrading its Attempt 1(b) from two Haagerup factors to one.
  decidable-host-classes-reduce-to-canonical-kazhdan-groups: that excludes discrete Haagerup host classes; this excludes lattices in products where only one non-discrete factor is Haagerup and the lattice itself need not be Haagerup.
  haagerup-cut-out-completions-force-haagerup-quotients: that pushes the Haagerup property from a completion down to a quotient of the source group; this uses injectivity of Bader-Shalom projections to embed a Kazhdan probe in a compact group.
---

**ESTABLISHED** through `one-haagerup-factor-kills-bader-shalom-universality-proof`.

Let `Γ < G_1 × G_2` satisfy the hypotheses of
`bader-shalom-normal-subgroup-theorem` (`n = 2`). Suppose `G_j` has the
Haagerup property for some `j`. Then:

1. for every subgroup `Λ ≤ Γ` with property (T), the closure `K` of `p_j(Λ)` is a
   compact group and `p_j` restricts to an injective homomorphism `Λ → K`;
2. `Γ` contains no infinite finitely generated simple group with property (T);
3. hence, if P1 (`decidable-simple-groups-embed-in-bader-shalom-lattices`) holds
   for even one input, namely a decidable simple Kazhdan host `H` of `Z` from `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`,
   then the lattice hosting `H` has **both** factors non-Haagerup. Moreover each
   `G_i` contains the closed subgroup `cl p_i(H)`, which is non-compact, and
   `cl p_i(H)` itself is not Haagerup.

**Classes killed.** No factor on either side may be amenable, a closed subgroup
of the automorphism group of a locally finite tree (BdlHV Definition 2.7.5 and
the remark after it), or any locally compact group acting continuously and
properly on a CAT(0) cube complex. That last class includes Neretin groups,
as in `haagerup-cut-out-completions-force-haagerup-quotients`. So every
Burger-Mozes, Wise and Rattaggi lattice dies, and so does every lattice in
(tree) × (anything). Attempt 1(b) of the target needed both factors to be
Haagerup, and its "stronger form" left a survivor with a Kazhdan probe sitting
discretely in the other factor. That survivor does not exist.

**Trust.** Items 1-3 rest only on established nodes and the verbatim BdlHV
import. In the list of classes killed, the amenable and tree cases are quoted
from BdlHV. The Haagerup property passes to closed subgroups by restricting `π`
and `b`. The cube-complex and Neretin cases carry the trust level of
`haagerup-cut-out-completions-force-haagerup-quotients-proof`, which lists
Cherix-Martin-Valette, Niblo-Reeves and Genevois-Lonjou-Urech as unquoted
standard inputs.

**Invariant and step.** The invariant is maximal almost periodicity of Kazhdan
subgroups of `Γ`. Every member of the class dies when the Kazhdan probe is
forced into the compact closure of its image in the Haagerup factor, because
the NST makes that projection injective.
