---
rg: 2
id: universal-hyperbolic-vtf-iff-rf
kind: claim
title: Universal torsion-free finite residuals, virtual torsion-freeness, and residual finiteness are equivalent for hyperbolic groups
distinct_from:
  hyperbolic-finite-residual-is-torsion-free: that is one of the three universal assertions; this records the theorem that it is exactly as strong as universal residual finiteness, rather than a weaker target.
  non-residually-finite-hyperbolic-group: that asks for one counterexample; this identifies three equivalent universal formulations and does not decide their common truth value.
---

The following assertions are equivalent.

1. Every word-hyperbolic group is residually finite.
2. For every word-hyperbolic group `G`, its finite residual

   ```text
   R_f(G) = intersection {ker(phi) : phi:G -> F, F finite}
   ```

   is torsion-free.
3. Every word-hyperbolic group is virtually torsion-free.

Consequently [[hyperbolic-finite-residual-is-torsion-free]] is not a
strictly weaker universal problem than residual finiteness: the two are
logically equivalent across the class of word-hyperbolic groups.

**Primary source.** Daniel T. Wise, *Complete square complexes*, Comment.
Math. Helv. **82** (2007), 683--724, DOI `10.4171/CMH/107`, Proposition 9.2,
Theorem 9.3, and its proof. Source checked 2026-08-30.
