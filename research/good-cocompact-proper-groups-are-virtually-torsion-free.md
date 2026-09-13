---
rg: 2
id: good-cocompact-proper-groups-are-virtually-torsion-free
kind: claim
title: Good hyperbolic groups are virtually torsion-free, and universal goodness would settle Gromov's question
distinct_from:
  good-groups-have-no-persistent-finite-cohomology: that says a good group has no persistent finite-coefficient class; this combines it with the persistence of Chern–Quillen classes to force virtual torsion-freeness, and weakens goodness to surjective inflation with trivial F_p coefficients in large degrees
  universal-hyperbolic-vtf-iff-rf: that equates universal virtual torsion-freeness with universal residual finiteness; this supplies a profinite-cohomological hypothesis that implies both
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Let `G` act on a contractible `G`-CW complex of finite dimension. Assume the action
has finitely many orbits of cells, finite stabilizers fixing their cells pointwise,
and a fixed point for every finite subgroup. This holds for every word-hyperbolic
group. Let `M` be the lcm of the orders of the finite subgroups.

1. **(G)** If `G` is good in Serre's sense, then `G` is virtually torsion-free.
2. **(G')** More weakly: suppose that for every prime `p | M`, inflation
   `H^q(G_hat;F_p) -> H^q(G;F_p)` is surjective for all sufficiently large `q`. Then
   `G` is virtually torsion-free. Only trivial coefficients and large degrees are
   used.
3. **(H) Universal form.** If every word-hyperbolic group satisfies (G'), in
   particular if every word-hyperbolic group is good, then every word-hyperbolic
   group is virtually torsion-free, hence residually finite.
4. **Contrapositive.** A non-residually-finite hyperbolic group produces, through
   `hyperbolic-rf-question-equals-vtf-question`, a hyperbolic group whose inflation
   from its profinite completion misses classes with trivial `F_p` coefficients in
   unboundedly many degrees. The missed classes are its Chern–Quillen classes.

So every counterexample to Lück 11.1(i) or to Gromov's question fails goodness
already for trivial coefficients. Goodness is known for hyperbolic virtually special
groups (Kropholler–Wilkes Theorem 9, recorded on
`good-groups-have-no-persistent-finite-cohomology`). Those groups are residually
finite anyway, so this is consistent and adds nothing for them.

Proof: `good-cocompact-proper-groups-are-virtually-torsion-free-proof`. Unreviewed;
not Lean-verified; no priority claimed (bounded check, artifact §6).
