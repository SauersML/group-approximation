---
rg: 2
id: sound-rule-transfinite-closure
kind: claim
title: Transfinite iteration of sound radical rules stays inside the MF radical
distinct_from:
  mf-relation-closure: That claim names the full semantic closure, which is not computable in general; this one closes any supplied family of proved lower bounds under quotient iteration and shows the result is still a lower bound — an inference calculus running inside that closure.
  defect-saturation-full-mf-radical: That claim is a single-group existence statement whose one saturation step already fills the radical; this one is the generic iteration scheme, valid for every group and every sound rule, with a completeness criterion.
---

Call `Delta` a **sound rule** if it assigns to every countable group `H` a
normal subgroup `Delta(H) <= Rad_MF(H)`.  Given a countable group `G`, set

```text
N_0 = 1,   N_(alpha+1) = preimage in G of Delta(G/N_alpha),
N_lambda = union of the N_alpha, alpha < lambda,
```

an increasing chain of normal subgroups.  Then:

1. `N_alpha <= Rad_MF(G)` for every ordinal `alpha`;
2. the chain stabilizes at a countable ordinal; write `Cl_Delta(G)` for the
   stable value;
3. `Cl_Delta(G) <= Rad_MF(G)`;
4. `Cl_Delta(G) = Rad_MF(G)` if and only if `G/Cl_Delta(G)` is MF — a
   **completeness criterion** for the rule `Delta` on the group `G`;
5. if `Cl_Delta(G) = G` then `Rad_MF(G) = G`: every homomorphism to an MF
   group is trivial.

**Why iterate.**  New obstruction hypotheses can become true only after
earlier MF-forced relations have been imposed: modulo `N_alpha` an element
may become torsion, an orbit may start to commute, two sites may become
identified, a subgroup may become normal, a defect may become normally
generating.  Quotient iteration turns every sound obstruction into a rule of
inference rather than a terminal contradiction.  Sound rules already proved
in this program: finite-normal collapse pieces, the normal property-(T)
pieces of the intrinsic compression defect, pointwise torsion collapse
(`compression-torsion-collapse`), and the routing-data closures of
notes/COMPRESSION_COLLAPSE_MF_RADICAL.md; `defect-saturation-full-mf-radical`
is the case where a single application already gives `Cl_Delta(G) = G`.

## Ideas

**Obstruction depth.**  For `g in Cl_Delta(G)` put
`depth_Delta(g) = min { alpha : g in N_alpha }`, and give `G` the supremum.
Cascades where `r_1 = 1` in every MF image first makes the hypotheses for
`r_2` true, and so on — possibly through genuine `omega`-stage examples —
would show the iteration is not an artifact.  No example of depth `> 2` is
on record; constructing one is an open engineering problem, not a claim.
