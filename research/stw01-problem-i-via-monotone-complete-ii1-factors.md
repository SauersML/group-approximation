---
rg: 2
id: stw01-problem-i-via-monotone-complete-ii1-factors
kind: route
title: Split Kaplansky into monotone completeness of II_1 AW*-factors and exclusion of wild II_1 factors
target: stw99-problem-i-quasitraces-are-traces
requires:
  - stw01-ii1-awstar-factors-are-monotone-complete
  - stw01-monotone-complete-ii1-awstar-factors-are-w-star
  - stw01-kaplansky-2q-pedersen-retract-equivalence
---

**Derivation.**
- If every type `II_1` AW*-factor is monotone complete, and every monotone
  complete one is W*, then every type `II_1` AW*-factor is a W*-factor.
- By Gow's Theorem A, (i) implies (ii) (`stw01-kaplansky-2q-pedersen-retract-equivalence`),
  so every bounded 2-quasitrace on a unital C*-algebra is a trace.

**Converse.** Problem I makes every type `II_1` AW*-factor W*, hence monotone
complete and trivially non-wild. So Problem I is equivalent to the conjunction of
the two open prerequisites.

This sharpens Gow's §6 bridge (arXiv:2601.04431v2). Gow assumes Question 6.3 for
every monotone complete C*-algebra. Only its type `II_1` factor case is needed, and
by Gow Corollary 4.10 that case is the non-existence of wild `II_1` factors.
