---
rg: 2
id: literal-group-not-stable-in-finite-actions-proof
kind: route
title: Contrapose the stability principle against literal soficity
target: literal-group-not-stable-in-finite-actions
requires: [literal-group-sofic, marked-quotients-not-lef, sofic-stable-implies-residually-finite]
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - non_mf_groups_exist.tex
---

## Why sufficient

Corollary 5.7 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` (that document has
no section 8).  Three inputs, one line of reasoning.

1. `E` is sofic (`literal-group-sofic`, established by the block-tower proof).
2. `E` is not residually finite: `marked-quotients-not-lef` shows `E` is not
   even LEF, by transporting the compression collapse into a local embedding
   and using cardinality in the finite target, and residual finiteness implies
   LEF.  This input is purely group-theoretic.

   Two independent replacements exist if that node is ever revised.  (a) The
   original operator-norm route: `literal-central-mark-corona-invisible` kills
   `w` in every norm matrix corona, and the regular representation of a finite
   quotient is an exact finite-dimensional unitary representation, so every
   finite quotient of `E` kills `w != 1` (manuscript `cor:notRFD`).  (b) The
   level-collapse route of `literal-mark-quotient-finite-residual`: the marked
   sites are both at level 1, so any finite quotient identifies their lamps and
   kills `w`.  The requirement was rewired from (a) to the group-theoretic form
   on `cairn-verify2`'s recommendation — not to fix a trust surface, since (a)
   is in-repo and Lean-backed, but so that a permutation-approximation theorem
   does not depend on the corona machinery.
3. A sofic group that is stable in finite actions is residually finite
   (`sofic-stable-implies-residually-finite`).

Hence `E` is not stable in finite actions.  Since every standard permutation
stability notion implies stability in finite actions (Gohla--Thom Lemma 3.6 and
the remark after it), `E` fails all of them.

Trust surface, split by conclusion (corrected 2026-08-14 by `cairn-verify2`;
the previous "none external" was inconsistent with this route's own use of
Gohla--Thom Lemma 3.6 one paragraph above).

* *"`E` is not stable in finite actions"* — internal end to end.  Input 3 was
  a literature import when this route was written and is now proved in-repo
  (`notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`, Theorem 3.1),
  so the only external inputs are the standard permanence facts listed in
  `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` section 6a, of which the sole
  non-elementary one is Elek--Szabo.
* *"hence not `rho`-stable, not flexibly stable, not weakly flexibly stable"* —
  this strengthening, which is what the claim's "in any standard sense" asserts,
  rests on Gohla--Thom Lemma 3.6 and the remark after it.  That is external.
  It is source-verified (read from the PDF of `arXiv:2403.09582v2` and recorded
  in `gohla-thom-stable-base-nonsofic-extension`), so the surface is one
  verified citation rather than an unread one, but it is not in-repo and should
  not be described as internal.
