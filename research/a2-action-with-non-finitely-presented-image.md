---
rg: 2
id: a2-action-with-non-finitely-presented-image
kind: claim
title: Some type [A_2] action has an action image that is not finitely presented, answering Fournier-Facio--Wu--Zaremsky Question 5.8
distinct_from:
  abstract-btb-simple-quotient-fp-gate: that proves the simple quotient of a finitely presented abstract twisted Brin-Thompson group is finitely presented exactly when the action image is; this exhibits an action whose image is not finitely presented, so for it that simple quotient is not finitely presented.
  bffhz-computable-core-fp-upgrade-is-false: that shows the faithful relative automorphism action over a non-finitely-presented simple core has a non-finitely-presented acting group, so it is not of type [A_2]; this is a type [A_2] action of a finitely presented group whose image is not finitely presented.
  normalizer-extension-of-type-a-actor-is-a2-cover: that is the general construction and its criterion; this is an explicit instance in which the criterion's hypothesis holds.
  twisted-btb-clopen-action-is-type-a: that is the type (A) clopen action of a twisted Brin-Thompson group; this extends that action by a diagonal Thompson group and computes the resulting image.
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**ESTABLISHED** by `a2-non-fp-image-via-diagonal-normalizer-proof`.

**The question.** Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Question
5.8, read from the PDF text extracted on MSI:

> "Does there exist an example of a group action G ↷ S that is of type [A_2]
> such that G/ker(G ↷ S) is not finitely presented? (This is equivalent to the
> induced action of this quotient on S being not of type (A_2).)"

Just before it, their Section 5 says: "(That being said, we do not know an
explicit example where it fails, see Question 5.8.)"

**Answer: yes.**
- **Base action.** Thompson's group `V` acts on the set `Ω_C` of proper
  nonempty clopen subsets of binary Cantor space `C` with type (A). This is
  `twisted-btb-clopen-action-is-type-a` for the trivial group on one point, and
  also `fp-full-binary-cantor-groups-have-type-a-actions` with `D = V`.
- **Actor.** `Γ = SV_V` is the twisted Brin--Thompson group of that action,
  acting on the cube `C^(Ω_C)`. It is finitely presented. Let `Ω` be the proper
  nonempty clopen subsets of the cube. Then `Γ` acts on `Ω` with type (A)
  (`twisted-btb-clopen-action-is-type-a`).
- **Diagonal copy of V.** For `w in V` put `δ_w(κ)(s) = w(κ(s))`. Each `δ_w`
  normalizes `Γ`, and `δ_w` does not lie in `Γ` unless `w = 1`.
- **A wreath product.** Thompson's group `F <= V` contains `b, t` generating
  `Z wr Z`. Let `Q = <δ_b, δ_t> ≅ Z wr Z`.
- **The action.** `G~ = Γ x| F_2` acts on `Ω` by
  `(γ, u) . U = γ δ_(φ(u)) U`, where `φ : F_2 -> <b,t>` sends the basis to
  `b, t`.

Then:
1. `G~` acting on `Ω` is of type `[A_2]`;
2. its kernel is isomorphic to `ker φ`, and its image is `Γ x| Q`, which is not
   finitely presented, because `Z wr Z` is not (G. Baumslag, Math. Z. 75
   (1961));
3. the abstract twisted Brin--Thompson group `SV_(G~)` is finitely presented,
   but its canonical simple quotient is not (`abstract-btb-simple-quotient-fp-gate`).

**What this does not do.**
- **The kernel is removable.** The first part of FFWZ Question 5.9 has a
  positive answer for this action: `(G~, ker)` sharply embeds in
  `Γ x| (F_2 * V)`, acting through `Γ x| δ(V)`, whose kernel is finitely
  normally generated (see the proof). So this is not evidence against
  `a2-pairs-embed-in-a2-pairs-with-fng-kernels`.
- **The kernel is recursive.** The image has solvable word problem, consistent
  with `a2-kernel-removal-forces-recursive-kernel`.
- **No new permutational Boone--Higman inputs.** Every group here already lies
  in the permutational Boone--Higman class.

**Novelty: not checked beyond the source.** The FFWZ text poses the question and
says no explicit example is known. No later literature search was possible this
session.
