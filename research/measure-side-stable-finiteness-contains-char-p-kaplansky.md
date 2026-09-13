---
rg: 2
id: measure-side-stable-finiteness-contains-char-p-kaplansky
kind: claim
title: Proving that invariant measures make Cantor crossed-product algebras stably finite would prove Kaplansky stable finiteness over the same field
distinct_from:
  kaplansky-direct-stable-finiteness-one-universal-group: that reduces Kaplansky finiteness for all groups to one finitely presented group; this shows the measure side of the paradox/measure dichotomy for Steinberg algebras already contains Kaplansky finiteness.
  no-invariant-measure-steinberg-elementary-no-mf-quotient: that is the paradox side, where no invariant measure forces a properly infinite multiple of the unit; this is the firewall on the other side.
artifacts:
  - research/artifacts/un-paradox-groupoid-tarski-2026-09-13-part2.md
---

Let `k` be a countable field. Suppose that for every countably infinite group `Γ` and every free
minimal action `Γ ↷ X` on the Cantor set with an invariant Borel probability measure, the algebraic
crossed product `LC(X, k) ⋊ Γ` is stably finite. Then `k[Γ]` is stably finite for every group `Γ`.

Consequences for the UN program:
- The boundary of the one-sided transport mechanism on the measure side cannot be settled over
  fields of positive characteristic without settling Kaplansky's stable finiteness conjecture there.
  That conjecture is known for sofic groups (Elek–Szabó) and open in general.
- In characteristic 0 Kaplansky's theorem holds, and the measure side is expected to be settled by a
  faithful trace. That is a separate claim, not asserted here.
