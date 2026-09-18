---
rg: 2
id: proper-sft-covers-exclude-finite-orbits-and-sofic-constants
kind: claim
title: A proper SFT that strongly post-surjects onto its full shift has no finite orbit over a residually finite group and no constant point over a sofic group
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that concludes pre-injectivity for strongly irreducible domains; this concludes non-existence of any strongly post-surjective cover, with no irreducibility, for domains with a finite orbit (residually finite groups) or a constant point (sofic groups).
  quantitative-surjunctivity-constants-lift-from-quotients: that transfers surjunctivity constants from quotients; this counts fixed points of one finite quotient against lifts of a post-surjective map on a proper domain.
  nonamenable-groups-carry-arrow-shift-strict-automata: that builds arrow-shift domains, which have no finite orbit; this explains why such domains are the only candidates over residually finite groups.
artifacts:
  - research/artifacts/constant-point-domain-count-2026-09-17.md
---

**ESTABLISHED** by `proper-sft-cover-quotient-and-microstate-count-proof` (elementary counting; no novelty
claimed for the technique, which is the Weiss / Ceccherini-Silberstein–Coornaert periodic-point count).

**Setting.** `G` a group, `A` a finite alphabet, `X ⊊ A^G` a subshift of finite type, and `F : X → A^G` an
automaton that is strongly post-surjective with lifts inside `X`, as in
`strict-pairs-give-dual-failures-on-bounded-defect-domains`. Domain and target use the same alphabet.

**Theorem.**
1. **(Finite quotients.)** There is a finite `B ⊆ G`, depending only on the window of `X`, the memory of `F`,
   the lift constant `Φ` and one forbidden pattern, such that for every finite-index `H ⊴ G` with
   `H ∩ B = {1}`, `X` has no `H`-fixed point. If `G` is residually finite, `X` has no finite `G`-orbit.
2. **(Sofic groups.)** If `G` is sofic, `X` contains no constant configuration.

Neither part uses strong irreducibility of `X` or non-pre-injectivity of `F`.

**Consequences.**
- Every domain `X_R` from `strict-pairs-give-dual-failures-on-bounded-defect-domains` contains the constant
  `τ(a^G)`. So part 2 reproves Gottschalk's conjecture for sofic groups (Gromov, Weiss), through the
  proper-domain route.
- Over residually finite groups, any counterexample to `proper-sft-domains-admit-no-dual-failures` is an SFT
  without finite orbits. For strongly irreducible SFTs on free groups, the existence of such an SFT is an
  open problem (arXiv 2401.16774), so that kill-test is at least as hard as the periodic-point question.
