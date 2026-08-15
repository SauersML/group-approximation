---
rg: 2
id: atlas-steinberg-rank-five-translation
kind: claim
title: An explicit usable relator list from the rank-five Steinberg presentation
distinct_from:
  atlas-relator-central-sufficiency: that proves which lists are usable and that the Steinberg route lands in the usable class; this is the concrete extraction — actually writing the finite list as words in the twelve atlas generators.
  leavitt-steinberg-hs-unstable: that is the branch selection the finished list would feed (through the one-unitary criterion); this is the missing input datum, purely presentational, with no analytic content.
artifacts:
  - research/artifacts/atlas-relator-extraction-2026-08-15.md
---

**Claim.**  There is an explicitly written finite set `T_St` of words in
the twelve adjacent-transvection generators of `P̄ = A₈ * A₈` such that
`P̄/⟨⟨T_St⟩⟩ ≅ St₅(L_{F₂}(1,2))` compatibly over `Q` — hence, by
`atlas-relator-central-sufficiency`, a usable relator list for the
canonical regular-`A₈` criterion, making the one-unitary optimization of
`docs/EXPLICIT_LEAVITT_ATLAS.md` §9 fully concrete for the first time.

The program (from the notes file, steps 1–4): fix a five-leaf complete
prefix code and its `Θ`-isomorphism `M₅(L) ≅ L`, giving `E₅(L) ≅ Q` and
the 100 generators `x_ij(a)`, `a ∈ {1, e, f, e^*, f^*}`; express each
`x_ij(a)` as an explicit word in the twelve atlas generators (the real
work — a factorization problem in `Q` over the atlas, the rank-3
analogue being (7) of the atlas doc); translate the finite Steinberg
presentation of `St₅` over the finite ring presentation of `L` through
that dictionary; validate the output against the finite-quotient screens
(any output failing them is wrong).  Correctness needs only centrality
of `K₂(5, L)` in `St₅(L)` — not its vanishing, not its finite
generation, not `U_Q ≅ St₅(L)`.

## Attempts

- **Steps 2 AND 3 COMPLETE (2026-08-15, night).**  Forward dictionary:
  `atlas-rank-five-dictionary` (100 generators, machine-verified).
  Reverse dictionary: `atlas-reverse-dictionary` (the twelve atlas
  generators as `x`-words, eight of them single generators) — closing a
  genuine gap the naive program missed: surjectivity of the comparison
  map `ψ : St₅(L) → P̄/⟨⟨T_St⟩⟩` is NOT automatic and is exactly what the
  reverse dictionary supplies.  Full translated family emitted and
  verified: **1,112 distinct nonidentity relators, all in `R̄`**
  (X-lengths 4–595), plus the twelve reverse-dictionary relators:
  `|T_St| = 1,124`.  Cross-validation: `132` of the 1,112 escape the
  cartesian subgroup, as `atlas-kernel-window-length-nine` demands.

  **The usability chain, with its one gap.**  (1) every defining relator
  of `St₅(L)` dies in `G = P̄/⟨⟨T_St⟩⟩`, so `ψ` exists — *this is the
  gap*; (2) `ψ` surjective — proved in-repo
  (`atlas-reverse-dictionary`); (3) `ker(G ↠ Q) = ψ(K₂(5,L))`; (4)
  `K₂(5,L)` central at rank ≥ 5 (Kervaire–Steinberg, tagged), and
  central images under surjections are central; (5) hence
  `N̄ ≤ ⟨⟨T_St⟩⟩ ≤ R̄` and `T_St` is usable
  (`atlas-relator-central-sufficiency`).  Nothing about `K₂(5,L)` beyond
  centrality is used.

  **Step (1) audited and sharpened (2026-08-15, night).**  Auditing the
  1,112-relator family against the pinned scheme (St1)–(St3) shows it is
  a strict subset of even the generator instantiation: (St2) was emitted
  for only 3 of 25 coefficient pairs, root-subgroup commutativity
  `[x_ij(a), x_ij(b)] = 1` was missing entirely, and (St3) only where
  the product lands back in the letter set.  So the 1,112 words are a
  NECESSARY set (their kernel membership and cartesian escape stand),
  not a candidate presentation; the full generator instantiation, with
  the dictionary extended to two-letter coefficients so (St3)'s
  right-hand sides exist, is being emitted and verified.  And (St1)
  contributes no relator on the generating set — `x_ij(r+s)` is DEFINED
  as a product — so the true content of completeness is
  **well-definedness with bounded contexts**: that `x_ij(c)` is
  independent of how `c ∈ L` is written as a sum of monomials, enforced
  by finitely many contexts `u·r·v` of each defining ring relation `r`.
  That bounded-context statement is the actual content of
  [KrM, Theorem 3] for this program (pinned verbatim in the artifact:
  Krstić–McCool, JPAA 141 (1999) 175–183; `n = 5 ≥ 4` safely above the
  sharp `n = 3` failure of their Corollary 2), and it is the derivation
  now being attempted directly for this particular `L`.
- **Amalgam route (dead).**  `atlas-charts-overlap-trivially`: the charts
  meet trivially, so no relative presentation falls out of overlap
  identifications; every relator must be produced as a genuine
  mixed-chart Steinberg relation.
- **Enumeration route (provably cannot finish).**
  `atlas-kernel-window-length-nine`: enumeration produces subgroups of
  `R̄` and never an upper bound on `N̄`; and every list of X-length `≤ 8`
  is certified insufficient by the retraction screen, so the recursive
  exhaustion program cannot terminate below length nine and can never
  self-certify.  Its enumerated windows remain valid necessary
  constraints for the nonhyperlinearity direction.
- **Uniform-refinement trap — CORRECTED (2026-08-15, late; the first
  version of this bullet misread the finding and would have steered the
  next session away from the construction that worked).**  The common
  refinement `E = (000,001,010,011,1)` IS a legal complete prefix code —
  the join of the two charts — and it is the code the entire dictionary
  runs on, its shared leaf the hinge of Case B.  The non-uniform
  multiplicities cost exactly one thing: `GL(E)` contains neither chart
  group, so root elements are not chart *members*; they are chart
  *words*, which is all the criterion needs.  The `4·2^k` uniform
  refinements are the superperfect hosts of §9, not the Steinberg chart.
- **Next screen (designed, cheap, not yet run).**  Extend the
  finite-quotient screens to the one Goursat-uncovered family — finite
  `F` generated by two non-commuting injective copies of `A₈` with
  `F ≇ A₈` (candidates `A₉, S₈, A₁₀, GL₅(2), Sp₆(2), M₂₄`) — using the
  centralizer precomputation that cuts the search before word
  evaluation.  A survivor pushes the lower bound past nine; none is one
  more passed screen for the radius-5 boundary words.
