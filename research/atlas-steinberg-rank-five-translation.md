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
`notes/EXPLICIT_LEAVITT_ATLAS.md` §9 fully concrete for the first time.

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

## ESTABLISHED (2026-08-15, night)

The claim is proved: `T_St` exists explicitly — **4,648 verified words**
(`atlas-steinberg-rank-five-translation-proof`), with the completeness
of the underlying presentation proved in-repo
(`atlas-steinberg-spare-index-independence`, adversarially verified) and
the once-planned Krstić–McCool import fully discharged; the only
remaining literature premise on the route is Kervaire–Steinberg
centrality.  The canonical regular-`A₈` one-unitary criterion is now a
fully explicit finite object.  The attack log below is retained as the
history of how each obstruction fell.

## Attempts (historical)

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

  **Step (1) audited, sharpened, and partly closed (2026-08-15, night).**
  The audit against the pinned scheme showed the first emitted family
  (1,112 relators, mirroring the rank-3 `relation_family()`) is a strict
  subset of the generator instantiation — a NECESSARY set, not a
  candidate presentation.  The **full instantiation** is now emitted and
  verified (MSI job 15860125): 200 root-subgroup commutativity
  relations, 2,980 cross-root commutations (index-disjoint, same-source
  AND same-target — the same-target instances feed the corrected
  transfer identity's `[V,Z] = 1` hypothesis), 1,432 Steinberg products
  over all 25 coefficient pairs, on a dictionary extended by 500
  exactly-verified two-letter entries — **4,612 distinct relators, all
  verified in `R̄`**, X-lengths 4–556; with the twelve reverse
  relators, `|T_St| = 4,624`; `72` escape the cartesian subgroup, as the
  length-nine wall demands.

  Two pieces of the completeness gap are now CLOSED in-repo, no JPAA
  needed:

  - **Context absorption.**  `x_ij(uρv) = [x_ik(u), [x_kl(ρ), x_lj(v)]]`
    shows that killing each defining ring relation `ρ` at a single root
    kills it in every monomial context — the relations absorb their own
    contexts, provided enough distinct indices keep every nested root
    legal.  This is precisely where the `n ≥ 4` threshold of
    [KrM, Theorem 3] comes from, matching the sharp `n = 3` failure of
    their Corollary 2; at `n = 5` there is room to spare.  The five
    context-free ring relations needed are exactly the Cuntz–Krieger
    relations, all present in the family.
  - **Length-two well-definedness, by construction.**  The (St3) block
    emits, for every root and every coefficient pair, the relation for
    ALL THREE intermediate indices against one canonical right-hand
    side, so the alternative chains are identified by emitted relations
    rather than assumed equal.

  **Step-4 acceptance PASSED (MSI job 15860399):** on `T_St` itself,
  screen (D) passes (72 of 4,612 escape the cartesian kernel) and the
  degree-10 screen passes (0 survivors of 2·1,814,400 pairs).
  Necessary, not sufficient — but a failure would have disproved the
  construction, and there was none.  Context absorption is now its own
  established claim (`atlas-steinberg-context-absorption`).

  **The remaining gap, now two-thirds closed (2026-08-15, night).**  The
  direct completeness derivation stands as: ring consistency CLOSED
  (bilinearity + `atlas-steinberg-context-absorption`); split
  independence REDUCED to spare independence; spare independence given
  by the proved transfer identity
  (`atlas-steinberg-transfer-identity`, machine-cross-checked) MODULO
  its commutation hypotheses — which at length ≥ 3 were, *as of that
  afternoon pass*, exactly the then-open Lemma X
  (`atlas-steinberg-spare-index-independence`: length 2 proved, five
  rejected routes recorded, the one-sentence obstruction stated — ALL
  CLOSED the same night; the "obstruction" was an artifact of the
  identity's original over-strong hypotheses, see that node).  With
  Lemma X, `G₀ ≅ St₅(L)` and `T_St` is complete with no import beyond
  Kervaire–Steinberg centrality.  **Risk note:** enlarging `T_St` is
  always safe — any additional word verified in `R̄` keeps
  `⟨⟨T_St⟩⟩ ≤ R̄` and can only help reach `N̄` — so if Lemma X needs
  finitely many extra relators as axioms, the construction degrades
  gracefully rather than breaking.
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
