---
rg: 2
id: atlas-relator-central-sufficiency
kind: claim
title: Usable atlas relator lists are exactly the central extensions of Q
distinct_from:
  leavitt-steinberg-hs-unstable: that is the branch selection the criterion feeds; this is a structural theorem about which finite relator lists make the criterion well-posed, and it moves the extraction target from N̄ to any central extension.
  leavitt-steinberg-hs-stability-fork: that is the dichotomy consuming the criterion; this repairs the criterion's input specification one level down.
artifacts:
  - research/artifacts/atlas-relator-extraction-2026-08-15.md
---

Let `P̄ = A₈ * A₈ ↠ Q = L_{F₂}(1,2)^×` be the canonical atlas source of
`notes/EXPLICIT_LEAVITT_ATLAS.md` §9, `R̄ = ker`, `N̄ = [P̄, R̄]`.

**Theorem.**  For a finite `T ⊆ P̄`, the canonical regular-`A₈` criterion
(§9, (25)–(26)) holds verbatim with the normal generating set `S̄` of `N̄`
replaced by `T` **iff**

```text
N̄ ≤ ⟨⟨T⟩⟩_P̄ ≤ R̄,
```

equivalently: `T ⊆ R̄` and `P̄/⟨⟨T⟩⟩` is a **central extension of `Q`**.
Three consequences that change the extraction problem:

1. **`T` need not lie in `N̄`, and the largest legal target is a relative
   presentation of `Q` itself.**  The necessity direction of §9 kills `R̄`
   exactly and only ever uses `T ⊆ R̄`; the sufficiency direction needs
   only that `P̄/⟨⟨T⟩⟩` is perfect and central over the simple `Q` — the
   identification with `U_Q` is never used.
2. **Derived-list lemma: no search separates a presentation from an
   `N̄`-list.**  If `X` generates `P̄` and `R̄ = ⟨⟨r_1,…,r_s⟩⟩`, then
   `N̄ = ⟨⟨[x, r_i] : x ∈ X⟩⟩`, of size `≤ |X|·s`: in `P̄/⟨⟨[x,r_i]⟩⟩`
   each `r̄_i` is centralized by the generating set, hence central, so
   `R̄`'s image is central and `[P̄, R̄]` dies.
3. **The Steinberg route becomes unconditional on `K₂`-side inputs.**  A
   finite relator set `T_St` with `P̄/⟨⟨T_St⟩⟩ ≅ St₅(L)` compatibly over
   `Q` is usable because `R̄/⟨⟨T_St⟩⟩ ≅ K₂(5, L)` is **central** in
   `St₅(L)` (Kervaire–Steinberg centrality at `n ≥ 5`; recorded
   literature premise, `notes/NOTEPAD.md:21650-21652`) — never needing
   `K₂(5,L) = 0`, its finite generation, or `U_Q ≅ St₅(L)`.

The asymmetry worth exploiting: the **nonhyperlinearity** attack (lower
bound on window energy) uses only necessity, so every finite kernel window
already enumerated is legitimate for it; only the **hyperlinearity**
construction is blocked on the usable list.
