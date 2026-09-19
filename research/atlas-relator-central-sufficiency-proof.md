---
rg: 2
id: atlas-relator-central-sufficiency-proof
kind: route
title: Read both directions of the criterion for what they use, then centralize a presentation
target: atlas-relator-central-sufficiency
requires: []
---

# Read both directions of the criterion for what they use, then centralize a presentation

**Necessity (1 ⟹ 2 of §9) uses only `T ⊆ R̄`.**  The pulled-back
hyperlinear model of `Q` kills `R̄` exactly; finite-group HS-stability
corrects the two factor restrictions to exact representations of the
canonical form (25), changing every fixed word by `o(1)`
(`notes/EXPLICIT_LEAVITT_ATLAS.md:534-570`, which itself concludes "since
the original pulled-back models kill `R̄`, they kill (24)
asymptotically").  Nothing distinguishes elements of `N̄` from other
elements of `R̄` anywhere in the direction.

**Sufficiency (2 ⟹ 1 of §9) uses only centrality over `Q`.**  Condition
(26) makes the exact representations (25) an asymptotic homomorphism
killing `⟨⟨T⟩⟩`, so it factors through `V := P̄/⟨⟨T⟩⟩` and gives
`Ψ : V → Π_ω U(20160 k_n)`.  The remainder of §9's proof
(`:592-607`) evaluates `Ψ` on a commutator of the first factor to get a
nontrivial hyperlinear image of a group that is perfect (a quotient of
`A₈ * A₈`) and central over `Q` — exactly the hypotheses of the
one-witness certificate; the identification `V ≅ U_Q` is decoration
(`notes/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md:566-568` records the same
remark for its own Theorem 4).  Centrality of `R̄/⟨⟨T⟩⟩` in `V` is
precisely the hypothesis `N̄ ≤ ⟨⟨T⟩⟩`; conversely if `N̄ ≤ ⟨⟨T⟩⟩ ≤ R̄`
then `V` is a perfect central extension of `Q`.  The two directions
together give the stated iff.

**Derived-list lemma.**  `⟨⟨[x, r_i]⟩⟩ ≤ N̄` is clear.  Conversely in
`M := P̄/⟨⟨[x,r_i] : x ∈ X, i⟩⟩` every `r̄_i` commutes with the image of
the generating set `X`, hence is central; a central element's normal
closure is the cyclic subgroup it generates, so the image of `R̄` — the
normal closure of the `r̄_i` — is the central subgroup `⟨r̄_1,…,r̄_s⟩`,
and `[P̄, R̄]` maps to `1`.  Hence `N̄ ≤ ⟨⟨[x,r_i]⟩⟩`.

**The Steinberg specialization.**  If `P̄/⟨⟨T_St⟩⟩ ≅ St₅(L)` over `Q`,
then `R̄/⟨⟨T_St⟩⟩` is the kernel of `St₅(L) ↠ E₅(L) ≅ Q`, which is
`K₂(5, L)`, central for `n ≥ 5` by Kervaire–Steinberg (recorded
literature premise, tagged: `notes/NOTEPAD.md:21650-21652`).  So
`N̄ ≤ ⟨⟨T_St⟩⟩` holds automatically and `T_St` is usable.  Derivation and
screens: `research/artifacts/atlas-relator-extraction-2026-08-15.md` §(a).
