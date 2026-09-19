# The K₂ localization step for the SK open row: assessment (lane sk-k2-loc, 2026-09-19)

Census row `768ac9454e9b` (`simple_kazhdan_sofic_group.tex` l.733–735) is the one `open` SK row.
Every Lean route to it on main ends in one statement. Each of the following is logically equivalent
to the others (proved equivalences on main):

- stable `K₂(C_2(𝔽₂)) = 0`, i.e. `LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2`;
- `LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement` (`skCohnLimK2_iff_cohn`,
  `SKFix01.skFix01_degreeZeroSurj_iff_cohn`);
- `LVCohnGraded.skCohnGr_gradedGenStatement` (`Reduction.lean`);
- given two-generator Gersten, `LVPolyK2.skLoc_LocalizationStatement`, via
  `LVK2Route.freeBaseSurjective_iff_stableK2Trivial`. This last one feeds stable
  `K₂(L_{𝔽₂}(1,2)) = 0`.

## What the step is

`C = C_2(𝔽₂)` is the corner skew Laurent ring `C₀[t₊, t₋; φ]` with `t₊ = x₀`, `t₋ = y₀` and
`φ(a) = x₀ a y₀`. Here `C₁ = C₀ x₀`, since `a = (a y₀) x₀`, and `C₋₁ = y₀ C₀`. The degree-zero part
`C₀` is ultramatricial, and stable `K₂(C₀) = 0` is proved on main (`LVCohnColimit.skCohnLimK2_stableK2Trivial_degreeZero`). The
missing step is the degree-two piece of the skew Yao sequence,
`K₂(C₀) → K₂(C) → K₁(C₀)`, together with `K₁(C₀) = 0` over `𝔽₂`. These make `K₂(C₀) → K₂(C)`
stably onto. The same holds for `L = L₀[t₊, t₋; φ]`.

## Sources checked

- **Ara–Brustenga–Cortiñas**, Münster J. Math. 2 (2009), Thm 3.6, read on MSI in
  `lit-groups/abc-clean.txt` l.387–440.
  - The proof passes to the colimit `η⁻¹R`, where `φ` becomes an automorphism. That is
    `LVCohnColimit.CohnLimit`.
  - It then applies Yao's twisted fundamental theorem (ABC ref. [34], proof of its Thm 2.1) as a
    homotopy fibration of nonconnective K-theory spectra, using excision for H-unital rings
    (Suslin–Wodzicki).
  - The twisted nil terms `NK(R, φ^{±1})` are killed by the hypothesis of Thm 7.6 (`k` regular
    supercoherent).
  - None of these steps is a Steinberg-group argument.
- **Khanh**, arXiv:2609.08428, *General linear and Steinberg groups over `L_{𝔽₂}(1,2)`*.
  - It proves `GL_r(L)` acyclic (Thm 4.4) and `St_r(L) ≅ GL_r(L)` for `r ≥ 3` (Thm 5.4).
  - Stable vanishing itself is cited from ABC Thm 7.6, not re-proved.
  - Its compression swindle (`c(u) = e u e* + f f*`) moves *stable* vanishing to finite rank. It
    does not produce stable vanishing.
- The formal symmetries of `L` do not give stable vanishing either:
  - The doubling endomorphism `σ(a) = x₀ a y₀ + x₁ a y₁` acts as `2·id` on `K_{≥1}`, and each corner
    map `a ↦ xᵢ a yᵢ` acts as `id`.
  - These relations are consistent with any value of `K₁` or `K₂`. The vanishing needs the input
    `K(𝔽₂) → K(C)` from the Cohn–Leavitt localization sequence, i.e. the step above.

**Conclusion:** no elementary (Steinberg-word) proof of the step is known to me or appears in these
sources.

## What a full Lean proof needs

The cheapest faithful route is Yao at `K₂` for the honest skew Laurent ring
`B[t, t⁻¹; α]`, `B = CohnLimit`, which is locally matricial over `𝔽₂`. It needs three inputs.
1. A twisted Bass–Heller–Swan decomposition at `K₂`:
   `K₂(B[t,t⁻¹;α]) ≅ coker(1 − α_* on K₂B) ⊕ ker(1 − α_* on K₁B) ⊕ NK₂(B,α) ⊕ NK₂(B,α⁻¹)`.
2. `NK₂(B, α^{±1}) = 0` for `B` locally matricial over `𝔽₂`. This is Quillen/Waldhausen-type
   regularity for the twisted polynomial rings `B_i[t; α]` over finite semisimple `B_i`.
3. Corner-to-honest transfer, `C ↪ B[t,t⁻¹;α]`. The colimit half of this is on main.

Item 1 at `K₂` has no Steinberg-level proof in the literature I know, even untwisted over a
general ring. Item 2 is the twisted analogue of `K₂(R[t]) = K₂(R)` for regular `R`. Formalizing
items 1–2 is a large project, measured in weeks to months, and not a single-lane step.

## Cheapest honest alternative (for the census owner and the user; not applied)

The open clause of row `768ac9454e9b` is a citation, not a claim of the paper: "Infinite finitely
presented simple Kazhdan groups exist~\cite{CapraceRemy}". No theorem of the paper uses it. The
section has no theorem, and `thm:main` needs only `S` infinite and minimal. The rest of the row is
already formalized: a finitely presented LEF group is residually finite, and an infinite simple
group is not. Grading the existence clause `attribution` would be consistent with the census's 16
existing attribution rows, and SK would then have 0 open rows. This is the census owners' and the
user's call. The Lean route above stays available if a Lean proof of the cited fact is wanted.
