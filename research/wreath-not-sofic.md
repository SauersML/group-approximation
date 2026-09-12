---
rg: 2
id: wreath-not-sofic
kind: claim
title: The wreath candidate is not sofic
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Nonsoficity of the wreath candidate. **Now ESTABLISHED by source-verified
citation** via `wreath-not-sofic-proof`, after the candidate was given a
formula (below) and the two identification gaps recorded by the 2026-08-14
literature scout were discharged. The trust surface is one external
unrefereed preprint and nothing else; it is stated in the route.

## Available citation (2026-08-14 literature scout)

Kun--Thom, *Nonsofic wreath products of residually finite groups*,
arXiv:2608.06222v1 (2026-08-06, 16 pp), read from the PDF, prove:

> **Theorem A.** Let `Gamma` be an infranormal but not normal subgroup of `G`,
> and suppose that both `Gamma` and `G` have Kazhdan's property (T).  Then
> `(Z/2Z) wr_(G/Gamma) G` is not sofic.

with `Gamma` *infranormal* meaning that the compression semigroup
`P_Gamma={g in G : g Gamma g^(-1) <= Gamma}` generates `G`.  Their
Theorem E supplies an explicit pair: for a prime power `q` and `r,d>=3`,
`R_+=F_q[x_1,...,x_d]`, `R=F_q[x_1^(±1),...,x_d^(±1)]` with `SL_d(Z)` acting by
monomial substitutions, `Gamma=EL_r(R_+)` and `G=EL_r(R) semidirect SL_d(Z)`
are residually finite Kazhdan groups with `Gamma` infranormal and not normal.
Corollary D adds that the generalized Bernoulli action
`G action (K,kappa)^(G/Gamma)` is not sofic.

This is the same architecture as `notes/OBSTRUCTIONS.md` §4 (compressors from
`SL_d(Z)` monomial substitutions), and `notes/FALSE_HALO_ACTION_AUDIT.md`
already writes the candidate as `W=(directSum_(G/Gamma) C_2) semidirect G`
and calls it the Kun--Thom group.

Three independent reads now agree word for word on Theorem A, Theorem E and
Theorem 4.1: the scout's PDF read, a 2026-08-08 fetch recorded in
`notes/NOTEPAD.md`, and a 2026-08-14 fetch of the abstract page together with
`arxiv.org/html/2608.06222v1`. Full verbatim transcription, with provenance
and trust surface, is in the artifact.

## The wreath candidate, pinned

The scout's two gaps were both gaps of *identification*, and identification
was impossible because the graph had never given the candidate a formula: no
`research/*.md` file and no section of `notes/OBSTRUCTIONS.md` defines it. It
is fixed here, in the form the rest of the corpus already uses
(`notes/COMMUTING_WREATH_SOFIC_RADICAL.md`,
`notes/PERFECT_CORE_KUN_THOM_WREATH.md`,
`notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md`), which is Kun--Thom's Theorem E pair
verbatim. Let `q` be a prime power and `r, d ≥ 3`; put

    R₊ = 𝔽_q[x₁,…,x_d],   R = 𝔽_q[x₁^{±1},…,x_d^{±1}],

with `SL_d(ℤ)` acting on `R` by monomial substitutions, and set

    Γ = EL_r(R₊),    G = EL_r(R) ⋊ SL_d(ℤ).

The **wreath candidate** is

    W = (⊕_{G/Γ} ℤ/2ℤ) ⋊ G = (ℤ/2ℤ) ≀_{G/Γ} G,

the generalized (permutational) wreath product of `ℤ/2ℤ` over the coset space
`G/Γ`. The corpus's running instance is `q = 2`. The explicit compressor is
`t = u₁₂ ∈ SL_d(ℤ)`, i.e. the substitution `x₂ ↦ x₁x₂`, with
`tΓt⁻¹ = EL_r(𝔽_q[x₁, x₁x₂, x₃,…,x_d]) ⊊ Γ` of infinite index.

With that definition both gaps close by inspection rather than by argument:
the lamp is `ℤ/2ℤ`, and the pair is Theorem E's pair, so Theorem E supplies
infranormality, non-normality and (T) on both sides. The scout's caution about
`ℤ` lamps is correct and is preserved below as a scope boundary — it applies
to a *different* node, not to this one.

**Notation discipline.** Throughout this graph `G` is the *acting* group above
and `W` is the wreath product. `notes/OBSTRUCTIONS.md` §5 uses `G` in that
sense ("If `G` is flexibly HS-stable then the wreath candidate is not
hyperlinear"). `research/wreath-flexible-hs-stability.md` currently reuses the
letter `G` for the wreath itself; that node is owned elsewhere, but the two
readings are not interchangeable and the rigidity route needs the acting-group
reading.

## Variants that are NOT this group

Four neighbours in the corpus are close enough to be confused with `W` and are
**not** covered by the citation:

- the perfect index-two core `P₂ = I_X ⋊ G`, `I_X = ker(ε : ⊕_X 𝔽₂ → 𝔽₂)`,
  which is `[W,W]` (`notes/PERFECT_CORE_KUN_THOM_WREATH.md`);
- the Clifford central cover `H_Cl = C(X) ⋊ G` with anticommuting lamps, whose
  central quotient is `W`;
- the **split integral wreath candidate** `W_Y = ℤ^{(Y)} ⋊ Q` with
  `Q = G *_N G`, `N = ⟨⟨Γ⟩⟩_G`, `Y = Q/Γ` — a different lamp (`ℤ`, not `ℤ/2`)
  over a different index set (`Q/Γ`, not `G/Γ`). This is the group the scout's
  first gap is about, and nonsoficity for it does **not** follow from Theorem A:
  soficity does not pass to quotients in the needed direction, so the lamp
  surjection `ℤ ↠ ℤ/2` transports nothing;
- the free-lamp group `H_K = G *_Γ (Γ × K)`, an amalgam, not a wreath product.

## Why the claim is not a rewrite of the compression no-gos

Nonsoficity of `W` is *not* derived from the compression–centralizer criterion
formalized in this repository. That criterion
(`Criterion/CriterionAssembly.not_isSofic_of_not_isLEF`, which requires a
`CompressionSetup G Γ J`, property (T) at both `G` and `Γ`, and a non-LEF
commuting witness `J`) is instantiated only at elementary/GL/unit groups over
Leavitt algebras — its universal witness is `EL₄(L_{𝔽₂}(1,2))` =
`UniversalRankFour.Ambient`, and its general form is
`Leavitt/GeneralCornerTheorem.corner_not_isSofic` for `EL_{m+1}(R)`. No wreath
product, lamplighter, free-lamp amalgam or Kun--Thom candidate is proved
nonsofic anywhere under `GroupApproximation/`; the wreath material there
(`Sofic/MonomialModel.wreathPerm` and friends) is finite-model gadgetry plus
explicit no-gos about proof routes. The mechanism is the same family; the
theorem is not, and the substitution would have been exactly the kind of
group-mismatch the doctrine exists to prevent.
