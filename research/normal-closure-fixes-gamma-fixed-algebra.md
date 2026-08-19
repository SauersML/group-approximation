---
rg: 2
id: normal-closure-fixes-gamma-fixed-algebra
kind: claim
title: The normal closure of an infranormal Kazhdan subgroup fixes its fixed algebra pointwise
distinct_from:
  kt-centralizer-normalization-hs: that asks for the Hilbert--Schmidt/tracial analogue of Kun--Thom centralizer normalization, which is open; this stays entirely on the permutation side, where Theorem 4.1 is available, and extracts a reusable consequence — pointwise triviality of the normal closure's action on the Γ-fixed algebra — that the paper does not state and the two-point refutation needs.
  finite-infranormal-subgroup-is-normal: that is an elementary normalizer lemma for FINITE infranormal subgroups, forcing genuine normality in the group itself; this is about infinite Kazhdan Γ inside a sofic ultraproduct, where Γ is not normal and what becomes rigid is not Γ but the action of its normal closure on the fixed algebra.
  finite-quotient-blindness: that is the finite-quotient collapse (the image of Γ is normal); this is its sofic-ultraproduct sibling, where no quotient exists and normality is replaced by invariance of the fixed algebra.
  exact-models-cannot-separate-marked-pair: that fights an ε-deleted set at a fixed window with expansion; this is the window-free ultraproduct statement that makes the expansion unnecessary when the window quantifier is spent.
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Let `Γ` be infranormal in `G` with both `Γ` and `G` Kazhdan, and let
`σ : G → S_𝒰 = Π_{n→𝒰} Sym(A_n)` be a sofic representation.  Write `D_𝒰`
for the diagonal (ultraproduct of coordinates) abelian algebra and
`D_𝒰^{σ(Γ)}` for its `σ(Γ)`-fixed subalgebra.

**Theorem.**

1. `D_𝒰^{σ(Γ)}` is `σ(G)`-invariant.
2. Every `g` in the normal closure `⟨⟨Γ⟩⟩_G` acts **trivially** on
   `D_𝒰^{σ(Γ)}`: `σ(g)b = b` for all `b ∈ D_𝒰^{σ(Γ)}`.

For the Kun--Thom Theorem E pair, `⟨⟨Γ⟩⟩_G = EL_r(R)`: the whole
elementary part acts trivially on the `Γ`-fixed algebra of every sofic
representation, while elements with nontrivial `SL_d(ℤ)`-component are
exactly the ones the fixed algebra can see
(`compressor-coset-two-point-exact`).

The input is Kun--Thom Theorem 4.1 — `C_{S_𝒰}(σ(Γ))` is normalized by
`σ(G)` — imported from the verbatim in-repo artifact and corroborated by
two independent in-repo fetches (notes/NOTEPAD.md:1420, :21232).  Three
trust-surface facts, recorded per the LITERATURE_INPUT gate: the
unrefereed-preprint surface of 2608.06222 travels with this claim exactly
as with `kun-thom-nonsofic-wreath`; Theorem 4.1 does **not** require `Γ`
non-normal, so this claim imports strictly less than Theorem A consumes
(only 4.1 + Theorem E; Theorems A, B, C, Corollary D and the announced
results are not used); and the definitional hole flagged at landing is now **discharged** (source
pass 2026-08-15, late; transcriptions in the artifact): Definition 2.1
says a sofic representation is a homomorphism into `Π_𝒰 Sym(Y_n)` with
`tr(σ(g)) = 0` for all `g ≠ 1`, exactly what the tensor construction of
`two-point-data-yields-invariant-projection` produces on the nose, and
`D_𝒰^{σ(H)}` is defined exactly as used here.  The same pass surfaced
**Proposition 3.1**, which gives the fixed-algebra invariance (item 1)
*directly* for finitely generated infranormal `Γ` whenever the generator
graphs of `σ|_Γ` and `σ` are expander-decomposable — automatic for both
Kazhdan by the quoted ultrafilter form of Kun's theorem — so the doubling
bridge in the proof route is one of two valid derivations, not the only
one.
