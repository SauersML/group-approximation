import GroupApproximation.Manuscript.NonMF.GerasimovaOsinLemma44
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Slice

/-!
# Gerasimova–Osin, Lemma 4.5

Gerasimova–Osin (arXiv:1910.14524v3), §4:

> **Lemma 4.5.** The set `tF` freely generates a free subsemigroup of `G`.
>
> *Proof.* It suffices to show that if some words `w = t f₁ t f₂ … t fₙ` and
> `u = t g₁ t g₂ … t gₘ` in the alphabet `𝒜`, where `f₁, …, fₙ, g₁, …, gₘ ∈ F`, represent
> the same element in `G` then the words `w` and `u` are equal, i.e., `m = n` and we have
> `f₁ = g₁, …, fₙ = gₙ` (19).
>
> Let `p` and `q` be paths in `Γ(G, 𝒜)` starting at `1` and labelled by `w` and `u`,
> respectively, and let `p = a₁b₁ … aₙbₙ`, and `q = c₁d₁ … cₘdₘ` be their canonical
> decompositions.  By Lemma 4.4 we have `m = n` and `aᵢ` is connected to `cᵢ` for all
> `i ∈ {1, …, n}`.  Let `eᵢ, fᵢ` be edges of `Γ(G, 𝒜)` labelled by elements of `H` and
> connecting `(aᵢ)₋` to `(cᵢ)₋` and `(cᵢ)₊` to `(aᵢ)₊`, respectively.  Reading the label of
> the cycle `fᵢ bᵢ eᵢ₊₁ dᵢ⁻¹` and using (13), we obtain `Lab(fᵢ) ∈ FHF⁻¹ ∩ H = {1}` for all
> `1 ≤ i ≤ n` (for `i = n`, we read the label of the triangle `fₙ bₙ dₙ⁻¹`).  Thus, we have
> `(aᵢ)₊ = (cᵢ)₊` for all `1 ≤ i ≤ n`.  Similarly, `(aᵢ)₋ = (cᵢ)₋` for all `1 ≤ i ≤ n`.
> This obviously implies (19).

## Repository form

Both `p` and `q` are geodesic (Lemma 4.4, "in particular"), so each is the geodesic `q`
of Lemma 4.4 for the other, which gives `m = n`; then `|q| = 2n` pins the component
connected to `aᵢ` at position `2(i-1)` (`GOMatch.tight`), which is `cᵢ`.  (13) is
`GOCondition13`, the two-sided form of Lemma 4.2 carried by
`GerasimovaOsinLemma42Statement`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 4.1(a)).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

universe u

variable {G : Type u} [Group G] {D : RelGenSet G Unit} {F : Set G} {t : G} {C : ℕ}

/-- **Gerasimova–Osin (13)**, `FHF⁻¹ ∩ H = {1}`. -/
def GOCondition13 (D : RelGenSet G Unit) (F : Set G) : Prop :=
  ∀ f ∈ F, ∀ g ∈ F, ∀ h ∈ D.fam (), f * h * g⁻¹ ∈ D.fam () → f * h * g⁻¹ = 1

/-- **Lemma 4.5, on words**: `t f₁ ⋯ t fₙ` and `t g₁ ⋯ t gₘ` representing one element
have `m = n` and `fᵢ = gᵢ`. -/
theorem gerasimovaOsinLemma45_words (hS : GOSetting D F t C) (h13 : GOCondition13 D F)
    {fs gs : List G} (hfs : ∀ f ∈ fs, f ∈ F) (hgs : ∀ g ∈ gs, g ∈ F)
    (heq : RelLetter.listVal (altWord t fs) = RelLetter.listVal (altWord t gs)) : fs = gs := by
  have hu : IsGeodesicWord D 1 (RelLetter.listVal (altWord t fs)) (altWord t gs) := by
    rw [heq]
    exact isGeodesicWord_altWord hS hgs
  have hw : IsGeodesicWord D 1 (RelLetter.listVal (altWord t gs)) (altWord t fs) := by
    rw [← heq]
    exact isGeodesicWord_altWord hS hfs
  have hm := gerasimovaOsinLemma44 hS hfs hu
  have hm' := gerasimovaOsinLemma44 hS hgs hw
  have hlen : fs.length = gs.length := by
    have h1 := hm.1
    have h2 := hm'.1
    rw [length_altWord] at h1 h2
    omega
  have htight : (altWord t gs).length = 2 * fs.length := by
    rw [length_altWord, hlen]
  -- `aᵢ` is connected to `cᵢ`
  have hconn : ∀ i, i < fs.length →
      (vertex (1 : G) (altWord t fs) (2 * i))⁻¹ * vertex (1 : G) (altWord t gs) (2 * i)
        ∈ D.fam () :=
    fun i hi => (hm.tight htight hi).2
  have hend : vertex (1 : G) (altWord t fs) (2 * fs.length)
      = vertex (1 : G) (altWord t gs) (2 * fs.length) := by
    have e1 := vertex_length (1 : G) (altWord t fs)
    have e2 := vertex_length (1 : G) (altWord t gs)
    rw [length_altWord] at e1
    rw [length_altWord, ← hlen] at e2
    rw [e1, e2, heq]
  -- `Lab(fᵢ) ∈ FHF⁻¹ ∩ H = {1}`, so `(aᵢ)₊ = (cᵢ)₊`, hence `(aᵢ)₋ = (cᵢ)₋`
  have hplus : ∀ i, i < fs.length →
      vertex (1 : G) (altWord t fs) (2 * i) = vertex (1 : G) (altWord t gs) (2 * i) := by
    intro i hi
    have hig : i < gs.length := hlen ▸ hi
    have hnext : (vertex (1 : G) (altWord t fs) (2 * (i + 1)))⁻¹ *
        vertex (1 : G) (altWord t gs) (2 * (i + 1)) ∈ D.fam () := by
      rcases Nat.lt_or_ge (i + 1) fs.length with h1 | h1
      · exact hconn (i + 1) h1
      · have e : i + 1 = fs.length := by omega
        rw [e, hend, inv_mul_cancel]
        exact one_mem _
    rw [vertex_altWord_two_mul_succ (1 : G) t fs hi,
      vertex_altWord_two_mul_succ (1 : G) t gs hig] at hnext
    have hPQ : (vertex (1 : G) (altWord t fs) (2 * i) * t)⁻¹ *
        (vertex (1 : G) (altWord t gs) (2 * i) * t) ∈ D.fam () := by
      have e : (vertex (1 : G) (altWord t fs) (2 * i) * t)⁻¹ *
          (vertex (1 : G) (altWord t gs) (2 * i) * t)
          = t⁻¹ * ((vertex (1 : G) (altWord t fs) (2 * i))⁻¹ *
            vertex (1 : G) (altWord t gs) (2 * i)) * t := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hS.t_mem) (hconn i hi)) hS.t_mem
    have hform : (vertex (1 : G) (altWord t fs) (2 * i) * t)⁻¹ *
        (vertex (1 : G) (altWord t gs) (2 * i) * t)
        = fs[i] * ((vertex (1 : G) (altWord t fs) (2 * i) * t * fs[i])⁻¹ *
          (vertex (1 : G) (altWord t gs) (2 * i) * t * gs[i])) * (gs[i])⁻¹ := by group
    have h1 := h13 (fs[i]) (hfs _ (List.getElem_mem hi)) (gs[i]) (hgs _ (List.getElem_mem hig))
      _ hnext (by rw [← hform]; exact hPQ)
    rw [← hform] at h1
    exact mul_right_cancel (inv_mul_eq_one.mp h1)
  have hletter : ∀ (i : ℕ) (hi : i < fs.length) (hig : i < gs.length), fs[i] = gs[i] := by
    intro i hi hig
    have hnextEq : vertex (1 : G) (altWord t fs) (2 * (i + 1))
        = vertex (1 : G) (altWord t gs) (2 * (i + 1)) := by
      rcases Nat.lt_or_ge (i + 1) fs.length with h1 | h1
      · exact hplus (i + 1) h1
      · have e : i + 1 = fs.length := by omega
        rw [e]
        exact hend
    rw [vertex_altWord_two_mul_succ (1 : G) t fs hi,
      vertex_altWord_two_mul_succ (1 : G) t gs hig, hplus i hi] at hnextEq
    exact mul_left_cancel hnextEq
  exact List.ext_getElem hlen hletter

/-- **Gerasimova–Osin, Lemma 4.5.**  The set `tF` freely generates a free subsemigroup
of `G`. -/
theorem gerasimovaOsinLemma45 (hS : GOSetting D F t C) (h13 : GOCondition13 D F) :
    FreelyGeneratesFreeSubsemigroup ((fun x => t * x) '' F) := by
  intro w w' hw hw' _ _ hprod
  have hmap : ∀ l : List G, l = (l.map fun x => t⁻¹ * x).map fun f => t * f := by
    intro l
    simp [List.map_map, Function.comp_def]
  have hF : ∀ l : List G, (∀ x ∈ l, x ∈ (fun x => t * x) '' F) →
      ∀ f ∈ l.map (fun x => t⁻¹ * x), f ∈ F := by
    intro l hl f hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    obtain ⟨f', hf', rfl⟩ := hl x hx
    simpa using hf'
  have heq : RelLetter.listVal (altWord t (w.map fun x => t⁻¹ * x))
      = RelLetter.listVal (altWord t (w'.map fun x => t⁻¹ * x)) := by
    rw [listVal_altWord, listVal_altWord, ← hmap w, ← hmap w']
    exact hprod
  have hwords := gerasimovaOsinLemma45_words hS h13 (hF w hw) (hF w' hw') heq
  calc w = (w.map fun x => t⁻¹ * x).map fun f => t * f := hmap w
    _ = (w'.map fun x => t⁻¹ * x).map fun f => t * f := by rw [hwords]
    _ = w' := (hmap w').symm

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.GerasimovaOsinWords

#audit_axioms gerasimovaOsinLemma45_words
#audit_axioms gerasimovaOsinLemma45
