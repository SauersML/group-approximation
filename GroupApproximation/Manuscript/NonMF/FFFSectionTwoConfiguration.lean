import GroupApproximation.Manuscript.NonMF.SimpleInDefect
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Fournier-Facio, Section 2: the configuration, corrected

`non_mf_groups_exist.tex`, `sec:torsion-free`, tex 1584-1600, cites
Fournier-Facio, *A torsion-free non-sofic group*, arXiv:2608.02025, §2 for a
group `G₀` carrying `Γ`, `t` and a simple `J` with three relations.  This module
proves the **group-theoretic content of that section** — everything in it that
is not a citation of Higman, Osin, Minasyan–Osin, Hull, Burger–Mozes or the
density model — unconditionally, and it corrects one step of the source along
the way.

Read from the PDF of `arXiv:2608.02025v2` (14 Aug 2026), §2, whose last
paragraph is:

> Let `Γ = π(P) ≤ G` and `tᵢ = π(uᵢ)`.  Being a quotient of `P`, `Γ` also has
> property (T), and it is infinite because it contains `π(S) ≅ S`.  Moreover
> `G = ⟨Γ, t₁, t₂⟩` and `tᵢΓtᵢ⁻¹ ⊂ Γ`, because the analogous statements hold
> for `E = ⟨P, u₁, u₂⟩`.  Let `J = t₁π(S)t₁⁻¹`.  Since `[P₁, S] = 1`, we have
> `[Γ, J] = 1`.  Finally, we claim that `Γ ∩ J = {1}`: since `Γ` and `J`
> commute, an element in the intersection belongs to the centre of `J`, which
> is trivial because `J ≅ S` is simple.

Here `P₁ × P₂ × S ≤ P` is a direct product, `E` is the double HNN extension of
`P` with stable letters `u₁, u₂` where `uᵢ` conjugates `P` onto `Pᵢ`, and
`π : E ↠ G`.

## The two clauses that do not hold at the printed `Γ` and `J`

`S ≤ P` and `u₁Pu₁⁻¹ = P₁ ≤ P`, so `J = π(u₁Su₁⁻¹) ≤ π(P₁) ≤ π(P) = Γ`: the
printed `J` **is contained in** the printed `Γ`.  Both of the last two claims
fail for that pair, and not marginally:

* `Γ ∩ J = J`, which is nontrivial, so `Γ ∩ J = {1}` is false
  (`inf_ne_bot_of_conj_le`);
* `[Γ, J] = 1` together with `J ≤ Γ` says `J` is abelian, and `J ≅ S` is simple
  and infinite (`not_centralizes_of_le`).

`printedSectionTwo_refuted` is the two together, over §2's own hypotheses.  The
step quoted for the second one, *"since `[P₁, S] = 1`"*, gives `[P₁, S] = 1`,
whereas `[Γ, J] = [π(P), π(u₁Su₁⁻¹)] = 1` would need `[P, P₁] = 1`.

## The correction

Take `Γ = π(P₁P₂)` and `J = π(S)`.  Then every clause of §2 holds, and
`sectionTwoConfiguration` below is that statement: over an abstract group `G`
with subgroups `P₁, P₂, S ≤ P` such that `P₁` and `P₂` each centralize `S`, and
elements `t₁, t₂` with `tᵢPtᵢ⁻¹ ≤ Pᵢ`,

* `tᵢ(P₁ ⊔ P₂)tᵢ⁻¹ ≤ P₁ ⊔ P₂` — `conj_sup_mem`;
* `[P₁ ⊔ P₂, S] = 1` — `sup_centralizes`;
* `(P₁ ⊔ P₂) ⊓ S = ⊥` — `inf_eq_bot_of_centralizes_of_isSimpleGroup`;
* `Γ` is a homomorphic image of `P₁ × P₂ ≅ P × P`, so it keeps property (T) —
  `range_noncommCoprod_subtype`;
* `t₁St₁⁻¹ ≤ P₁ ⊔ P₂` — `conj_simpleFactor_mem_sup`;
* `⟨P₁ ⊔ P₂, t₁, t₂⟩ = G` whenever `⟨P, t₁, t₂⟩ = G` — `sup_closure_eq_top`.

The manuscript prints **one** `t` where §2 has two, and at one `t` the smaller
`Γ = tπ(P)t⁻¹ = π(P₁)` already works.  That is what this repository's
`TorsionFreePrinted.compressedCore` is, so the Lean already runs the corrected
configuration; what was missing is that this is a correction to §2 rather than
a repackaging of it.  With two stable letters `π(P₁)` is not enough, because
`t₂π(P₁)t₂⁻¹ ≤ π(P₂)`, and the join is.

## The clause the manuscript does not print, and does not have to assume

§2 needs `Γ ∩ J = {1}` because that is a hypothesis of the criterion it feeds.
`non_mf_groups_exist.tex` does not print that clause and does not use it:
`thm:torsion-free` runs through the manuscript's own compression criterion.
`PrintedFournierFacioData` accordingly has no such field — and needs none,
because `PrintedData.core_inf_simpleFactor` **derives** it from the fields it
does have.  So the printed paragraph, weaker than §2 in appearance, still
yields §2's own conclusion.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace FFFSectionTwo

universe u

/-! ## The centre of a simple nonabelian group -/

/-- **The centre of a simple nonabelian group is trivial.**

§2: *"an element in the intersection belongs to the centre of `J`, which is
trivial because `J ≅ S` is simple"*.  The centre is normal, so it is `⊥` or
`⊤`, and `⊤` says the group is abelian. -/
theorem center_eq_bot_of_isSimpleGroup {J : Type u} [Group J] [IsSimpleGroup J]
    (hnonab : ∃ x y : J, ¬ Commute x y) : Subgroup.center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J)
    inferInstance with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hnonab
    refine absurd ?_ hxy
    have hx : x ∈ Subgroup.center J := h ▸ Subgroup.mem_top x
    have hcomm : y * x = x * y := Subgroup.mem_center_iff.mp hx y
    exact (commute_iff_eq x y).mpr hcomm.symm

/-! ## `Γ ∩ J = {1}` -/

/-- **A subgroup that centralizes a simple nonabelian subgroup meets it
trivially.**

§2's last sentence, verbatim: *"since `Γ` and `J` commute, an element in the
intersection belongs to the centre of `J`, which is trivial because `J ≅ S` is
simple"*.

The hypothesis is exactly `PrintedFournierFacioData.simpleFactor_centralizes`
together with `simple` and `nonabelian`, so the printed paragraph of
`non_mf_groups_exist.tex` gives this clause without assuming it. -/
theorem inf_eq_bot_of_centralizes_of_isSimpleGroup {G : Type u} [Group G]
    (core simpleFactor : Subgroup G)
    (hcent : ∀ c ∈ simpleFactor, ∀ γ ∈ core, Commute c γ)
    (hsimple : IsSimpleGroup ↥simpleFactor)
    (hnonab : ∃ x y : ↥simpleFactor, ¬ Commute x y) :
    core ⊓ simpleFactor = ⊥ := by
  haveI : IsSimpleGroup ↥simpleFactor := hsimple
  have hcenter : Subgroup.center ↥simpleFactor = ⊥ :=
    center_eq_bot_of_isSimpleGroup hnonab
  refine le_bot_iff.mp ?_
  intro x hx
  obtain ⟨hxcore, hxJ⟩ := Subgroup.mem_inf.mp hx
  -- `x` lies in the centre of `J`, because every `c ∈ J` commutes with `x ∈ Γ`.
  have hxmem : (⟨x, hxJ⟩ : ↥simpleFactor) ∈ Subgroup.center ↥simpleFactor := by
    refine Subgroup.mem_center_iff.mpr ?_
    intro c
    refine Subtype.ext ?_
    have hc : (c : G) * x = x * (c : G) := (hcent (c : G) c.2 x hxcore).eq
    simpa using hc
  rw [hcenter, Subgroup.mem_bot] at hxmem
  have hx1 : x = 1 := by
    have hval := congrArg Subtype.val hxmem
    simpa using hval
  exact Subgroup.mem_bot.mpr hx1

/-- **The same, in the exact shape the corner criterion asks for.**

`Endpoint.ManuscriptStatements.theoremD_subgroups` — this repository's form of
the criterion Fournier-Facio's §2 quotes as Proposition 1.2 — takes both
`hcent : ∀ x ∈ conjSubgroup q₀ Γ, ∀ y ∈ J, x * y = y * x` and
`hdisj : conjSubgroup q₀ Γ ⊓ J = ⊥`.  The second is redundant whenever `J` is
simple and nonabelian, which is the only case either §2 or `[Ope26]` uses it
in: `J` is Thompson's `V` there and a Burger–Mozes or Hyde–Lodha group here.
This lemma is stated with `x * y = y * x` rather than `Commute` so that it
matches `hcent` verbatim. -/
theorem inf_eq_bot_of_mul_comm_of_isSimpleGroup {G : Type u} [Group G]
    (core simpleFactor : Subgroup G)
    (hcent : ∀ x ∈ core, ∀ y ∈ simpleFactor, x * y = y * x)
    (hsimple : IsSimpleGroup ↥simpleFactor)
    (hnonab : ∃ x y : ↥simpleFactor, ¬ Commute x y) :
    core ⊓ simpleFactor = ⊥ :=
  inf_eq_bot_of_centralizes_of_isSimpleGroup core simpleFactor
    (fun c hc γ hγ => (commute_iff_eq c γ).mpr (hcent γ hγ c hc).symm)
    hsimple hnonab

/-! ## The correction, over an abstract direct product -/

section Configuration

variable {G : Type u} [Group G]

/-- `t` compresses `P₁ ⊔ P₂` into itself.

§2's `tᵢΓtᵢ⁻¹ ⊂ Γ`, at the corrected `Γ = π(P₁P₂)`.  Conjugation by `tᵢ` sends
all of `P` into `Pᵢ`, and `P₁ ⊔ P₂ ≤ P`. -/
theorem conj_sup_mem (P P₁ P₂ : Subgroup G) (t : G)
    (hP₁ : P₁ ≤ P) (hP₂ : P₂ ≤ P)
    (hconj : ∀ p ∈ P, t * p * t⁻¹ ∈ P₁ ⊔ P₂) :
    ∀ γ ∈ P₁ ⊔ P₂, t * γ * t⁻¹ ∈ P₁ ⊔ P₂ := by
  intro γ hγ
  exact hconj γ ((sup_le hP₁ hP₂ : P₁ ⊔ P₂ ≤ P) hγ)

/-- `[P₁ ⊔ P₂, S] = 1` when `P₁` and `P₂` each centralize `S`.

This is §2's *"since `[P₁, S] = 1`"* used where it actually applies: the
centralizer of `S` is a subgroup, so it contains the join as soon as it
contains both factors. -/
theorem sup_centralizes (P₁ P₂ S : Subgroup G)
    (hcomm₁ : ∀ a ∈ P₁, ∀ s ∈ S, Commute a s)
    (hcomm₂ : ∀ a ∈ P₂, ∀ s ∈ S, Commute a s) :
    ∀ c ∈ S, ∀ γ ∈ P₁ ⊔ P₂, Commute c γ := by
  have hle : P₁ ⊔ P₂ ≤ Subgroup.centralizer (S : Set G) := by
    refine sup_le ?_ ?_
    · intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun s hs => ((hcomm₁ a ha s hs).eq).symm
    · intro a ha
      exact Subgroup.mem_centralizer_iff.mpr fun s hs => ((hcomm₂ a ha s hs).eq).symm
  intro c hc γ hγ
  exact (commute_iff_eq c γ).mpr (Subgroup.mem_centralizer_iff.mp (hle hγ) c hc)

/-- **`Γ = P₁ ⊔ P₂` is the range of one homomorphism out of `P₁ × P₂`.**

Inside the direct product `P₁ × P₂ × S ≤ P` the factors `P₁` and `P₂` commute,
so `(a, b) ↦ ab` is a homomorphism and its range is the join.

This is what the correction costs on the property-(T) side, and it costs
nothing: §2 gets property (T) for `Γ = π(P)` because `Γ` is a quotient of `P`,
and the corrected `Γ` is a quotient of `P₁ × P₂ ≅ P × P` by the same argument.
The equation below is the shape `HasKazhdanPropertyT.of_surjective` consumes,
the one `TorsionFreePrinted.hasKazhdanPropertyT_compressedCore` already uses at
a single stable letter. -/
theorem range_noncommCoprod_subtype (P₁ P₂ : Subgroup G)
    (hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, Commute a b) :
    (MonoidHom.noncommCoprod P₁.subtype P₂.subtype
      (fun a b => hcomm (a : G) a.2 (b : G) b.2)).range = P₁ ⊔ P₂ := by
  rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]

/-- `tSt⁻¹ ≤ P₁ ⊔ P₂`, from `S ≤ P` and `tPt⁻¹ ≤ P₁`. -/
theorem conj_simpleFactor_mem_sup (P P₁ P₂ S : Subgroup G) (t : G)
    (hS : S ≤ P) (hconj : ∀ p ∈ P, t * p * t⁻¹ ∈ P₁) :
    ∀ c ∈ S, t * c * t⁻¹ ∈ P₁ ⊔ P₂ :=
  fun c hc => Subgroup.mem_sup_left (hconj c (hS hc))

/-- `G = ⟨P₁ ⊔ P₂, t₁, t₂⟩` whenever `G = ⟨P, t₁, t₂⟩`.

§2's *"`G = ⟨Γ, t₁, t₂⟩` … because the analogous statements hold for
`E = ⟨P, u₁, u₂⟩`"*, at the corrected `Γ`.  Each `p ∈ P` is
`t₁⁻¹(t₁pt₁⁻¹)t₁` with `t₁pt₁⁻¹ ∈ P₁`, so `P` is inside the subgroup generated
by `P₁ ⊔ P₂` and the two letters. -/
theorem sup_closure_eq_top (P P₁ P₂ : Subgroup G) (t₁ t₂ : G)
    (hconj : ∀ p ∈ P, t₁ * p * t₁⁻¹ ∈ P₁)
    (hgen : P ⊔ Subgroup.closure ({t₁, t₂} : Set G) = ⊤) :
    (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) = ⊤ := by
  have hclos : Subgroup.closure ({t₁, t₂} : Set G) ≤
      (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) := le_sup_right
  have hP₁K : P₁ ≤ (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) :=
    le_trans (le_sup_left : P₁ ≤ P₁ ⊔ P₂) le_sup_left
  have ht₁ : t₁ ∈ (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) :=
    hclos (Subgroup.subset_closure (by simp))
  have hPK : P ≤ (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) := by
    intro p hp
    have hmem : t₁ * p * t₁⁻¹ ∈ (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) :=
      hP₁K (hconj p hp)
    have hprod : t₁⁻¹ * (t₁ * p * t₁⁻¹) * t₁ ∈
        (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) :=
      mul_mem (mul_mem (inv_mem ht₁) hmem) ht₁
    have hrw : t₁⁻¹ * (t₁ * p * t₁⁻¹) * t₁ = p := by group
    rwa [hrw] at hprod
  refine eq_top_iff.mpr ?_
  rw [← hgen]
  exact sup_le hPK hclos

/-- **The corrected configuration of §2, in one statement.**

Over any group `G` with `P₁, P₂, S ≤ P`, each of `P₁` and `P₂` centralizing `S`,
and `t₁, t₂` with `tᵢPtᵢ⁻¹ ≤ Pᵢ`, the join `Γ = P₁ ⊔ P₂` satisfies every clause
Section 2 asks of it, including the two that fail at the printed `Γ = P`. -/
theorem sectionTwoConfiguration (P P₁ P₂ S : Subgroup G) (t₁ t₂ : G)
    (hP₁ : P₁ ≤ P) (hP₂ : P₂ ≤ P) (hS : S ≤ P)
    (hconj₁ : ∀ p ∈ P, t₁ * p * t₁⁻¹ ∈ P₁)
    (hconj₂ : ∀ p ∈ P, t₂ * p * t₂⁻¹ ∈ P₂)
    (hcomm₁ : ∀ a ∈ P₁, ∀ s ∈ S, Commute a s)
    (hcomm₂ : ∀ a ∈ P₂, ∀ s ∈ S, Commute a s)
    (hsimple : IsSimpleGroup ↥S) (hnonab : ∃ x y : ↥S, ¬ Commute x y)
    (hgen : P ⊔ Subgroup.closure ({t₁, t₂} : Set G) = ⊤) :
    (∀ γ ∈ P₁ ⊔ P₂, t₁ * γ * t₁⁻¹ ∈ P₁ ⊔ P₂) ∧
      (∀ γ ∈ P₁ ⊔ P₂, t₂ * γ * t₂⁻¹ ∈ P₁ ⊔ P₂) ∧
        (∀ c ∈ S, ∀ γ ∈ P₁ ⊔ P₂, Commute c γ) ∧
          (P₁ ⊔ P₂) ⊓ S = ⊥ ∧
            (∀ c ∈ S, t₁ * c * t₁⁻¹ ∈ P₁ ⊔ P₂) ∧
              (P₁ ⊔ P₂) ⊔ Subgroup.closure ({t₁, t₂} : Set G) = ⊤ := by
  have hcent : ∀ c ∈ S, ∀ γ ∈ P₁ ⊔ P₂, Commute c γ :=
    sup_centralizes P₁ P₂ S hcomm₁ hcomm₂
  refine ⟨conj_sup_mem P P₁ P₂ t₁ hP₁ hP₂
      (fun p hp => Subgroup.mem_sup_left (hconj₁ p hp)),
    conj_sup_mem P P₁ P₂ t₂ hP₁ hP₂
      (fun p hp => Subgroup.mem_sup_right (hconj₂ p hp)),
    hcent,
    inf_eq_bot_of_centralizes_of_isSimpleGroup (P₁ ⊔ P₂) S hcent hsimple hnonab,
    conj_simpleFactor_mem_sup P P₁ P₂ S t₁ hS hconj₁,
    sup_closure_eq_top P P₁ P₂ t₁ t₂ hconj₁ hgen⟩

end Configuration

/-! ## The printed choice, refuted -/

section Refutation

variable {G : Type u} [Group G]

/-- `tSt⁻¹ ≤ P` when `S ≤ P` and `t` compresses `P` into itself. -/
theorem map_conj_le (P S : Subgroup G) (t : G) (hS : S ≤ P)
    (hconj : ∀ p ∈ P, t * p * t⁻¹ ∈ P) :
    S.map (MulAut.conj t).toMonoidHom ≤ P := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  simpa using hconj s (hS hs)

/-- Two elements of `G` that witness nonabelianness of a subgroup, from the
same statement inside the subgroup.  Everything downstream works in `G`. -/
theorem exists_mem_not_commute (S : Subgroup G)
    (hnonab : ∃ x y : ↥S, ¬ Commute x y) :
    ∃ a ∈ S, ∃ b ∈ S, ¬ Commute a b := by
  obtain ⟨x, y, hxy⟩ := hnonab
  refine ⟨(x : G), x.2, (y : G), y.2, fun h => hxy ?_⟩
  refine (commute_iff_eq x y).mpr (Subtype.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.eq

/-- Conjugation is an automorphism, so it does not create commuting pairs. -/
theorem not_commute_conj {a b : G} (t : G) (hab : ¬ Commute a b) :
    ¬ Commute (t * a * t⁻¹) (t * b * t⁻¹) := by
  intro h
  refine hab ((commute_iff_eq a b).mpr ?_)
  have h2 : t * (a * b) * t⁻¹ = t * (b * a) * t⁻¹ := by
    calc t * (a * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹) := by group
      _ = t * b * t⁻¹ * (t * a * t⁻¹) := h.eq
      _ = t * (b * a) * t⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

/-- **`Γ ∩ J = {1}` is false at §2's printed `Γ = π(P)` and `J = t₁π(S)t₁⁻¹`.**

`S ≤ P` and `tPt⁻¹ ≤ P` force `tSt⁻¹ ≤ P`, so the intersection is all of
`tSt⁻¹`, which is nontrivial as soon as `S` is. -/
theorem inf_ne_bot_of_conj_le (P S : Subgroup G) (t : G) (hS : S ≤ P)
    (hconj : ∀ p ∈ P, t * p * t⁻¹ ∈ P) (hne : S ≠ ⊥) :
    P ⊓ S.map (MulAut.conj t).toMonoidHom ≠ ⊥ := by
  obtain ⟨s, hs, hs1⟩ := (Subgroup.bot_or_exists_ne_one S).resolve_left hne
  have hmemJ : t * s * t⁻¹ ∈ S.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨s, hs, by simp⟩
  have hmemP : t * s * t⁻¹ ∈ P := map_conj_le P S t hS hconj hmemJ
  have hne1 : t * s * t⁻¹ ≠ 1 := by
    intro hz
    refine hs1 ?_
    have h2 : t * s * t⁻¹ = t * 1 * t⁻¹ := by rw [hz]; group
    exact mul_left_cancel (mul_right_cancel h2)
  intro hbot
  have hmem : t * s * t⁻¹ ∈ P ⊓ S.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_inf.mpr ⟨hmemP, hmemJ⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne1 hmem

/-- **`[Γ, J] = 1` is false when `J ≤ Γ` and `J` is nonabelian.**

A subgroup contained in `Γ` that is centralized by `Γ` is abelian, and §2's
`J ≅ S` is simple and infinite. -/
theorem not_centralizes_of_le (core simpleFactor : Subgroup G)
    (hle : simpleFactor ≤ core) {a b : G} (ha : a ∈ simpleFactor)
    (hb : b ∈ simpleFactor) (hab : ¬ Commute a b) :
    ¬ ∀ c ∈ simpleFactor, ∀ γ ∈ core, Commute c γ :=
  fun h => hab (h a ha b (hle hb))

/-- **The printed §2 pair, both clauses at once.**

Under §2's own hypotheses — `S ≤ P`, `tPt⁻¹ ≤ P`, `S` simple and nonabelian —
neither `Γ ∩ J = {1}` nor `[Γ, J] = 1` can hold for `Γ = P` and `J = tSt⁻¹`. -/
theorem printedSectionTwo_refuted (P S : Subgroup G) (t : G) (hS : S ≤ P)
    (hconj : ∀ p ∈ P, t * p * t⁻¹ ∈ P)
    (hnonab : ∃ x y : ↥S, ¬ Commute x y) :
    P ⊓ S.map (MulAut.conj t).toMonoidHom ≠ ⊥ ∧
      ¬ ∀ c ∈ S.map (MulAut.conj t).toMonoidHom, ∀ γ ∈ P, Commute c γ := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_not_commute S hnonab
  have hne : S ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at ha
    subst ha
    exact hab (Commute.one_left b)
  refine ⟨inf_ne_bot_of_conj_le P S t hS hconj hne, ?_⟩
  refine not_centralizes_of_le P (S.map (MulAut.conj t).toMonoidHom)
    (map_conj_le P S t hS hconj) (a := t * a * t⁻¹) (b := t * b * t⁻¹)
    (Subgroup.mem_map.mpr ⟨a, ha, by simp⟩)
    (Subgroup.mem_map.mpr ⟨b, hb, by simp⟩) (not_commute_conj t hab)

end Refutation

/-! ## The printed datum yields §2's own clause -/

namespace PrintedData

variable {E : Type u} [Group E]

/-- **`Γ ∩ J = {1}` for the printed Fournier-Facio datum.**

`non_mf_groups_exist.tex` 1584-1600 does not print this clause and does not use
it; Fournier-Facio's §2 does, because it is a hypothesis of the criterion §2
feeds.  It is not an extra assumption: the three fields
`simpleFactor_centralizes`, `simple` and `nonabelian` give it. -/
theorem core_inf_simpleFactor (F : PrintedFournierFacioData E) :
    F.core ⊓ F.simpleFactor = ⊥ :=
  inf_eq_bot_of_centralizes_of_isSimpleGroup F.core F.simpleFactor
    F.simpleFactor_centralizes F.simple F.nonabelian

/-- **`Γ ∩ S = S` for the manuscript's `S = tJt⁻¹`**, which is the shape that
makes §2's printed choice fail.

The printed `tJt⁻¹` lies **inside** `Γ` — that is
`PrintedFournierFacioData.conjFactor_le_core`, the manuscript's own
`S ≤ Γ` — so the intersection of `Γ` with it is all of it.  §2 takes its `J` to
be this conjugated subgroup and then asks for `Γ ∩ J = {1}`; the manuscript
keeps `J` unconjugated, which is why `core_inf_simpleFactor` above is available
to it and the source's claim is not. -/
theorem core_inf_conjFactor (F : PrintedFournierFacioData E) :
    F.core ⊓ F.conjFactor = F.conjFactor :=
  inf_eq_right.mpr F.conjFactor_le_core

end PrintedData

end FFFSectionTwo
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.center_eq_bot_of_isSimpleGroup

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.inf_eq_bot_of_centralizes_of_isSimpleGroup

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.sectionTwoConfiguration

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.printedSectionTwo_refuted

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.PrintedData.core_inf_simpleFactor

#audit_axioms GroupApproximation.Manuscript.NonMF.FFFSectionTwo.inf_eq_bot_of_mul_comm_of_isSimpleGroup
