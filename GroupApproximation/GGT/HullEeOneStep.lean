import GroupApproximation.GGT.HullLemmaEe
import GroupApproximation.GGT.OsinTheorem54SepSymmetric

/-!
# `EeOneStep`: moving a hyperbolically embedded subgroup into the base

`GGT/HullLemmaEe.lean` reduces Hull's Lemma `ee` to one geometric clause,
`EeOneStep`: if `E ↪_h (G, X ⊔ ℋ)` then the family `{H_λ}` stays hyperbolically
embedded when `E` is moved into the base.  This module builds the enlarged
relative generating set, **proves clause (a) outright**, and reduces clause (b)
to `EeLocalFiniteness`.

## Clause (a) is free, and the reason is the point of the construction

Hull disposes of it in five words --- *"clearly `Γ(G, (Y₀ ⊔ E(a)) ⊔ ℋ)` is
hyperbolic"* --- and the reason is that the two relative generating sets in play
have **the same alphabet**.  Write `D` for the given data and `D_E` for the one
witnessing `E ↪_h`.  Then

    D_E's alphabet  =  X ∪ ⋃H_λ  ∪  E        (base `X ∪ ⋃H_λ`, family `E`)
    the enlarged    =  (X ∪ E) ∪ ⋃H_λ        (base `X ∪ E`, family `{H_λ}`)

and those two sets are equal, by `Set.union_right_comm` and nothing else.  The
family moved from one side of the union to the other, so the Cayley graph did not
change at all --- only the bookkeeping of which letters count as peripheral.
`alphabet_eq_relGenSetAddSubgroup` records the equality at the level of
`Alphabet`, which is where it is usable: hyperbolicity is a statement about the
type `Cayley A` together with the metric instance `A` determines, so equal
alphabets are needed, not merely equal carriers.  `Alphabet` has one data field
and one `Prop` field, so `alphabet_eq_of_carrier_eq` upgrades the one to the
other.

This is the same phenomenon as `OsinTheorem54SepZTrick.base_union_fam_union_relBall`,
where the added elements already lay inside the family so the carrier was
literally unchanged.  Here the carrier does grow --- `E` is not inside `⋃H_λ` ---
but it grows the *same way* on both sides, which is all clause (a) needs.

## What is left, and what discharging it takes

`EeLocalFiniteness` is clause (b): each `(H_λ, d̂_λ)` is still locally finite
after the enlargement.  That is the whole of Hull's argument and none of it is
here.  Discharging it takes, in order:

1. a shortest admissible word for `h ∈ H_λ` in the enlarged alphabet, closed into
   a cycle by the `H_λ`-edge back;
2. that cycle read in `D_E`, where the `E`-letters are the *components* and the
   peripheral letters have become base letters --- a translation between
   `List (RelLetter G Λ)` and `List (RelLetter G Unit)` that swaps which letters
   are peripheral;
3. each `E`-letter isolated in the cycle, since `e` is not an `E`-component and
   minimality forbids a second one connected to it;
4. `OsinComponents.exists_isolatedComponentBound_nGon`, giving
   `label ∈ D_E.relBall () R` --- and, per the docstring of `HullLemmaEe`, the
   **non-uniform** radius suffices, because only finiteness of the resulting set
   is ever read;
5. local finiteness of `D_E` making that set finite --- this is `F_n`;
6. `GGT.DGOCorollary427` at `X` versus `X ∪ F_n`, a finite symmetric difference,
   giving local finiteness of the `F_n`-enlargement;
7. and the observation that the two balls agree, every letter of a shortest word
   lying in `X ∪ F_n ∪ ℋ`.

Step 6 is where `DGOCorollary427` enters the development, and it is the only
place: `HullLemmaEe` deliberately does not name it, and neither does this module.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Enlarge

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  Alphabets are determined by their carriers -/

/-- Hyperbolicity travels along an equality of alphabets.

That two alphabets with the same letters are the same alphabet --- the second
field being a `Prop` --- is already
`OsinComponents.alphabet_eq_of_carrier_eq`, which is why this module imports
`GGT/OsinTheorem54SepSymmetric.lean` rather than reproving it.  The import is
cheap and lands `GGT/OsinComponents.lean` in the closure, which is where the
isolated-component vocabulary that discharges `EeLocalFiniteness` lives.

The equality is needed at the level of `Alphabet` and not merely of carriers,
because hyperbolicity is a statement about `Cayley A` together with the metric
instance that `A` determines. -/
theorem hyperbolic_of_alphabet_eq {A₁ A₂ : Alphabet G} (h : A₁ = A₂)
    (hh : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley A₂)) :
    ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley A₁) := by
  subst h
  exact hh

/-! ## 2.  The enlarged relative generating set -/

/-- **Moving a set out of the family side of the union and into the base leaves
the union alone.**  This is `Set.union_right_comm`, named because it is the whole
of clause (a). -/
theorem base_union_union_fam (D : RelGenSet G Λ) (S : Set G) :
    (D.base ∪ S) ∪ ⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)
      = D.alphabet.carrier ∪ S :=
  Set.union_right_comm _ _ _

/-- **A symmetric generating set stays one when a subgroup is adjoined.**
Inversion is closed on each side separately, and enlarging a generating set
cannot shrink what it generates. -/
theorem isSymmetricGeneratingSet_union_subgroup {S : Set G}
    (hS : IsSymmetricGeneratingSet S) (E : Subgroup G) :
    IsSymmetricGeneratingSet (S ∪ (E : Set G)) where
  inv_mem := by
    rintro x (hx | hx)
    · exact Or.inl (hS.inv_mem x hx)
    · exact Or.inr (SetLike.mem_coe.mpr (E.inv_mem (SetLike.mem_coe.mp hx)))
  closure_eq := by
    refine eq_top_iff.mpr ?_
    rw [← hS.closure_eq]
    exact Subgroup.closure_mono Set.subset_union_left

/-- **The base enlarged by a subgroup**, the family untouched.  This is the `Y`
of Hull's Lemma `ee` at one element, with `E = E(a)`. -/
def relGenSetAddSubgroup (D : RelGenSet G Λ) (E : Subgroup G) : RelGenSet G Λ where
  base := D.base ∪ (E : Set G)
  fam := D.fam
  symmetricGenerating := by
    rw [base_union_union_fam D (E : Set G)]
    exact isSymmetricGeneratingSet_union_subgroup D.symmetricGenerating E

@[simp] theorem base_relGenSetAddSubgroup (D : RelGenSet G Λ) (E : Subgroup G) :
    (relGenSetAddSubgroup D E).base = D.base ∪ (E : Set G) := rfl

@[simp] theorem fam_relGenSetAddSubgroup (D : RelGenSet G Λ) (E : Subgroup G) :
    (relGenSetAddSubgroup D E).fam = D.fam := rfl

/-- **The enlarged alphabet is the old one with `E` thrown in.** -/
theorem alphabet_carrier_relGenSetAddSubgroup (D : RelGenSet G Λ)
    (E : Subgroup G) :
    (relGenSetAddSubgroup D E).alphabet.carrier
      = D.alphabet.carrier ∪ (E : Set G) :=
  base_union_union_fam D (E : Set G)

/-! ## 3.  The witnessing single-subgroup data has the same alphabet -/

/-- **A one-element family contributes just its subgroup.**  The union over
`Unit` is the single term. -/
theorem alphabet_carrier_unit (DE : RelGenSet G Unit) :
    DE.alphabet.carrier = DE.base ∪ ((DE.fam () : Subgroup G) : Set G) := by
  have hU : (⋃ lam : Unit, ((DE.fam lam : Subgroup G) : Set G))
      = ((DE.fam () : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨lam, hlam⟩
      cases lam
      exact hlam
    · intro hx
      exact ⟨(), hx⟩
  show DE.base ∪ (⋃ lam : Unit, ((DE.fam lam : Subgroup G) : Set G))
      = DE.base ∪ ((DE.fam () : Subgroup G) : Set G)
  rw [hU]

/-- **The two relative generating sets are two readings of one Cayley graph.**

`D_E` has base `X ∪ ⋃H_λ` and family `E`; the enlargement has base `X ∪ E` and
family `{H_λ}`.  The alphabets coincide, so every metric statement about one is a
metric statement about the other --- which is exactly why clause (a) of Lemma
`ee` costs nothing. -/
theorem alphabet_eq_relGenSetAddSubgroup {D : RelGenSet G Λ} {E : Subgroup G}
    {DE : RelGenSet G Unit} (hbase : DE.base = D.alphabet.carrier)
    (hfam : DE.fam = fun _ => E) :
    (relGenSetAddSubgroup D E).alphabet = DE.alphabet := by
  refine OsinComponents.alphabet_eq_of_carrier_eq ?_
  rw [alphabet_carrier_relGenSetAddSubgroup, alphabet_carrier_unit, hbase, hfam]

end Enlarge

/-! ## 4.  Clause (b), isolated -/

/-- **Local finiteness of the family after the enlargement.**

The whole content of Hull's proof of Lemma `ee`, and the only clause of
`EeOneStep` not proved below.  The module header lists what discharging it takes;
the short version is the isolated-component estimate, the finite set `F_n` it
produces, and `GGT.DGOCorollary427` at a finite symmetric difference.

The hypothesis is `IsHypEmbeddedOf G D.alphabet.carrier E` rather than a bare
subgroup, because both halves of the argument read it: local finiteness of `E`'s
own relative metric is what makes `F_n` finite, and hyperbolicity of the shared
alphabet is what the polygon estimate runs in. -/
def EeLocalFiniteness : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
      ∀ E : Subgroup G, IsHypEmbeddedOf G D.alphabet.carrier E →
        ∀ (lam : Λ) (n : ℕ),
          ((relGenSetAddSubgroup D E).relBall lam n).Finite

/-- **`EeOneStep` from clause (b) alone.**

Clause (a) is discharged here, by the alphabet coincidence; clause (b) is the
hypothesis.  So the geometric debt of Hull's Lemma `ee` is exactly
`EeLocalFiniteness`, and the chain from there to the lemma is complete:
`eeOneStep_of_localFiniteness` feeds `HullLemmaEe.hullLemmaEe_of_inputs`. -/
theorem eeOneStep_of_localFiniteness (h : EeLocalFiniteness.{u, w}) :
    EeOneStep.{u, w} := by
  intro G _instG Λ D hD E hE
  refine ⟨relGenSetAddSubgroup D E, rfl, rfl, ⟨?_, ?_⟩⟩
  · obtain ⟨DE, hbase, hfam, hDE⟩ := hE
    exact hyperbolic_of_alphabet_eq
      (alphabet_eq_relGenSetAddSubgroup hbase hfam) hDE.hyperbolic
  · intro lam n
    exact h G Λ D hD E hE lam n

end GGT
end GroupApproximation
