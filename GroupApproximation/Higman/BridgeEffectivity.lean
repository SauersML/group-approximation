import GroupApproximation.Higman.FinalReduction

/-!
# The effectivity clause of the bridge, repaired and reduced

`Higman.BridgeRecursive` (`Higman/BridgeTorsion.lean`) is the last clause of the
Higman--Neumann--Neumann bridge: that the three-generator overgroup `Ext g` of a
recursively presented countable group is recursively presented.  Its
construction (`Higman.HNNEmbedding`) and its torsion clause
(`Higman.BridgeTorsion`) are proved.

**The clause as stated is false, and this file says why and repairs it.**

## Why the stated form cannot be proved

`BridgeRecursive` quantifies over an *arbitrary* surjection `g : ℕ → A`, asking
only that `A` be recursively presented **in its own generating family `p.gen`**.
But `Ext g` is built out of `g`, and inside it every `g i` is an explicit word
in the three generators:

    g i  =  t · (x^{-i} y x^{i}) · t⁻¹ · (x^{-i} y x^{i})⁻¹ ,

which is `embA_eq_bridge` and `of_aFam_eq` below, and `bridgeFree i` as a word.
Substituting that word letter by letter turns a raw word `w` over `g` into a raw
word over `{x, y, t}`, and `evalRaw_eq_one_iff_bridgeSubst` proves the
substitution faithful: `evalRaw g w = 1` exactly when the substituted word dies
in `Ext g`.  The substitution is computable in `w`.  So a recursive presentation
of `Ext g` --- on *any* finite generating set, since finite generating sets are
interchangeable by a fixed finite table --- would make

    { w | evalRaw g w = 1 }

recursively enumerable, for **every** surjection `g`.  Take `A = ℤ` with its own
(decidable) presentation and let `g` enumerate `ℤ` with a non-recursively-
enumerable collision pattern: then `{(i,j) | g i = g j}` is not recursively
enumerable, so neither is that set, and `Ext g` is not recursively presented.

The counterexample itself is not formalized here --- it needs a non-r.e. subset
of `ℕ` transported into a surjection --- so this file claims no refutation
theorem.  What it proves is the reduction, which is the part that matters: the
hypothesis on `g` cannot be dropped.

## The repair

`BridgeEffective` asks of `g` exactly what the construction needs, and nothing
about surjectivity:

* `Subgroup.closure (Set.range g) = ⊤` --- *spanning* rather than surjectivity;
  it is all `closure_gens_eq_top_of_spans` uses, and it is what a recursive
  presentation supplies (`RecursivePresentation.spans`);
* `REPred (fun w => evalRaw g w = 1)` --- the word problem **in the family `g`
  itself**, which is what `RecursivePresentation.re` supplies.

`countableToFG_of_effective` then proves `Higman.CountableToFG` from it by
taking `g := p.gen`: no auxiliary surjection is chosen, so the mismatch that
makes the original statement false never arises.  `statement_of_four_effective`
is `Higman.statement_of_four` with the repaired input in place of the false one.

## What is left of it

`ExtWordProblemRE`: the word problem of `Ext g` on the three generators is
recursively enumerable when the word problem of `A` in `g` is.  Everything else
--- that the three generators generate, that the presentation map is onto, the
embedding, the torsion clause --- is proved here or in `BridgeTorsion`.  The
route to it is `Higman.RelatorRE.rePred_wordProblem_of_relators` (whose
docstring already names this clause as its intended third instance) together
with `Higman.exists_primrec_of_rePred`; its one nontrivial input is the
presentation of the HNN extension over the presented base, i.e. that the kernel
of `pi3` is the normal closure of the relators of `A` together with
`{ t a_i t⁻¹ (g_i a_i)⁻¹ }`.
-/

namespace GroupApproximation
namespace Higman
namespace BridgeEff

open GroupApproximation.Higman.HNNEmb

/-! ## 1.  The three generators, as a presentation map -/

/-- The three generators of the overgroup, indexed by `Fin 3`.  Noncomputable
because `HNNEmb.Ext` is an extension along the noncomputable `HNNEmb.psi`. -/
noncomputable def gen3 {A : Type} [Group A] (g : ℕ → A) : Fin 3 → Ext g := fun j =>
  if j = 0 then HNNExtension.of (xg : P A)
  else if j = 1 then HNNExtension.of (yg : P A)
  else (HNNExtension.t : Ext g)

@[simp] theorem gen3_zero {A : Type} [Group A] (g : ℕ → A) :
    gen3 g 0 = HNNExtension.of (xg : P A) := by
  unfold gen3
  simp

@[simp] theorem gen3_one {A : Type} [Group A] (g : ℕ → A) :
    gen3 g 1 = HNNExtension.of (yg : P A) := by
  unfold gen3
  simp

@[simp] theorem gen3_two {A : Type} [Group A] (g : ℕ → A) :
    gen3 g 2 = (HNNExtension.t : Ext g) := by
  unfold gen3
  simp

/-- **The presentation map on three generators.** -/
noncomputable def pi3 {A : Type} [Group A] (g : ℕ → A) : FreeGroup (Fin 3) →* Ext g :=
  FreeGroup.lift (gen3 g)

@[simp] theorem pi3_zero {A : Type} [Group A] (g : ℕ → A) :
    pi3 g (FreeGroup.of 0) = HNNExtension.of (xg : P A) := by
  unfold pi3
  rw [FreeGroup.lift_apply_of, gen3_zero]

@[simp] theorem pi3_one {A : Type} [Group A] (g : ℕ → A) :
    pi3 g (FreeGroup.of 1) = HNNExtension.of (yg : P A) := by
  unfold pi3
  rw [FreeGroup.lift_apply_of, gen3_one]

@[simp] theorem pi3_two {A : Type} [Group A] (g : ℕ → A) :
    pi3 g (FreeGroup.of 2) = (HNNExtension.t : Ext g) := by
  unfold pi3
  rw [FreeGroup.lift_apply_of, gen3_two]

/-! ## 2.  Spanning is enough to generate

`HNNEmb.closure_gens_eq_top` asks for a surjection because `HNNEmb.of_iA_mem`
does.  Only the *subgroup generated by* the range of `g` is ever used, so the
hypothesis weakens to spanning, by one closure induction. -/

/-- **Every element of the base is a word in the three generators**, when the
range of `g` generates. -/
theorem of_iA_mem_of_spans {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (α : A) :
    HNNExtension.of (iA α : P A) ∈ Subgroup.closure (gens g) := by
  have hmem : α ∈ Subgroup.closure (Set.range g) := by
    rw [hspan]
    exact Subgroup.mem_top α
  refine Subgroup.closure_induction
    (p := fun x _ => HNNExtension.of (iA x : P A) ∈ Subgroup.closure (gens g))
    ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨i, rfl⟩
    have hsplit : (iA (g i) : P A) = bFam g i * (aFam i)⁻¹ := by
      unfold bFam
      group
    rw [hsplit, map_mul, map_inv, ← conj_aFam g i]
    have ht : (HNNExtension.t : Ext g) ∈ Subgroup.closure (gens g) :=
      Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ (of_aFam_mem g i))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht (of_aFam_mem g i))
      (Subgroup.inv_mem _ ht)
  · rw [map_one, map_one]
    exact Subgroup.one_mem _
  · intro u v _ _ hu hv
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    rw [map_inv, map_inv]
    exact Subgroup.inv_mem _ hu

/-- **The three generators generate**, under spanning alone. -/
theorem closure_gens_eq_top_of_spans {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Subgroup.closure (gens g) = ⊤ := by
  refine top_le_iff.mp ?_
  intro z _hz
  clear _hz
  induction z using HNNExtension.induction_on with
  | of q =>
      have hmem : q ∈ Subgroup.closure ((Set.range (iA : A →* P A)) ∪
          (Set.range (iF : FreeGroup (Fin 2) →* P A))) := by
        rw [coprod_closure_top]
        exact Subgroup.mem_top q
      refine Subgroup.closure_induction
        (p := fun u _ => HNNExtension.of (u : P A) ∈ Subgroup.closure (gens g))
        ?_ ?_ ?_ ?_ hmem
      · rintro _ (⟨α, rfl⟩ | ⟨v, rfl⟩)
        · exact of_iA_mem_of_spans g hspan α
        · exact of_iF_mem g v
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro u v _ _ hu hv
        rw [map_mul]
        exact Subgroup.mul_mem _ hu hv
      · intro u _ hu
        rw [map_inv]
        exact Subgroup.inv_mem _ hu
  | t =>
      exact Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  | mul u v hu hv => exact Subgroup.mul_mem _ hu hv
  | inv u hu => exact Subgroup.inv_mem _ hu

/-- **The presentation map is onto.** -/
theorem pi3_surjective {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) : Function.Surjective (pi3 g) := by
  have hle : Subgroup.closure (gens g) ≤ (pi3 g).range := by
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : x = HNNExtension.of (xg : P A) ∨ x = HNNExtension.of (yg : P A)
        ∨ x = (HNNExtension.t : Ext g) := hx
    rcases hx' with rfl | rfl | rfl
    · exact ⟨FreeGroup.of 0, pi3_zero g⟩
    · exact ⟨FreeGroup.of 1, pi3_one g⟩
    · exact ⟨FreeGroup.of 2, pi3_two g⟩
  intro z
  have hz : z ∈ (pi3 g).range := by
    refine hle ?_
    rw [closure_gens_eq_top_of_spans g hspan]
    exact Subgroup.mem_top z
  exact hz

/-! ## 3.  The base sits in the overgroup by explicit words

This is the reduction that makes the stated form of `BridgeRecursive`
unprovable, and it is also what a proof of the repaired form would use: it says
the generating family `g` is *recovered* from the three generators, uniformly
and computably in the index. -/

/-- **The defining relation, solved for the group element.** -/
theorem embA_eq_bridge {A : Type} [Group A] (g : ℕ → A) (i : ℕ) :
    embA g (g i)
      = (HNNExtension.t : Ext g) * HNNExtension.of (aFam i : P A)
        * (HNNExtension.t : Ext g)⁻¹ * (HNNExtension.of (aFam i : P A))⁻¹ := by
  have hsplit : (iA (g i) : P A) = bFam g i * (aFam i)⁻¹ := by
    unfold bFam
    group
  show HNNExtension.of (iA (g i) : P A) = _
  rw [hsplit, map_mul, map_inv, ← conj_aFam g i]

/-- **The untwisted family, in the three generators.** -/
theorem of_aFam_eq {A : Type} [Group A] (g : ℕ → A) (i : ℕ) :
    (HNNExtension.of (aFam i : P A) : Ext g)
      = (HNNExtension.of (xg : P A) : Ext g) ^ (-(i : ℤ))
        * HNNExtension.of (yg : P A)
        * (HNNExtension.of (xg : P A) : Ext g) ^ (i : ℤ) := by
  show HNNExtension.of ((xg : P A) ^ (-(i : ℤ)) * yg * xg ^ (i : ℤ)) = _
  rw [map_mul, map_mul, map_zpow, map_zpow]

/-- The word in the three generators that spells the `i`-th member of the
generating family. -/
def bridgeFree (i : ℕ) : FreeGroup (Fin 3) :=
  FreeGroup.of 2
    * (FreeGroup.of 0 ^ (-(i : ℤ)) * FreeGroup.of 1 * FreeGroup.of 0 ^ (i : ℤ))
    * (FreeGroup.of 2)⁻¹
    * (FreeGroup.of 0 ^ (-(i : ℤ)) * FreeGroup.of 1 * FreeGroup.of 0 ^ (i : ℤ))⁻¹

/-- **The word spells the group element.** -/
theorem pi3_bridgeFree {A : Type} [Group A] (g : ℕ → A) (i : ℕ) :
    pi3 g (bridgeFree i) = embA g (g i) := by
  rw [embA_eq_bridge, of_aFam_eq]
  simp only [bridgeFree, map_mul, map_inv, map_zpow, pi3_zero, pi3_one, pi3_two]

/-- The substitution of the bridge words into a raw word over the generating
family.  It is computable in the word: `bridgeFree i` is an explicit word of
length `4i + 4`. -/
def bridgeSubst : RawWord → FreeGroup (Fin 3)
  | [] => 1
  | (i, s) :: w => (if s then bridgeFree i else (bridgeFree i)⁻¹) * bridgeSubst w

@[simp] theorem bridgeSubst_nil : bridgeSubst [] = 1 := rfl

@[simp] theorem bridgeSubst_cons (i : ℕ) (s : Bool) (w : RawWord) :
    bridgeSubst ((i, s) :: w)
      = (if s then bridgeFree i else (bridgeFree i)⁻¹) * bridgeSubst w := rfl

/-- **The substitution computes the value of the word in the base.** -/
theorem pi3_bridgeSubst {A : Type} [Group A] (g : ℕ → A) (w : RawWord) :
    pi3 g (bridgeSubst w) = embA g (evalRaw g w) := by
  induction w with
  | nil =>
      rw [bridgeSubst_nil, map_one, evalRaw_nil, map_one]
  | cons x w ih =>
      obtain ⟨i, s⟩ := x
      rw [bridgeSubst_cons, map_mul, ih, evalRaw_cons, map_mul]
      congr 1
      cases s
      · show pi3 g ((bridgeFree i)⁻¹) = embA g ((g i)⁻¹)
        rw [map_inv, map_inv, pi3_bridgeFree]
      · show pi3 g (bridgeFree i) = embA g (g i)
        exact pi3_bridgeFree g i

/-- **The word problem of the base reduces to the word problem of the
overgroup.**  This is the reduction the first section of the docstring uses: it
holds for *every* `g`, with no hypothesis, so the stated
`Higman.BridgeRecursive` --- which assumes nothing about the word problem of `g`
--- would make the left-hand side recursively enumerable for every surjection
`g`, which it is not. -/
theorem evalRaw_eq_one_iff_bridgeSubst {A : Type} [Group A] (g : ℕ → A)
    (w : RawWord) : evalRaw g w = 1 ↔ pi3 g (bridgeSubst w) = 1 := by
  rw [pi3_bridgeSubst]
  constructor
  · intro hw
    rw [hw, map_one]
  · intro hw
    refine embA_injective g ?_
    rw [hw, map_one]

/-! ## 4.  The repaired input, and what it still owes -/

/-- **The effectivity clause of the bridge, repaired.**  The overgroup of a
group whose word problem *in the family the overgroup is built from* is
recursively enumerable is again recursively presented.

Compare `Higman.BridgeRecursive`, which asks the same of an arbitrary surjection
`g` while assuming recursive enumerability only for a different family; §1 of
this file's docstring shows that form is false.

**Nothing inhabits this structure.** -/
structure BridgeEffective where
  /-- The overgroup is finitely generated and recursively presented. -/
  recursive : ∀ (A : Type) [Group A] (g : ℕ → A),
    Subgroup.closure (Set.range g) = ⊤ →
    REPred (fun w : RawWord => evalRaw g w = 1) →
    Nonempty (FGRecursive (HNNEmb.Ext g))

/-- **What is left of the repaired clause: one word problem.**  Everything else
in `BridgeEffective` --- generation, the presentation map, its surjectivity ---
is proved above, and `bridgeEffective_of_extWordProblem` puts them together.

**Nothing inhabits this structure.** -/
structure ExtWordProblemRE where
  /-- The word problem of the overgroup on the three generators. -/
  re : ∀ (A : Type) [Group A] (g : ℕ → A),
    REPred (fun w : RawWord => evalRaw g w = 1) →
    REPred (fun v : RawWord => pi3 g (rawToFree 2 v) = 1)

/-- The finitely generated recursive presentation of the overgroup, from the
word problem. -/
noncomputable def fgRecursiveExt {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤)
    (hre : REPred (fun v : RawWord => pi3 g (rawToFree 2 v) = 1)) :
    FGRecursive (HNNEmb.Ext g) where
  rank := 2
  π := pi3 g
  π_surjective := pi3_surjective g hspan
  re := hre

/-- **The repaired clause, from the word problem alone.** -/
theorem bridgeEffective_of_extWordProblem (h : ExtWordProblemRE) : BridgeEffective where
  recursive := by
    intro A _ g hspan hre
    exact ⟨fgRecursiveExt g hspan (h.re A g hre)⟩

/-! ## 5.  The bridge, and the four-input theorem, off the repaired clause -/

/-- **The bridge, from the repaired effectivity clause.**  The torsion clause is
`Higman.torsionFree_ext`, which is unconditional, and the generating family is
the one the recursive presentation already carries --- so no auxiliary
surjection is chosen, and the mismatch that makes `Higman.BridgeRecursive` false
does not arise. -/
theorem countableToFG_of_effective (h : BridgeEffective) : CountableToFG where
  bridge := by
    intro A _ p htf
    obtain ⟨q⟩ := h.recursive A p.gen p.spans p.re
    exact ⟨{ Carrier := HNNEmb.Ext p.gen
             recursive := q
             torsionFree := torsionFree_ext p.gen htf
             emb := HNNEmb.embA p.gen
             emb_injective := HNNEmb.embA_injective p.gen }⟩

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1 from four inputs**, with the
bridge's clause in its repaired form.  This is `Higman.statement_of_four` with
`Higman.BridgeRecursive` replaced by `BridgeEffective`. -/
theorem statement_of_four_effective (h₁ : OperationClosures) (h₂ : HigmanTheoremThree)
    (h₃ : TransportSectionFive) (h₄ : BridgeEffective) :
    ChiodoBelegradek.Statement :=
  statement_of_higman
    (torsionFreeHigmanEmbedding_of_inputs (countableToFG_of_effective h₄)
      (torsionPreservation_of_reBenignTF (reBenignTF_of_inputs h₁ h₂ h₃)))

/-- The same, landing on `KC.21`'s first input. -/
theorem nonempty_host_of_four_effective (h₁ : OperationClosures)
    (h₂ : HigmanTheoremThree) (h₃ : TransportSectionFive) (h₄ : BridgeEffective) :
    Nonempty FournierFacioUniversal.UniversalTorsionFreeHost :=
  nonempty_host_of_higman
    (torsionFreeHigmanEmbedding_of_inputs (countableToFG_of_effective h₄)
      (torsionPreservation_of_reBenignTF (reBenignTF_of_inputs h₁ h₂ h₃)))

end BridgeEff
end Higman
end GroupApproximation
