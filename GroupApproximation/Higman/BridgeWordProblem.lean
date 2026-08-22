import GroupApproximation.Higman.BridgeEffectivity
import GroupApproximation.Higman.RelatorRE
import GroupApproximation.Higman.AddRelators
import GroupApproximation.Higman.REPredNormalForm

/-!
# The word problem of the bridge extension, reduced to its presentation

`Higman.BridgeEff.ExtWordProblemRE` is the one atom left of the repaired
effectivity clause of the Higman--Neumann--Neumann bridge: the word problem of
`Ext g` on its three generators is recursively enumerable whenever the word
problem of `A` in the family `g` is.  This file reduces it to a single
*algebraic* statement --- that `Ext g` is presented, on the obvious countable
family, by the relators one would write down --- with every computability step
proved.

    ExtPresentation  ⟹  ExtWordProblemRE  ⟹  BridgeEffective  ⟹  CountableToFG .

## The three moves

**1.  A countable family, not three generators.**  `extGen g` lists the three
generators first and then the whole of `A`:

    0 ↦ x,   1 ↦ y,   2 ↦ t,   k+3 ↦ g k .

The three-generator word problem reduces to this one by the *relabelling*
`k ↦ k % 3`, which is primitive recursive, so nothing is lost
(`pi3_rawToFree`, `rePred_pi3_of_extGen`).  Going the other way would need the
`g k` as words in `x, y, t` --- which `Higman.BridgeEff.bridgeFree` supplies ---
but the easy direction is the one the reduction wants.

**2.  The relators.**  Two families, in the alphabet `extGen` fixes:

* the relators of `A`, shifted into the tail of the alphabet ---
  `FreeGroup.map (· + 3) '' wordSet g`, where `wordSet g` is the *whole* word
  problem of `A`, so no presentation of `A` has to be chosen;
* the stable-letter relations `t aᵢ t⁻¹ (gᵢ aᵢ)⁻¹`, spelled as raw words by
  `hnnRaw`, with `aᵢ = x^{-i} y x^{i}` built by the recursion
  `a₀ = y`, `a_{i+1} = x⁻¹ aᵢ x` (`aRaw`).

Both are recursively enumerable, and `search_relSet` proves it with the lane's
own tools: `Higman.search_image` for the shifted word problem (membership in an
image is *witnessed*, not decided), `Higman.mem_range_iff_search` with
`Higman.primrec_rangeSearch` for the indexed family, `Higman.search_reindex` to
put both searches over `ℕ`, and `Higman.search_union` to join them.  The family
`hnnFam` interleaves each relator with its inverse, which is what makes the
relator set symmetric --- and `Higman.RelatorRE` asks for `symmetrize`, not for
the set itself.

**3.  The presentation.**  What is left is `ExtPresentation`: that a raw word
dies in `Ext g` exactly when its free value lies in the normal closure of those
relators.  One half of it is proved here as evidence that the relators are the
right ones (`evalRaw_shift`, `evalRaw_hnnRaw`: every relator does die); the
other half --- that nothing else does --- is the presentation theorem for an HNN
extension over a presented base, which
`Computability.HNNPresentedForward` flags as the expensive direction and does
not attempt.

Given it, `extWordProblemRE_of_presentation` closes the atom through
`Higman.rePred_wordProblem_of_relators`, whose docstring names this clause as
its intended third instance.
-/

namespace GroupApproximation
namespace Higman
namespace BridgeWP

open GroupApproximation.Higman.HNNEmb
open GroupApproximation.Higman.BridgeEff

/-! ## 1.  The countable generating family -/

/-- The generating family of the extension: the three generators, and then the
base group through its own family. -/
noncomputable def extGen {A : Type} [Group A] (g : ℕ → A) : ℕ → Ext g := fun k =>
  if h : k < 3 then gen3 g ⟨k, h⟩ else embA g (g (k - 3))

theorem extGen_of_lt {A : Type} [Group A] (g : ℕ → A) (k : ℕ) (h : k < 3) :
    extGen g k = gen3 g ⟨k, h⟩ := by
  unfold extGen
  rw [dif_pos h]

theorem extGen_add_three {A : Type} [Group A] (g : ℕ → A) (k : ℕ) :
    extGen g (k + 3) = embA g (g k) := by
  have hlt : ¬ k + 3 < 3 := by omega
  have hsub : k + 3 - 3 = k := by omega
  unfold extGen
  rw [dif_neg hlt, hsub]

theorem extGen_zero {A : Type} [Group A] (g : ℕ → A) :
    extGen g 0 = HNNExtension.of (xg : P A) := by
  rw [extGen_of_lt g 0 (by omega)]
  rfl

theorem extGen_one {A : Type} [Group A] (g : ℕ → A) :
    extGen g 1 = HNNExtension.of (yg : P A) := by
  rw [extGen_of_lt g 1 (by omega)]
  rfl

theorem extGen_two {A : Type} [Group A] (g : ℕ → A) :
    extGen g 2 = (HNNExtension.t : Ext g) := by
  rw [extGen_of_lt g 2 (by omega)]
  rfl

/-! ## 2.  Raw words, free groups, and the reduction to three letters -/

theorem evalRaw_eq_prod {G : Type} [Group G] (x : ℕ → G) (v : RawWord) :
    evalRaw x v = (v.map fun p ↦ if p.2 then x p.1 else (x p.1)⁻¹).prod := by
  induction v with
  | nil => rfl
  | cons p v ih =>
      obtain ⟨i, b⟩ := p
      rw [evalRaw_cons, List.map_cons, List.prod_cons, ih]

/-- **Reading a raw word in a free group of finite rank is `evalRaw` at the
letters it names.** -/
theorem lift_rawToFree {G : Type} [Group G] (n : ℕ) (f : Fin (n + 1) → G)
    (v : RawWord) :
    FreeGroup.lift f (rawToFree n v)
      = evalRaw (fun k : ℕ ↦ f ⟨k % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩) v := by
  rw [evalRaw_eq_prod]
  show FreeGroup.lift f (FreeGroup.mk (v.map fun p ↦
    ((⟨p.1 % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)), p.2))) = _
  rw [FreeGroup.lift_mk, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ ↦ ?_)
  obtain ⟨i, b⟩ := p
  cases b
  · rfl
  · rfl

/-- **The three-letter presentation map, read on the countable family.** -/
theorem pi3_rawToFree {A : Type} [Group A] (g : ℕ → A) (v : RawWord) :
    pi3 g (rawToFree 2 v) = evalRaw (extGen g) (relabel (fun k ↦ k % 3) v) := by
  rw [evalRaw_relabel]
  show FreeGroup.lift (gen3 g) (rawToFree 2 v) = _
  rw [lift_rawToFree]
  refine congrArg (fun y : ℕ → Ext g ↦ evalRaw y v) ?_
  funext k
  exact (extGen_of_lt g (k % 3) (Nat.mod_lt _ (Nat.succ_pos 2))).symm

/-- Recursive enumerability pulls back along a computable map. -/
theorem rePred_comp {α β : Type} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {f : α → β} (hf : Computable f) : REPred fun a ↦ p (f a) :=
  Partrec.comp hp hf

/-- **The three-letter word problem reduces to the countable one.** -/
theorem rePred_pi3_of_extGen {A : Type} [Group A] (g : ℕ → A)
    (h : REPred fun w : RawWord ↦ evalRaw (extGen g) w = 1) :
    REPred fun v : RawWord ↦ pi3 g (rawToFree 2 v) = 1 := by
  have hmod : Primrec fun k : ℕ ↦ k % 3 :=
    Primrec.nat_mod.comp Primrec.id (Primrec.const 3)
  have hcomp : Computable fun v : RawWord ↦ relabel (fun k ↦ k % 3) v :=
    (primrec_relabel hmod).to_comp
  exact (rePred_comp h hcomp).of_eq fun v ↦ by rw [pi3_rawToFree]

/-! ## 3.  The relators -/

/-- The word problem of the base, as a set of free-group elements. -/
def wordSet {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup ℕ) :=
  {z | FreeGroup.lift g z = 1}

theorem lift_freeEval {A : Type} [Group A] (x : ℕ → A) (v : RawWord) :
    FreeGroup.lift x (freeEval v) = evalRaw x v := by
  unfold freeEval
  rw [map_evalRaw]
  refine congrArg (fun y : ℕ → A ↦ evalRaw y v) ?_
  funext k
  show FreeGroup.lift x (FreeGroup.of k) = x k
  rw [FreeGroup.lift_apply_of]

theorem mem_wordSet_iff {A : Type} [Group A] (g : ℕ → A) (v : RawWord) :
    freeEval v ∈ wordSet g ↔ evalRaw g v = 1 := by
  show FreeGroup.lift g (freeEval v) = 1 ↔ _
  rw [lift_freeEval]

theorem inv_mem_wordSet {A : Type} [Group A] (g : ℕ → A) {z : FreeGroup ℕ}
    (hz : z ∈ wordSet g) : z⁻¹ ∈ wordSet g := by
  show FreeGroup.lift g z⁻¹ = 1
  rw [map_inv]
  show (FreeGroup.lift g z)⁻¹ = 1
  rw [show FreeGroup.lift g z = 1 from hz, inv_one]

/-- The untwisted family as raw words: `a₀ = y` and `a_{i+1} = x⁻¹ aᵢ x`. -/
def aRaw (i : ℕ) : RawWord :=
  Nat.rec (motive := fun _ ↦ RawWord) [(1, true)]
    (fun _ ih ↦ ((0, false) : ℕ × Bool) :: (ih ++ [((0 : ℕ), true)])) i

@[simp] theorem aRaw_zero : aRaw 0 = [((1 : ℕ), true)] := rfl

@[simp] theorem aRaw_succ (i : ℕ) :
    aRaw (i + 1) = ((0, false) : ℕ × Bool) :: (aRaw i ++ [((0 : ℕ), true)]) := rfl

/-- The stable-letter relator `t aᵢ t⁻¹ (gᵢ aᵢ)⁻¹`, as a raw word. -/
def hnnRaw (i : ℕ) : RawWord :=
  (((2 : ℕ), true) :: aRaw i) ++
    (((2 : ℕ), false) :: invRaw (((i + 3 : ℕ), true) :: aRaw i))

/-- The stable-letter relators together with their inverses, indexed by `ℕ`.
Interleaving is what makes the relator set symmetric, which is what
`Higman.RelatorRE` consumes. -/
def hnnFam (n : ℕ) : RawWord :=
  cond (decide (n % 2 = 0)) (hnnRaw (n / 2)) (invRaw (hnnRaw (n / 2)))

theorem hnnFam_even {n : ℕ} (h : n % 2 = 0) : hnnFam n = hnnRaw (n / 2) := by
  unfold hnnFam
  simp [h]

theorem hnnFam_odd {n : ℕ} (h : ¬ n % 2 = 0) :
    hnnFam n = invRaw (hnnRaw (n / 2)) := by
  unfold hnnFam
  simp [h]

/-- **The relator set of the extension.** -/
def relSet {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup ℕ) :=
  (FreeGroup.map fun k ↦ k + 3) '' wordSet g ∪ Set.range fun n ↦ freeEval (hnnFam n)

/-! ## 4.  The relators die

Not needed for the reduction --- `ExtPresentation` is a hypothesis --- but it is
what makes the hypothesis credible: these two lemmas are the easy half of it,
and they check that the raw words above spell the relations they should. -/

theorem freeEval_invRaw (u : RawWord) : freeEval (invRaw u) = (freeEval u)⁻¹ := by
  unfold freeEval
  rw [evalRaw_invRaw]

/-- **The shifted relators of the base die.** -/
theorem evalRaw_shift {A : Type} [Group A] (g : ℕ → A) (w : RawWord) :
    evalRaw (extGen g) (relabel (fun k ↦ k + 3) w) = embA g (evalRaw g w) := by
  rw [evalRaw_relabel, map_evalRaw]
  refine congrArg (fun y : ℕ → Ext g ↦ evalRaw y w) ?_
  funext k
  exact extGen_add_three g k

/-- The untwisted family, evaluated. -/
theorem evalRaw_aRaw {A : Type} [Group A] (g : ℕ → A) (i : ℕ) :
    evalRaw (extGen g) (aRaw i) = HNNExtension.of (aFam i : P A) := by
  induction i with
  | zero =>
      have hval : evalRaw (extGen g) (aRaw 0) = extGen g 1 := by
        show evalRaw (extGen g) [((1 : ℕ), true)] = extGen g 1
        simp only [evalRaw_cons, evalRaw_nil, mul_one]
      rw [hval, extGen_one]
      refine congrArg (fun z : P A ↦ HNNExtension.of z) ?_
      show (yg : P A) = aFam 0
      unfold aFam
      simp
  | succ i ih =>
      have hstep : (aFam (i + 1) : P A) = xg⁻¹ * (aFam i * xg) := by
        unfold aFam
        push_cast
        group
      have hval : evalRaw (extGen g) (aRaw (i + 1))
          = (extGen g 0)⁻¹ * (evalRaw (extGen g) (aRaw i) * extGen g 0) := by
        rw [aRaw_succ]
        simp only [evalRaw_cons, evalRaw_append, evalRaw_nil, mul_one]
      rw [hval, ih, extGen_zero, hstep, map_mul, map_mul, map_inv]

/-- **The stable-letter relators die.** -/
theorem evalRaw_hnnRaw {A : Type} [Group A] (g : ℕ → A) (i : ℕ) :
    evalRaw (extGen g) (hnnRaw i) = 1 := by
  have hconj : (HNNExtension.t : Ext g) * HNNExtension.of (aFam i : P A) *
      (HNNExtension.t : Ext g)⁻¹
      = embA g (g i) * HNNExtension.of (aFam i : P A) := by
    rw [conj_aFam g i]
    show HNNExtension.of (bFam g i : P A) = _
    unfold bFam
    rw [map_mul]
    rfl
  unfold hnnRaw
  simp only [evalRaw_append, evalRaw_cons, evalRaw_invRaw, evalRaw_nil, mul_one]
  rw [evalRaw_aRaw, extGen_two, extGen_add_three, ← hconj]
  group

/-! ## 5.  The relator set is symmetric, and enumerable -/

theorem inv_mem_relSet {A : Type} [Group A] (g : ℕ → A) {z : FreeGroup ℕ}
    (hz : z ∈ relSet g) : z⁻¹ ∈ relSet g := by
  rcases hz with ⟨u, hu, rfl⟩ | ⟨n, rfl⟩
  · refine Or.inl ⟨u⁻¹, inv_mem_wordSet g hu, ?_⟩
    rw [map_inv]
  · by_cases hpar : n % 2 = 0
    · refine Or.inr ⟨2 * (n / 2) + 1, ?_⟩
      have hidx : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      have h1 : hnnFam (2 * (n / 2) + 1) = invRaw (hnnRaw (n / 2)) := by
        rw [hnnFam_odd (n := 2 * (n / 2) + 1) (by omega), hidx]
      rw [h1, hnnFam_even hpar, freeEval_invRaw]
    · refine Or.inr ⟨2 * (n / 2), ?_⟩
      have hidx : 2 * (n / 2) / 2 = n / 2 := by omega
      have h1 : hnnFam (2 * (n / 2)) = hnnRaw (n / 2) := by
        rw [hnnFam_even (n := 2 * (n / 2)) (by omega), hidx]
      rw [h1, hnnFam_odd hpar, freeEval_invRaw, inv_inv]

theorem symmetrize_relSet {A : Type} [Group A] (g : ℕ → A) :
    symmetrize (relSet g) = relSet g := by
  refine Set.union_eq_self_of_subset_right ?_
  rintro _ ⟨z, hz, rfl⟩
  exact inv_mem_relSet g hz

theorem primrec_aRaw : Primrec aRaw := by
  have h : Primrec fun p : ℕ × RawWord ↦
      ((0, false) : ℕ × Bool) :: (p.2 ++ [((0 : ℕ), true)]) :=
    Primrec.list_cons.comp (Primrec.const ((0, false) : ℕ × Bool))
      (Primrec.list_append.comp Primrec.snd (Primrec.const [((0 : ℕ), true)]))
  exact Primrec.nat_rec₁ _ h.to₂

theorem primrec_hnnRaw : Primrec hnnRaw := by
  have h1 : Primrec fun i : ℕ ↦ (((2 : ℕ), true) : ℕ × Bool) :: aRaw i :=
    Primrec.list_cons.comp (Primrec.const (((2 : ℕ), true) : ℕ × Bool)) primrec_aRaw
  have h2 : Primrec fun i : ℕ ↦ (((i + 3 : ℕ), true) : ℕ × Bool) :: aRaw i :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_add.comp Primrec.id (Primrec.const 3))
        (Primrec.const true)) primrec_aRaw
  have h3 : Primrec fun i : ℕ ↦ (((2 : ℕ), false) : ℕ × Bool) ::
      invRaw ((((i + 3 : ℕ), true) : ℕ × Bool) :: aRaw i) :=
    Primrec.list_cons.comp (Primrec.const (((2 : ℕ), false) : ℕ × Bool))
      (primrec_invRaw.comp h2)
  exact Primrec.list_append.comp h1 h3

theorem primrec_hnnFam : Primrec hnnFam := by
  have hhalf : Primrec fun n : ℕ ↦ n / 2 :=
    Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hcond : Primrec fun n : ℕ ↦ decide (n % 2 = 0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)
  exact Primrec.cond hcond (primrec_hnnRaw.comp hhalf)
    (primrec_invRaw.comp (primrec_hnnRaw.comp hhalf))

/-- **The relator set is recursively enumerable**, as a search over `ℕ`. -/
theorem search_relSet {A : Type} [Group A] (g : ℕ → A)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      ∀ v : RawWord, freeEval v ∈ relSet g ↔ ∃ n, f v n = true := by
  unfold relSet
  obtain ⟨F, hF, hFspec⟩ := exists_primrec_of_rePred hre
  have hword : ∀ v : RawWord, freeEval v ∈ wordSet g ↔ ∃ n, F v n = true := by
    intro v
    rw [mem_wordSet_iff]
    exact hFspec v
  have hshift : Primrec fun k : ℕ ↦ k + 3 :=
    Primrec.nat_add.comp Primrec.id (Primrec.const 3)
  obtain ⟨f₁, hf₁, hf₁spec⟩ := search_image hshift hF hword
  obtain ⟨f₁', hf₁', hf₁'spec⟩ := search_reindex f₁ hf₁
  obtain ⟨f₂', hf₂', hf₂'spec⟩ :=
    search_reindex (fun (v : RawWord) (p : ℕ × List ℕ) ↦
      decide (Computability.applySteps (hnnFam p.1 ++ invRaw v) p.2 = some []))
      (primrec_rangeSearch primrec_hnnFam)
  refine search_union hf₁' hf₂' (fun v ↦ ?_) (fun v ↦ ?_)
  · exact (hf₁spec v).trans (hf₁'spec v)
  · refine (mem_range_iff_search hnnFam v).trans (Iff.trans ?_ (hf₂'spec v))
    exact exists_congr fun _ ↦ decide_eq_true_iff.symm

/-! ## 6.  The one algebraic input, and the atom it closes -/

/-- **Input: the extension is presented by those relators.**  A raw word in the
countable family dies in `Ext g` exactly when its free value lies in the normal
closure of `relSet g`.

One half is proved above: `evalRaw_shift` and `evalRaw_hnnRaw` say every relator
dies, so the normal closure is contained in the kernel.  The other half is the
presentation theorem for an HNN extension over a presented base --- a map *into*
the presented group, which is the direction
`Computability.HNNPresentedForward` records as the expensive one.  Its
ingredients are all present: `Monoid.Coprod.lift` for the free product,
`HNNExtension.lift` for the stable letter, and `Higman.presentedGroupUnionEquiv`
for the passage from a presented base to a presented extension; what has to be
checked is that the stable-letter condition, which `HNNExtension.lift` demands
on the whole associated subgroup, follows from the relators on its free basis.

**Nothing inhabits this structure.** -/
structure ExtPresentation where
  /-- The extension is presented on `extGen` by `relSet`. -/
  pres : ∀ (A : Type) [Group A] (g : ℕ → A) (w : RawWord),
    evalRaw (extGen g) w = 1 ↔ freeEval w ∈ Subgroup.normalClosure (relSet g)

/-- **The word problem of the extension on the countable family.** -/
theorem rePred_extGen_of_presentation (hpres : ExtPresentation) {A : Type} [Group A]
    (g : ℕ → A) (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    REPred fun w : RawWord ↦ evalRaw (extGen g) w = 1 := by
  obtain ⟨f, hf, hfspec⟩ := search_relSet g hre
  refine rePred_wordProblem_of_relators f (extGen g) (relSet g) (hpres.pres A g) hf
    (fun v ↦ ?_)
  rw [symmetrize_relSet]
  exact hfspec v

/-- **The remaining atom of the bridge, closed by the presentation.** -/
theorem extWordProblemRE_of_presentation (hpres : ExtPresentation) :
    ExtWordProblemRE where
  re := by
    intro A _ g hre
    exact rePred_pi3_of_extGen g (rePred_extGen_of_presentation hpres g hre)

/-- **The bridge, from the presentation alone.** -/
theorem bridgeEffective_of_presentation (hpres : ExtPresentation) : BridgeEffective :=
  bridgeEffective_of_extWordProblem (extWordProblemRE_of_presentation hpres)

/-- **Chiodo Theorem 3.10 = Belegradek Theorem A.1**, with the bridge reduced to
the presentation of its HNN extension. -/
theorem statement_of_four_presentation (h₁ : OperationClosures)
    (h₂ : HigmanTheoremThree) (h₃ : TransportSectionFive) (h₄ : ExtPresentation) :
    ChiodoBelegradek.Statement :=
  statement_of_four_effective h₁ h₂ h₃ (bridgeEffective_of_presentation h₄)

end BridgeWP
end Higman
end GroupApproximation
