import GroupApproximation.Algebra.HyperbolicGeodesicPrefix
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Set.Finite.List

/-!
# A hyperbolic group is finitely presented

`GGT/RelHypFournierFacioProp23.lean` carries `Group.IsFinitelyPresented Lam` as
a hypothesis of `FournierFacioProposition23` and says why: "`Λ` finitely
presented is *not* in Proposition 2.3, where it is implied by `Λ` hyperbolic.
It is a hypothesis here because 'hyperbolic implies finitely presented' is a
theorem this repository does not have."  This module proves that theorem, so the
hypothesis can be dropped.

`isFinitelyPresented_of_isHyperbolicGroup : IsHyperbolicGroup G →
Group.IsFinitelyPresented G`, with no literature input and no open leaves.

## The route, and why it is not the Rips complex

The textbook proof builds the Rips complex at parameter `4δ + 1`, shows it is
simply connected, and quotes "a group acting properly cocompactly on a simply
connected complex is finitely presented".  None of the three steps is available
here or in Mathlib at this revision, and the last one is a substantial piece of
combinatorial topology.

The proof below is the combinatorial one, and it is a single telescoping
induction over lists.  Fix the hyperbolic alphabet `S` and let `φ : FreeGroup
(Alph S) →* G` be the induced epimorphism.  `geo g` is the chosen geodesic
spelling of `g`.

**Step 1, the telescoping.**  For a list `l` of free letters put

    Q n = mk (l.take n) * (toFree (geo (φ (mk (l.take n)))))⁻¹ .

`Q 0 = 1` because `geo 1 = []`, and `Q (n+1) = Q n * B n` where `B n` is the
*bigon* `toFree (geo g) * w * (toFree (geo (g * φ w)))⁻¹` at `g = φ (mk (l.take
n))` and the single free letter `w = mk ((l.drop n).take 1)`.  So once every
bigon lies in the normal closure `N` of the short relators, every `Q n` does,
and for `w ∈ ker φ` --- writing `w = mk l` and taking `n = l.length` ---
`Q n` *is* `w`.  There is no van Kampen diagram anywhere.

**Step 2, the bigon, by a ladder.**  Write `a = geo g`, `b = geo (g * s)`,
`A j`, `B j` for their length-`j` prefix words, and `T j` for a geodesic
spelling of the displacement between the two prefix *points*.  Then
`P j = A j * T j * (B j)⁻¹` satisfies `P 0 = 1` and

    P (j+1) = (A j * C j * (A j)⁻¹) * P j ,
    C j = α j * T (j+1) * (β j)⁻¹ * (T j)⁻¹ ,

with `α j`, `β j` the single letters cut off at index `j`.  The cell `C j` dies
under `φ` --- one group identity --- and is spelled by at most `2K + 2` letters,
where `K` bounds the distance between the two prefix points.  So each cell is a
short relator, each conjugate of it is in `N`, and the induction runs.  At the
top `P M` is `toFree a * toFree (geo s) * (toFree b)⁻¹`, and one further relator
of length `2` exchanges `toFree (geo s)` for the letter itself.

**Step 3, the constant.**  `K = 2δ + 3`, by
`Algebra/HyperbolicGeodesicPrefix.wordDist_prefix_fellow`, which is one
application of the four-point condition and no slim-triangle input at all.  So
`relRadius δ = 4δ + 8` and the relator set is the ball of that radius inside
`ker φ`, finite by `List.finite_length_le`.

## The transport to `Fin n`

Mathlib's `Group.IsFinitelyPresented` asks for a hom out of `FreeGroup (Fin n)`.
Everything above is proved at `FreeGroup (Alph S)`; `FreeGroup.map` along
`Fintype.equivFin` transports it, and the kernel survives by
`Subgroup.IsFinitelyNormallyGenerated.comap`, whose second hypothesis is
discharged because an isomorphism has trivial kernel.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u

variable {G : Type u} [Group G]

/-! ## 1.  The relator ball -/

/-- The radius of the relator ball: `2K + 2` at the fellow-travelling constant
`K = 2δ + 3`. -/
def relRadius (δ : ℕ) : ℕ := 4 * δ + 8

/-- **The relators**: the words of length at most `N` that die in `G`. -/
def relSet (S : Finset G) (N : ℕ) : Set (FreeGroup (Alph S)) :=
  {w | FreeLen w N ∧ wordHom S w = 1}

theorem relSet_finite (S : Finset G) (N : ℕ) : (relSet S N).Finite := by
  have hsub : relSet S N
      ⊆ FreeGroup.mk '' {l : List (Alph S × Bool) | l.length ≤ N} := by
    rintro w ⟨⟨l, hl, hw⟩, -⟩
    exact ⟨l, hl, hw⟩
  exact Set.Finite.subset
    (Set.Finite.image _ (List.finite_length_le (Alph S × Bool) N)) hsub

/-- The normal closure of the relator ball. -/
def relClosure (S : Finset G) (N : ℕ) : Subgroup (FreeGroup (Alph S)) :=
  Subgroup.normalClosure (relSet S N)

instance instRelClosureNormal (S : Finset G) (N : ℕ) : (relClosure S N).Normal :=
  Subgroup.normalClosure_normal

theorem mem_relClosure {S : Finset G} {N : ℕ} {w : FreeGroup (Alph S)}
    (h : w ∈ relSet S N) : w ∈ relClosure S N :=
  Subgroup.subset_normalClosure h

theorem conj_mem_relClosure {S : Finset G} {N : ℕ} {w : FreeGroup (Alph S)}
    (h : w ∈ relClosure S N) (c : FreeGroup (Alph S)) :
    c * w * c⁻¹ ∈ relClosure S N :=
  (instRelClosureNormal S N).conj_mem w h c

/-! ## 2.  A single free letter has word norm at most one -/

theorem wordNorm_wordHom_le_one {S : Finset G}
    (hS : IsSymmetricGeneratingSet (S : Set G)) {w : FreeGroup (Alph S)}
    (hw : FreeLen w 1) : wordNorm (S : Set G) (wordHom S w) ≤ 1 := by
  obtain ⟨l, hl, rfl⟩ := hw
  cases l with
  | nil =>
    have h1 : (FreeGroup.mk ([] : List (Alph S × Bool))) = 1 := rfl
    rw [h1, map_one, wordNorm_one]
    exact Nat.zero_le 1
  | cons x t =>
    have ht : t = [] := by
      rw [List.length_cons] at hl
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    obtain ⟨a, b⟩ := x
    have hval : wordHom S (FreeGroup.mk [(a, b)])
        = cond b (a : G) (a : G)⁻¹ := by
      simp [wordHom]
    have hmem : cond b (a : G) (a : G)⁻¹ ∈ (S : Set G) := by
      cases b
      · exact hS.inv_mem _ (Finset.mem_coe.mpr a.2)
      · exact Finset.mem_coe.mpr a.2
    rw [hval]
    exact wordNorm_le_one_of_mem hmem

/-! ## 3.  The rungs of the ladder -/

section Ladder

variable {S : Finset G}

/-- The `j`-th prefix point of the chosen geodesic to `g`. -/
noncomputable def prefPt (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G)
    (j : ℕ) : G := eval ((geo hS g).take j)

/-- The `j`-th prefix word of the chosen geodesic to `g`. -/
noncomputable def prefWord (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G)
    (j : ℕ) : FreeGroup (Alph S) := toFree ((geo hS g).take j)

/-- The letter cut off at index `j`; the empty word past the end. -/
noncomputable def stepWord (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G)
    (j : ℕ) : FreeGroup (Alph S) := toFree (((geo hS g).drop j).take 1)

/-- The `j`-th rung: a geodesic spelling of the displacement between the two
prefix points. -/
noncomputable def rung (hS : IsSymmetricGeneratingSet (S : Set G)) (g s : G)
    (j : ℕ) : FreeGroup (Alph S) :=
  toFree (geo hS ((prefPt hS g j)⁻¹ * prefPt hS (g * s) j))

theorem prefPt_zero (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) :
    prefPt hS g 0 = 1 := by simp [prefPt]

theorem prefWord_zero (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) :
    prefWord hS g 0 = 1 := by simp [prefWord]

theorem prefPt_succ (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) (j : ℕ) :
    prefPt hS g (j + 1) = prefPt hS g j * eval (((geo hS g).drop j).take 1) := by
  rw [prefPt, prefPt, take_succ_append, eval_append]

theorem prefWord_succ (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G) (j : ℕ) :
    prefWord hS g (j + 1) = prefWord hS g j * stepWord hS g j := by
  rw [prefWord, prefWord, stepWord, take_succ_append, toFree_append]

theorem wordHom_stepWord (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G)
    (j : ℕ) :
    wordHom S (stepWord hS g j) = eval (((geo hS g).drop j).take 1) := by
  rw [stepWord, wordHom_toFree]

theorem wordHom_rung (hS : IsSymmetricGeneratingSet (S : Set G)) (g s : G)
    (j : ℕ) :
    wordHom S (rung hS g s j) = (prefPt hS g j)⁻¹ * prefPt hS (g * s) j := by
  rw [rung, wordHom_toFree, geo_eval]

theorem freeLen_stepWord (hS : IsSymmetricGeneratingSet (S : Set G)) (g : G)
    (j : ℕ) : FreeLen (stepWord hS g j) 1 := by
  refine (freeLen_toFree (((geo hS g).drop j).take 1)).mono ?_
  simp

theorem freeLen_rung {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) (g s : G)
    (hs : wordNorm (S : Set G) s ≤ 1) (j : ℕ) :
    FreeLen (rung hS g s j) (2 * δ + 3) := by
  refine (freeLen_toFree (geo hS ((prefPt hS g j)⁻¹ * prefPt hS (g * s) j))).mono ?_
  rw [geo_length]
  exact wordDist_prefix_fellow hS hδ g s hs j

/-- The `j`-th cell of the ladder. -/
noncomputable def cell (hS : IsSymmetricGeneratingSet (S : Set G)) (g s : G)
    (j : ℕ) : FreeGroup (Alph S) :=
  stepWord hS g j * rung hS g s (j + 1) * (stepWord hS (g * s) j)⁻¹
    * (rung hS g s j)⁻¹

theorem cell_mem_relSet {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) (g s : G)
    (hs : wordNorm (S : Set G) s ≤ 1) (j : ℕ) :
    cell hS g s j ∈ relSet S (relRadius δ) := by
  have hlen : FreeLen (cell hS g s j) (relRadius δ) := by
    have hbase := ((((freeLen_stepWord hS g j).mul
      (freeLen_rung hS hδ g s hs (j + 1))).mul
        (freeLen_stepWord hS (g * s) j).inv).mul
          (freeLen_rung hS hδ g s hs j).inv)
    exact hbase.mono (by simp only [relRadius]; omega)
  have hker : wordHom S (cell hS g s j) = 1 := by
    have h1 := prefPt_succ hS g j
    have h2 := prefPt_succ hS (g * s) j
    simp only [cell, map_mul, map_inv, wordHom_stepWord, wordHom_rung]
    rw [h1, h2]
    group
  exact ⟨hlen, hker⟩

/-- **The ladder.**  Every rung sits inside the normal closure of the relator
ball, by induction on the index. -/
theorem ladder_mem {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) (g s : G)
    (hs : wordNorm (S : Set G) s ≤ 1) (j : ℕ) :
    prefWord hS g j * rung hS g s j * (prefWord hS (g * s) j)⁻¹
      ∈ relClosure S (relRadius δ) := by
  induction j with
  | zero =>
    have hr : rung hS g s 0 = 1 := by
      simp only [rung, prefPt_zero, inv_one, one_mul, geo_one hS, toFree_nil]
    simp only [prefWord_zero, hr, one_mul, inv_one]
    exact Subgroup.one_mem _
  | succ j ih =>
    have hkey :
        prefWord hS g (j + 1) * rung hS g s (j + 1)
            * (prefWord hS (g * s) (j + 1))⁻¹
          = (prefWord hS g j * cell hS g s j * (prefWord hS g j)⁻¹)
            * (prefWord hS g j * rung hS g s j * (prefWord hS (g * s) j)⁻¹) := by
      rw [prefWord_succ, prefWord_succ, cell]
      group
    rw [hkey]
    exact Subgroup.mul_mem _
      (conj_mem_relClosure (mem_relClosure (cell_mem_relSet hS hδ g s hs j)) _) ih

/-! ## 4.  The bigon -/

/-- **The bigon lies in the normal closure of the relator ball.**  The top of
the ladder, corrected by one relator of length two that exchanges the chosen
geodesic spelling of the letter for the letter itself. -/
theorem bigon_mem {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) (g s : G)
    (w : FreeGroup (Alph S)) (hw : FreeLen w 1) (hws : wordHom S w = s) :
    toFree (geo hS g) * w * (toFree (geo hS (g * s)))⁻¹
      ∈ relClosure S (relRadius δ) := by
  have hs : wordNorm (S : Set G) s ≤ 1 := by
    rw [← hws]
    exact wordNorm_wordHom_le_one hS hw
  obtain ⟨M, hMa, hMb⟩ : ∃ M : ℕ,
      (geo hS g).length ≤ M ∧ (geo hS (g * s)).length ≤ M :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have hta : (geo hS g).take M = geo hS g := List.take_of_length_le hMa
  have htb : (geo hS (g * s)).take M = geo hS (g * s) :=
    List.take_of_length_le hMb
  have hA : prefWord hS g M = toFree (geo hS g) := by rw [prefWord, hta]
  have hB : prefWord hS (g * s) M = toFree (geo hS (g * s)) := by
    rw [prefWord, htb]
  have hP : prefPt hS g M = g := by rw [prefPt, hta, geo_eval]
  have hQ : prefPt hS (g * s) M = g * s := by rw [prefPt, htb, geo_eval]
  have hR : rung hS g s M = toFree (geo hS s) := by
    rw [rung, hP, hQ, inv_mul_cancel_left]
  have hlad := ladder_mem hS hδ g s hs M
  rw [hA, hB, hR] at hlad
  have hgs : FreeLen (toFree (geo hS s)) 1 := by
    refine (freeLen_toFree (geo hS s)).mono ?_
    rw [geo_length]
    exact hs
  have hDlen : FreeLen ((toFree (geo hS s))⁻¹ * w) (relRadius δ) :=
    (hgs.inv.mul hw).mono (by simp only [relRadius]; omega)
  have hDker : wordHom S ((toFree (geo hS s))⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, wordHom_toFree, geo_eval, hws, inv_mul_cancel]
  have hD := conj_mem_relClosure (mem_relClosure ⟨hDlen, hDker⟩)
    (toFree (geo hS (g * s)))
  have hfin : toFree (geo hS g) * w * (toFree (geo hS (g * s)))⁻¹
      = (toFree (geo hS g) * toFree (geo hS s) * (toFree (geo hS (g * s)))⁻¹)
        * (toFree (geo hS (g * s)) * ((toFree (geo hS s))⁻¹ * w)
            * (toFree (geo hS (g * s)))⁻¹) := by
    group
  rw [hfin]
  exact Subgroup.mul_mem _ hlad hD

/-! ## 5.  The telescoping -/

theorem telescope_mem {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ)
    (l : List (Alph S × Bool)) (n : ℕ) :
    FreeGroup.mk (l.take n)
        * (toFree (geo hS (wordHom S (FreeGroup.mk (l.take n)))))⁻¹
      ∈ relClosure S (relRadius δ) := by
  induction n with
  | zero =>
    have h1 : FreeGroup.mk ((l.take 0)) = 1 := by
      rw [List.take_zero]; rfl
    rw [h1, map_one, geo_one hS, toFree_nil, inv_one, mul_one]
    exact Subgroup.one_mem _
  | succ n ih =>
    have hmk : FreeGroup.mk (l.take (n + 1))
        = FreeGroup.mk (l.take n) * FreeGroup.mk ((l.drop n).take 1) := by
      rw [take_succ_append, FreeGroup.mul_mk]
    have hlen : FreeLen (FreeGroup.mk ((l.drop n).take 1)) 1 := by
      refine ⟨(l.drop n).take 1, ?_, rfl⟩
      simp
    have hbig := bigon_mem hS hδ (wordHom S (FreeGroup.mk (l.take n)))
      (wordHom S (FreeGroup.mk ((l.drop n).take 1)))
      (FreeGroup.mk ((l.drop n).take 1)) hlen rfl
    rw [hmk, map_mul]
    have hid : FreeGroup.mk (l.take n) * FreeGroup.mk ((l.drop n).take 1)
        * (toFree (geo hS (wordHom S (FreeGroup.mk (l.take n))
            * wordHom S (FreeGroup.mk ((l.drop n).take 1)))))⁻¹
      = (FreeGroup.mk (l.take n)
            * (toFree (geo hS (wordHom S (FreeGroup.mk (l.take n)))))⁻¹)
        * (toFree (geo hS (wordHom S (FreeGroup.mk (l.take n))))
            * FreeGroup.mk ((l.drop n).take 1)
            * (toFree (geo hS (wordHom S (FreeGroup.mk (l.take n))
                * wordHom S (FreeGroup.mk ((l.drop n).take 1)))))⁻¹) := by
      group
    rw [hid]
    exact Subgroup.mul_mem _ ih hbig

/-! ## 6.  The kernel is the normal closure of the relator ball -/

theorem ker_le_relClosure {δ : ℕ} (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) :
    (wordHom S).ker ≤ relClosure S (relRadius δ) := by
  classical
  intro w hw
  obtain ⟨l, hl⟩ : ∃ l : List (Alph S × Bool), FreeGroup.mk l = w :=
    ⟨FreeGroup.toWord w, FreeGroup.mk_toWord⟩
  have h := telescope_mem hS hδ l l.length
  rw [List.take_length, hl, MonoidHom.mem_ker.mp hw, geo_one hS, toFree_nil,
    inv_one, mul_one] at h
  exact h

theorem relClosure_le_ker (S : Finset G) (N : ℕ) :
    relClosure S N ≤ (wordHom S).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro w ⟨_hlen, hw⟩
  exact MonoidHom.mem_ker.mpr hw

theorem isFinitelyNormallyGenerated_ker {δ : ℕ}
    (hS : IsSymmetricGeneratingSet (S : Set G))
    (hδ : IsFourPointHyperbolic (S : Set G) δ) :
    (wordHom S).ker.IsFinitelyNormallyGenerated :=
  ⟨relSet S (relRadius δ), relSet_finite S _,
    le_antisymm (relClosure_le_ker S _) (ker_le_relClosure hS hδ)⟩

end Ladder

/-! ## 7.  The theorem -/

/-- **A word-hyperbolic group is finitely presented.**

Proved from `Hyperbolic.IsHyperbolicGroup` --- a finite symmetric generating set
whose word metric satisfies Gromov's four-point condition --- with no literature
input.  The relators are the words of length at most `4δ + 8` that die in `G`,
and the whole content is the ladder of
`Algebra/HyperbolicGeodesicPrefix.wordDist_prefix_fellow`. -/
theorem isFinitelyPresented_of_isHyperbolicGroup (h : IsHyperbolicGroup G) :
    Group.IsFinitelyPresented G := by
  classical
  obtain ⟨S, hS, δ, hδ⟩ := h
  refine ⟨Fintype.card (Alph S),
    (wordHom S).comp (FreeGroup.map ⇑(Fintype.equivFin (Alph S)).symm), ?_, ?_⟩
  · intro x
    obtain ⟨w, hw⟩ := wordHom_surjective hS x
    obtain ⟨v, hv⟩ :=
      FreeGroup.map_surjective (Fintype.equivFin (Alph S)).symm.surjective w
    exact ⟨v, by rw [MonoidHom.comp_apply, hv, hw]⟩
  · rw [← MonoidHom.comap_ker]
    refine Subgroup.IsFinitelyNormallyGenerated.comap
      (isFinitelyNormallyGenerated_ker hS hδ)
      (FreeGroup.map_surjective (Fintype.equivFin (Alph S)).symm.surjective) ?_
    rw [MonoidHom.ker_eq_bot _
      (FreeGroup.map_injective (Fintype.equivFin (Alph S)).symm.injective)]
    exact Subgroup.IsFinitelyNormallyGenerated.bot

end Hyperbolic
end GroupApproximation
