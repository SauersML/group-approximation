import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Simple lamps: one relation generates the whole invisible kernel

**Section 51** of the dossier.  When the lamp group is nonabelian simple and the
acting group is transitive on the sites, the entire lamp subgroup of the
permutational wreath product is the normal closure of a *single* nontrivial
one-site lamp.

Two ingredients:

* `Lamp.mem_closure_singles` — every finitely supported configuration is a
  product of one-site lamps.  The induction peels one site off the support at a
  time.
* `lamp_le_normalClosure_single` — simplicity of the lamp group makes the normal
  closure meet the one-site copy at the base site in all of `K`, and
  transitivity of the site action spreads that across every site.

The consequence recorded in the dossier is that adding the single relation
`r = 1` collapses the wreath product onto the acting group.
-/

namespace GroupApproximation

universe u v w

namespace Lamp

variable {K : Type u} [Group K] {X : Type v}

/-- The (finite) support of a lamp configuration. -/
noncomputable def support (f : Lamp K X) : Finset X :=
  (f.2 : {x : X | (f : X → K) x ≠ 1}.Finite).toFinset

theorem mem_support {f : Lamp K X} {x : X} :
    x ∈ f.support ↔ f.toFun x ≠ 1 :=
  Set.Finite.mem_toFinset _

theorem support_eq_empty_iff {f : Lamp K X} : f.support = ∅ ↔ f = 1 := by
  constructor
  · intro h
    refine ext fun x => ?_
    by_contra hx
    have hmem : x ∈ f.support := mem_support.mpr hx
    rw [h] at hmem
    simp at hmem
  · rintro rfl
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact (mem_support.mp hx) rfl

variable [DecidableEq X]

/-- Peeling one site off a configuration. -/
theorem support_mul_single_inv_subset (f : Lamp K X) (x : X) :
    (f * (single x (f.toFun x))⁻¹).support ⊆ f.support.erase x := by
  intro y hy
  rw [mem_support] at hy
  have hne : y ≠ x := by
    rintro rfl
    exact hy (by rw [mul_apply, inv_apply, single_apply_self, mul_inv_cancel])
  refine Finset.mem_erase.mpr ⟨hne, mem_support.mpr ?_⟩
  intro hcon
  refine hy ?_
  rw [mul_apply, inv_apply, single_apply_of_ne hne, inv_one, mul_one, hcon]

/-- **Every configuration is a product of one-site lamps.** -/
theorem mem_closure_singles (f : Lamp K X) :
    f ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} := by
  classical
  suffices h : ∀ n : ℕ, ∀ f : Lamp K X, f.support.card ≤ n →
      f ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} by
    exact h f.support.card f le_rfl
  intro n
  induction n with
  | zero =>
      intro f hf
      have hempty : f.support = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hf)
      rw [support_eq_empty_iff.mp hempty]
      exact Subgroup.one_mem _
  | succ n ih =>
      intro f hf
      by_cases hempty : f.support = ∅
      · rw [support_eq_empty_iff.mp hempty]
        exact Subgroup.one_mem _
      · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
        have hcard : (f * (single x (f.toFun x))⁻¹).support.card ≤ n := by
          have hsub := Finset.card_le_card (support_mul_single_inv_subset f x)
          rw [Finset.card_erase_of_mem hx] at hsub
          omega
        have hrest := ih _ hcard
        have hsingle : single x (f.toFun x)
            ∈ Subgroup.closure {g : Lamp K X | ∃ (x : X) (k : K), g = single x k} :=
          Subgroup.subset_closure ⟨x, f.toFun x, rfl⟩
        have hsplit : f = (f * (single x (f.toFun x))⁻¹) * single x (f.toFun x) := by
          rw [inv_mul_cancel_right]
        rw [hsplit]
        exact Subgroup.mul_mem _ hrest hsingle

end Lamp

/-! ## The normal closure of a single lamp -/

section Simple

open SemidirectProduct

variable (K : Type u) [Group K] (G : Type w) [Group G] (X : Type v)
variable [MulAction G X] [DecidableEq X]

/-- Conjugating a one-site lamp by the acting group moves the site. -/
theorem conj_inl_single (g : G) (x : X) (k : K) :
    (inr g : Wreath K G X) * inl (Lamp.single x k) * (inr g)⁻¹
      = inl (Lamp.single (g • x) k) := by
  rw [← map_inv, ← inl_aut]
  exact congrArg inl (lampAut_single g x k)

end Simple

section SimpleClosure

open SemidirectProduct

/-- **Section 51.1.**  For a simple lamp group and a transitive site action the
whole lamp subgroup is the normal closure of one nontrivial one-site lamp. -/
theorem lamp_le_normalClosure_single {K : Type u} [Group K] {G : Type w}
    [Group G] {X : Type v} [MulAction G X] [DecidableEq X] [IsSimpleGroup K]
    (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) {k₀ : K} (hk₀ : k₀ ≠ 1)
    (f : Lamp K X) :
    (inl f : Wreath K G X)
      ∈ Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)} := by
  classical
  set N : Subgroup (Wreath K G X) :=
    Subgroup.normalClosure {(inl (Lamp.single x₀ k₀) : Wreath K G X)} with hNdef
  haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
  set ι : K →* Wreath K G X :=
    (inl : Lamp K X →* Wreath K G X).comp (Lamp.singleHom x₀) with hι
  -- the values realised at the base site form a normal subgroup of `K`
  set N₀ : Subgroup K := N.comap ι with hN₀
  have hk₀mem : k₀ ∈ N₀ := by
    rw [hN₀, Subgroup.mem_comap, hι]
    exact Subgroup.subset_normalClosure rfl
  haveI : N₀.Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [hN₀, Subgroup.mem_comap] at ha ⊢
    have hconj : ι (b * a * b⁻¹) = ι b * ι a * (ι b)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact hNnormal.conj_mem _ ha _
  have hNtop : N₀ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ inferInstance with h | h
    · exact absurd (h ▸ hk₀mem) (by simpa using hk₀)
    · exact h
  -- every one-site lamp lies in the normal closure
  have hsingle : ∀ (x : X) (k : K), (inl (Lamp.single x k) : Wreath K G X) ∈ N := by
    intro x k
    obtain ⟨g, rfl⟩ := htrans x
    have hbase : (inl (Lamp.single x₀ k) : Wreath K G X) ∈ N := by
      have : k ∈ N₀ := by rw [hNtop]; exact Subgroup.mem_top k
      rw [hN₀, Subgroup.mem_comap] at this
      exact this
    rw [← conj_inl_single K G X g x₀ k]
    exact hNnormal.conj_mem _ hbase _
  -- and configurations are products of one-site lamps
  have hcl : Subgroup.closure
      {g : Lamp K X | ∃ (x : X) (k : K), g = Lamp.single x k}
      ≤ N.comap (inl : Lamp K X →* Wreath K G X) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨x, k, rfl⟩
    exact hsingle x k
  exact hcl (Lamp.mem_closure_singles f)

end SimpleClosure


/-! ## Generation and simple quotients -/

section Generation

open SemidirectProduct

/-- **Section 43.3.**  For a transitive site action the wreath product is
generated by generators of the acting group together with one-site lamps at a
single base site.  In particular a finitely generated acting group and a
finitely generated lamp group give a finitely generated wreath product. -/
theorem wreath_eq_closure {K : Type u} [Group K] {G : Type w} [Group G]
    {X : Type v} [MulAction G X] [DecidableEq X] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)
    {SG : Set G} (hSG : Subgroup.closure SG = ⊤)
    {SK : Set K} (hSK : Subgroup.closure SK = ⊤) :
    Subgroup.closure
        (((inr : G →* Wreath K G X) '' SG) ∪
          ((fun k => (inl (Lamp.single x₀ k) : Wreath K G X)) '' SK)) = ⊤ := by
  classical
  set C : Subgroup (Wreath K G X) := Subgroup.closure
      (((inr : G →* Wreath K G X) '' SG) ∪
        ((fun k => (inl (Lamp.single x₀ k) : Wreath K G X)) '' SK)) with hC
  have hinr : ∀ g : G, (inr g : Wreath K G X) ∈ C := by
    intro g
    have hle : Subgroup.closure SG ≤ C.comap (inr : G →* Wreath K G X) := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      exact Subgroup.subset_closure (Or.inl ⟨y, hy, rfl⟩)
    rw [hSG] at hle
    exact hle (Subgroup.mem_top g)
  have hbase : ∀ k : K, (inl (Lamp.single x₀ k) : Wreath K G X) ∈ C := by
    intro k
    have hle : Subgroup.closure SK ≤
        C.comap ((inl : Lamp K X →* Wreath K G X).comp (Lamp.singleHom x₀)) := by
      refine (Subgroup.closure_le _).mpr fun y hy => ?_
      exact Subgroup.subset_closure (Or.inr ⟨y, hy, rfl⟩)
    rw [hSK] at hle
    exact hle (Subgroup.mem_top k)
  have hsingle : ∀ (x : X) (k : K),
      (inl (Lamp.single x k) : Wreath K G X) ∈ C := by
    intro x k
    obtain ⟨g, rfl⟩ := htrans x
    rw [← conj_inl_single K G X g x₀ k]
    exact C.mul_mem (C.mul_mem (hinr g) (hbase k)) (C.inv_mem (hinr g))
  have hlamp : ∀ f : Lamp K X, (inl f : Wreath K G X) ∈ C := by
    intro f
    have hcl : Subgroup.closure
        {g : Lamp K X | ∃ (x : X) (k : K), g = Lamp.single x k}
        ≤ C.comap (inl : Lamp K X →* Wreath K G X) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨x, k, rfl⟩
      exact hsingle x k
    exact hcl (Lamp.mem_closure_singles f)
  refine eq_top_iff.mpr fun w _ => ?_
  have hw : w = inl w.left * inr w.right := (inl_left_mul_inr_right w).symm
  rw [hw]
  exact C.mul_mem (hlamp w.left) (hinr w.right)

end Generation

section SimpleQuotient

/-- Each coordinate copy of the lamp group is normal in the lamp group. -/
instance singleHom_range_normal {K : Type u} [Group K] {X : Type v}
    [DecidableEq X] (x : X) : ((Lamp.singleHom (K := K) (X := X) x).range).Normal := by
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨k, rfl⟩ := hn
  exact ⟨f.toFun x * k * (f.toFun x)⁻¹, by
    simpa using (Lamp.conj_single f x k).symm⟩

/-- **Section 52.2.**  Every simple quotient of the lamp group over a simple
lamp group is a quotient of a single coordinate copy, hence isomorphic to the
lamp group itself.  So the isomorphism type of the lamp group is recoverable
from the invisible kernel. -/
theorem exists_site_bijective_of_simple_quotient {K : Type u} [Group K]
    {X : Type v} [DecidableEq X] [IsSimpleGroup K] {T : Type u} [Group T]
    [IsSimpleGroup T] (φ : Lamp K X →* T) (hφ : Function.Surjective φ) :
    ∃ x : X, Function.Injective (φ.comp (Lamp.singleHom x)) ∧
      Function.Surjective (φ.comp (Lamp.singleHom x)) := by
  classical
  by_cases hall : ∀ (x : X) (k : K), φ (Lamp.single x k) = 1
  · exfalso
    have htriv : ∀ f : Lamp K X, φ f = 1 := by
      intro f
      have hcl : Subgroup.closure
          {g : Lamp K X | ∃ (x : X) (k : K), g = Lamp.single x k} ≤ φ.ker := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro y ⟨x, k, rfl⟩
        exact hall x k
      exact hcl (Lamp.mem_closure_singles f)
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    obtain ⟨u, rfl⟩ := hφ a
    obtain ⟨v, rfl⟩ := hφ b
    exact hab (by rw [htriv u, htriv v])
  · push Not at hall
    obtain ⟨x, k, hk⟩ := hall
    have hkne : (φ.comp (Lamp.singleHom x)) k ≠ 1 := by
      simpa using hk
    refine ⟨x, ?_, ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (φ.comp (Lamp.singleHom x)).ker inferInstance with h | h
      · exact h
      · exact absurd (by
          have : k ∈ (φ.comp (Lamp.singleHom x)).ker := by rw [h]; trivial
          exact MonoidHom.mem_ker.mp this) hkne
    · have hrange : (φ.comp (Lamp.singleHom x)).range
          = ((Lamp.singleHom (K := K) (X := X) x).range).map φ :=
        (MonoidHom.range_comp _ _)
      haveI : ((φ.comp (Lamp.singleHom x)).range).Normal := by
        rw [hrange]
        exact Subgroup.Normal.map inferInstance φ hφ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (φ.comp (Lamp.singleHom x)).range inferInstance with h | h
      · exact absurd (by
          have : (φ.comp (Lamp.singleHom x)) k ∈ (φ.comp (Lamp.singleHom x)).range :=
            ⟨k, rfl⟩
          rw [h, Subgroup.mem_bot] at this
          exact this) hkne
      · intro t
        have : t ∈ (φ.comp (Lamp.singleHom x)).range := by rw [h]; trivial
        exact this

end SimpleQuotient


/-! ## The lamp group determines the lamp -/

/-- **Section 52.2, transported.**  A simple lamp group is recoverable from the
lamp group it generates: if two lamp groups over simple lamps are isomorphic,
the lamps themselves are isomorphic.

This is what makes the hidden simple type of the invisible radical an invariant.
Combined with `alternatingGroup.isSimpleGroup`, the alternating lamps give
pairwise non-isomorphic invisible kernels behind one and the same visible
quotient. -/
theorem nonempty_mulEquiv_of_lamp_mulEquiv {K : Type u} [Group K]
    [IsSimpleGroup K] {L : Type u} [Group L] [IsSimpleGroup L] {X : Type v}
    [DecidableEq X] (hX : Nonempty X) (e : Lamp K X ≃* Lamp L X) :
    Nonempty (K ≃* L) := by
  classical
  haveI := hX
  obtain ⟨x₀⟩ := hX
  set φ : Lamp K X →* L := (evalHom x₀).comp e.toMonoidHom with hφ
  have hsurj : Function.Surjective φ := by
    intro l
    refine ⟨e.symm (Lamp.single x₀ l), ?_⟩
    show (evalHom x₀) (e (e.symm (Lamp.single x₀ l))) = l
    rw [MulEquiv.apply_symm_apply]
    exact Lamp.single_apply_self x₀ l
  obtain ⟨y, hinj, hsur⟩ := exists_site_bijective_of_simple_quotient φ hsurj
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, hsur⟩⟩


/-- **Section 52.3, algebraic core.**  The alternating lamps give pairwise
non-isomorphic lamp groups.  Since the lamp subgroup is the invisible radical of
the corresponding wreath product, this is what makes the family of examples
pairwise distinguishable even though their visible quotients agree. -/
theorem alternating_lamp_not_mulEquiv {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n)
    (hmn : m ≠ n) {X : Type v} [DecidableEq X] (hX : Nonempty X) :
    IsEmpty (Lamp (alternatingGroup (Fin m)) X ≃*
      Lamp (alternatingGroup (Fin n)) X) := by
  classical
  haveI := hX
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  refine ⟨fun e => ?_⟩
  obtain ⟨ee⟩ := nonempty_mulEquiv_of_lamp_mulEquiv hX e
  have hcard : Nat.card (alternatingGroup (Fin m))
      = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr ee.toEquiv
  have h2 : Nat.card (Equiv.Perm (Fin m)) = Nat.card (Equiv.Perm (Fin n)) := by
    rw [← two_mul_nat_card_alternatingGroup, ← two_mul_nat_card_alternatingGroup,
      hcard]
  have hfac : Nat.factorial m = Nat.factorial n := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h2
  rcases lt_trichotomy m n with h | h | h
  · have := (Nat.factorial_lt (show 0 < m by omega)).mpr h
    omega
  · exact hmn h
  · have := (Nat.factorial_lt (show 0 < n by omega)).mpr h
    omega

end GroupApproximation
