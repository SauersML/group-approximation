import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.TowerLocalize
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiFragment
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Window cylinders of a subshift

For a subshift `S` with shift `T`, `(T x)_n = x_{n+1}`, and `z : ℤ → A`, the window cylinder
`cyl S z a b` is the set of points agreeing with `z` on `[a, b]`.

* `subshiftHomeo_zpow_val`: `((T ^ k) x)_n = x_{k+n}`.
* `mem_cyl_zpow_iff`, `mem_zpow_cyl_iff`, `mem_cyl_iff_zpow_one`: shifting a cylinder shifts
  its window.
* `exists_sepRadius`: for an infinite minimal subshift and each `p` there is `R` such that no
  point agrees with its `e`-shift (`0 < |e| ≤ p`) on a window of length `2R + 1`. This is the
  compactness form of aperiodicity.
* `cyl_sepK`: so cylinders on windows of length at least `2R + 1` return to themselves after no
  `d` steps with `0 < |d| ≤ p` (`SepK`).
* `cyl_cross`: the cylinders `cyl z a c` and `cyl (z (1 + ·)) a c` meet their `d`-shifts only
  for `d = 1` (`|d| ≤ 4`).
* `mem_cyl_succ_iff`: `cyl z a (c+1) = {x ∈ cyl z a c | T x ∈ cyl (z (1 + ·)) a c}`.
* `exists_cyl_radius`: a clopen set is a union of cylinders on `[-r, r]` for all large `r`.
* `threeCycle_mem_of_cyl`: a three-cycle splits into the three-cycles on the cylinders of one
  radius.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.Full.StepanovMatui.Matui
open SymbolicDynamics.FullShift

variable {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)

/-- The window cylinder of `z` on `[a, b]`. -/
def cyl (z : ℤ → A) (a b : ℤ) : Set S.carrier := {x | ∀ n, a ≤ n → n ≤ b → x.1 n = z n}

theorem mem_cyl {z : ℤ → A} {a b : ℤ} {x : S.carrier} :
    x ∈ cyl S z a b ↔ ∀ n, a ≤ n → n ≤ b → x.1 n = z n := Iff.rfl

theorem cyl_eq_of_eq {z z' : ℤ → A} (h : ∀ n, z n = z' n) (a b : ℤ) :
    cyl S z a b = cyl S z' a b := by
  rw [funext h]

/-- The shift acts on coordinates by `((T ^ k) x)_n = x_{k + n}`. -/
theorem subshiftHomeo_zpow_val (k : ℤ) (x : S.carrier) (n : ℤ) :
    ((SimpleKazhdanSofic.subshiftHomeo S ^ k) x).1 n = x.1 (k + n) := by
  induction k using Int.induction_on generalizing x n with
  | zero => rw [zpow_zero, Homeomorph.one_apply, zero_add]
  | succ i ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih]
    show x.1 (1 + ((i : ℤ) + n)) = x.1 ((i : ℤ) + 1 + n)
    exact congrArg x.1 (by ring)
  | pred i ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, ih, Homeomorph.inv_apply]
    show x.1 (-1 + (-(i : ℤ) + n)) = x.1 (-(i : ℤ) - 1 + n)
    exact congrArg x.1 (by ring)

theorem toEquiv_zpow_val (k : ℤ) (x : S.carrier) (n : ℤ) :
    (((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ k) x).1 n = x.1 (k + n) := by
  rw [toEquiv_zpow_apply, subshiftHomeo_zpow_val]

theorem isClopen_cyl [DiscreteTopology A] (z : ℤ → A) (a b : ℤ) : IsClopen (cyl S z a b) := by
  have e : cyl S z a b = ⋂ n ∈ Finset.Icc a b, {x : S.carrier | x.1 n = z n} := by
    ext x
    simp only [mem_cyl, Set.mem_iInter, Finset.mem_Icc, Set.mem_setOf_eq]
    exact ⟨fun h n hn => h n hn.1 hn.2, fun h n h1 h2 => h n ⟨h1, h2⟩⟩
  rw [e]
  refine isClopen_biInter_finset fun n _ => ?_
  exact (isClopen_discrete {z n}).preimage ((continuous_apply n).comp continuous_subtype_val)

/-- Shifting a cylinder shifts its window. -/
theorem mem_cyl_zpow_iff {z : ℤ → A} {a b : ℤ} (k : ℤ) (x : S.carrier) :
    x ∈ cyl S z a b ↔ ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ k) x ∈
      cyl S (fun n => z (k + n)) (a - k) (b - k) := by
  simp only [mem_cyl, toEquiv_zpow_val]
  constructor
  · intro h n h1 h2
    exact h (k + n) (by omega) (by omega)
  · intro h n h1 h2
    have := h (n - k) (by omega) (by omega)
    rwa [show k + (n - k) = n by ring] at this

theorem mem_zpow_cyl_iff {z : ℤ → A} {a b : ℤ} (k : ℤ) (x : S.carrier) :
    x ∈ cyl S (fun n => z (n - k)) (a + k) (b + k) ↔
      ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ k) x ∈ cyl S z a b := by
  simp only [mem_cyl, toEquiv_zpow_val]
  constructor
  · intro h n h1 h2
    have := h (k + n) (by omega) (by omega)
    rwa [show k + n - k = n by ring] at this
  · intro h n h1 h2
    have := h (n - k) (by omega) (by omega)
    rwa [show k + (n - k) = n by ring] at this

theorem mem_cyl_iff_zpow_one {z : ℤ → A} {a c : ℤ} (x : S.carrier) :
    x ∈ cyl S z a (c + 1) ↔ ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ (1 : ℤ)) x ∈
      cyl S (fun n => z (1 + n)) (a - 1) c := by
  simp only [mem_cyl, toEquiv_zpow_val]
  constructor
  · intro h n h1 h2
    exact h (1 + n) (by omega) (by omega)
  · intro h n h1 h2
    have := h (n - 1) (by omega) (by omega)
    rwa [show 1 + (n - 1) = n by ring] at this

/-- `cyl z a (c + 1)` is the set of points of `cyl z a c` whose shift lies in
`cyl (z (1 + ·)) a c`. -/
theorem mem_cyl_succ_iff {z : ℤ → A} {a c : ℤ} (hac : a ≤ c) (x : S.carrier) :
    x ∈ cyl S z a (c + 1) ↔ x ∈ cyl S z a c ∧
      (SimpleKazhdanSofic.subshiftHomeo S).toEquiv x ∈ cyl S (fun n => z (1 + n)) a c := by
  constructor
  · intro hx
    refine ⟨fun n h1 h2 => hx n h1 (by omega), fun n h1 h2 => ?_⟩
    show x.1 (1 + n) = z (1 + n)
    exact hx (1 + n) (by omega) (by omega)
  · rintro ⟨h1, h2⟩ n hn1 hn2
    by_cases hn : n ≤ c
    · exact h1 n hn1 hn
    · have h := h2 c hac le_rfl
      have hnc : n = 1 + c := by omega
      rw [hnc]
      exact h

/-! ## Aperiodicity with a uniform radius -/

/-- No point agrees with its `e`-shift (`0 < |e| ≤ p`) on a window of length `2R + 1`. -/
def SepRadius (p R : ℕ) : Prop :=
  ∀ x : S.carrier, ∀ e : ℤ, e ≠ 0 → -(p : ℤ) ≤ e → e ≤ p → ∀ c : ℤ,
    ∃ m : ℤ, c - R ≤ m ∧ m ≤ c + R ∧ x.1 (e + m) ≠ x.1 m

theorem exists_sepRadius [DiscreteTopology A] [Finite A] (hinf : Infinite S.carrier)
    (hmin : SimpleKazhdanSofic.IsMinimal S) (p : ℕ) : ∃ R : ℕ, SepRadius S p R := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  have hone : ∀ e : ℤ, e ≠ 0 → ∃ R : ℕ, ∀ x : S.carrier, ∃ m : ℤ, -(R : ℤ) ≤ m ∧ m ≤ R ∧
      x.1 (e + m) ≠ x.1 m := by
    intro e he
    have hfree : ∀ x : S.carrier, ∃ m : ℤ, x.1 (e + m) ≠ x.1 m := by
      intro x
      by_contra hc
      push Not at hc
      apply SK05.subshiftHomeo_zpow_apply_ne_self S hinf hmin he x
      apply Subtype.ext
      funext m
      rw [subshiftHomeo_zpow_val]
      exact hc m
    let O : ℕ → Set S.carrier := fun R =>
      {x | ∃ m : ℤ, -(R : ℤ) ≤ m ∧ m ≤ R ∧ x.1 (e + m) ≠ x.1 m}
    have hO : ∀ R, IsOpen (O R) := by
      intro R
      have e2 : O R = ⋃ m ∈ Finset.Icc (-(R : ℤ)) R, {x : S.carrier | x.1 (e + m) ≠ x.1 m} := by
        ext x
        simp only [O, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
        exact ⟨fun ⟨m, h1, h2, h3⟩ => ⟨m, ⟨h1, h2⟩, h3⟩, fun ⟨m, ⟨h1, h2⟩, h3⟩ => ⟨m, h1, h2, h3⟩⟩
      rw [e2]
      exact isOpen_iUnion fun m => isOpen_iUnion fun _ =>
        isOpen_ne_fun ((continuous_apply (e + m)).comp continuous_subtype_val)
          ((continuous_apply m).comp continuous_subtype_val)
    have hcover : (Set.univ : Set S.carrier) ⊆ ⋃ R, O R := by
      intro x _
      obtain ⟨m, hm⟩ := hfree x
      refine Set.mem_iUnion.mpr ⟨m.natAbs, ?_⟩
      simp only [O, Set.mem_setOf_eq]
      exact ⟨m, by omega, by omega, hm⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO hcover
    refine ⟨t.sup id, fun x => ?_⟩
    obtain ⟨R, hRt, hxR⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    simp only [O, Set.mem_setOf_eq] at hxR
    obtain ⟨m, h1, h2, h3⟩ := hxR
    have hR : R ≤ t.sup id := Finset.le_sup (f := id) hRt
    exact ⟨m, by omega, by omega, h3⟩
  choose! Rf hRf using hone
  refine ⟨(Finset.Icc (-(p : ℤ)) p).sup Rf, fun x e he h1 h2 c => ?_⟩
  obtain ⟨m', hm1, hm2, hm3⟩ := hRf e he ((SimpleKazhdanSofic.subshiftHomeo S ^ c) x)
  have hle : Rf e ≤ (Finset.Icc (-(p : ℤ)) p).sup Rf :=
    Finset.le_sup (f := Rf) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  refine ⟨c + m', by omega, by omega, ?_⟩
  rw [subshiftHomeo_zpow_val, subshiftHomeo_zpow_val] at hm3
  rwa [show e + (c + m') = c + (e + m') by ring]

theorem SepRadius.mono {p q R : ℕ} (h : SepRadius S p R) (hqp : q ≤ p) : SepRadius S q R :=
  fun x e he h1 h2 c => h x e he (by omega) (by omega) c

/-- Long cylinders do not return to themselves within `p` steps. -/
theorem cyl_sepK {p R : ℕ} (hR : SepRadius S p R) {z : ℤ → A} {a b : ℤ}
    (hab : a + 2 * (R : ℤ) ≤ b) :
    SepK (SimpleKazhdanSofic.subshiftHomeo S).toEquiv (cyl S z a b) p := by
  intro x hx d hd h1 h2 hmem
  obtain ⟨m, hm1, hm2, hm3⟩ := hR x d hd h1 h2 (a + R)
  apply hm3
  have e1 := hmem m (by omega) (by omega)
  have e2 := hx m (by omega) (by omega)
  rw [toEquiv_zpow_val] at e1
  rw [e1, e2]

/-- `cyl z a c` meets the `d`-shift of `cyl (z (1 + ·)) a c` only for `d = 1`, `|d| ≤ 4`. -/
theorem cyl_cross {p R : ℕ} (hR : SepRadius S p R) (hp : 5 ≤ p) {z : ℤ → A} {a c : ℤ}
    (hac : a + 1 + 2 * (R : ℤ) ≤ c) :
    ∀ x ∈ cyl S z a c, ∀ d : ℤ, -4 ≤ d → d ≤ 4 → d ≠ 1 →
      ((SimpleKazhdanSofic.subshiftHomeo S).toEquiv ^ d) x ∉ cyl S (fun n => z (1 + n)) a c := by
  intro x hx d h1 h2 hd hmem
  obtain ⟨m, hm1, hm2, hm3⟩ := hR x (d - 1) (by omega) (by omega) (by omega) (a + 1 + R)
  apply hm3
  have e1 := hmem (m - 1) (by omega) (by omega)
  beta_reduce at e1
  rw [toEquiv_zpow_val] at e1
  have e2 := hx m (by omega) (by omega)
  rw [show d - 1 + m = d + (m - 1) by ring, e1, show 1 + (m - 1) = m by ring, e2]

/-! ## Clopen sets as unions of cylinders -/

theorem exists_cyl_radius [DiscreteTopology A] [Finite A] {C : Set S.carrier} (hC : IsClopen C) :
    ∃ r₀ : ℕ, ∀ y ∈ C, ∀ r : ℕ, r₀ ≤ r → cyl S y.1 (-(r : ℤ)) r ⊆ C := by
  haveI := SimpleKazhdanSofic.compactSpace_carrier S
  have hloc : ∀ y ∈ C, ∃ r : ℕ, cyl S y.1 (-(r : ℤ)) r ⊆ C := by
    intro y hy
    obtain ⟨O, hO, hOC⟩ := isOpen_induced_iff.mp hC.isOpen
    have hyO : y.1 ∈ O := by
      rw [← hOC] at hy
      exact hy
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hO y.1 hyO
    refine ⟨I.sup Int.natAbs, fun x hx => ?_⟩
    rw [← hOC]
    show x.1 ∈ O
    apply hIu
    intro n hn
    have hn' : n ∈ I := Finset.mem_coe.mp hn
    have hnr : n.natAbs ≤ I.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hn'
    have hxn := hx n (by omega) (by omega)
    rw [hxn]
    exact (hu n hn').2
  choose! rf hrf using hloc
  obtain ⟨t, htC, hcover⟩ := hC.isClosed.isCompact.elim_nhds_subcover
    (fun y => cyl S y.1 (-(rf y : ℤ)) (rf y))
    (fun y _ => (isClopen_cyl S _ _ _).isOpen.mem_nhds (fun n _ _ => rfl))
  refine ⟨t.sup rf, fun y hy r hr x hx => ?_⟩
  obtain ⟨y', hy't, hyy'⟩ := Set.mem_iUnion₂.mp (hcover hy)
  have hle : rf y' ≤ t.sup rf := Finset.le_sup (f := rf) hy't
  apply hrf y' (htC y' hy't)
  intro n h1 h2
  rw [hx n (by omega) (by omega)]
  exact hyy' n h1 h2

/-- A three-cycle is the product of its restrictions to the cylinders of one radius. -/
theorem threeCycle_mem_of_cyl [Finite A] {G : Subgroup (Equiv.Perm S.carrier)}
    {f : Equiv.Perm S.carrier} {U : Set S.carrier} (hdat : IsThreeCycleDatum f U) (r : ℕ)
    (hsub : ∀ y ∈ U, cyl S y.1 (-(r : ℤ)) r ⊆ U)
    (hmem : ∀ y ∈ U, threeCycle f (cyl S y.1 (-(r : ℤ)) r) ∈ G) : threeCycle f U ∈ G := by
  classical
  set P : Set (Set S.carrier) := (fun y : U => cyl S y.1.1 (-(r : ℤ)) r) '' Set.univ
  have hfin : P.Finite := by
    refine Set.Finite.subset (Set.finite_range fun w : (Finset.Icc (-(r : ℤ)) r → A) =>
      {x : S.carrier | ∀ n (hn : n ∈ Finset.Icc (-(r : ℤ)) r), x.1 n = w ⟨n, hn⟩}) ?_
    rintro _ ⟨y, -, rfl⟩
    refine ⟨fun n => y.1.1 n, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, mem_cyl, Finset.mem_Icc]
    exact ⟨fun h n h1 h2 => h n ⟨h1, h2⟩, fun h n hn => h n hn.1 hn.2⟩
  have key : ∀ s : Finset (Set S.carrier), (∀ Q ∈ s, Q ∈ P) →
      threeCycle f (⋃ Q ∈ s, Q) ∈ G := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have e : (⋃ Q ∈ (∅ : Finset (Set S.carrier)), Q) = ∅ := by simp
      rw [e, threeCycle_empty]
      exact G.one_mem
    | insert Q s hQs ih =>
      intro hs
      have hs' : ∀ Q' ∈ s, Q' ∈ P := fun Q' h => hs Q' (Finset.mem_insert_of_mem h)
      obtain ⟨y, -, rfl⟩ := hs _ (Finset.mem_insert_self _ s)
      rw [Finset.set_biUnion_insert]
      have hQU : cyl S y.1.1 (-(r : ℤ)) r ⊆ U := hsub y.1 y.2
      have hsU : (⋃ Q' ∈ s, Q') ⊆ U := by
        intro x hx
        obtain ⟨Q', hQ's, hxQ'⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨y', -, rfl⟩ := hs' Q' hQ's
        exact hsub y'.1 y'.2 hxQ'
      have hdisj : Disjoint (cyl S y.1.1 (-(r : ℤ)) r) (⋃ Q' ∈ s, Q') := by
        rw [Set.disjoint_left]
        intro x hx hx'
        obtain ⟨Q', hQ's, hxQ'⟩ := Set.mem_iUnion₂.mp hx'
        obtain ⟨y', -, rfl⟩ := hs' Q' hQ's
        apply hQs
        have hcyl : cyl S y'.1.1 (-(r : ℤ)) r = cyl S y.1.1 (-(r : ℤ)) r := by
          ext w
          simp only [mem_cyl]
          constructor
          · intro h n h1 h2
            rw [h n h1 h2, ← hxQ' n h1 h2, hx n h1 h2]
          · intro h n h1 h2
            rw [h n h1 h2, ← hx n h1 h2, hxQ' n h1 h2]
        show cyl S y.1.1 (-(r : ℤ)) r ∈ s
        rw [← hcyl]
        exact hQ's
      rw [threeCycle_union hdat hQU hsU hdisj]
      exact G.mul_mem (hmem y.1 y.2) (ih hs')
  have hU : (⋃ Q ∈ hfin.toFinset, Q) = U := by
    ext x
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨Q, ⟨y, -, rfl⟩, hx⟩
      exact hsub y.1 y.2 hx
    · intro hx
      exact ⟨_, ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩, fun n _ _ => rfl⟩
  rw [← hU]
  exact key hfin.toFinset fun Q hQ => (Set.Finite.mem_toFinset hfin).mp hQ

end GroupApproximation.Full.SKTFG

#audit_axioms GroupApproximation.Full.SKTFG.exists_sepRadius
#audit_axioms GroupApproximation.Full.SKTFG.exists_cyl_radius
#audit_axioms GroupApproximation.Full.SKTFG.threeCycle_mem_of_cyl
