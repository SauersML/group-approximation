import GroupApproximation.KTheory.K1Functorial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVUnivLocK2.B5Transfer

/-!
# The canonical model of stable `K₂` (lane LVUnivLocK2, B5)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, input W1.
`B5Transfer` translates exactness statements about a model `StableK2Model R A` of stable `K₂(R)`
into finite-stage base surjectivity.  This file builds the canonical model, the sequential
colimit of the groups `K₂(n, R) = ker (St_n(R) → E_n(R))` along the padding maps
`indexMap (Fin.castLEEmb h)`:

* `K2Stage R n`, `k2Pad`, `k2Tower R`: the tower `n ↦ K₂(n, R)`;
* `StableK2Group R`: its colimit (`GroupTower.Colim`), i.e. stable Steinberg `K₂(R)`;
* `canonicalModel R : StableK2Model R (StableK2Group R)`;
* `stableK2Map f : StableK2Group R →* StableK2Group S`, induced by `ringMap f`, natural for
  the canonical models (`natural_stableK2Map`);
* `stableK2BaseSurjective_iff_surjective_stableK2Map`: finite-stage base surjectivity of `f`
  is surjectivity of `stableK2Map f`.
-/

namespace GroupApproximation.Full.LVUnivLocK2

open SteinbergGroup

noncomputable section

section Tower

variable (R : Type*) [Ring R]

/-- Level `n` of the stable `K₂` tower: `K₂(n, R) = ker (St_n(R) → E_n(R))`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
abbrev K2Stage (n : ℕ) : Type _ :=
  ↥(projection (I := Fin n) (R := R)).ker

variable {R}

/-- Padding `K₂(n, R) → K₂(m, R)` for `n ≤ m`, the restriction of `indexMap (Fin.castLEEmb h)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def k2Pad {n m : ℕ} (h : n ≤ m) : K2Stage R n →* K2Stage R m where
  toFun k := ⟨indexMap (Fin.castLEEmb h) k.1,
    MonoidHom.mem_ker.mpr (LVH2GL3.projection_indexMap_eq_one _ (MonoidHom.mem_ker.mp k.2))⟩
  map_one' := Subtype.ext (by
    change indexMap (Fin.castLEEmb h) (1 : SteinbergGroup (Fin n) R) = 1
    exact map_one _)
  map_mul' k l := Subtype.ext (by
    change indexMap (Fin.castLEEmb h) (k.1 * l.1) =
      indexMap (Fin.castLEEmb h) k.1 * indexMap (Fin.castLEEmb h) l.1
    exact map_mul _ _ _)

/-- The underlying Steinberg element of a padded `K₂` element.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem k2Pad_val {n m : ℕ} (h : n ≤ m) (k : K2Stage R n) :
    ((k2Pad h k : K2Stage R m) : SteinbergGroup (Fin m) R) =
      indexMap (Fin.castLEEmb h) (k : SteinbergGroup (Fin n) R) :=
  rfl

variable (R)

/-- The tower `n ↦ K₂(n, R)` with the padding maps.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def k2Tower : GroupTower (K2Stage R) where
  map h := k2Pad h
  map_self := by
    intro n h k
    refine Subtype.ext ?_
    change indexMap (Fin.castLEEmb h) k.1 = k.1
    exact LVH2GL3.indexMap_castLEEmb_self h k.1
  map_trans := by
    intro n m p h₁ h₂ k
    refine Subtype.ext ?_
    change indexMap (Fin.castLEEmb h₂) (indexMap (Fin.castLEEmb h₁) k.1) =
      indexMap (Fin.castLEEmb (h₁.trans h₂)) k.1
    exact LVH2GL3.indexMap_castLEEmb_castLEEmb h₁ h₂ k.1

/-- **Stable Steinberg `K₂(R)`**: the colimit of `K₂(n, R)` along the padding maps.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
abbrev StableK2Group : Type _ := (k2Tower R).Colim

/-- The canonical model of stable `K₂(R)`: the class of `k ∈ K₂(n, R)` is its image in the
colimit.  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def canonicalModel : StableK2Model R (StableK2Group R) where
  cls n k hk := (k2Tower R).mkAt n ⟨k, MonoidHom.mem_ker.mpr hk⟩
  cls_indexMap _ _ h k hk := (k2Tower R).mkAt_map h ⟨k, MonoidHom.mem_ker.mpr hk⟩
  exists_cls a := by
    obtain ⟨n, x, rfl⟩ := (k2Tower R).exists_mkAt a
    exact ⟨n, x.1, MonoidHom.mem_ker.mp x.2, rfl⟩
  exists_indexMap_eq n m k l hk hl hkl := by
    have hrel : (k2Tower R).Rel ⟨n, ⟨k, MonoidHom.mem_ker.mpr hk⟩⟩
        ⟨m, ⟨l, MonoidHom.mem_ker.mpr hl⟩⟩ :=
      Quotient.exact (show Quotient.mk (k2Tower R).setoid ⟨n, ⟨k, MonoidHom.mem_ker.mpr hk⟩⟩ =
        Quotient.mk (k2Tower R).setoid ⟨m, ⟨l, MonoidHom.mem_ker.mpr hl⟩⟩ from hkl)
    obtain ⟨N, hn, hm, e⟩ := hrel
    exact ⟨N, hn, hm, congrArg Subtype.val e⟩

/-- The class map of the canonical model.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem canonicalModel_cls (n : ℕ) (k : SteinbergGroup (Fin n) R) (hk : projection k = 1) :
    (canonicalModel R).cls n k hk = (k2Tower R).mkAt n ⟨k, MonoidHom.mem_ker.mpr hk⟩ :=
  rfl

end Tower

section Functoriality

variable {R S : Type*} [Ring R] [Ring S]

/-- A coefficient map on `K₂(n, -)`: the restriction of `ringMap f`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def k2RingMap (f : R →+* S) (n : ℕ) : K2Stage R n →* K2Stage S n where
  toFun k := ⟨ringMap f k.1,
    MonoidHom.mem_ker.mpr (projection_ringMap_eq_one f (MonoidHom.mem_ker.mp k.2))⟩
  map_one' := Subtype.ext (by
    change ringMap f (1 : SteinbergGroup (Fin n) R) = 1
    exact map_one _)
  map_mul' k l := Subtype.ext (by
    change ringMap f (k.1 * l.1) = ringMap f k.1 * ringMap f l.1
    exact map_mul _ _ _)

/-- The underlying Steinberg element of `k2RingMap`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem k2RingMap_val (f : R →+* S) (n : ℕ) (k : K2Stage R n) :
    ((k2RingMap f n k : K2Stage S n) : SteinbergGroup (Fin n) S) =
      ringMap f (k : SteinbergGroup (Fin n) R) :=
  rfl

/-- Coefficient maps commute with padding on `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem k2RingMap_map (f : R →+* S) {n m : ℕ} (h : n ≤ m) (k : K2Stage R n) :
    k2RingMap f m ((k2Tower R).map h k) = (k2Tower S).map h (k2RingMap f n k) := by
  refine Subtype.ext ?_
  change ringMap f (indexMap (Fin.castLEEmb h) k.1) =
    indexMap (Fin.castLEEmb h) (ringMap f k.1)
  exact (LVStableK2.indexMap_ringMap (Fin.castLEEmb h) f k.1).symm

/-- The homomorphism of stable `K₂` induced by a ring homomorphism.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def stableK2Map (f : R →+* S) : StableK2Group R →* StableK2Group S :=
  GroupTower.colimMap (k2Tower R) (k2Tower S) (k2RingMap f) fun h k => k2RingMap_map f h k

/-- `stableK2Map f` on the class of a finite-stage element.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Map_mkAt (f : R →+* S) (n : ℕ) (k : K2Stage R n) :
    stableK2Map f ((k2Tower R).mkAt n k) = (k2Tower S).mkAt n (k2RingMap f n k) :=
  rfl

/-- `stableK2Map f` is natural for the canonical models.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem natural_stableK2Map (f : R →+* S) :
    (canonicalModel R).Natural (canonicalModel S) f (stableK2Map f) :=
  fun _ _ _ => rfl

/-- **B5, canonical form.**  Finite-stage base surjectivity of `f` is surjectivity of the induced
map `stableK2Map f : K₂(R) → K₂(S)` on stable Steinberg `K₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2BaseSurjective_iff_surjective_stableK2Map (f : R →+* S) :
    LVStableK2.StableK2BaseSurjective f ↔ Function.Surjective (stableK2Map f) :=
  stableK2BaseSurjective_iff_surjective f (canonicalModel R) (canonicalModel S) (stableK2Map f)
    (natural_stableK2Map f)

end Functoriality

end

end GroupApproximation.Full.LVUnivLocK2
