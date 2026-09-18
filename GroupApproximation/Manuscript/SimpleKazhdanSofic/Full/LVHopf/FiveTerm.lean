import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVHopf.Multiplier

/-!
# The five-term exact sequence in Hopf form (lane LVHopf, leaf T1b.iv)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  The route there goes through
`K₂(4, L_{𝔽₂}(1,2)) = ⊥` (Khanh arXiv:2609.08428), which uses low-dimensional group homology.
This file proves the five-term exact sequence of a normal subgroup `N ⊴ G`
(Stallings 1965, Stammbach; Brown, *Cohomology of Groups*, II.5, exercise 6):

`H₂(G) → H₂(G ⧸ N) → N ⧸ [G, N] → H₁(G) → H₁(G ⧸ N) → 0`,

stated purely group-theoretically.  Fix a surjection `f : F ↠ G` with `R = ker f` (for a free
presentation, `hopfMultiplier f` is `H₂(G; ℤ)` by Hopf's formula), and put `S = ker (F ↠ G ⧸ N)`.

* `H₂(G) = hopfMultiplier f ⊆ F ⧸ [F, R]` and `H₂(G ⧸ N) = hopfMultiplier (mk' N ∘ f) ⊆ F ⧸ [F, S]`;
* `N ⧸ [G, N]` is the image of `N` in `G ⧸ [G, N]`;
* `H₁(G) = Abelianization G` and `H₁(G ⧸ N) = Abelianization (G ⧸ N)`.

The maps are `fiveTermH2Map` (induced by `id : F → F`), `fiveTermConnectingMap` (induced by `f`),
`fiveTermAbelianizationMap` (induced by `Abelianization.of`) and `Abelianization.map (mk' N)`.
Exactness at each spot is the subgroup identity "image = kernel restricted to the next term":
`fiveTerm_exact_H2Q`, `fiveTerm_exact_N`, `fiveTerm_exact_H1`, and `fiveTerm_surjective_H1`.
-/

namespace GroupApproximation.Full.LVHopf

open scoped commutatorElement

universe u v

variable {F : Type u} {G : Type v} [Group F] [Group G]

/-- The kernel of `F → G → G ⧸ N` is `f⁻¹ N`. -/
theorem ker_comp_mk' (f : F →* G) (N : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).comp f).ker = N.comap f := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem mem_ker_comp_mk' (f : F →* G) (N : Subgroup G) [N.Normal] {x : F} :
    x ∈ ((QuotientGroup.mk' N).comp f).ker ↔ f x ∈ N := by
  rw [ker_comp_mk', Subgroup.mem_comap]

/-- For surjective `f`, the image of `S = ker (F → G ⧸ N)` is `N`. -/
theorem map_ker_comp_mk' (f : F →* G) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).comp f).ker.map f = N := by
  rw [ker_comp_mk', Subgroup.map_comap_eq_self_of_surjective hf]

theorem ker_le_ker_comp_mk' (f : F →* G) (N : Subgroup G) [N.Normal] :
    f.ker ≤ ((QuotientGroup.mk' N).comp f).ker.comap (MonoidHom.id F) := by
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.id_apply, mem_ker_comp_mk', MonoidHom.mem_ker.mp hx]
  exact one_mem N

/-- The map `H₂(G) → H₂(G ⧸ N)`, induced on `F ⧸ [F, R] → F ⧸ [F, S]` by the identity of `F`. -/
def fiveTermH2Map (f : F →* G) (N : Subgroup G) [N.Normal] :
    F ⧸ ⁅(⊤ : Subgroup F), f.ker⁆ →*
      F ⧸ ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ :=
  hopfQuotientMap f ((QuotientGroup.mk' N).comp f) (MonoidHom.id F) (ker_le_ker_comp_mk' f N)

theorem fiveTermH2Map_mk' (f : F →* G) (N : Subgroup G) [N.Normal] (x : F) :
    fiveTermH2Map f N (QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ x) =
      QuotientGroup.mk' ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ x :=
  rfl

theorem commutator_ker_comp_mk'_le (f : F →* G) (N : Subgroup G) [N.Normal] :
    ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ ≤
      ⁅(⊤ : Subgroup G), N⁆.comap f := by
  rw [Subgroup.commutator_le]
  intro a _ b hb
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (f a))
    ((mem_ker_comp_mk' f N).mp hb)

/-- The connecting map `H₂(G ⧸ N) → N ⧸ [G, N]`, induced on `F ⧸ [F, S] → G ⧸ [G, N]` by `f`. -/
def fiveTermConnectingMap (f : F →* G) (N : Subgroup G) [N.Normal] :
    F ⧸ ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ →* G ⧸ ⁅(⊤ : Subgroup G), N⁆ :=
  QuotientGroup.map ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ ⁅(⊤ : Subgroup G), N⁆ f
    (commutator_ker_comp_mk'_le f N)

theorem fiveTermConnectingMap_mk' (f : F →* G) (N : Subgroup G) [N.Normal] (x : F) :
    fiveTermConnectingMap f N
        (QuotientGroup.mk' ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ x) =
      QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆ (f x) :=
  rfl

/-- The map `N ⧸ [G, N] → H₁(G)`, induced on `G ⧸ [G, N] → Abelianization G` by `of`. -/
def fiveTermAbelianizationMap (N : Subgroup G) [N.Normal] :
    G ⧸ ⁅(⊤ : Subgroup G), N⁆ →* Abelianization G :=
  QuotientGroup.lift ⁅(⊤ : Subgroup G), N⁆ Abelianization.of
    (by rw [Abelianization.ker_of]; exact commutator_top_le_commutator N)

theorem fiveTermAbelianizationMap_mk' (N : Subgroup G) [N.Normal] (g : G) :
    fiveTermAbelianizationMap N (QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆ g) =
      Abelianization.of g :=
  rfl

/-- **Exactness at `H₂(G ⧸ N)`**: the kernel of `H₂(G ⧸ N) → N ⧸ [G, N]` is the image of `H₂(G)`.
(`simple_kazhdan_sofic_group.tex` l.733-735; five-term sequence.) -/
theorem fiveTerm_exact_H2Q (f : F →* G) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] :
    hopfMultiplier ((QuotientGroup.mk' N).comp f) ⊓ (fiveTermConnectingMap f N).ker =
      (hopfMultiplier f).map (fiveTermH2Map f N) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier ((QuotientGroup.mk' N).comp f)).mp hy1
    have hxc : x ∈ commutator F := (Subgroup.mem_inf.mp hx).2
    have h0 := MonoidHom.mem_ker.mp hy2
    rw [fiveTermConnectingMap_mk'] at h0
    have h1 : f x ∈ ⁅(⊤ : Subgroup G), N⁆ := (mk'_eq_one_iff ⁅(⊤ : Subgroup G), N⁆ (f x)).mp h0
    have h2 : f x ∈ ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆.map f := by
      rw [map_commutator_top_of_surjective f hf, map_ker_comp_mk' f hf N]
      exact h1
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp h2
    have hck : c⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    have hcc : c⁻¹ * x ∈ commutator F :=
      mul_mem (inv_mem (commutator_top_le_commutator ((QuotientGroup.mk' N).comp f).ker hc)) hxc
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), f.ker⁆ (c⁻¹ * x),
      (mem_hopfMultiplier f).mpr ⟨c⁻¹ * x, Subgroup.mem_inf.mpr ⟨hck, hcc⟩, rfl⟩, ?_⟩
    rw [fiveTermH2Map_mk', map_mul, map_inv,
      (mk'_eq_one_iff ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ c).mpr hc,
      inv_one, one_mul]
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier f).mp hz
    obtain ⟨hxk, hxc⟩ := Subgroup.mem_inf.mp hx
    have hxS : x ∈ ((QuotientGroup.mk' N).comp f).ker := by
      rw [mem_ker_comp_mk', MonoidHom.mem_ker.mp hxk]
      exact one_mem N
    rw [fiveTermH2Map_mk']
    refine Subgroup.mem_inf.mpr ⟨(mem_hopfMultiplier ((QuotientGroup.mk' N).comp f)).mpr
      ⟨x, Subgroup.mem_inf.mpr ⟨hxS, hxc⟩, rfl⟩, ?_⟩
    rw [MonoidHom.mem_ker, fiveTermConnectingMap_mk', MonoidHom.mem_ker.mp hxk, map_one]

/-- **Exactness at `N ⧸ [G, N]`**: the kernel of `N ⧸ [G, N] → H₁(G)` is the image of `H₂(G ⧸ N)`.
(`simple_kazhdan_sofic_group.tex` l.733-735; five-term sequence.) -/
theorem fiveTerm_exact_N (f : F →* G) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal] :
    N.map (QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆) ⊓ (fiveTermAbelianizationMap N).ker =
      (hopfMultiplier ((QuotientGroup.mk' N).comp f)).map (fiveTermConnectingMap f N) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy1
    have h0 := MonoidHom.mem_ker.mp hy2
    rw [fiveTermAbelianizationMap_mk', abelianization_of_eq_one_iff,
      ← map_commutator_of_surjective f hf] at h0
    obtain ⟨x, hxc, hxn⟩ := Subgroup.mem_map.mp h0
    have hxS : x ∈ ((QuotientGroup.mk' N).comp f).ker := by
      rw [mem_ker_comp_mk', hxn]
      exact hn
    refine Subgroup.mem_map.mpr
      ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup F), ((QuotientGroup.mk' N).comp f).ker⁆ x,
        (mem_hopfMultiplier ((QuotientGroup.mk' N).comp f)).mpr
          ⟨x, Subgroup.mem_inf.mpr ⟨hxS, hxc⟩, rfl⟩, ?_⟩
    rw [fiveTermConnectingMap_mk', hxn]
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := (mem_hopfMultiplier ((QuotientGroup.mk' N).comp f)).mp hz
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.mp hx
    rw [fiveTermConnectingMap_mk']
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem (QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆)
      ((mem_ker_comp_mk' f N).mp hxS), ?_⟩
    rw [MonoidHom.mem_ker, fiveTermAbelianizationMap_mk', abelianization_of_eq_one_iff]
    exact map_commutator_le f (Subgroup.mem_map_of_mem f hxc)

/-- **Exactness at `H₁(G)`**: the kernel of `H₁(G) → H₁(G ⧸ N)` is the image of `N ⧸ [G, N]`.
(`simple_kazhdan_sofic_group.tex` l.733-735; five-term sequence.) -/
theorem fiveTerm_exact_H1 (N : Subgroup G) [N.Normal] :
    (Abelianization.map (QuotientGroup.mk' N)).ker =
      (N.map (QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆)).map (fiveTermAbelianizationMap N) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨g, rfl⟩ := abelianization_of_surjective G z
    have h0 := MonoidHom.mem_ker.mp hz
    rw [Abelianization.map_of, abelianization_of_eq_one_iff,
      ← map_commutator_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)] at h0
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp h0
    have hn : c⁻¹ * g ∈ N := by
      rw [← mk'_eq_one_iff N (c⁻¹ * g), map_mul, map_inv, hcg, inv_mul_cancel]
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆ (c⁻¹ * g),
      Subgroup.mem_map_of_mem (QuotientGroup.mk' ⁅(⊤ : Subgroup G), N⁆) hn, ?_⟩
    rw [fiveTermAbelianizationMap_mk', map_mul, map_inv, (abelianization_of_eq_one_iff c).mpr hc,
      inv_one, one_mul]
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    rw [MonoidHom.mem_ker, fiveTermAbelianizationMap_mk', Abelianization.map_of,
      (mk'_eq_one_iff N n).mpr hn, map_one]

/-- **Exactness at `H₁(G ⧸ N)`**: `H₁(G) → H₁(G ⧸ N)` is surjective.
(`simple_kazhdan_sofic_group.tex` l.733-735; five-term sequence.) -/
theorem fiveTerm_surjective_H1 (N : Subgroup G) [N.Normal] :
    Function.Surjective (Abelianization.map (QuotientGroup.mk' N)) := by
  intro z
  obtain ⟨y, rfl⟩ := abelianization_of_surjective (G ⧸ N) z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact ⟨Abelianization.of g, Abelianization.map_of (QuotientGroup.mk' N) g⟩

/-- The image of `H₂(G)` lies in `H₂(G ⧸ N)`. -/
theorem fiveTermH2Map_map_le (f : F →* G) (N : Subgroup G) [N.Normal] :
    (hopfMultiplier f).map (fiveTermH2Map f N) ≤ hopfMultiplier ((QuotientGroup.mk' N).comp f) :=
  map_hopfMultiplier_le f ((QuotientGroup.mk' N).comp f) (MonoidHom.id F) (ker_le_ker_comp_mk' f N)

end GroupApproximation.Full.LVHopf
