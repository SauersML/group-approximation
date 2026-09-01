import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCLemma44OrientedCells
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GroupTheory.NormalClosureReducedProduct

/-!
# The exact reduced power diagram behind Hull's Lemma 4.9

The kernel-power conclusion of Hull's Lemma 4.9 has one elementary branch:
if the chosen power is already trivial, the correction is the identity.  In
the remaining branch, membership in the one-relator normal closure supplies a
least-area product of signed conjugates of that relator.  Flattening this
product produces the reduced power diagram formalized here.

The final geometric content of Lemma 4.9 is isolated as
`HullLemma49ShortestGeodesicPowerDiagramStatement`: under the published `C₁`
hypotheses, every oriented least-area diagram with its geodesic power boundary
admits the required kernel correction.  The last theorem proves that this
exact diagram statement implies the manuscript's quotient-free
`HullLemma49KernelPowerStatement`.
-/

namespace GroupApproximation
namespace HullSC

open RelatorDefectBudget
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Shortest representatives of quotient conjugacy classes -/

/-- `h` represents a conjugate of `g` modulo the normal subgroup `N`.

The explicit formula is the lift-level version of conjugacy in `G ⧸ N` and
is the form used in Hull's proof when a shortest word representing a conjugate
of the quotient element is selected. -/
def ConjugateModulo {G : Type u} [Group G]
    (N : Subgroup G) (g h : G) : Prop :=
  ∃ a k : G, k ∈ N ∧ h = a * g * a⁻¹ * k

namespace ConjugateModulo

theorem refl {G : Type u} [Group G] (N : Subgroup G) (g : G) :
    ConjugateModulo N g g := by
  exact ⟨1, 1, N.one_mem, by simp⟩

theorem trans {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h z : G} (hgh : ConjugateModulo N g h)
    (hhz : ConjugateModulo N h z) : ConjugateModulo N g z := by
  obtain ⟨a, k, hk, rfl⟩ := hgh
  obtain ⟨b, l, hl, rfl⟩ := hhz
  refine ⟨b * a, b * k * b⁻¹ * l, ?_, ?_⟩
  · exact N.mul_mem ((inferInstance : N.Normal).conj_mem k hk b) hl
  · group

/-- Membership of a positive power in a normal subgroup is invariant under
changing the lift inside a quotient conjugacy class. -/
theorem pow_mem {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h : G} {n : ℕ} (hgh : ConjugateModulo N g h)
    (hg : g ^ n ∈ N) : h ^ n ∈ N := by
  obtain ⟨a, k, hk, rfl⟩ := hgh
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hkker : k ∈ q.ker := by
    rwa [QuotientGroup.ker_mk']
  have hkq : q k = 1 := MonoidHom.mem_ker.mp hkker
  have hgker : g ^ n ∈ q.ker := by
    rwa [QuotientGroup.ker_mk']
  have hgq : q (g ^ n) = 1 := MonoidHom.mem_ker.mp hgker
  rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  simp only [map_pow, map_mul, map_inv]
  rw [hkq, mul_one]
  rw [conj_pow, ← map_pow, hgq, mul_one, mul_inv_cancel]

/-- A power correction for one lift transports back across quotient
conjugacy.  This is the exact algebraic step used after Hull chooses a shortest
representative of the quotient conjugacy class. -/
theorem correction {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {g h : G} {n : ℕ} (hgh : ConjugateModulo N g h)
    (hcorr : ∃ k ∈ N, (h * k) ^ n = 1) :
    ∃ k ∈ N, (g * k) ^ n = 1 := by
  obtain ⟨a, k₀, hk₀, rfl⟩ := hgh
  obtain ⟨k₁, hk₁, hpow⟩ := hcorr
  let k : G := a⁻¹ * (k₀ * k₁) * a
  have hk : k ∈ N := by
    dsimp [k]
    simpa only [inv_inv] using
      (inferInstance : N.Normal).conj_mem (k₀ * k₁) (N.mul_mem hk₀ hk₁) a⁻¹
  refine ⟨k, hk, ?_⟩
  have heq : g * k = a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) * a := by
    dsimp [k]
    group
  rw [heq]
  have hconjpow :
      (a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) * a) ^ n =
        a⁻¹ * ((a * g * a⁻¹ * k₀) * k₁) ^ n * a := by
    clear hpow
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ih]
        group
  rw [hconjpow, hpow, mul_one, inv_mul_cancel]

end ConjugateModulo

/-- `g` has least word length among all lifts of its quotient conjugacy
class. -/
def IsShortestModuloConjugacy {G : Type u} [Group G]
    (A : Set G) (N : Subgroup G) (g : G) : Prop :=
  ∀ h : G, ConjugateModulo N g h → wordNorm A g ≤ wordNorm A h

/-- Every quotient conjugacy class has a shortest lift, by well-ordering of
the natural-valued word length. -/
theorem exists_shortest_conjugateModulo {G : Type u} [Group G]
    (A : Set G) (N : Subgroup G) [N.Normal] (g : G) :
    ∃ h : G, ConjugateModulo N g h ∧ IsShortestModuloConjugacy A N h := by
  classical
  let P : ℕ → Prop := fun m ↦
    ∃ h : G, ConjugateModulo N g h ∧ wordNorm A h = m
  have hex : ∃ m, P m :=
    ⟨wordNorm A g, g, ConjugateModulo.refl N g, rfl⟩
  obtain ⟨h, hgh, hlength⟩ := Nat.find_spec hex
  refine ⟨h, hgh, ?_⟩
  intro y hhy
  have hgy : ConjugateModulo N g y := hgh.trans hhy
  have hy : P (wordNorm A y) := ⟨y, hgy, rfl⟩
  rw [hlength]
  exact Nat.find_min' hex hy

/-- A least-area algebraic van Kampen diagram whose boundary is the positive
power `g ^ n`.  Reducedness says that no nonempty consecutive block of cells
has trivial product. -/
structure Lemma49ReducedPowerDiagram {G : Type u} [Group G]
    (R : Set G) (g : G) (n : ℕ) where
  exponent_pos : 0 < n
  power_ne_one : g ^ n ≠ 1
  area : ℕ
  area_pos : 0 < area
  factors : List G
  factors_length : factors.length = area
  factors_prod : factors.prod = g ^ n
  factors_cells : ∀ x ∈ factors, IsSignedConjugate R x
  reduced : ∀ (pre mid suf : List G),
    factors = pre ++ mid ++ suf → mid ≠ [] → mid.prod ≠ 1
  no_cancelling_pair : ∀ (pre between suf : List G) (x y : G),
    factors = pre ++ x :: (between ++ y :: suf) →
      (between.prod)⁻¹ * x * between.prod * y ≠ 1

/-- A nontrivial power in a normal closure has a least-area reduced power
diagram, with no geometric or literature input. -/
theorem exists_lemma49ReducedPowerDiagram
    {G : Type u} [Group G] {R : Set G} {g : G} {n : ℕ}
    (hn : 0 < n) (hpow : g ^ n ∈ Subgroup.normalClosure R)
    (hne : g ^ n ≠ 1) :
    Nonempty (Lemma49ReducedPowerDiagram R g n) := by
  classical
  have hex : ∃ area : ℕ, IsRelatorProduct R area (g ^ n) :=
    exists_isRelatorProduct hpow
  let area : ℕ := Nat.find hex
  have hcertificate : IsRelatorProduct R area (g ^ n) := Nat.find_spec hex
  obtain ⟨factors, hlength, hprod, hcells⟩ := hcertificate.exists_flatten
  have harea_pos : 0 < area := by
    by_contra hnot
    have hzero : area = 0 := Nat.eq_zero_of_not_pos hnot
    have hcertificate0 : IsRelatorProduct R 0 (g ^ n) := by
      simpa only [hzero] using hcertificate
    exact hne hcertificate0.eq_one_of_index_zero
  have hminimal : ∀ {m : ℕ}, IsRelatorProduct R m (g ^ n) → area ≤ m := by
    intro m hm
    exact Nat.find_min' hex hm
  refine ⟨{
    exponent_pos := hn
    power_ne_one := hne
    area := area
    area_pos := harea_pos
    factors := factors
    factors_length := hlength
    factors_prod := hprod
    factors_cells := hcells
    reduced := no_trivial_subproduct_of_minimal hlength hprod hcells hminimal
    no_cancelling_pair :=
      no_cancelling_pair_of_minimal hlength hprod hcells hminimal }⟩

/-! ## Oriented cells for the power diagram -/

/-- A signed conjugate of the singleton relator can be oriented by a member of
its symmetrized family. -/
theorem exists_lemma49OrientedCell
    {G : Type u} [Group G] {Λ : Type w}
    (v : List (GGT.RelLetter G Λ)) {x : G}
    (hx : IsSignedConjugate
      ({GGT.RelLetter.listVal v} : Set G) x) :
    ∃ C : Lemma44OrientedRelatorCell (RelWord.symmetrized v), C.value = x := by
  obtain ⟨c, r, hr, hx | hx⟩ := hx
  · have hr' : r = GGT.RelLetter.listVal v := Set.mem_singleton_iff.mp hr
    subst r
    exact ⟨⟨c, v, RelWord.self_mem_symmetrized v⟩, hx.symm⟩
  · have hr' : r = GGT.RelLetter.listVal v := Set.mem_singleton_iff.mp hr
    subst r
    refine ⟨⟨c, RelWord.revInv v, ?_⟩, ?_⟩
    · exact RelWord.mem_symmetrized.mpr
        (RelWord.Sym.inv RelWord.Sym.base)
    · rw [Lemma44OrientedRelatorCell.value, RelWord.listVal_revInv]
      exact hx.symm

/-- Orient every factor of a singleton-relator power diagram. -/
theorem exists_lemma49OrientedCells
    {G : Type u} [Group G] {Λ : Type w}
    (v : List (GGT.RelLetter G Λ)) :
    ∀ factors : List G,
      (∀ x ∈ factors, IsSignedConjugate
        ({GGT.RelLetter.listVal v} : Set G) x) →
      ∃ cells : List
          (Lemma44OrientedRelatorCell (RelWord.symmetrized v)),
        cells.map Lemma44OrientedRelatorCell.value = factors
  | [], _ => ⟨[], rfl⟩
  | x :: xs, hcells => by
      obtain ⟨C, hC⟩ := exists_lemma49OrientedCell v
        (hcells x (by simp))
      obtain ⟨tail, htail⟩ := exists_lemma49OrientedCells v xs
        (fun y hy => hcells y (by simp [hy]))
      exact ⟨C :: tail, by simp [hC, htail]⟩

/-- A least-area power diagram with an oriented word attached to every cell. -/
structure Lemma49OrientedPowerDiagram
    {G : Type u} [Group G] {Λ : Type w}
    (v : List (GGT.RelLetter G Λ)) (g : G) (n : ℕ)
    extends Lemma49ReducedPowerDiagram
      ({GGT.RelLetter.listVal v} : Set G) g n where
  cells : List (Lemma44OrientedRelatorCell (RelWord.symmetrized v))
  cell_values : cells.map Lemma44OrientedRelatorCell.value = factors

/-- The symmetrized family orients every cell of a reduced power diagram. -/
theorem Lemma49ReducedPowerDiagram.exists_oriented
    {G : Type u} [Group G] {Λ : Type w}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49ReducedPowerDiagram
      ({GGT.RelLetter.listVal v} : Set G) g n) :
    Nonempty (Lemma49OrientedPowerDiagram v g n) := by
  obtain ⟨cells, hcells⟩ :=
    exists_lemma49OrientedCells v Z.factors Z.factors_cells
  exact ⟨{
    toLemma49ReducedPowerDiagram := Z
    cells := cells
    cell_values := hcells }⟩

/-- Reducedness on oriented cells: two relator cells cannot cancel through
the product of all cells strictly between them. -/
theorem Lemma49OrientedPowerDiagram.noCancellingCellPair
    {G : Type u} [Group G] {Λ : Type w}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49OrientedPowerDiagram v g n)
    (pre between suf : List
      (Lemma44OrientedRelatorCell (RelWord.symmetrized v)))
    (C₁ C₂ : Lemma44OrientedRelatorCell (RelWord.symmetrized v))
    (hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)) :
    ((between.map Lemma44OrientedRelatorCell.value).prod)⁻¹ * C₁.value *
        (between.map Lemma44OrientedRelatorCell.value).prod * C₂.value ≠ 1 := by
  apply Z.no_cancelling_pair
    (pre.map Lemma44OrientedRelatorCell.value)
    (between.map Lemma44OrientedRelatorCell.value)
    (suf.map Lemma44OrientedRelatorCell.value) C₁.value C₂.value
  rw [← Z.cell_values, hsplit]
  simp only [List.map_append, List.map_cons]

/-- The relator boundaries of two oriented power-diagram cells are not inverse
conjugates through the intervening subdiagram. -/
theorem Lemma49OrientedPowerDiagram.relators_ne_inverseConjugate
    {G : Type u} [Group G] {Λ : Type w}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49OrientedPowerDiagram v g n)
    (pre between suf : List
      (Lemma44OrientedRelatorCell (RelWord.symmetrized v)))
    (C₁ C₂ : Lemma44OrientedRelatorCell (RelWord.symmetrized v))
    (hsplit : Z.cells = pre ++ C₁ :: (between ++ C₂ :: suf)) :
    GGT.RelLetter.listVal C₂.relator ≠
      ((C₁.conjugator⁻¹ *
          (between.map Lemma44OrientedRelatorCell.value).prod *
          C₂.conjugator)⁻¹ *
        (GGT.RelLetter.listVal C₁.relator)⁻¹ *
        (C₁.conjugator⁻¹ *
          (between.map Lemma44OrientedRelatorCell.value).prod *
          C₂.conjugator)) := by
  intro hcancel
  apply Z.noCancellingCellPair pre between suf C₁ C₂ hsplit
  rw [Lemma44OrientedRelatorCell.value,
    Lemma44OrientedRelatorCell.value, hcancel]
  group

/-! ## The geodesic power boundary -/

/-- The word obtained by reading `w` exactly `n` times. -/
def lemma49BoundaryPower {G : Type u} {Λ : Type w}
    (w : List (GGT.RelLetter G Λ)) : ℕ → List (GGT.RelLetter G Λ)
  | 0 => []
  | n + 1 => w ++ lemma49BoundaryPower w n

@[simp] theorem lemma49BoundaryPower_length
    {G : Type u} {Λ : Type w} (w : List (GGT.RelLetter G Λ)) :
    ∀ n : ℕ, (lemma49BoundaryPower w n).length = n * w.length
  | 0 => by simp [lemma49BoundaryPower]
  | n + 1 => by
      simp [lemma49BoundaryPower, lemma49BoundaryPower_length,
        Nat.succ_mul, Nat.add_comm]

@[simp] theorem listVal_lemma49BoundaryPower
    {G : Type u} [Group G] {Λ : Type w}
    (w : List (GGT.RelLetter G Λ)) :
    ∀ n : ℕ, GGT.RelLetter.listVal (lemma49BoundaryPower w n) =
      (GGT.RelLetter.listVal w) ^ n
  | 0 => by simp [lemma49BoundaryPower, GGT.RelLetter.listVal_nil]
  | n + 1 => by
      rw [lemma49BoundaryPower, RelWord.listVal_append,
        listVal_lemma49BoundaryPower, pow_succ']

/-- The oriented cell diagram together with a shortest relative word for its
boundary element.  Its repeated boundary word literally spells the power
filled by the cells. -/
structure Lemma49GeodesicPowerDiagram
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    (v : List (GGT.RelLetter G Λ)) (g : G) (n : ℕ)
    extends Lemma49OrientedPowerDiagram v g n where
  boundaryWord : List (GGT.RelLetter G Λ)
  boundary_geodesic : GGT.OsinComponents.IsGeodesicWord D 1 g boundaryWord

/-- Every oriented power diagram has a geodesic representative of `g` on its
outer boundary. -/
theorem Lemma49OrientedPowerDiagram.exists_geodesicBoundary
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49OrientedPowerDiagram v g n) :
    Nonempty (Lemma49GeodesicPowerDiagram D v g n) := by
  obtain ⟨boundaryWord, hboundary⟩ :=
    GGT.OsinComponents.existsGeodesicWord D 1 g
  exact ⟨{
    toLemma49OrientedPowerDiagram := Z
    boundaryWord := boundaryWord
    boundary_geodesic := hboundary }⟩

/-- The repeated outer word has the same value as the product of all oriented
relator cells. -/
theorem Lemma49GeodesicPowerDiagram.boundaryPower_value_eq_cells
    {G : Type u} [Group G] {Λ : Type w} {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n) :
    GGT.RelLetter.listVal (lemma49BoundaryPower Z.boundaryWord n) =
      (Z.cells.map Lemma44OrientedRelatorCell.value).prod := by
  have hboundaryVal : GGT.RelLetter.listVal Z.boundaryWord = g := by
    simpa using Z.boundary_geodesic.2.1
  rw [listVal_lemma49BoundaryPower, hboundaryVal]
  rw [Z.cell_values, Z.factors_prod]

/-- A cyclic rotation of a shortest quotient-conjugacy representative is
again geodesic.  This is the exact minimality consequence used on the repeated
outer boundary in Hull's Lemma 4.9. -/
theorem isGeodesicWord_rotate_of_shortestModuloConjugacy
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    (N : Subgroup G) [N.Normal] {g : G}
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {w : List (GGT.RelLetter G Λ)}
    (hw : GGT.OsinComponents.IsGeodesicWord D 1 g w)
    {m : ℕ} (hm : m ≤ w.length) :
    GGT.OsinComponents.IsGeodesicWord D 1
      (GGT.RelLetter.listVal (w.rotate m)) (w.rotate m) := by
  have hletters : ∀ a ∈ w.rotate m, D.IsLetter a := by
    intro a ha
    exact hw.1 a (List.mem_rotate.mp ha)
  refine ⟨hletters, by simp, ?_⟩
  let p : G := GGT.RelLetter.listVal (w.take m)
  have hwval : GGT.RelLetter.listVal w = g := by simpa using hw.2.1
  have hrotate : GGT.RelLetter.listVal (w.rotate m) = p⁻¹ * g * p := by
    rw [RelWord.listVal_rotate w hm]
    dsimp only [p]
    rw [hwval]
  have hconj : ConjugateModulo N g
      (GGT.RelLetter.listVal (w.rotate m)) := by
    refine ⟨p⁻¹, 1, N.one_mem, ?_⟩
    rw [hrotate]
    simp only [inv_inv, mul_one]
  have hlower : wordNorm D.alphabet.carrier g ≤
      wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (w.rotate m)) := hshort _ hconj
  have hupper : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (w.rotate m)) ≤ (w.rotate m).length :=
    GGT.OsinComponents.wordNorm_listVal_le D (w.rotate m) hletters
  have hlenLower : (w.rotate m).length ≤
      wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal (w.rotate m)) := by
    rw [List.length_rotate, hw.2.2, wordDist_one_left]
    exact hlower
  rw [wordDist_one_left]
  exact Nat.le_antisymm hlenLower hupper

/-- Every segment of a cyclic rotation of the shortest boundary word is
geodesic between its endpoint vertices. -/
theorem isGeodesicWord_cyclicSegment_of_shortestModuloConjugacy
    {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ)
    (N : Subgroup G) [N.Normal] {g : G}
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {w : List (GGT.RelLetter G Λ)}
    (hw : GGT.OsinComponents.IsGeodesicWord D 1 g w)
    {m i j : ℕ} (hm : m ≤ w.length) (hij : i ≤ j)
    (hj : j ≤ (w.rotate m).length) :
    GGT.OsinComponents.IsGeodesicWord D
      (GGT.OsinComponents.vertex 1 (w.rotate m) i)
      (GGT.OsinComponents.vertex 1 (w.rotate m) j)
      (((w.rotate m).drop i).take (j - i)) := by
  exact GGT.OsinComponents.isGeodesicWord_segment D
    (isGeodesicWord_rotate_of_shortestModuloConjugacy D N hshort hw hm)
    hij hj

/-- The remaining geometric statement of Hull's Lemma 4.9, after quotient
conjugacy minimization, order, normal-closure, least-area, reducedness,
orientation, and the geodesic power boundary have been constructed.  The
diagram argument is required only for a shortest lift of its quotient
conjugacy class, exactly as in Hull's proof. -/
def HullLemma49ShortestGeodesicPowerDiagramStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → IsAcylindrical G (Cayley D.alphabet) →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : G) (n : ℕ),
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure
                  ({GGT.RelLetter.listVal v} : Set G)) g →
              Lemma49GeodesicPowerDiagram D v g n →
                ∃ k ∈ Subgroup.normalClosure
                    ({GGT.RelLetter.listVal v} : Set G),
                  (g * k) ^ n = 1

/-- The geodesic power-diagram statement implies the exact quotient-free
kernel-power statement consumed by the canonical Hull filling. -/
theorem hullLemma49KernelPowerStatement_of_geodesicPowerDiagram
    (hdiagram : HullLemma49ShortestGeodesicPowerDiagramStatement.{u, w}) :
    HullLemma49KernelPowerStatement.{u, w} := by
  intro G _ Λ D hemb hacy
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdiagram D hemb hacy
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hn hpow
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  obtain ⟨h, hgh, hshort⟩ :=
    exists_shortest_conjugateModulo D.alphabet.carrier N g
  have hhpow : h ^ n ∈ N := hgh.pow_mem hpow
  have hcorr : ∃ k ∈ N, (h * k) ^ n = 1 := by
    by_cases htrivial : h ^ n = 1
    · exact ⟨1, N.one_mem, by simpa using htrivial⟩
    · obtain ⟨P₀⟩ := exists_lemma49ReducedPowerDiagram hn hhpow htrivial
      obtain ⟨P₁⟩ := P₀.exists_oriented
      obtain ⟨P₂⟩ := P₁.exists_geodesicBoundary D
      exact hgood W v hv hinput h n hshort P₂
  exact hgh.correction hcorr

end HullSC
end GroupApproximation
