import GroupApproximation.GGT.HullSCUnconeClosingJump
import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepGeodesicRuns
import GroupApproximation.GGT.OsinTheorem54SepRuns
import GroupApproximation.GGT.OsinTheorem54SepCommIndex
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinTheorem54SepFinite
import GroupApproximation.GGT.OsinTheorem54SepTriangle
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 3: paths that stay out of a coset

The comparisons of the un-coning argument close a path made of pieces of geodesic sides by one
component letter, and they need the path to stay out of the coset that letter lies in.  On a
geodesic word the pieces are controlled by the fact that a geodesic crosses each coset at most once
(`OsinComponents.not_connected_of_isCompStart_of_geodesic`), and every component of a geodesic is a
single letter (`OsinComponents.isComp_eq_succ_of_isGeodesicWord`).

* `AvoidsCosetFrom D lam K f u`: no `λ`-letter of `u`, read from `f`, is read at a vertex of the
  coset `K`.
* `mk_vertex_ne_of_isGeodesicWord`, `mk_vertex_ne_of_noComp`: the two sources of avoidance.
* `AvoidsCosetFrom.take`, `.drop`, `.revWord`: avoidance passes to prefixes, suffixes and reversals,
  each read from its own starting vertex.
* `avoidsCosetFrom_take_of_isComp`, `avoidsCosetFrom_drop_of_isComp`: the parts of a geodesic before
  and after its component on `K` avoid `K`.
* `closingJump_located`: three avoiding geodesic pieces from `a` to a point `b₃` of the coset of `a`
  have `b₃⁻¹a` in the `d̂_λ`-ball of radius `4C`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

namespace Uncone

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The two sources of avoidance -/

/-- **A word with no component on `K` reads no `λ`-letter at a vertex of `K`**: a `λ`-letter lies
in a maximal run, and the whole run stays in one coset. -/
theorem mk_vertex_ne_of_noComp (D : RelGenSet G Λ) {lam : Λ} {f : G}
    {u : List (RelLetter G Λ)} (hlet : ∀ a ∈ u, D.IsLetter a) {K : G ⧸ D.fam lam}
    (hno : ∀ i k : ℕ, IsComp lam u i k →
      (QuotientGroup.mk (vertex f u i) : G ⧸ D.fam lam) ≠ K)
    {t : ℕ} (ht : t < u.length) (hct : (u[t]'ht).IsCompOf lam) :
    (QuotientGroup.mk (vertex f u t) : G ⧸ D.fam lam) ≠ K := by
  obtain ⟨i, k, hit, htk, hcomp⟩ := exists_isComp_of_isCompOf lam u t ht hct
  intro hK
  apply hno i k hcomp
  rw [← hK]
  have hspan : (vertex f u i)⁻¹ * vertex f u t ∈ D.fam lam :=
    span_mem_fam D lam f hlet t (le_of_lt ht) i hit
      (fun j hj1 hj2 hj3 => hcomp.2.2.1 j hj1 (by omega) hj3)
  exact QuotientGroup.eq.mpr hspan

/-- **A geodesic word crosses a coset at most once**: a `λ`-letter other than the component at `i`
is not read at a vertex of that component's coset. -/
theorem mk_vertex_ne_of_isGeodesicWord (D : RelGenSet G Λ) {lam : Λ} {f g : G}
    {u : List (RelLetter G Λ)} (hu : IsGeodesicWord D f g u) {i k : ℕ}
    (hcomp : IsComp lam u i k) {t : ℕ} (ht : t < u.length) (hct : (u[t]'ht).IsCompOf lam)
    (hne : t ≠ i) :
    (QuotientGroup.mk (vertex f u t) : G ⧸ D.fam lam)
      ≠ QuotientGroup.mk (vertex f u i) := by
  obtain ⟨s, k', hst, htk', hcomp'⟩ := exists_isComp_of_isCompOf lam u t ht hct
  have hk' := isComp_eq_succ_of_isGeodesicWord D lam hu hcomp'
  have hs : s = t := by omega
  rw [hs] at hcomp'
  intro hK
  exact not_connected_of_isCompStart_of_geodesic D hu ⟨k, hcomp⟩ ⟨k', hcomp'⟩ (Ne.symm hne)
    (QuotientGroup.eq.mp hK.symm)

/-! ## Avoiding a coset -/

/-- **`u`, read from `f`, never reads a `λ`-letter at a vertex of the coset `K`.** -/
def AvoidsCosetFrom (D : RelGenSet G Λ) (lam : Λ) (K : G ⧸ D.fam lam) (f : G)
    (u : List (RelLetter G Λ)) : Prop :=
  ∀ (t : ℕ) (ht : t < u.length), (u[t]'ht).IsCompOf lam →
    (QuotientGroup.mk (vertex f u t) : G ⧸ D.fam lam) ≠ K

/-- The vertices of a suffix, read from the vertex it starts at, are the vertices of the word. -/
theorem vertex_drop (f : G) (u : List (RelLetter G Λ)) (m t : ℕ) (hm : m ≤ u.length) :
    vertex (vertex f u m) (u.drop m) t = vertex f u (m + t) := by
  have hsplit := vertex_append_add (u.take m) (u.drop m) f t
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hm] at hsplit
  rw [vertex_eq_mul_listVal_take u f m]
  exact hsplit.symm

theorem AvoidsCosetFrom.take {D : RelGenSet G Λ} {lam : Λ} {K : G ⧸ D.fam lam} {f : G}
    {u : List (RelLetter G Λ)} (h : AvoidsCosetFrom D lam K f u) (m : ℕ) :
    AvoidsCosetFrom D lam K f (u.take m) := by
  intro t ht hct
  have htm : t < m := by
    simp only [List.length_take] at ht
    omega
  have ht' : t < u.length := by
    simp only [List.length_take] at ht
    omega
  have hget : (u.take m)[t]'ht = u[t]'ht' := by simp
  rw [vertex_take_eq f u m t (le_of_lt htm)]
  exact h t ht' (by rwa [hget] at hct)

theorem AvoidsCosetFrom.drop {D : RelGenSet G Λ} {lam : Λ} {K : G ⧸ D.fam lam} {f : G}
    {u : List (RelLetter G Λ)} (h : AvoidsCosetFrom D lam K f u) {m : ℕ} (hm : m ≤ u.length) :
    AvoidsCosetFrom D lam K (vertex f u m) (u.drop m) := by
  intro t ht hct
  have ht' : m + t < u.length := by
    simp only [List.length_drop] at ht
    omega
  have hget : (u.drop m)[t]'ht = u[m + t]'ht' := by simp
  rw [vertex_drop f u m t hm]
  exact h (m + t) ht' (by rwa [hget] at hct)

/-- **Reversal keeps avoidance**, the reversed word being read from the far endpoint: a reversed
`λ`-letter is read at the far end of the original letter, which is in the same coset as its near
end. -/
theorem AvoidsCosetFrom.revWord {D : RelGenSet G Λ} {lam : Λ} {K : G ⧸ D.fam lam} {f : G}
    {u : List (RelLetter G Λ)} (hlet : ∀ a ∈ u, D.IsLetter a) (h : AvoidsCosetFrom D lam K f u) :
    AvoidsCosetFrom D lam K (f * RelLetter.listVal u) (OsinComponents.revWord u) := by
  intro t ht hct
  have htu : t < u.length := by rwa [length_revWord] at ht
  have hs : u.length - 1 - t < u.length := by omega
  have hcs : (u[u.length - 1 - t]'hs).IsCompOf lam :=
    (isCompOf_getElem_revWord u lam ht hs).mp hct
  have hv : vertex (f * RelLetter.listVal u) (OsinComponents.revWord u) t
      = vertex f u (u.length - 1 - t + 1) := by
    have h1 := vertex_revWord_of_end u f (u.length - 1 - t + 1)
    have h2 : u.length - (u.length - 1 - t + 1) = t := by omega
    rw [h2] at h1
    exact h1
  rw [hv, vertex_succ u f (u.length - 1 - t) hs]
  have hval : (u[u.length - 1 - t]'hs).val ∈ D.fam lam :=
    val_mem_fam_of_isCompOf D (hlet _ (List.getElem_mem hs)) hcs
  intro hK
  apply h (u.length - 1 - t) hs hcs
  rw [← hK]
  refine QuotientGroup.eq.mpr ?_
  rw [inv_mul_cancel_left]
  exact hval

/-- A word with no component on `K` avoids `K`. -/
theorem avoidsCosetFrom_of_noComp (D : RelGenSet G Λ) {lam : Λ} {f : G}
    {u : List (RelLetter G Λ)} (hlet : ∀ a ∈ u, D.IsLetter a) {K : G ⧸ D.fam lam}
    (hno : ∀ i k : ℕ, IsComp lam u i k →
      (QuotientGroup.mk (vertex f u i) : G ⧸ D.fam lam) ≠ K) :
    AvoidsCosetFrom D lam K f u :=
  fun _ ht hct => mk_vertex_ne_of_noComp D hlet hno ht hct

/-- **The part of a geodesic before its component on `K` avoids `K`.** -/
theorem avoidsCosetFrom_take_of_isComp (D : RelGenSet G Λ) {lam : Λ} {f g : G}
    {u : List (RelLetter G Λ)} (hu : IsGeodesicWord D f g u) {i k : ℕ}
    (hcomp : IsComp lam u i k) :
    AvoidsCosetFrom D lam (QuotientGroup.mk (vertex f u i)) f (u.take i) := by
  intro t ht hct
  have hti : t < i := by
    simp only [List.length_take] at ht
    omega
  have ht' : t < u.length := by
    have h1 := hcomp.1
    have h2 := hcomp.2.1
    omega
  have hget : (u.take i)[t]'ht = u[t]'ht' := by simp
  rw [vertex_take_eq f u i t (le_of_lt hti)]
  exact mk_vertex_ne_of_isGeodesicWord D hu hcomp ht' (by rwa [hget] at hct) (by omega)

/-- **The part of a geodesic after its component on `K` avoids `K`.** -/
theorem avoidsCosetFrom_drop_of_isComp (D : RelGenSet G Λ) {lam : Λ} {f g : G}
    {u : List (RelLetter G Λ)} (hu : IsGeodesicWord D f g u) {i k : ℕ}
    (hcomp : IsComp lam u i k) :
    AvoidsCosetFrom D lam (QuotientGroup.mk (vertex f u i)) (vertex f u k) (u.drop k) := by
  have hkw : k ≤ u.length := hcomp.2.1
  intro t ht hct
  have ht' : k + t < u.length := by
    simp only [List.length_drop] at ht
    omega
  have hget : (u.drop k)[t]'ht = u[k + t]'ht' := by simp
  rw [vertex_drop f u k t hkw]
  exact mk_vertex_ne_of_isGeodesicWord D hu hcomp ht' (by rwa [hget] at hct)
    (by have := hcomp.1; omega)

/-! ## The located closing jump -/

/-- **Located avoidance is avoidance from the translated basepoint.** -/
theorem avoidsFrom_of_avoidsCosetFrom (D : RelGenSet G Λ) (lam : Λ) {a c : G}
    {u : List (RelLetter G Λ)}
    (h : AvoidsCosetFrom D lam (QuotientGroup.mk a) (a * c) u) :
    AvoidsFrom D.fam lam u c := by
  rw [avoidsFrom_iff_forall]
  intro t ht hct hmem
  apply h t ht hct
  rw [vertex_smul]
  refine (QuotientGroup.eq.mpr ?_).symm
  rw [inv_mul_cancel_left]
  exact hmem

/-- **Three avoiding geodesic pieces closed by one component letter.**  Geodesic words from `a` to
`b₁`, from `b₁` to `b₂` and from `b₂` to `b₃`, with `b₃` in the coset `aH_λ`, none of which reads a
`λ`-letter at a vertex of that coset, give `b₃⁻¹a ∈ D.relBall lam (C * 4)`. -/
theorem closingJump_located (D : RelGenSet G Λ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (lam : Λ) {a b₁ b₂ b₃ : G} {p q r : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D a b₁ p) (hq : IsGeodesicWord D b₁ b₂ q)
    (hr : IsGeodesicWord D b₂ b₃ r)
    (hcoset : (QuotientGroup.mk b₃ : G ⧸ D.fam lam) = QuotientGroup.mk a)
    (hap : AvoidsCosetFrom D lam (QuotientGroup.mk a) a p)
    (haq : AvoidsCosetFrom D lam (QuotientGroup.mk a) b₁ q)
    (har : AvoidsCosetFrom D lam (QuotientGroup.mk a) b₂ r) :
    b₃⁻¹ * a ∈ D.relBall lam (C * 4) := by
  have hh : a⁻¹ * b₃ ∈ D.fam lam := QuotientGroup.eq.mp hcoset.symm
  have e1 : a * RelLetter.listVal p = b₁ := hp.2.1
  have e2 : b₁ * RelLetter.listVal q = b₂ := hq.2.1
  have e3 : b₂ * RelLetter.listVal r = b₃ := hr.2.1
  have hval : RelLetter.listVal p * RelLetter.listVal q * RelLetter.listVal r = a⁻¹ * b₃ := by
    rw [← e3, ← e2, ← e1]
    group
  have hav : AvoidsFrom D.fam lam (p ++ q ++ r) 1 := by
    rw [avoidsFrom_append_iff, avoidsFrom_append_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine avoidsFrom_of_avoidsCosetFrom D lam (a := a) ?_
      rw [mul_one]
      exact hap
    · refine avoidsFrom_of_avoidsCosetFrom D lam (a := a) ?_
      rw [one_mul, e1]
      exact haq
    · refine avoidsFrom_of_avoidsCosetFrom D lam (a := a) ?_
      rw [one_mul, listVal_append, ← mul_assoc, e1, e2]
      exact har
  have hjump := closingJump_inv_mem_relBall D hsymm hbnd lam (isGeodesicWord_one_of D hp)
    (isGeodesicWord_one_of D hq) (isGeodesicWord_one_of D hr) hh hval hav
  have hinv : (a⁻¹ * b₃)⁻¹ = b₃⁻¹ * a := by group
  rwa [hinv] at hjump

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.mk_vertex_ne_of_noComp
#audit_axioms GroupApproximation.GGT.Uncone.mk_vertex_ne_of_isGeodesicWord
#audit_axioms GroupApproximation.GGT.Uncone.vertex_drop
#audit_axioms GroupApproximation.GGT.Uncone.AvoidsCosetFrom.take
#audit_axioms GroupApproximation.GGT.Uncone.AvoidsCosetFrom.drop
#audit_axioms GroupApproximation.GGT.Uncone.AvoidsCosetFrom.revWord
#audit_axioms GroupApproximation.GGT.Uncone.avoidsCosetFrom_take_of_isComp
#audit_axioms GroupApproximation.GGT.Uncone.avoidsCosetFrom_drop_of_isComp
#audit_axioms GroupApproximation.GGT.Uncone.closingJump_located
