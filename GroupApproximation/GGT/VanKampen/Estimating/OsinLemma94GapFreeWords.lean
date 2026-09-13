import GroupApproximation.GGT.VanKampen.Estimating.QuasiGeodesicValueOneGap
import GroupApproximation.GGT.VanKampen.WordPolygonReplacement

/-!
# Gap-free class words

Osin (math/0411039v3, §9), proof of Lemma 9.4.  The sides of a component polygon are counted in
classes.  A class is read along one relator cell or one section of `∂Δ`, with the gaps between
consecutive sides included, and every gap is a closed path, so its word has value one.  This
module drops the gaps.  The gap-free class word is still quasi-geodesic, has the same value, and
carries a fixed fraction of the letters, so a count over class words passes to gap-free words at
a factor `M²` in `ρ`.

* `IsLambdaCQuasiGeodesicWord.of_append_listVal_eq_one`: for `0 ≤ λ`, removing a value-one block
  from a `(λ, c)`-quasi-geodesic word leaves a `(λ, c)`-quasi-geodesic word.
* `IsLambdaCQuasiGeodesicWord.flatMap_of_gaps`: a class word without its gaps is
  `(λ, c)`-quasi-geodesic.
* `listVal_flatMap_of_gaps`: it has the same value.
* `IsLambdaCQuasiGeodesicWord.length_flatMap_le_of_gaps`: for `0 < λ`, the class word has at
  most `1 + ⌈c / λ⌉₊` letters per letter of its gap-free word.
* `classWordLength_le_mul` and `dense_of_mul_covers`: `S ≤ M F + L n`, `4 L² ≤ ρ` and `n √ρ ≤ S`
  give `n √⌊ρ / (4 M²)⌋ ≤ F`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

section Words

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- **The vertices behind a removed block.**  If `g` has value one, then reading `p ++ q` for `k`
letters reaches the vertex that `p ++ g ++ q` reaches after `k` letters, or after `k + |g|`
letters once `k` has passed `p`. -/
theorem vertex_append_of_listVal_eq_one {p g q : List (RelLetter G Lambda)}
    (hg : RelLetter.listVal g = 1) (k : ℕ) :
    GGT.OsinComponents.vertex 1 (p ++ g ++ q) (if k ≤ p.length then k else k + g.length) =
      GGT.OsinComponents.vertex 1 (p ++ q) k := by
  rw [GGT.OsinComponents.vertex_eq_mul_listVal_take,
    GGT.OsinComponents.vertex_eq_mul_listVal_take]
  split_ifs with hk
  · rw [List.append_assoc p g q, List.take_append_of_le_length hk,
      List.take_append_of_le_length hk]
  · have hp : p.length ≤ k := by omega
    have hp' : p.length ≤ k + g.length := by omega
    have hg' : g.length ≤ k + g.length - p.length := by omega
    have hsub : k + g.length - p.length - g.length = k - p.length := by omega
    have h1 : (p ++ g ++ q).take (k + g.length) = p ++ g ++ q.take (k - p.length) := by
      rw [List.append_assoc p g q, List.take_append, List.take_of_length_le hp',
        List.take_append, List.take_of_length_le hg', hsub, List.append_assoc]
    have h2 : (p ++ q).take k = p ++ q.take (k - p.length) := by
      rw [List.take_append, List.take_of_length_le hp]
    rw [h1, h2, HullSC.RelWord.listVal_append, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_append, hg, mul_one]

/-- **Removing a value-one block keeps a word quasi-geodesic.**  The vertices of `p ++ q` are
vertices of `p ++ g ++ q` at positions at least as far apart, so for `0 ≤ λ` the quasi-geodesic
inequality passes to `p ++ q`. -/
theorem IsLambdaCQuasiGeodesicWord.of_append_listVal_eq_one (hlambda : 0 ≤ lambda)
    {p g q : List (RelLetter G Lambda)} (h : IsLambdaCQuasiGeodesicWord D lambda c (p ++ g ++ q))
    (hg : RelLetter.listVal g = 1) : IsLambdaCQuasiGeodesicWord D lambda c (p ++ q) := by
  refine ⟨fun a ha => h.1 a ?_, fun i j hij hj => ?_⟩
  · rcases List.mem_append.1 ha with ha | ha <;> simp [ha]
  · have hq := h.2 (if i ≤ p.length then i else i + g.length)
      (if j ≤ p.length then j else j + g.length) (by split_ifs <;> omega)
      (by simp only [List.length_append] at hj ⊢; split_ifs <;> omega)
    rw [vertex_append_of_listVal_eq_one hg, vertex_append_of_listVal_eq_one hg] at hq
    have hgap : j - i ≤ (if j ≤ p.length then j else j + g.length) -
        (if i ≤ p.length then i else i + g.length) := by
      split_ifs <;> omega
    have hmono : lambda * ((j - i : ℕ) : ℝ) ≤ lambda * (((if j ≤ p.length then j else
        j + g.length) - (if i ≤ p.length then i else i + g.length) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hgap) hlambda
    linarith

/-- **A class word without its gaps is quasi-geodesic.**  The gaps are removed one at a time,
from the front, behind a growing prefix `p`. -/
theorem IsLambdaCQuasiGeodesicWord.flatMap_of_gaps {ι : Type*} (hlambda : 0 ≤ lambda)
    (side gap : ι → List (RelLetter G Lambda)) (l : List ι)
    (hgap : ∀ s ∈ l, RelLetter.listVal (gap s) = 1) (p : List (RelLetter G Lambda))
    (h : IsLambdaCQuasiGeodesicWord D lambda c (p ++ l.flatMap fun s => side s ++ gap s)) :
    IsLambdaCQuasiGeodesicWord D lambda c (p ++ l.flatMap side) := by
  induction l generalizing p with
  | nil => simpa using h
  | cons s l ih =>
    have h' : IsLambdaCQuasiGeodesicWord D lambda c
        (p ++ side s ++ gap s ++ l.flatMap fun s => side s ++ gap s) := by
      simpa only [List.flatMap_cons, List.append_assoc] using h
    have h'' := ih (fun t ht => hgap t (by simp [ht])) (p ++ side s)
      (h'.of_append_listVal_eq_one hlambda (hgap s (by simp)))
    simpa only [List.flatMap_cons, List.append_assoc] using h''

/-- **Dropping the gaps keeps the value.** -/
theorem listVal_flatMap_of_gaps {ι : Type*} (side gap : ι → List (RelLetter G Lambda))
    (l : List ι) (hgap : ∀ s ∈ l, RelLetter.listVal (gap s) = 1) :
    RelLetter.listVal (l.flatMap side) =
      RelLetter.listVal (l.flatMap fun s => side s ++ gap s) := by
  induction l with
  | nil => simp
  | cons s l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_append, HullSC.RelWord.listVal_append, hgap s (by simp), mul_one,
      ih (fun t ht => hgap t (by simp [ht]))]

/-- **A gap is short.**  For `0 < λ`, a value-one block of a `(λ, c)`-quasi-geodesic word has at
most `⌈c / λ⌉₊` letters. -/
theorem IsLambdaCQuasiGeodesicWord.length_le_ceil_of_append {p g q : List (RelLetter G Lambda)}
    (h : IsLambdaCQuasiGeodesicWord D lambda c (p ++ g ++ q)) (hlambda : 0 < lambda)
    (hg : RelLetter.listVal g = 1) : g.length ≤ ⌈c / lambda⌉₊ := by
  refine h.le_ceil_of_listVal_eq_one hlambda (i := p.length)
    (by simp only [List.length_append]; omega) ?_
  rw [List.append_assoc, List.drop_left, List.take_left]
  exact hg

end Words

/-- **Gap-free words carry a fixed fraction of the letters.**  Every side has a letter and every
gap at most `g₀` letters, so the class word has at most `1 + g₀` letters per gap-free letter. -/
theorem length_flatMap_append_le {α ι : Type*} (side gap : ι → List α) {g0 : ℕ} (l : List ι)
    (hside : ∀ s ∈ l, side s ≠ []) (hgap : ∀ s ∈ l, (gap s).length ≤ g0) :
    (l.flatMap fun s => side s ++ gap s).length ≤ (1 + g0) * (l.flatMap side).length := by
  induction l with
  | nil => simp
  | cons s l ih =>
    have hs : 1 ≤ (side s).length := List.length_pos_iff.2 (hside s (by simp))
    have hg := hgap s (by simp)
    have ih' := ih (fun t ht => hside t (by simp [ht])) (fun t ht => hgap t (by simp [ht]))
    simp only [List.flatMap_cons, List.length_append]
    nlinarith [mul_le_mul_of_nonneg_left hs (Nat.zero_le g0)]

section Words

variable {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- **The class length bound.**  For `0 < λ`, a `(λ, c)`-quasi-geodesic class word with nonempty
sides and value-one gaps has at most `1 + ⌈c / λ⌉₊` letters per letter of its gap-free word. -/
theorem IsLambdaCQuasiGeodesicWord.length_flatMap_le_of_gaps {ι : Type*} (hlambda : 0 < lambda)
    (side gap : ι → List (RelLetter G Lambda)) (l : List ι) (hside : ∀ s ∈ l, side s ≠ [])
    (hgap : ∀ s ∈ l, RelLetter.listVal (gap s) = 1)
    (h : IsLambdaCQuasiGeodesicWord D lambda c (l.flatMap fun s => side s ++ gap s)) :
    (l.flatMap fun s => side s ++ gap s).length ≤
      (1 + ⌈c / lambda⌉₊) * (l.flatMap side).length := by
  refine length_flatMap_append_le side gap l hside fun s hs => ?_
  obtain ⟨as, bs, rfl⟩ := List.append_of_mem hs
  have h' : IsLambdaCQuasiGeodesicWord D lambda c
      (as.flatMap (fun s => side s ++ gap s) ++ side s ++ gap s ++
        bs.flatMap fun s => side s ++ gap s) := by
    simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc] using h
  exact h'.length_le_ceil_of_append hlambda (hgap s hs)

omit [Group G] in
/-- **Class lengths scale termwise.**  If every word of the class is at most `M` times the
corresponding gap-free word, then so is the class length. -/
theorem classWordLength_le_mul (word word' : ℕ → List (RelLetter G Lambda)) (n M : ℕ)
    (A : Set ℕ) (hle : ∀ i < n, i ∈ A → (word i).length ≤ M * (word' i).length) :
    classWordLength word n A ≤ M * classWordLength word' n A := by
  unfold classWordLength
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  split_ifs with hA
  · exact_mod_cast hle i (Finset.mem_range.1 hi) hA
  · simp

end Words

/-- **Density survives a multiplicative cover.**  "Assume that `S ≥ n √ρ`."  If `S ≤ M F + L n`
and `4 L² ≤ ρ`, then `2 L ≤ √ρ`, so `M F ≥ n √ρ / 2`, and `2 M √⌊ρ / (4 M²)⌋ ≤ √ρ`.  So `F` is
dense at `⌊ρ / (4 M²)⌋`. -/
theorem dense_of_mul_covers {n S F : ℝ} {M L rho : ℕ} (hM : 0 < M) (hn : 0 ≤ n)
    (hcover : S ≤ M * F + L * n) (hL : 4 * L * L ≤ rho) (hge : n * Real.sqrt rho ≤ S) :
    n * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) ≤ F := by
  have hrho0 : (0 : ℝ) ≤ (rho : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ ((rho / (4 * M * M) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdiv : (4 : ℝ) * M * M * ((rho / (4 * M * M) : ℕ) : ℝ) ≤ rho := by
    have h' : ((rho / (4 * M * M) * (4 * M * M) : ℕ) : ℝ) ≤ rho := by
      exact_mod_cast Nat.div_mul_le_self rho (4 * M * M)
    push_cast at h'
    linarith
  have hsqrtL : 2 * (L : ℝ) ≤ Real.sqrt rho := by
    rw [Real.le_sqrt (by positivity) hrho0]
    have hL' : (4 : ℝ) * L * L ≤ rho := by exact_mod_cast hL
    nlinarith
  have hsqrtm : 2 * (M : ℝ) * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ) ≤ Real.sqrt rho := by
    rw [Real.le_sqrt (by positivity) hrho0, mul_pow, Real.sq_sqrt hm0]
    nlinarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : n * (2 * (M : ℝ) * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ)) ≤ n * Real.sqrt rho :=
    mul_le_mul_of_nonneg_left hsqrtm hn
  have h2 : n * (2 * (L : ℝ)) ≤ n * Real.sqrt rho := mul_le_mul_of_nonneg_left hsqrtL hn
  have h3 : (M : ℝ) * (n * Real.sqrt ((rho / (4 * M * M) : ℕ) : ℝ)) ≤ M * F := by linarith
  by_contra hlt
  exact not_le.2 (mul_lt_mul_of_pos_left (not_le.1 hlt) hMpos) h3

#audit_axioms GroupApproximation.GGT.VanKampen.vertex_append_of_listVal_eq_one
#audit_axioms
  GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.of_append_listVal_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.flatMap_of_gaps
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_flatMap_of_gaps
#audit_axioms
  GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.length_le_ceil_of_append
#audit_axioms GroupApproximation.GGT.VanKampen.length_flatMap_append_le
#audit_axioms
  GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.length_flatMap_le_of_gaps
#audit_axioms GroupApproximation.GGT.VanKampen.classWordLength_le_mul
#audit_axioms GroupApproximation.GGT.VanKampen.dense_of_mul_covers

end GroupApproximation.GGT.VanKampen
