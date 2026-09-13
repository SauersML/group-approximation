import GroupApproximation.GGT.HullSCLemma51LetterPullbackInduction
import GroupApproximation.GGT.HullSCLemma51LetterPullbackRotate
import GroupApproximation.GGT.HullSCLemma51LetterMoves

/-!
# The arcs of the shortcut move

Let `x ++ comp λ h⁻¹ :: y` be a rotated lift whose value is spelled by a geodesic word `g`.  A
peripheral letter `g[j]` of index `λ` closes a face of the source Cayley graph: the respelled
inverse of `g.take j`, then `x ++ comp λ h⁻¹ :: y`, then the respelled inverse of `g.drop (j + 1)`,
read from `listVal (g.take j)`.  By geodesicity, `g[j]` is the only letter of `g` of index `λ` read
at the coset `listVal (g.take j) · H_λ` (`eq_of_isCompOf_coset_of_isRelGeodesic`).  So the letters
of the respelled arcs read at that coset are base letters of `H_λ`, and their inverses are atoms
(`cosetLettersAt_respellInv_atoms`, `_take`, `_drop`).

* If `g[j]` is read at `c · q(H_λ)` but not at the coset of `listVal x`, its value is a bounded
  product of the atoms (`val_mem_boundedProducts_of_rotatedLift`).
* If no letter of `g` of index `λ` is read at the coset of `listVal x`, the face `y`, the respelled
  inverse of `g`, `x` shows that `h` is a bounded product
  (`mem_boundedProducts_of_rotatedLift_of_forall`).
* If `g[k]` is read there, `g` is the new quotient-null word with designated letter `g[k]`, of value
  `(T⁻¹ X) h⁻¹ (Y S⁻¹)` for two bounded products `T⁻¹ X` and `Y S⁻¹`
  (`pullbackOutcome_of_rotatedLift_of_designated`).
-/

namespace GroupApproximation
namespace HullSC

universe u v w

section Words

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The respelled inverse of an arc with no peripheral letter at the coset.**  Its letters read
at the coset `c · H_λ` are base letters of `H_λ`, whose inverses are atoms. -/
theorem cosetLettersAt_respellInv_atoms (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r : ℕ} (hr : 1 ≤ r) (c x : G)
    {u : List (GGT.RelLetter G Lambda)} (hu : ∀ a ∈ u, D.IsLetter a)
    (hno : ∀ (i : ℕ) (hi : i < u.length), GGT.RelLetter.IsCompOf lam u[i] →
      c⁻¹ * (x * GGT.RelLetter.listVal (u.take i)) ∈ D.fam lam → False) :
    CosetLettersAt D lam (pullbackAtoms W D lam r) c (x * GGT.RelLetter.listVal u)
      (respellInv D u) := by
  refine cosetLettersAt_respellInv D lam _ c x u hu ?_
  intro k hk hk' hv
  rcases hk' with hcomp | ⟨y, hy, hyH⟩
  · exact (hno k hk hcomp hv).elim
  · have hyb : y ∈ D.base := by
      have hl := hu u[k] (List.getElem_mem hk)
      rw [hy] at hl
      exact hl
    rw [val_invLetter, hy]
    exact inv_mem_pullbackAtoms_of_mem_base hyb hyH hr

/-- **The respelled inverse of a prefix of an arc.**  If every peripheral letter of index `λ` read
at the coset `c · H_λ` comes at or after `k`, the respelled inverse of `g.take k` has atoms at the
coset. -/
theorem cosetLettersAt_respellInv_take (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r : ℕ} (hr : 1 ≤ r) (c : G)
    {g : List (GGT.RelLetter G Lambda)} (hg : ∀ a ∈ g, D.IsLetter a) (k : ℕ)
    (hno : ∀ (i : ℕ) (hi : i < g.length), GGT.RelLetter.IsCompOf lam g[i] →
      c⁻¹ * GGT.RelLetter.listVal (g.take i) ∈ D.fam lam → k ≤ i) :
    CosetLettersAt D lam (pullbackAtoms W D lam r) c (GGT.RelLetter.listVal (g.take k))
      (respellInv D (g.take k)) := by
  have hno' : ∀ (i : ℕ) (hi : i < (g.take k).length),
      GGT.RelLetter.IsCompOf lam (g.take k)[i] →
        c⁻¹ * (1 * GGT.RelLetter.listVal ((g.take k).take i)) ∈ D.fam lam → False := by
    intro i hi hcomp hv
    have hik : i < k := lt_of_lt_of_le hi (List.length_take_le k g)
    have hig : i < g.length := lt_of_lt_of_le hi (List.length_take_le' k g)
    rw [List.getElem_take] at hcomp
    rw [one_mul, List.take_take, Nat.min_eq_left hik.le] at hv
    have := hno i hig hcomp hv
    omega
  have h1 := cosetLettersAt_respellInv_atoms W D lam hr c 1 (u := g.take k)
    (fun a ha => hg a (List.mem_of_mem_take ha)) hno'
  rwa [one_mul] at h1

/-- **The respelled inverse of a suffix of an arc.**  If every peripheral letter of index `λ` read
at the coset `c · H_λ` comes at or before `k`, the respelled inverse of `g.drop (k + 1)`, read from
`listVal g`, has atoms at the coset. -/
theorem cosetLettersAt_respellInv_drop (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r : ℕ} (hr : 1 ≤ r) (c : G)
    {g : List (GGT.RelLetter G Lambda)} (hg : ∀ a ∈ g, D.IsLetter a) (k : ℕ)
    (hno : ∀ (i : ℕ) (hi : i < g.length), GGT.RelLetter.IsCompOf lam g[i] →
      c⁻¹ * GGT.RelLetter.listVal (g.take i) ∈ D.fam lam → i ≤ k) :
    CosetLettersAt D lam (pullbackAtoms W D lam r) c (GGT.RelLetter.listVal g)
      (respellInv D (g.drop (k + 1))) := by
  have hno' : ∀ (i : ℕ) (hi : i < (g.drop (k + 1)).length),
      GGT.RelLetter.IsCompOf lam (g.drop (k + 1))[i] →
        c⁻¹ * (GGT.RelLetter.listVal (g.take (k + 1)) *
          GGT.RelLetter.listVal ((g.drop (k + 1)).take i)) ∈ D.fam lam → False := by
    intro i hi hcomp hv
    have hlen : (g.drop (k + 1)).length = g.length - (k + 1) := List.length_drop
    have hig : k + 1 + i < g.length := by omega
    rw [List.getElem_drop] at hcomp
    rw [← GGT.OsinComponents.listVal_append, ← List.take_add] at hv
    have := hno (k + 1 + i) hig hcomp hv
    omega
  have h1 := cosetLettersAt_respellInv_atoms W D lam hr c
    (GGT.RelLetter.listVal (g.take (k + 1))) (u := g.drop (k + 1))
    (fun a ha => hg a (List.mem_of_mem_drop ha)) hno'
  rwa [← GGT.OsinComponents.listVal_append, List.take_append_drop] at h1

theorem listVal_take_succ (g : List (GGT.RelLetter G Lambda)) {k : ℕ} (hk : k < g.length) :
    GGT.RelLetter.listVal (g.take (k + 1)) = GGT.RelLetter.listVal (g.take k) * g[k].val := by
  rw [List.take_succ_eq_append_getElem hk, GGT.OsinComponents.listVal_append,
    RelWord.listVal_singleton]

theorem listVal_take_succ_add (g : List (GGT.RelLetter G Lambda)) {k : ℕ} (hk : k < g.length)
    (i : ℕ) :
    GGT.RelLetter.listVal (g.take k) * g[k].val *
        GGT.RelLetter.listVal ((g.drop (k + 1)).take i) =
      GGT.RelLetter.listVal (g.take (k + 1 + i)) := by
  rw [List.take_add, GGT.OsinComponents.listVal_append, listVal_take_succ g hk]

theorem listVal_eq_take_mul_getElem_mul_drop (g : List (GGT.RelLetter G Lambda)) {j : ℕ}
    (hj : j < g.length) :
    GGT.RelLetter.listVal g = GGT.RelLetter.listVal (g.take j) *
      (g[j].val * GGT.RelLetter.listVal (g.drop (j + 1))) := by
  have e := congrArg GGT.RelLetter.listVal (List.take_append_drop j g)
  rw [List.drop_eq_getElem_cons hj, GGT.OsinComponents.listVal_append,
    GGT.OsinComponents.listVal_cons] at e
  exact e.symm

theorem listVal_append_comp_cons (x y : List (GGT.RelLetter G Lambda)) (lam : Lambda) (h : G) :
    GGT.RelLetter.listVal (x ++ GGT.RelLetter.comp lam h :: y) =
      GGT.RelLetter.listVal x * h * GGT.RelLetter.listVal y := by
  have e : (GGT.RelLetter.comp lam h : GGT.RelLetter G Lambda).val = h := rfl
  rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons, e, mul_assoc]

/-- The coset of `X h⁻¹` is the coset of `X` when `h ∈ H_λ`. -/
theorem inv_mul_mem_fam_iff_of_mem (D : GGT.RelGenSet G Lambda) (lam : Lambda) {h : G}
    (hh : h ∈ D.fam lam) (X T : G) :
    (X * h⁻¹)⁻¹ * T ∈ D.fam lam ↔ T⁻¹ * X ∈ D.fam lam := by
  constructor
  · intro hT
    have e : T⁻¹ * X = ((X * h⁻¹)⁻¹ * T)⁻¹ * h := by group
    rw [e]
    exact mul_mem (inv_mem hT) hh
  · intro hT
    have e : (X * h⁻¹)⁻¹ * T = h * (T⁻¹ * X)⁻¹ := by group
    rw [e]
    exact mul_mem hh (inv_mem hT)

/-- **A face read at one coset spells a bounded product of the atoms.** -/
theorem mem_boundedProducts_pullbackAtoms_of_cosetLettersAt
    (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda) (lam : Lambda)
    {r N : ℕ} (a : G) {rest : List (GGT.RelLetter G Lambda)}
    (hrest : ∀ b ∈ rest, D.IsLetter b) (hval : GGT.RelLetter.listVal rest ∈ D.fam lam)
    (hA : CosetLettersAt D lam (pullbackAtoms W D lam r) a a rest) (hlen : rest.length ≤ r)
    (hN : r + 1 ≤ N) :
    GGT.RelLetter.listVal rest ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have h1 := listVal_mem_boundedProducts_of_cosetLettersAt_from D lam _ a hrest hval hA
  have hsub : pullbackAtoms W D lam r ∪ D.relBall lam rest.length ⊆ pullbackAtoms W D lam r :=
    Set.union_subset (fun _ hb => hb) fun _ hb =>
      relBall_subset_pullbackAtoms W D lam r
        (GGT.OsinComponents.relBall_mono_radius D lam hlen hb)
  exact boundedProducts_mono hsub (by omega : rest.length + 1 ≤ N) h1

end Words

section Lift

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- The vertex after the designated letter lies over the base coset. -/
theorem RotatedLift.coset_right {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {x y : List (GGT.RelLetter G Lambda)} (hlift : RotatedLift D q hq lam h c x y)
    (hh : h ∈ D.fam lam) :
    c⁻¹ * q (GGT.RelLetter.listVal x * h⁻¹) ∈ (D.mapSurjective q hq).fam lam := by
  rw [map_mul, ← mul_assoc, map_inv]
  exact mul_mem hlift.coset (inv_mem (Subgroup.mem_map_of_mem q hh))

/-- **The image coset condition from source bounds.** -/
theorem cosetLettersAt_mapHom_of_forall (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (B : Set G) {c : Q} {xG : G}
    {u : List (GGT.RelLetter G Lambda)}
    (hatom : ∀ (i : ℕ) (hi : i < u.length), GGT.RelLetter.IsCompOf lam u[i] →
      c⁻¹ * q (xG * GGT.RelLetter.listVal (u.take i)) ∈ (D.mapSurjective q hq).fam lam →
        u[i].val ∈ B) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' B) c (q xG)
      (u.map (GGT.RelLetter.mapHom q)) := by
  intro i hi hcomp hv
  have hi' : i < u.length := by simpa using hi
  simp only [List.getElem_map, GGT.RelLetter.isCompOf_mapHom] at hcomp
  rw [← List.map_take, GGT.RelLetter.listVal_map_mapHom, ← map_mul] at hv
  simp only [List.getElem_map, GGT.RelLetter.val_mapHom]
  exact ⟨u[i].val, hatom i hi' hcomp hv, rfl⟩

/-- **A peripheral letter of the shortcut off the coset of `x` has a bounded value.** -/
theorem val_mem_boundedProducts_of_rotatedLift (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) {lam : Lambda}
    {h : G} {c : Q} {x y g : List (GGT.RelLetter G Lambda)} {r N : ℕ}
    (hlift : RotatedLift D q hq lam h c x y) (hg : ∀ a ∈ g, D.IsLetter a)
    (hgeo : IsRelGeodesic D g)
    (hgval : GGT.RelLetter.listVal g =
      GGT.RelLetter.listVal (x ++ GGT.RelLetter.comp lam h⁻¹ :: y))
    (hr1 : 1 ≤ r) (hr : g.length + x.length + y.length ≤ r) (hN : r + 1 ≤ N) {j : ℕ}
    (hj : j < g.length) (hcomp : GGT.RelLetter.IsCompOf lam g[j])
    (hcos : c⁻¹ * q (GGT.RelLetter.listVal (g.take j)) ∈ (D.mapSurjective q hq).fam lam)
    (hout : (GGT.RelLetter.listVal (g.take j))⁻¹ * GGT.RelLetter.listVal x ∉ D.fam lam) :
    g[j].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have huniq : ∀ (i : ℕ) (hi : i < g.length), GGT.RelLetter.IsCompOf lam g[i] →
      (GGT.RelLetter.listVal (g.take j))⁻¹ * GGT.RelLetter.listVal (g.take i) ∈ D.fam lam →
        i = j := by
    intro i hi hci hv
    refine eq_of_isCompOf_coset_of_isRelGeodesic D hg hgeo hi hj hci hcomp ?_
    have e : (GGT.RelLetter.listVal (g.take i))⁻¹ * GGT.RelLetter.listVal (g.take j) =
        ((GGT.RelLetter.listVal (g.take j))⁻¹ * GGT.RelLetter.listVal (g.take i))⁻¹ := by
      group
    rw [e]
    exact inv_mem hv
  have hpre : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) (GGT.RelLetter.listVal (g.take j))
      (respellInv D (g.take j)) :=
    cosetLettersAt_respellInv_take W D lam hr1 (GGT.RelLetter.listVal (g.take j)) hg j
      fun i hi hci hv => (huniq i hi hci hv).ge
  have hsuf : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) (GGT.RelLetter.listVal g)
      (respellInv D (g.drop (j + 1))) :=
    cosetLettersAt_respellInv_drop W D lam hr1 (GGT.RelLetter.listVal (g.take j)) hg j
      fun i hi hci hv => (huniq i hi hci hv).le
  have hx : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) 1 x :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ x
      (by rw [map_one, mul_one]; exact hlift.avoid_left) hcos
  have he : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) (1 * GGT.RelLetter.listVal x)
      [GGT.RelLetter.comp lam h⁻¹] :=
    cosetLettersAt_singleton fun _ hv => (hout (by rwa [one_mul] at hv)).elim
  have hy : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j))
      (1 * GGT.RelLetter.listVal x * GGT.RelLetter.listVal [GGT.RelLetter.comp lam h⁻¹]) y :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ y
      (by rw [one_mul, RelWord.listVal_singleton]; exact hlift.avoid_right) hcos
  have hs : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) 1 (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) := by
    have h2 := he.append hy
    rw [List.singleton_append] at h2
    exact hx.append h2
  have hv1 : GGT.RelLetter.listVal (g.take j) *
      GGT.RelLetter.listVal (respellInv D (g.take j)) = 1 := by
    rw [listVal_respellInv, mul_inv_cancel]
  have hv2 : GGT.RelLetter.listVal (g.take j) *
      GGT.RelLetter.listVal (respellInv D (g.take j) ++ (x ++ GGT.RelLetter.comp lam h⁻¹ :: y)) =
        GGT.RelLetter.listVal g := by
    rw [GGT.OsinComponents.listVal_append, ← mul_assoc, hv1, one_mul, hgval]
  have hall : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take j)) (GGT.RelLetter.listVal (g.take j))
      (respellInv D (g.take j) ++ (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) ++
        respellInv D (g.drop (j + 1))) := by
    refine CosetLettersAt.append (hpre.append ?_) ?_
    · rw [hv1]
      exact hs
    · rw [hv2]
      exact hsuf
  have hdec := listVal_eq_take_mul_getElem_mul_drop g hj
  have hvalEq : GGT.RelLetter.listVal (respellInv D (g.take j) ++
      (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) ++ respellInv D (g.drop (j + 1))) = g[j].val := by
    rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_append, listVal_respellInv,
      listVal_respellInv, ← hgval, hdec]
    group
  have hval : GGT.RelLetter.listVal (respellInv D (g.take j) ++
      (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) ++ respellInv D (g.drop (j + 1))) ∈ D.fam lam := by
    rw [hvalEq]
    exact val_mem_fam_of_isCompOf (hg _ (List.getElem_mem hj)) hcomp
  have hrest : ∀ b ∈ respellInv D (g.take j) ++ (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) ++
      respellInv D (g.drop (j + 1)), D.IsLetter b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact isLetter_respellInv D (word := g.take j)
          (fun a ha => hg a (List.mem_of_mem_take ha)) b hb
      · exact hlift.letters b hb
    · exact isLetter_respellInv D (word := g.drop (j + 1))
        (fun a ha => hg a (List.mem_of_mem_drop ha)) b hb
  have hlen : (respellInv D (g.take j) ++ (x ++ GGT.RelLetter.comp lam h⁻¹ :: y) ++
      respellInv D (g.drop (j + 1))).length ≤ r := by
    simp only [List.length_append, List.length_cons, length_respellInv, List.length_take,
      List.length_drop]
    omega
  have hmem := mem_boundedProducts_pullbackAtoms_of_cosetLettersAt W D lam
    (GGT.RelLetter.listVal (g.take j)) hrest hval hall hlen hN
  rwa [hvalEq] at hmem

/-- **With no peripheral letter at the coset of `x`, `h` is a bounded product.** -/
theorem mem_boundedProducts_of_rotatedLift_of_forall (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) {lam : Lambda}
    {h : G} {c : Q} {x y g : List (GGT.RelLetter G Lambda)} {r N : ℕ}
    (hlift : RotatedLift D q hq lam h c x y) (hh : h ∈ D.fam lam) (hg : ∀ a ∈ g, D.IsLetter a)
    (hgval : GGT.RelLetter.listVal g =
      GGT.RelLetter.listVal (x ++ GGT.RelLetter.comp lam h⁻¹ :: y))
    (hr1 : 1 ≤ r) (hr : g.length + x.length + y.length ≤ r) (hN : r + 1 ≤ N)
    (hno : ∀ (k : ℕ) (hk : k < g.length), GGT.RelLetter.IsCompOf lam g[k] →
      (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x ∉ D.fam lam) :
    h ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have hc1 := hlift.coset_right hh
  have hy : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal x * h⁻¹) y :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ y hlift.avoid_right hc1
  have hgr : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal g) (respellInv D g) := by
    have h1 := cosetLettersAt_respellInv_atoms W D lam hr1 (GGT.RelLetter.listVal x * h⁻¹) 1
      (u := g) hg fun k hk hkc hv => hno k hk hkc
        ((inv_mul_mem_fam_iff_of_mem D lam hh (GGT.RelLetter.listVal x)
          (GGT.RelLetter.listVal (g.take k))).mp (by rwa [one_mul] at hv))
    rwa [one_mul] at h1
  have hx : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) 1 x :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ x
      (by rw [map_one, mul_one]; exact hlift.avoid_left) hc1
  have hvy : GGT.RelLetter.listVal x * h⁻¹ * GGT.RelLetter.listVal y =
      GGT.RelLetter.listVal g := by
    rw [hgval, listVal_append_comp_cons]
  have hvx : GGT.RelLetter.listVal x * h⁻¹ *
      GGT.RelLetter.listVal (y ++ respellInv D g) = 1 := by
    rw [GGT.OsinComponents.listVal_append, ← mul_assoc, hvy, listVal_respellInv, mul_inv_cancel]
  have hall : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal x * h⁻¹)
      (y ++ respellInv D g ++ x) := by
    refine CosetLettersAt.append (hy.append ?_) ?_
    · rw [hvy]
      exact hgr
    · rw [hvx]
      exact hx
  have hvalEq : GGT.RelLetter.listVal (y ++ respellInv D g ++ x) = h := by
    rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_append, listVal_respellInv,
      ← hvy]
    group
  have hval : GGT.RelLetter.listVal (y ++ respellInv D g ++ x) ∈ D.fam lam := by
    rw [hvalEq]
    exact hh
  have hrest : ∀ b ∈ y ++ respellInv D g ++ x, D.IsLetter b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact hlift.letters b (List.mem_append_right x (List.mem_cons_of_mem _ hb))
      · exact isLetter_respellInv D hg b hb
    · exact hlift.letters b (List.mem_append_left _ hb)
  have hlen : (y ++ respellInv D g ++ x).length ≤ r := by
    simp only [List.length_append, length_respellInv]
    omega
  have hmem := mem_boundedProducts_pullbackAtoms_of_cosetLettersAt W D lam
    (GGT.RelLetter.listVal x * h⁻¹) hrest hval hall hlen hN
  rwa [hvalEq] at hmem

/-- **With a peripheral letter at the coset of `x`, the shortcut is the new word.** -/
theorem pullbackOutcome_of_rotatedLift_of_designated (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) {lam : Lambda}
    {h : G} {c : Q} {x y g : List (GGT.RelLetter G Lambda)} {r N n : ℕ}
    (hlift : RotatedLift D q hq lam h c x y) (hh : h ∈ D.fam lam) (hg : ∀ a ∈ g, D.IsLetter a)
    (hgeo : IsRelGeodesic D g)
    (hgval : GGT.RelLetter.listVal g =
      GGT.RelLetter.listVal (x ++ GGT.RelLetter.comp lam h⁻¹ :: y))
    (hr1 : 1 ≤ r) (hr : g.length + x.length + y.length ≤ r) (hN : r + 1 ≤ N)
    (hgn : g.length ≤ n + 1) {k : ℕ} (hk : k < g.length)
    (hkcomp : GGT.RelLetter.IsCompOf lam g[k])
    (hkcos : (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x ∈ D.fam lam) :
    PullbackOutcome D q hq lam (pullbackAtoms W D lam r) N h n := by
  have hdec := listVal_eq_take_mul_getElem_mul_drop g hk
  have hsplit : g.take k ++ g[k] :: g.drop (k + 1) = g := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hgnull : q (GGT.RelLetter.listVal g) = 1 := by
    rw [hgval]
    exact hlift.null
  have hcosQ : c⁻¹ * q (GGT.RelLetter.listVal (g.take k)) ∈ (D.mapSurjective q hq).fam lam := by
    have e : c⁻¹ * q (GGT.RelLetter.listVal (g.take k)) =
        (c⁻¹ * q (GGT.RelLetter.listVal x)) *
          q (((GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x)⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact mul_mem hlift.coset (Subgroup.mem_map_of_mem q (inv_mem hkcos))
  have huniqX : ∀ (i : ℕ) (hi : i < g.length), GGT.RelLetter.IsCompOf lam g[i] →
      (GGT.RelLetter.listVal (g.take i))⁻¹ * GGT.RelLetter.listVal x ∈ D.fam lam → i = k := by
    intro i hi hci hv
    refine eq_of_isCompOf_coset_of_isRelGeodesic D hg hgeo hi hk hci hkcomp ?_
    have e : (GGT.RelLetter.listVal (g.take i))⁻¹ * GGT.RelLetter.listVal (g.take k) =
        ((GGT.RelLetter.listVal (g.take i))⁻¹ * GGT.RelLetter.listVal x) *
          ((GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x)⁻¹ := by
      group
    rw [e]
    exact mul_mem hv (inv_mem hkcos)
  have huniq2 : ∀ (i : ℕ) (hi : i < g.length), GGT.RelLetter.IsCompOf lam g[i] →
      (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal (g.take i) ∈ D.fam lam →
        i = k := by
    intro i hi hci hv
    refine eq_of_isCompOf_coset_of_isRelGeodesic D hg hgeo hi hk hci hkcomp ?_
    have e : (GGT.RelLetter.listVal (g.take i))⁻¹ * GGT.RelLetter.listVal (g.take k) =
        ((GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal (g.take i))⁻¹ := by
      group
    rw [e]
    exact inv_mem hv
  -- The bounded product `T⁻¹ X` before the unknown.
  have hpre2 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take k)) (GGT.RelLetter.listVal (g.take k))
      (respellInv D (g.take k)) :=
    cosetLettersAt_respellInv_take W D lam hr1 (GGT.RelLetter.listVal (g.take k)) hg k
      fun i hi hci hv => (huniq2 i hi hci hv).ge
  have hx2 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take k)) 1 x :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ x
      (by rw [map_one, mul_one]; exact hlift.avoid_left) hcosQ
  have hall2 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal (g.take k)) (GGT.RelLetter.listVal (g.take k))
      (respellInv D (g.take k) ++ x) := by
    refine hpre2.append ?_
    rw [listVal_respellInv, mul_inv_cancel]
    exact hx2
  have hval2 : GGT.RelLetter.listVal (respellInv D (g.take k) ++ x) =
      (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x := by
    rw [GGT.OsinComponents.listVal_append, listVal_respellInv]
  have hrest2 : ∀ b ∈ respellInv D (g.take k) ++ x, D.IsLetter b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact isLetter_respellInv D (word := g.take k)
        (fun a ha => hg a (List.mem_of_mem_take ha)) b hb
    · exact hlift.letters b (List.mem_append_left _ hb)
  have hlen2 : (respellInv D (g.take k) ++ x).length ≤ r := by
    simp only [List.length_append, length_respellInv, List.length_take]
    omega
  have hV2 : (GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x ∈
      boundedProducts (pullbackAtoms W D lam r) N := by
    have hmem := mem_boundedProducts_pullbackAtoms_of_cosetLettersAt W D lam
      (GGT.RelLetter.listVal (g.take k)) hrest2 (by rw [hval2]; exact hkcos) hall2 hlen2 hN
    rwa [hval2] at hmem
  -- The bounded product `Y S⁻¹` after the unknown.
  have hc1 := hlift.coset_right hh
  have hy1 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal x * h⁻¹) y :=
    cosetLettersAt_of_avoidsFrom_mapHom D q hq lam _ y hlift.avoid_right hc1
  have hsuf1 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal g)
      (respellInv D (g.drop (k + 1))) :=
    cosetLettersAt_respellInv_drop W D lam hr1 (GGT.RelLetter.listVal x * h⁻¹) hg k
      fun i hi hci hv => (huniqX i hi hci
        ((inv_mul_mem_fam_iff_of_mem D lam hh (GGT.RelLetter.listVal x)
          (GGT.RelLetter.listVal (g.take i))).mp hv)).le
  have hvy : GGT.RelLetter.listVal x * h⁻¹ * GGT.RelLetter.listVal y =
      GGT.RelLetter.listVal g := by
    rw [hgval, listVal_append_comp_cons]
  have hall1 : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal x * h⁻¹) (GGT.RelLetter.listVal x * h⁻¹)
      (y ++ respellInv D (g.drop (k + 1))) := by
    refine hy1.append ?_
    rw [hvy]
    exact hsuf1
  have hY : GGT.RelLetter.listVal y = h * (GGT.RelLetter.listVal x)⁻¹ *
      (GGT.RelLetter.listVal (g.take k) *
        (g[k].val * GGT.RelLetter.listVal (g.drop (k + 1)))) := by
    rw [← hdec, ← hvy]
    group
  have hval1 : GGT.RelLetter.listVal (y ++ respellInv D (g.drop (k + 1))) =
      GGT.RelLetter.listVal y * (GGT.RelLetter.listVal (g.drop (k + 1)))⁻¹ := by
    rw [GGT.OsinComponents.listVal_append, listVal_respellInv]
  have hmemH1 : GGT.RelLetter.listVal y * (GGT.RelLetter.listVal (g.drop (k + 1)))⁻¹ ∈
      D.fam lam := by
    have e : GGT.RelLetter.listVal y * (GGT.RelLetter.listVal (g.drop (k + 1)))⁻¹ =
        h * ((GGT.RelLetter.listVal (g.take k))⁻¹ * GGT.RelLetter.listVal x)⁻¹ * g[k].val := by
      rw [hY]
      group
    rw [e]
    exact mul_mem (mul_mem hh (inv_mem hkcos))
      (val_mem_fam_of_isCompOf (hg _ (List.getElem_mem hk)) hkcomp)
  have hrest1 : ∀ b ∈ y ++ respellInv D (g.drop (k + 1)), D.IsLetter b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hlift.letters b (List.mem_append_right x (List.mem_cons_of_mem _ hb))
    · exact isLetter_respellInv D (word := g.drop (k + 1))
        (fun a ha => hg a (List.mem_of_mem_drop ha)) b hb
  have hlen1 : (y ++ respellInv D (g.drop (k + 1))).length ≤ r := by
    simp only [List.length_append, length_respellInv, List.length_drop]
    omega
  have hV1 : GGT.RelLetter.listVal y * (GGT.RelLetter.listVal (g.drop (k + 1)))⁻¹ ∈
      boundedProducts (pullbackAtoms W D lam r) N := by
    have hmem := mem_boundedProducts_pullbackAtoms_of_cosetLettersAt W D lam
      (GGT.RelLetter.listVal x * h⁻¹) hrest1 (by rw [hval1]; exact hmemH1) hall1 hlen1 hN
    rwa [hval1] at hmem
  have hdes : DesignatedValue (pullbackAtoms W D lam r) N h g[k].val := by
    refine ⟨_, _, hV2, hV1, Or.inr ?_⟩
    rw [hY]
    group
  -- The other peripheral letters read at the base coset.
  have hatomQ : ∀ (j : ℕ) (hj : j < g.length), GGT.RelLetter.IsCompOf lam g[j] →
      c⁻¹ * q (GGT.RelLetter.listVal (g.take j)) ∈ (D.mapSurjective q hq).fam lam → j ≠ k →
        g[j].val ∈ boundedProducts (pullbackAtoms W D lam r) N :=
    fun j hj hcj hvj hjk => val_mem_boundedProducts_of_rotatedLift W D q hq hlift hg hgeo hgval
      hr1 hr hN hj hcj hvj fun hin => hjk (huniqX j hj hcj hin)
  have hQ : CosetLettersAt (D.mapSurjective q hq) lam
      (q '' boundedProducts (pullbackAtoms W D lam r) N) c
      (q (GGT.RelLetter.listVal (g.take k) * g[k].val))
      ((g.drop (k + 1) ++ g.take k).map (GGT.RelLetter.mapHom q)) := by
    rw [List.map_append]
    refine CosetLettersAt.append ?_ ?_
    · refine cosetLettersAt_mapHom_of_forall D q hq lam _ ?_
      intro i hi hci hvi
      have hlen : (g.drop (k + 1)).length = g.length - (k + 1) := List.length_drop
      have hlt : k + 1 + i < g.length := by omega
      rw [List.getElem_drop] at hci ⊢
      rw [listVal_take_succ_add g hk i] at hvi
      exact hatomQ _ hlt hci hvi (by omega)
    · rw [GGT.RelLetter.listVal_map_mapHom, ← map_mul]
      refine cosetLettersAt_mapHom_of_forall D q hq lam _ ?_
      intro i hi hci hvi
      have hik : i < k := lt_of_lt_of_le hi (List.length_take_le k g)
      have hig : i < g.length := lt_of_lt_of_le hi (List.length_take_le' k g)
      rw [List.getElem_take] at hci ⊢
      have e : q (GGT.RelLetter.listVal (g.take k) * g[k].val *
          GGT.RelLetter.listVal (g.drop (k + 1)) * GGT.RelLetter.listVal ((g.take k).take i)) =
            q (GGT.RelLetter.listVal (g.take i)) := by
        rw [List.take_take, Nat.min_eq_left hik.le, mul_assoc (GGT.RelLetter.listVal (g.take k)),
          ← hdec, map_mul, hgnull, one_mul]
      rw [e] at hvi
      exact hatomQ i hig hci hvi (by omega)
  refine Or.inr ⟨g.take k, g.drop (k + 1), g[k], c, ?_, ?_, ?_, hkcomp, hcosQ, hdes, hQ⟩
  · rw [hsplit]
    exact hg
  · rw [hsplit]
    exact hgnull
  · simp only [List.length_append, List.length_drop, List.length_take]
    omega

end Lift

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_atoms
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_take
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_drop
#audit_axioms GroupApproximation.HullSC.listVal_take_succ
#audit_axioms GroupApproximation.HullSC.listVal_take_succ_add
#audit_axioms GroupApproximation.HullSC.listVal_eq_take_mul_getElem_mul_drop
#audit_axioms GroupApproximation.HullSC.listVal_append_comp_cons
#audit_axioms GroupApproximation.HullSC.inv_mul_mem_fam_iff_of_mem
#audit_axioms GroupApproximation.HullSC.mem_boundedProducts_pullbackAtoms_of_cosetLettersAt
#audit_axioms GroupApproximation.HullSC.RotatedLift.coset_right
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_mapHom_of_forall
#audit_axioms GroupApproximation.HullSC.val_mem_boundedProducts_of_rotatedLift
#audit_axioms GroupApproximation.HullSC.mem_boundedProducts_of_rotatedLift_of_forall
#audit_axioms GroupApproximation.HullSC.pullbackOutcome_of_rotatedLift_of_designated
