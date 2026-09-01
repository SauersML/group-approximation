import GroupApproximation.GGT.HullSCRelatorSeparation2RelativeSides
import GroupApproximation.GGT.HullSCRelatorSeparation2ExactCount

/-!
# Counting interior components for relative short sides

Hull's published pieces allow the two connector words to use the full relative
alphabet.  The finite-absorption polygon theorem therefore needs a finite run
of deep source components, rather than one chosen component.  This module
extracts that run directly from a prefix of the fixed exact relator.

There is only one base letter in the whole exact relator.  Deleting the two
boundary positions of a prefix costs at most two further component positions.
Thus a prefix of length at least `K + 3` contains `K` distinct, strictly
interior peripheral letters.  Their subgroup indices are allowed to vary; in
the exact relator they alternate, but finite absorption only needs the sharper
fact that there are two possible indices.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

omit [Group G] in
/-- Erasing one element from an arbitrary finite set loses at most one
cardinality. -/
theorem card_le_card_erase_add_one {T : Type*} [DecidableEq T]
    (S : Finset T) (x : T) : S.card ≤ (S.erase x).card + 1 := by
  by_cases hx : x ∈ S
  · rw [Finset.card_erase_add_one hx]
  · rw [Finset.erase_eq_of_notMem hx]
    omega

omit [Group G] in
/-- A position carrying a base letter contributes one to the base count. -/
theorem one_le_baseCount_of_base_getElem
    {T : Type*} {w : List (GGT.RelLetter T Bool)} {i : ℕ} {x : T}
    (hi : w[i]? = some (GGT.RelLetter.base x)) : 1 ≤ baseCount w := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a t ih =>
      cases a with
      | base z => simp [baseCount]
      | comp lam z =>
          cases i with
          | zero => simp at hi
          | succ i =>
              simp only [List.getElem?_cons_succ] at hi
              simpa only [baseCount] using ih hi

omit [Group G] in
/-- Two distinct positions carrying base letters contribute two to the base
count. -/
theorem two_le_baseCount_of_two_base_getElem
    {T : Type*} {w : List (GGT.RelLetter T Bool)} {i j : ℕ} {x y : T}
    (hi : w[i]? = some (GGT.RelLetter.base x))
    (hj : w[j]? = some (GGT.RelLetter.base y)) (hne : i ≠ j) :
    2 ≤ baseCount w := by
  induction w generalizing i j with
  | nil => simp at hi
  | cons a t ih =>
      cases a with
      | base z =>
          cases i with
          | zero =>
              cases j with
              | zero => exact False.elim (hne rfl)
              | succ j =>
                  simp only [List.getElem?_cons_succ] at hj
                  have := one_le_baseCount_of_base_getElem hj
                  simp only [baseCount]
                  omega
          | succ i =>
              cases j with
              | zero =>
                  simp only [List.getElem?_cons_succ] at hi
                  have := one_le_baseCount_of_base_getElem hi
                  simp only [baseCount]
                  omega
              | succ j =>
                  simp only [List.getElem?_cons_succ] at hi hj
                  simp only [baseCount]
                  have htwo := ih hi hj (fun h ↦ hne (congrArg Nat.succ h))
                  omega
      | comp lam z =>
          cases i with
          | zero => simp at hi
          | succ i =>
              cases j with
              | zero => simp at hj
              | succ j =>
                  simp only [List.getElem?_cons_succ] at hi hj
                  simpa only [baseCount] using
                    ih hi hj (fun h ↦ hne (congrArg Nat.succ h))

/-- A minimal spelling in the full relative alphabet, without the historical
two-letter base padding. -/
theorem exists_relative_spelling₂ (E : HypEmbeddedCore₂ A N) {y : G} {n : ℕ}
    (hy : wordNorm E.rel.alphabet.carrier y ≤ n) :
    ∃ p : List (GGT.RelLetter G Bool), p.length ≤ n ∧
      (∀ x ∈ p, E.rel.IsLetter x) ∧
      GGT.RelLetter.listVal p = y := by
  obtain ⟨l, hl, hlen⟩ :=
    exists_isWord_length_eq E.rel.alphabet.symmetricGenerating y
  obtain ⟨p, hplet, hpval, hplen⟩ :=
    GGT.OsinComponents.exists_relWord E.rel l hl.letters
  refine ⟨p, ?_, hplet, ?_⟩
  · rw [hplen, hlen]
    exact hy
  · rw [hpval, hl.prod_eq]

/-- A long prefix of a symmetrized exact relator contains any prescribed
finite number of distinct, strictly interior, deep singleton components.
Both the positions and their (possibly varying) `Bool` indices are returned,
in exactly the shape consumed by indexed finite absorption. -/
theorem exists_indexed_interior_components_of_sym_prefix
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {v u tail : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hu : v = u ++ tail) (K : ℕ) (hlen : K + 3 ≤ u.length) :
    ∃ (source : Fin K → ℕ) (index : Fin K → Bool),
      Function.Injective source ∧
      (∀ i, 0 < source i) ∧
      (∀ i, source i + 1 < u.length) ∧
      (∀ i, GGT.OsinComponents.IsComp (index i) u
        (source i) (source i + 1)) ∧
      (∀ i, (GGT.OsinComponents.vertex (1 : G) u (source i))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u (source i + 1) ∉
            E.rel.relBall (index i) rho) := by
  classical
  let positions := ((componentPositions u).erase 0).erase (u.length - 1)
  have hbaseV : baseCount v = 1 := by
    simpa using baseCount_of_sym_relatorWord₂ hv
  have hbaseU : baseCount u ≤ 1 := by
    have happ := baseCount_append u tail
    rw [← hu] at happ
    omega
  have hpartition := baseCount_add_compCount u
  have herase0 := card_componentPositions_le_card_erase_add_one u 0
  have heraseLast := card_le_card_erase_add_one
    ((componentPositions u).erase 0) (u.length - 1)
  have hcard : K ≤ positions.card := by
    dsimp only [positions]
    omega
  let pick : Fin K → positions := fun i =>
    positions.orderIsoOfFin rfl (Fin.castLE hcard i)
  let source : Fin K → ℕ := fun i => (pick i).val
  have hsource_inj : Function.Injective source := by
    intro i j hij
    have hpick : pick i = pick j := Subtype.ext hij
    have hfin : Fin.castLE hcard i = Fin.castLE hcard j :=
      (positions.orderIsoOfFin rfl).injective hpick
    apply Fin.ext
    simpa only [Fin.castLE] using
      congrArg (fun x : Fin positions.card => x.val) hfin
  have hsource_mem (i : Fin K) : source i ∈ positions := (pick i).property
  have hsource_pos (i : Fin K) : 0 < source i := by
    have hne : source i ≠ 0 := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hsource_mem i)).2).1
    omega
  have hsource_end (i : Fin K) : source i + 1 < u.length := by
    have hcompPos : source i ∈ componentPositions u :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp (hsource_mem i)).2).2
    obtain ⟨lam, g, hread⟩ := mem_componentPositions_iff.mp hcompPos
    have hlt : source i < u.length := (List.getElem?_eq_some_iff.mp hread).1
    have hne : source i ≠ u.length - 1 :=
      (Finset.mem_erase.mp (hsource_mem i)).1
    omega
  have hread : ∀ i, ∃ lam : Bool, ∃ g : G,
      u[source i]? = some (GGT.RelLetter.comp lam g) := by
    intro i
    apply mem_componentPositions_iff.mp
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hsource_mem i)).2).2
  choose index value hread using hread
  have hreadV (i : Fin K) :
      v[source i]? = some (GGT.RelLetter.comp (index i) (value i)) := by
    rw [hu, List.getElem?_append_left (by
      have := hsource_end i
      omega)]
    exact hread i
  have hsource_comp (i : Fin K) : GGT.OsinComponents.IsComp (index i) u
      (source i) (source i + 1) := by
    have hcomp := isComp_of_sym_exactRelator E hv (hreadV i)
    rw [hu] at hcomp
    exact isComp_prefix hcomp (by
      have := hsource_end i
      omega)
  have hsource_deep (i : Fin K) :
      (GGT.OsinComponents.vertex (1 : G) u (source i))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) u (source i + 1) ∉
            E.rel.relBall (index i) rho := by
    have hstep := vertex_succ_of_getElem?
      u (source i) (1 : G)
        (GGT.RelLetter.comp (index i) (value i)) (hread i)
    simp only [GGT.RelLetter.val] at hstep
    have hspan :
        (GGT.OsinComponents.vertex (1 : G) u (source i))⁻¹ *
            GGT.OsinComponents.vertex (1 : G) u (source i + 1) = value i := by
      rw [hstep]
      group
    rw [hspan]
    exact comp_value_not_mem_relBall_of_sym_exactRelator E hdesign hv (hreadV i)
  exact ⟨source, index, hsource_inj, hsource_pos, hsource_end,
    hsource_comp, hsource_deep⟩

/-- A sufficiently long exact prefix contains two adjacent deep components
which simultaneously avoid both relative short sides and the cyclic seam.
The sole base letter can spoil at most one of the disjoint candidate pairs;
the extra pair in the grid pays for exactly that exception. -/
theorem exists_adjacent_seam_clean_components_of_sym_prefix
    (E : HypEmbeddedCore₂ A N) {baseLetter : G}
    {rho eps diffRadius W target : ℕ} {ms : List ℕ}
    (hdesign : ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms)
    {v q tail : List (GGT.RelLetter G Bool)}
    (hv : RelWord.Sym
      (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v)
    (hq : v = q ++ tail) (p r s : List (GGT.RelLetter G Bool))
    (hlen : 2 * (p.length + r.length + 3) + 2 ≤ q.length)
    (hpairwise : ∀ (lam : Bool) (i j : ℕ),
      GGT.OsinComponents.IsComp lam q i (i + 1) →
      GGT.OsinComponents.IsComp lam q j (j + 1) →
      j + 1 < q.length →
      0 < i → 0 < j → i ≠ j →
      ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
        (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
        (p.length + i) (p.length + j)) :
    ∃ (lam lam' : Bool) (i : ℕ),
      0 < i ∧ i + 2 < q.length ∧
      GGT.OsinComponents.IsComp lam q i (i + 1) ∧
      GGT.OsinComponents.IsComp lam' q (i + 1) (i + 2) ∧
      (GGT.OsinComponents.vertex (1 : G) q i)⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q (i + 1) ∉
            E.rel.relBall lam rho ∧
      (GGT.OsinComponents.vertex (1 : G) q (i + 1))⁻¹ *
          GGT.OsinComponents.vertex (1 : G) q (i + 2) ∉
            E.rel.relBall lam' rho ∧
      (∀ m, GGT.OsinComponents.IsCompStart lam
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
        GGT.OsinComponents.Connected E.rel.fam lam 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + i) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
              m = p.length + q.length + b) ∨
            m = p.length + q.length + r.length + (s.length - 1))) ∧
      (∀ m, GGT.OsinComponents.IsCompStart lam'
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
        GGT.OsinComponents.Connected E.rel.fam lam' 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + (i + 1)) m →
        ¬ ((m < p.length ∨ ∃ b, b < r.length ∧
              m = p.length + q.length + b) ∨
            m = p.length + q.length + r.length + (s.length - 1))) := by
  classical
  let P := p.length + r.length + 3
  let source : Fin (2 * P) → ℕ := fun k ↦ k.val + 1
  have hsource_lt (k : Fin (2 * P)) : source k < q.length := by
    dsimp only [source, P]
    omega
  let index : Fin (2 * P) → Bool := fun k ↦
    match q[source k]? with
    | some (GGT.RelLetter.comp lam _) => lam
    | _ => false
  let left : Fin P → Fin (2 * P) := fun a ↦ ⟨2 * a, by omega⟩
  let right : Fin P → Fin (2 * P) := fun a ↦ ⟨2 * a + 1, by omega⟩
  let Valid : Fin P → Prop := fun a ↦
    (∃ x : G, q[source (left a)]? =
      some (GGT.RelLetter.comp (index (left a)) x)) ∧
    (∃ x : G, q[source (right a)]? =
      some (GGT.RelLetter.comp (index (right a)) x))
  have hbaseQ : baseCount q ≤ 1 := by
    have hbaseV : baseCount v = 1 := by
      simpa using baseCount_of_sym_relatorWord₂ hv
    have happ := baseCount_append q tail
    rw [← hq] at happ
    omega
  have hbase_of_invalid : ∀ a, ¬ Valid a →
      (∃ x : G, q[source (left a)]? = some (GGT.RelLetter.base x)) ∨
      (∃ x : G, q[source (right a)]? = some (GGT.RelLetter.base x)) := by
    intro a ha
    have hl := List.getElem?_eq_getElem (hsource_lt (left a))
    have hr := List.getElem?_eq_getElem (hsource_lt (right a))
    cases hla : q[source (left a)]'(hsource_lt (left a)) with
    | base x =>
        left
        exact ⟨x, by simpa only [hla] using hl⟩
    | comp lam x =>
        cases hra : q[source (right a)]'(hsource_lt (right a)) with
        | base y =>
            right
            exact ⟨y, by simpa only [hra] using hr⟩
        | comp lam' y =>
            exfalso
            apply ha
            constructor
            · refine ⟨x, ?_⟩
              have hread : q[source (left a)]? =
                  some (GGT.RelLetter.comp lam x) := by
                simpa only [hla] using hl
              change q[source (left a)]? = some (GGT.RelLetter.comp
                (match q[source (left a)]? with
                  | some (GGT.RelLetter.comp nu _) => nu
                  | _ => false) x)
              simp only [hread]
            · refine ⟨y, ?_⟩
              have hread : q[source (right a)]? =
                  some (GGT.RelLetter.comp lam' y) := by
                simpa only [hra] using hr
              change q[source (right a)]? = some (GGT.RelLetter.comp
                (match q[source (right a)]? with
                  | some (GGT.RelLetter.comp nu _) => nu
                  | _ => false) y)
              simp only [hread]
  have hinvalid : ∀ a b, ¬ Valid a → ¬ Valid b → a = b := by
    intro a b ha hb
    rcases hbase_of_invalid a ha with hxa | hxa <;>
      rcases hbase_of_invalid b hb with hxb | hxb
    · obtain ⟨x, hx⟩ := hxa
      obtain ⟨y, hy⟩ := hxb
      by_contra hab
      have hpos : source (left a) ≠ source (left b) := by
        dsimp only [source, left]
        intro heq
        apply hab
        apply Fin.ext
        omega
      have htwo := two_le_baseCount_of_two_base_getElem hx hy hpos
      omega
    · obtain ⟨x, hx⟩ := hxa
      obtain ⟨y, hy⟩ := hxb
      by_contra hab
      have hpos : source (left a) ≠ source (right b) := by
        dsimp only [source, left, right]
        intro heq
        apply hab
        apply Fin.ext
        omega
      have htwo := two_le_baseCount_of_two_base_getElem hx hy hpos
      omega
    · obtain ⟨x, hx⟩ := hxa
      obtain ⟨y, hy⟩ := hxb
      by_contra hab
      have hpos : source (right a) ≠ source (left b) := by
        dsimp only [source, left, right]
        intro heq
        apply hab
        apply Fin.ext
        omega
      have htwo := two_le_baseCount_of_two_base_getElem hx hy hpos
      omega
    · obtain ⟨x, hx⟩ := hxa
      obtain ⟨y, hy⟩ := hxb
      by_contra hab
      have hpos : source (right a) ≠ source (right b) := by
        dsimp only [source, right]
        intro heq
        apply hab
        apply Fin.ext
        omega
      have htwo := two_le_baseCount_of_two_base_getElem hx hy hpos
      omega
  have hpairwise' : ∀ a b, Valid a → Valid b →
      ∀ i j,
        (i = left a ∨ i = right a) →
        (j = left b ∨ j = right b) →
        index i = index j → i ≠ j →
        ¬ GGT.OsinComponents.Connected E.rel.fam (index i) 1
          (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
          (p.length + source i) (p.length + source j) := by
    intro a b hva hvb i j hi hj hab habne hconn
    have hvalidA : ∃ x : G, q[source i]? =
        some (GGT.RelLetter.comp (index i) x) := by
      rcases hi with rfl | rfl
      · exact hva.1
      · exact hva.2
    have hvalidB : ∃ x : G, q[source j]? =
        some (GGT.RelLetter.comp (index j) x) := by
      rcases hj with rfl | rfl
      · exact hvb.1
      · exact hvb.2
    obtain ⟨xa, hxa⟩ := hvalidA
    obtain ⟨xb, hxb⟩ := hvalidB
    have hcaV := isComp_of_sym_exactRelator E hv (by
      rw [hq, List.getElem?_append_left (hsource_lt i)]
      exact hxa)
    have hcbV := isComp_of_sym_exactRelator E hv (by
      rw [hq, List.getElem?_append_left (hsource_lt j)]
      exact hxb)
    rw [hq] at hcaV hcbV
    have hca := isComp_prefix hcaV (by dsimp only [source]; omega)
    have hcb0 := isComp_prefix hcbV (by dsimp only [source]; omega)
    have hcb : GGT.OsinComponents.IsComp (index i) q
        (source j) (source j + 1) := by simpa only [hab] using hcb0
    exact hpairwise (index i) (source i) (source j) hca hcb
      (by dsimp only [source, P]; omega)
      (by dsimp only [source]; omega) (by dsimp only [source]; omega)
      (fun h ↦ habne (Fin.ext (by dsimp only [source] at h ⊢; omega))) hconn
  obtain ⟨a, hva, hclean, hclean'⟩ :=
    GGT.OsinComponents.exists_valid_paired_seam_clean_sources E.rel.fam
      p q r s source index Valid hinvalid hpairwise'
  obtain ⟨x, hx⟩ := hva.1
  obtain ⟨x', hx'⟩ := hva.2
  let i := source (left a)
  have hi : i = 2 * a + 1 := by rfl
  have hi' : source (right a) = i + 1 := by
    dsimp only [source, left, right, i]
  have hcompV := isComp_of_sym_exactRelator E hv (by
    rw [hq, List.getElem?_append_left (hsource_lt (left a))]
    exact hx)
  have hcompV' := isComp_of_sym_exactRelator E hv (by
    rw [hq, List.getElem?_append_left (hsource_lt (right a))]
    exact hx')
  rw [hq] at hcompV hcompV'
  have hcomp := isComp_prefix hcompV (by dsimp only [source, left, P]; omega)
  have hcomp'0 := isComp_prefix hcompV' (by dsimp only [source, right, P]; omega)
  have hcomp' : GGT.OsinComponents.IsComp (index (right a)) q
      (i + 1) (i + 2) := by simpa only [hi'] using hcomp'0
  have hdeep := comp_value_not_mem_relBall_of_sym_exactRelator E hdesign hv (by
    rw [hq, List.getElem?_append_left (hsource_lt (left a))]
    exact hx)
  have hdeep' := comp_value_not_mem_relBall_of_sym_exactRelator E hdesign hv (by
    rw [hq, List.getElem?_append_left (hsource_lt (right a))]
    exact hx')
  have hspan := span_eq_val_of_getElem? (v := (1 : G)) hx
  have hspan' := span_eq_val_of_getElem? (v := (1 : G)) hx'
  refine ⟨index (left a), index (right a), i, by omega, ?_, hcomp,
    hcomp', ?_, ?_, ?_, ?_⟩
  · dsimp only [i, source, left, P]
    omega
  · rwa [hspan]
  · rw [← hi', hspan']
    exact hdeep'
  · simpa only [i, left, P] using hclean
  · simpa only [i, hi', right, P] using hclean'

/-- **Published-piece matching with arbitrary relative short sides.**

For a prefix of a member of the fixed symmetrized exact relator, the unique
base-letter count supplies `2 (|p| + |r|) + 1` deep interior components.
Indexed finite absorption then forces one of them to match the opposite long
side.  No letter of either short side is assumed to lie in the base alphabet;
their exact relative lengths are paid for in the finite capacity. -/
theorem exists_exact_prefix_opposite_match_relativeSides
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
        ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
        ∀ {v q tail : List (GGT.RelLetter G Bool)},
          RelWord.Sym
            (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
          v = q ++ tail →
          ∀ (p r s : List (GGT.RelLetter G Bool)),
            GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
              GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
            GGT.OsinComponents.IsQuasiGeodesicPolygon E.rel 1 (bn : ℝ) 4 1
              (p ++ q ++ r ++ GGT.OsinComponents.revWord s) →
            C * 4 ≤ rho →
            Fintype.card Bool * (p.length + r.length) + 1 + 3 ≤ q.length →
            (∀ (lam : Bool) (i : ℕ),
              GGT.OsinComponents.IsComp lam q i (i + 1) →
              ∀ i', i' ≤ q.length → i' ≠ i →
                GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i') →
                ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) (p.length + i')) →
            ∃ (lam : Bool) (i j : ℕ),
              0 < i ∧ i + 1 < q.length ∧
              GGT.OsinComponents.IsComp lam q i (i + 1) ∧
              j ≤ s.length ∧
              GGT.OsinComponents.IsCompStart lam
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              (∃ h : G, h ∈ E.rel.fam lam ∧
                GGT.RelLetter.listVal p *
                    GGT.OsinComponents.vertex (1 : G) q i * h =
                  GGT.OsinComponents.vertex (1 : G) s j) ∧
              ∀ m, GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
                GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) m →
                ¬ (m < p.length ∨
                  ∃ a : ℕ, a < r.length ∧
                    m = p.length + q.length + a) := by
  obtain ⟨C, hC, hmatch⟩ :=
    GGT.OsinComponents.exists_opposite_match_of_indexed_deep_run_relativeSides
      E.rel hsymm hδ
  refine ⟨C, hC, ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign v q tail hv hq
    p r s hclose hpoly hrho hlen hnotSame
  obtain ⟨source, index, hsource_inj, hsource_pos, hsource_end,
      hsource_comp, hsource_deep⟩ :=
    exists_indexed_interior_components_of_sym_prefix E hdesign hv hq
      (Fintype.card Bool * (p.length + r.length) + 1) hlen
  obtain ⟨a, j, hj, hjstart, ⟨h, hh, heq⟩, hclean⟩ :=
    hmatch rho p q r s hclose hpoly source index hsource_pos hsource_end
      hsource_comp hsource_inj hsource_deep hrho
      (fun i i' hi' hne hstart =>
        hnotSame (index i) (source i) (hsource_comp i) i' hi' hne hstart)
  exact ⟨index a, source a, j, hsource_pos a, hsource_end a,
    hsource_comp a, hj, hjstart, ⟨h, hh, heq⟩, hclean⟩

/-- The seam-safe published-gap candidate extracted from an exact prefix.
Compared with `exists_exact_prefix_opposite_match_relativeSides`, the count
includes one additional polygon position per peripheral index and therefore
returns a match not ending at the cyclic seam (`j ≠ 1`). -/
theorem exists_exact_prefix_seam_clean_match_relativeSides
    (E : HypEmbeddedCore₂ A N)
    (hsymm : ∀ x ∈ E.rel.base, x⁻¹ ∈ E.rel.base)
    {δ bn : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic E.rel.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {baseLetter : G} {rho eps diffRadius W target : ℕ} {ms : List ℕ},
        ExactRelatorDesign₂ E baseLetter rho eps diffRadius W target ms →
        ∀ {v q tail : List (GGT.RelLetter G Bool)},
          RelWord.Sym
            (relatorWord₂ [baseLetter] (E.lox false) (E.lox true) ms) v →
          v = q ++ tail →
          ∀ (p r s : List (GGT.RelLetter G Bool)),
            GGT.RelLetter.listVal s = GGT.RelLetter.listVal p *
              GGT.RelLetter.listVal q * GGT.RelLetter.listVal r →
            GGT.OsinComponents.IsQuasiGeodesicPolygon E.rel 1 (bn : ℝ) 4 1
              (p ++ q ++ r ++ GGT.OsinComponents.revWord s) →
            C * 4 ≤ rho →
            p.length + r.length + 2 + 3 ≤ q.length →
            (∀ (lam : Bool) (i : ℕ),
              GGT.OsinComponents.IsComp lam q i (i + 1) →
              ∀ i', i' < q.length → i' ≠ i →
                GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i') →
                ¬ GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) (p.length + i')) →
            ∃ (lam : Bool) (i j : ℕ),
              0 < i ∧ i + 1 < q.length ∧
              GGT.OsinComponents.IsComp lam q i (i + 1) ∧
              j ≤ s.length ∧ j ≠ 1 ∧
              GGT.OsinComponents.IsCompStart lam
                (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                (p.length + q.length + r.length + (s.length - j)) ∧
              (∃ h : G, h ∈ E.rel.fam lam ∧
                GGT.RelLetter.listVal p *
                    GGT.OsinComponents.vertex (1 : G) q i * h =
                  GGT.OsinComponents.vertex (1 : G) s j) ∧
              ∀ m, GGT.OsinComponents.IsCompStart lam
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s) m →
                GGT.OsinComponents.Connected E.rel.fam lam 1
                  (p ++ q ++ r ++ GGT.OsinComponents.revWord s)
                  (p.length + i) m →
                ¬ (m < p.length ∨
                  ∃ a : ℕ, a < r.length ∧
                    m = p.length + q.length + a) := by
  obtain ⟨C, hC, hmatch⟩ :=
    GGT.OsinComponents.exists_seam_clean_match_of_indexed_deep_run_relativeSides
      E.rel hsymm hδ
  refine ⟨C, hC, ?_⟩
  intro baseLetter rho eps diffRadius W target ms hdesign v q tail hv hq
    p r s hclose hpoly hrho hlen hnotSame
  obtain ⟨source, index, hsource_inj, hsource_pos, hsource_end,
      hsource_comp, hsource_deep⟩ :=
    exists_indexed_interior_components_of_sym_prefix E hdesign hv hq
      (p.length + r.length + 2) hlen
  obtain ⟨a, j, hj, hjne, hjstart, ⟨h, hh, heq⟩, hclean⟩ :=
    hmatch rho p q r s hclose hpoly source index hsource_pos hsource_end
      hsource_comp hsource_inj hsource_deep hrho
      (fun i i' hi' hne hstart ↦
        hnotSame (index i) (source i) (hsource_comp i) i' hi' hne hstart)
  exact ⟨index a, source a, j, hsource_pos a, hsource_end a,
    hsource_comp a, hj, hjne, hjstart, ⟨h, hh, heq⟩, hclean⟩

end HullSC
end GroupApproximation
