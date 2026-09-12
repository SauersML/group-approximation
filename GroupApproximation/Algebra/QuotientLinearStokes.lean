import GroupApproximation.Algebra.HyperbolicLinearStokes

/-!
# The linear Stokes inequality in a quotient, by amortized shortening

Let `q : G →* Q` be surjective and `S` a symmetric generating set of `G` satisfying the
linear Stokes inequality.  Suppose every word over `S` that dies in `Q` but not in `G`
admits one of two moves, the two branches of Osin's induction in the proof of his
Lemma 5.1 (arXiv:math/0411039v3, (18)--(21)):

* **a relator cut**: after a rotation the word reads `before ++ arc ++ after`, and
  `arc` can be replaced by a strictly shorter word `repl` with the same image in `Q`,
  through an intermediate word `ext` with the same value as `arc` in `G`, where
  `ext` and `repl` together have at most `B` letters;
* **a local shortening**: the word reads `α ++ sub ++ β`, and `sub` has the value of a
  word `geo` with `4 |geo| + 4 ≤ |sub|`.

Then the image alphabet `q '' S` satisfies the linear Stokes inequality
(`linearStokes_image_of_steps`).  Integrals along paths in `Q` are integrals of
pulled-back functions along lifted words (`wordSum_comp_map`).  A cut changes the
integral by the integral along the loop `arc ++ revList ext`, which is closed in `G`,
plus that along `ext ++ revList repl`, which is closed in `Q` and has at most `B`
letters.  A shortening changes it by the integral along `sub ++ revList geo`, closed
in `G`.  Each costs at most a fixed multiple of the letters it saves.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe u v

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- **Integrals of pulled-back functions along a word are integrals along its
image.** -/
theorem wordSum_comp_map (q : G →* Q) (φ ψ : Q → ℤ) :
    ∀ (b : G) (l : List G),
      wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters l) =
        wordSum (id : Q → Q) φ ψ (q b) (trueLetters (l.map q))
  | _, [] => rfl
  | b, x :: l => by
      show edgeTerm (φ ∘ q) (ψ ∘ q) b (b * letterVal (id : G → G) (x, true)) +
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * letterVal (id : G → G) (x, true))
            (trueLetters l) =
        edgeTerm φ ψ (q b) (q b * letterVal (id : Q → Q) (q x, true)) +
          wordSum (id : Q → Q) φ ψ (q b * letterVal (id : Q → Q) (q x, true))
            (trueLetters (l.map q))
      rw [wordSum_comp_map q φ ψ _ l]
      simp only [letterVal_true, id_eq, edgeTerm, Function.comp_apply, map_mul]

/-- Pulled-back integrals depend on the base point only through its image. -/
theorem wordSum_comp_base (q : G →* Q) (φ ψ : Q → ℤ) {b b' : G} (hbb : q b = q b')
    (l : List G) :
    wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters l) =
      wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b' (trueLetters l) := by
  rw [wordSum_comp_map, wordSum_comp_map, hbb]

/-- A function Lipschitz along the image letters pulls back to one Lipschitz along
the letters. -/
theorem lipschitz_comp {S : Set G} (q : G →* Q) {φ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ q '' S → |φ (g * s) - φ g| ≤ 1) :
    ∀ (g s : G), s ∈ S → |(φ ∘ q) (g * s) - (φ ∘ q) g| ≤ 1 := by
  intro g s hs
  simp only [Function.comp_apply, map_mul]
  exact hφ (q g) (q s) ⟨s, hs, rfl⟩

/-- The square bound along a word that closes up in `Q`. -/
theorem abs_wordSum_comp_le_of_map_closed {S : Set G} (q : G →* Q) {φ ψ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ q '' S → |φ (g * s) - φ g| ≤ 1)
    (hψ : ∀ (g s : Q), s ∈ q '' S → |ψ (g * s) - ψ g| ≤ 1)
    {l : List G} (hl : ∀ x ∈ l, x ∈ S) (hq : q l.prod = 1) (b : G) :
    |wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters l)| ≤ (l.length : ℤ) ^ 2 := by
  rw [wordSum_comp_map]
  have h := abs_wordSum_trueLetters_le_of_closed hφ hψ (l := l.map q)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact ⟨y, hl y hy, rfl⟩)
    (q b) (by rw [← MonoidHom.map_list_prod]; exact hq)
  rwa [List.length_map] at h

/-- Rotating a word that closes up in `Q` does not change the pulled-back integral. -/
theorem wordSum_comp_rotate (q : G →* Q) (φ ψ : Q → ℤ) (b : G) {w : List G}
    (hw : q w.prod = 1) {n : ℕ} (hn : n ≤ w.length) :
    wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * (w.take n).prod) (trueLetters (w.rotate n)) =
      wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters w) := by
  rw [List.rotate_eq_drop_append_take hn, trueLetters_append, wordSum_append,
    wordVal_trueLetters]
  conv_rhs => rw [← List.take_append_drop n w, trueLetters_append, wordSum_append,
    wordVal_trueLetters]
  rw [add_comm]
  congr 1
  apply wordSum_comp_base
  rw [map_mul, map_mul, mul_assoc, ← map_mul, ← List.prod_append, List.take_append_drop, hw,
    mul_one]

/-- A word of image letters lifts to a word of letters. -/
theorem exists_lift_word {S : Set G} (q : G →* Q) :
    ∀ l : List Q, (∀ x ∈ l, x ∈ q '' S) → ∃ w : List G, (∀ x ∈ w, x ∈ S) ∧ w.map q = l
  | [], _ => ⟨[], by simp, rfl⟩
  | y :: l, hl => by
      obtain ⟨x, hx, rfl⟩ := hl y (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨w, hw, hwl⟩ := exists_lift_word q l (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      refine ⟨x :: w, ?_, by rw [List.map_cons, hwl]⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hw z hz

/-- The arithmetic of one relator cut. -/
theorem abs_add_add_le_of_cut {x y z : ℤ} {m ly lz a p n C B K : ℕ}
    (hx : |x| ≤ (K : ℤ) * m) (hy : |y| ≤ (C : ℤ) * ly) (hz : |z| ≤ (lz : ℤ) ^ 2)
    (hm : m + a = n + p) (hly : ly + p ≤ a + B) (hlz : lz ≤ B) (hp : p < a)
    (hK : C + C * B + B ^ 2 ≤ K) : |x + y + z| ≤ (K : ℤ) * n := by
  have h1 := abs_add_le (x + y) z
  have h2 := abs_add_le x y
  have hm' : (m : ℤ) + a = n + p := by exact_mod_cast hm
  have hly' : (ly : ℤ) + p ≤ a + B := by exact_mod_cast hly
  have hlz' : (lz : ℤ) ≤ B := by exact_mod_cast hlz
  have hp' : (p : ℤ) + 1 ≤ a := by exact_mod_cast hp
  have hK' : (C : ℤ) + C * B + B ^ 2 ≤ K := by exact_mod_cast hK
  have hC0 : (0 : ℤ) ≤ C := Nat.cast_nonneg C
  have hB0 : (0 : ℤ) ≤ B := Nat.cast_nonneg B
  have hCly : (C : ℤ) * ly ≤ C * (((a : ℤ) - p) + B) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have hsq : (lz : ℤ) ^ 2 ≤ (B : ℤ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hlz' 2
  have hKd : ((C : ℤ) + C * B + B ^ 2) * ((a : ℤ) - p) ≤ K * ((a : ℤ) - p) :=
    mul_le_mul_of_nonneg_right hK' (by linarith)
  have hCBd : ((C : ℤ) * B + B ^ 2) * 1 ≤ ((C : ℤ) * B + B ^ 2) * ((a : ℤ) - p) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

/-- The arithmetic of one local shortening. -/
theorem abs_add_le_of_shorten {x y : ℤ} {m ly s g n C K : ℕ}
    (hx : |x| ≤ (K : ℤ) * m) (hy : |y| ≤ (C : ℤ) * ly) (hly : ly = s + g) (hm : m + s = n + g)
    (h4 : 4 * g + 4 ≤ s) (hK : 2 * C ≤ K) : |x + y| ≤ (K : ℤ) * n := by
  have h1 := abs_add_le x y
  have hm' : (m : ℤ) + s = n + g := by exact_mod_cast hm
  have hly' : (ly : ℤ) = s + g := by exact_mod_cast hly
  have h4' : 4 * (g : ℤ) + 4 ≤ s := by exact_mod_cast h4
  have hK' : 2 * (C : ℤ) ≤ K := by exact_mod_cast hK
  have hC0 : (0 : ℤ) ≤ C := Nat.cast_nonneg C
  have hCs : (C : ℤ) * ly ≤ C * (2 * ((s : ℤ) - g)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have hKd : 2 * (C : ℤ) * ((s : ℤ) - g) ≤ K * ((s : ℤ) - g) :=
    mul_le_mul_of_nonneg_right hK' (by linarith)
  nlinarith

/-- **The linear Stokes inequality for the image alphabet, by Osin's two moves.** -/
theorem linearStokes_image_of_steps {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (q : G →* Q) (hq : Function.Surjective q) {C B : ℕ} (hG : LinearStokes S C)
    (hstep : ∀ w : List G, (∀ x ∈ w, x ∈ S) → q w.prod = 1 → w.prod ≠ 1 →
      (∃ (r : ℕ) (before arc after ext repl : List G),
          w.rotate r = before ++ arc ++ after ∧ (∀ x ∈ ext, x ∈ S) ∧ (∀ x ∈ repl, x ∈ S) ∧
            ext.prod = arc.prod ∧ q repl.prod = q ext.prod ∧ repl.length < arc.length ∧
              ext.length + repl.length ≤ B) ∨
        (∃ (α sub β geo : List G), w = α ++ sub ++ β ∧ (∀ x ∈ geo, x ∈ S) ∧
          geo.prod = sub.prod ∧ 4 * geo.length + 4 ≤ sub.length)) :
    LinearStokes (q '' S) (3 * C + 2 * C * B + B ^ 2) := by
  intro φ ψ hφ hψ
  have hφG := lipschitz_comp q hφ
  have hψG := lipschitz_comp q hψ
  have hmain : ∀ (n : ℕ) (w : List G), w.length = n → (∀ x ∈ w, x ∈ S) → q w.prod = 1 →
      ∀ b : G, |wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters w)| ≤
        ((3 * C + 2 * C * B + B ^ 2 : ℕ) : ℤ) * (w.length : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro w hlen hw hqw b
    by_cases hone : w.prod = 1
    · have h := hG (φ ∘ q) (ψ ∘ q) hφG hψG w hw b hone
      have hCK : (C : ℤ) ≤ ((3 * C + 2 * C * B + B ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_add_right_of_le (Nat.le_add_right_of_le (by omega : C ≤ 3 * C))
      exact le_trans h (mul_le_mul_of_nonneg_right hCK (Nat.cast_nonneg _))
    rcases hstep w hw hqw hone with
        ⟨r, before, arc, after, ext, repl, hrot, hext, hrepl, hextprod, hqrepl, hlt, hB⟩ |
        ⟨α, sub, β, geo, hsplit, hgeo, hgeoprod, h4⟩
    · -- a relator cut
      have hwpos : 0 < w.length := by
        rcases w with _ | ⟨x, w⟩
        · exact absurd rfl hone
        · simp
      have hn'le : r % w.length ≤ w.length := (Nat.mod_lt _ hwpos).le
      have hrot' : w.rotate (r % w.length) = before ++ arc ++ after := by
        rw [List.rotate_mod]
        exact hrot
      have hrotsum := wordSum_comp_rotate q φ ψ b hqw hn'le
      rw [hrot'] at hrotsum
      obtain ⟨b', hb'⟩ : ∃ b', b' = b * (w.take (r % w.length)).prod := ⟨_, rfl⟩
      rw [← hb'] at hrotsum
      have hwrot : ∀ x ∈ before ++ arc ++ after, x ∈ S := by
        intro x hx
        rw [← hrot'] at hx
        exact hw x (List.mem_rotate.mp hx)
      have hbefore : ∀ x ∈ before, x ∈ S := fun x hx => hwrot x (by simp [hx])
      have harc : ∀ x ∈ arc, x ∈ S := fun x hx => hwrot x (by simp [hx])
      have hafter : ∀ x ∈ after, x ∈ S := fun x hx => hwrot x (by simp [hx])
      have hlenrot : before.length + arc.length + after.length = w.length := by
        have h := congrArg List.length hrot'
        simp only [List.length_append, List.length_rotate] at h
        omega
      -- the shortened word
      have hw''letters : ∀ x ∈ before ++ repl ++ after, x ∈ S := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hbefore x hx
        · exact hrepl x hx
        · exact hafter x hx
      have hqw'' : q (before ++ repl ++ after).prod = 1 := by
        have hrotprod : q (w.rotate (r % w.length)).prod = 1 := by
          rw [List.rotate_eq_drop_append_take hn'le, List.prod_append, map_mul]
          have h := hqw
          rw [← List.take_append_drop (r % w.length) w, List.prod_append, map_mul] at h
          exact mul_eq_one_comm.mp h
        rw [hrot'] at hrotprod
        simp only [List.prod_append, map_mul] at hrotprod ⊢
        rw [hqrepl, hextprod]
        exact hrotprod
      have hIH := ih (before ++ repl ++ after).length
        (by simp only [List.length_append]; omega) (before ++ repl ++ after) rfl hw''letters
        hqw'' b'
      -- the integral splits
      have hsum₁ : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b'
          (trueLetters (before ++ arc ++ after)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b' (trueLetters before) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters arc) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod * arc.prod)
              (trueLetters after) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc]
      have hsum₂ : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b'
          (trueLetters (before ++ repl ++ after)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b' (trueLetters before) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters repl) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod * repl.prod)
              (trueLetters after) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc]
      have hbb : q (b' * before.prod * arc.prod) = q (b' * before.prod * repl.prod) := by
        rw [map_mul, map_mul, ← hextprod, ← hqrepl]
      have hloopG : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod)
          (trueLetters (arc ++ revList ext)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters arc) -
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters ext) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, ← hextprod,
          wordSum_trueLetters_revList, sub_eq_add_neg]
      have hloopQ : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod)
          (trueLetters (ext ++ revList repl)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters ext) -
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod) (trueLetters repl) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters,
          wordSum_comp_base q φ ψ
            (show q (b' * before.prod * ext.prod) = q (b' * before.prod * repl.prod) by
              rw [map_mul, map_mul, hqrepl]),
          wordSum_trueLetters_revList, sub_eq_add_neg]
      have hsplit_sum : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b'
          (trueLetters (before ++ arc ++ after)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b' (trueLetters (before ++ repl ++ after)) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod)
              (trueLetters (arc ++ revList ext)) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b' * before.prod)
              (trueLetters (ext ++ revList repl)) := by
        rw [hsum₁, hsum₂, hloopG, hloopQ, wordSum_comp_base q φ ψ hbb after]
        ring
      -- the two loops
      have hGletters : ∀ x ∈ arc ++ revList ext, x ∈ S := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact harc x hx
        · exact letters_revList hS hext x hx
      have hGloop := hG (φ ∘ q) (ψ ∘ q) hφG hψG (arc ++ revList ext) hGletters
        (b' * before.prod) (by rw [List.prod_append, prod_revList, hextprod, mul_inv_cancel])
      have hQletters : ∀ x ∈ ext ++ revList repl, x ∈ S := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hext x hx
        · exact letters_revList hS hrepl x hx
      have hQloop := abs_wordSum_comp_le_of_map_closed q hφ hψ hQletters
        (by rw [List.prod_append, prod_revList, map_mul, map_inv, hqrepl, mul_inv_cancel])
        (b' * before.prod)
      rw [← hrotsum, hsplit_sum]
      exact abs_add_add_le_of_cut hIH hGloop hQloop
        (by simp only [List.length_append]; omega)
        (by simp only [List.length_append, length_revList]; omega)
        (by simp only [List.length_append, length_revList]; omega) hlt
        (by nlinarith [Nat.zero_le (C * B), Nat.zero_le C, Nat.zero_le (B ^ 2)])
    · -- a local shortening
      have hwα : ∀ x ∈ α ++ sub ++ β, x ∈ S := by
        rw [← hsplit]
        exact hw
      have hsub : ∀ x ∈ sub, x ∈ S := fun x hx => hwα x (by simp [hx])
      have hw''letters : ∀ x ∈ α ++ geo ++ β, x ∈ S := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hwα x (by simp [hx])
        · exact hgeo x hx
        · exact hwα x (by simp [hx])
      have hprod'' : (α ++ geo ++ β).prod = w.prod := by
        rw [hsplit]
        simp only [List.prod_append, hgeoprod]
      have hIH := ih (α ++ geo ++ β).length
        (by rw [hsplit] at hlen; simp only [List.length_append] at hlen ⊢; omega)
        (α ++ geo ++ β) rfl hw''letters (by rw [hprod'']; exact hqw) b
      have hsumw : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters (α ++ sub ++ β)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters α) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod) (trueLetters sub) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod * sub.prod) (trueLetters β) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc]
      have hsumw'' : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters (α ++ geo ++ β)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters α) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod) (trueLetters geo) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod * sub.prod) (trueLetters β) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc, hgeoprod]
      have hloop : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod)
          (trueLetters (sub ++ revList geo)) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod) (trueLetters sub) -
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod) (trueLetters geo) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, ← hgeoprod,
          wordSum_trueLetters_revList, sub_eq_add_neg]
      have hGletters : ∀ x ∈ sub ++ revList geo, x ∈ S := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hsub x hx
        · exact letters_revList hS hgeo x hx
      have hGloop := hG (φ ∘ q) (ψ ∘ q) hφG hψG (sub ++ revList geo) hGletters (b * α.prod)
        (by rw [List.prod_append, prod_revList, hgeoprod, mul_inv_cancel])
      have hsplit_sum : wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters w) =
          wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) b (trueLetters (α ++ geo ++ β)) +
            wordSum (id : G → G) (φ ∘ q) (ψ ∘ q) (b * α.prod)
              (trueLetters (sub ++ revList geo)) := by
        rw [hsplit, hsumw, hsumw'', hloop]
        ring
      rw [hsplit_sum]
      exact abs_add_le_of_shorten hIH hGloop
        (by simp only [List.length_append, length_revList])
        (by rw [hsplit]; simp only [List.length_append]; omega) h4
        (by nlinarith [Nat.zero_le (C * B), Nat.zero_le C, Nat.zero_le (B ^ 2)])
  intro l hl b hprod
  obtain ⟨w, hw, rfl⟩ := exists_lift_word q l hl
  obtain ⟨b₀, rfl⟩ := hq b
  rw [← wordSum_comp_map, List.length_map]
  exact hmain w.length w rfl hw (by rw [MonoidHom.map_list_prod]; exact hprod) b₀

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.wordSum_comp_map
#audit_axioms GroupApproximation.DiscreteStokes.wordSum_comp_rotate
#audit_axioms GroupApproximation.DiscreteStokes.abs_add_add_le_of_cut
#audit_axioms GroupApproximation.DiscreteStokes.abs_add_le_of_shorten
#audit_axioms GroupApproximation.DiscreteStokes.linearStokes_image_of_steps
