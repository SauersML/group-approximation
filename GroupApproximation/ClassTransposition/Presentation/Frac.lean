import GroupApproximation.Kourovka1759.Equi

/-!
# Permutations between ordered box partitions

Kourovka 17.61 lane, the finite presentation of `CT_P(ℤ)` (research node
`ct-p-z-is-finitely-presented-by-position-shifting`, §1).

For two ordered partitions `b, c` of `ℤ` into boxes, of the same length, `frac b c` is the
permutation mapping the `k`-th box of `b` canonically onto the `k`-th box of `c`. It is the only
such permutation (`eq_frac`). Together with the composition rules for canonical maps
(`GroupApproximation.Kourovka1759.forall₂_canon_comp`), this computes the evaluation of the
finite presentation.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

instance (B : Box) (n : ℤ) : Decidable (B.Mem n) := inferInstanceAs (Decidable (n % B.m = B.r))

/-- An ordered partition of `ℤ` into boxes. -/
def IsPart (b : List Box) : Prop := b.Pairwise Box.Disj ∧ ∀ n, ∃ B ∈ b, B.Mem n

/-- The piecewise canonical map sending the `k`-th box of `b` onto the `k`-th box of `c`. -/
def fracFun : List Box → List Box → ℤ → ℤ
  | B :: b, C :: c, n => if B.Mem n then C.r + n / B.m * C.m else fracFun b c n
  | _, _, n => n

theorem fracFun_cons (B C : Box) (b c : List Box) (n : ℤ) :
    fracFun (B :: b) (C :: c) n = if B.Mem n then C.r + n / B.m * C.m else fracFun b c n := rfl

/-- `f` maps `B` onto `C` canonically. -/
def CanonF (f : ℤ → ℤ) (B C : Box) : Prop := ∀ t : ℤ, f (B.r + t * B.m) = C.r + t * C.m

theorem canonF_fracFun_aux : ∀ (b c : List Box), b.Pairwise Box.Disj → b.length = c.length →
    ∀ f : ℤ → ℤ, (∀ n, (∃ B ∈ b, B.Mem n) → f n = fracFun b c n) →
    List.Forall₂ (CanonF f) b c
  | [], [], _, _, _, _ => .nil
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | B :: b, C :: c, hp, hl, f, hf => by
    rw [List.pairwise_cons] at hp
    refine .cons ?_ ?_
    · intro t
      rw [hf _ ⟨B, List.mem_cons_self, B.elt_mem t⟩, fracFun_cons, if_pos (B.elt_mem t), B.elt_div]
    · refine canonF_fracFun_aux b c hp.2 (by simpa using hl) f fun n ⟨B', hB', hn⟩ => ?_
      have hnB : ¬ B.Mem n := fun h => hp.1 B' hB' n h hn
      rw [hf n ⟨B', List.mem_cons_of_mem _ hB', hn⟩, fracFun_cons, if_neg hnB]

theorem canonF_fracFun {b c : List Box} (hp : b.Pairwise Box.Disj) (hl : b.length = c.length) :
    List.Forall₂ (CanonF (fracFun b c)) b c :=
  canonF_fracFun_aux b c hp hl _ fun _ _ => rfl

/-- A pair of `Forall₂`-related lists: every element on the left has a partner. -/
theorem forall₂_exists_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', hr⟩ := forall₂_exists_left h a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', hr⟩

theorem forall₂_and {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ S l l' →
      List.Forall₂ (fun a b => R a b ∧ S a b) l l'
  | _, _, .nil, .nil => .nil
  | _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (forall₂_and t1 t2)

theorem forall₂_flip {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ (fun b a => R a b) l' l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_flip t)

theorem fracFun_inv {b c : List Box} (hb : IsPart b) (hc : IsPart c)
    (hl : b.length = c.length) (n : ℤ) : fracFun c b (fracFun b c n) = n := by
  have h := forall₂_and (canonF_fracFun hb.1 hl) (forall₂_flip (canonF_fracFun hc.1 hl.symm))
  obtain ⟨B, hB, hn⟩ := hb.2 n
  obtain ⟨C, -, h1, h2⟩ := forall₂_exists_left h B hB
  conv_lhs => rw [← B.eq_of_mem hn]
  rw [h1, h2, B.eq_of_mem hn]

open Classical in
/-- The permutation mapping the ordered partition `b` onto `c` box by box (the identity when
`b, c` are not ordered partitions of the same length). -/
noncomputable def frac (b c : List Box) : Perm ℤ :=
  if h : IsPart b ∧ IsPart c ∧ b.length = c.length then
    { toFun := fracFun b c
      invFun := fracFun c b
      left_inv := fracFun_inv h.1 h.2.1 h.2.2
      right_inv := fracFun_inv h.2.1 h.1 h.2.2.symm }
  else 1

theorem frac_apply {b c : List Box} (hb : IsPart b) (hc : IsPart c) (hl : b.length = c.length)
    (n : ℤ) : frac b c n = fracFun b c n := by
  rw [frac, dif_pos ⟨hb, hc, hl⟩]; rfl

theorem frac_canon {b c : List Box} (hb : IsPart b) (hc : IsPart c) (hl : b.length = c.length) :
    List.Forall₂ (CanonOn (frac b c)) b c := by
  have h := canonF_fracFun hb.1 hl
  have e : ∀ n, frac b c n = fracFun b c n := frac_apply hb hc hl
  exact h.imp fun B C hBC t => by rw [e]; exact hBC t

/-- A permutation mapping an ordered partition `b` canonically onto `c`, box by box, is
`frac b c`. -/
theorem eq_frac {g : Perm ℤ} {b c : List Box} (hb : IsPart b) (hc : IsPart c)
    (hg : List.Forall₂ (CanonOn g) b c) : g = frac b c := by
  have hl := hg.length_eq
  have h := forall₂_and hg (frac_canon hb hc hl)
  ext n
  obtain ⟨B, hB, hn⟩ := hb.2 n
  obtain ⟨C, -, h1, h2⟩ := forall₂_exists_left h B hB
  exact h1.agree h2 hn

theorem frac_self {b : List Box} (hb : IsPart b) : frac b b = 1 :=
  (eq_frac hb hb (forall₂_canon_one b)).symm

/-- Composition: `frac c d * frac b c = frac b d`. -/
theorem frac_mul {b c d : List Box} (hb : IsPart b) (hc : IsPart c) (hd : IsPart d)
    (h1 : b.length = c.length) (h2 : c.length = d.length) :
    frac c d * frac b c = frac b d :=
  eq_frac hb hd (forall₂_canon_comp (frac_canon hb hc h1) (frac_canon hc hd h2))

theorem frac_inv {b c : List Box} (hb : IsPart b) (hc : IsPart c) (hl : b.length = c.length) :
    (frac b c)⁻¹ = frac c b :=
  eq_frac hc hb (forall₂_canon_inv (frac_canon hb hc hl))

end GroupApproximation.ClassTransposition.Presentation
