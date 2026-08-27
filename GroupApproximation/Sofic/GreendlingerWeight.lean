import GroupApproximation.Sofic.GreendlingerSlide
import GroupApproximation.Sofic.GreendlingerMinimal

/-!
# Expressions as data, and minimality of the total conjugator length

`IsConjProduct` counts factors and nothing else, so the only thing minimality
can say about it is that no two adjacent factors cancel.  The descent needs one
more thing --- that the destroyed block does not swallow a rotation whole --- and
what forbids *that* is minimality of the **total conjugator length**.  To speak
of it at all, an expression has to be data rather than a proposition, and this
file makes it so.

## The data

`conjEval` evaluates a list of conjugator-relator pairs, `ConjValid` says every
relator in it is symmetrized, and `conjWeight` adds up `FreeGroup.norm` of the
conjugators.  `isConjProduct_iff_exists_conjExpr` identifies the propositional
count with the data: `IsConjProduct R n g` holds exactly when some valid
expression of length `n` evaluates to `g`.

`IsMinimalConjExpr` is minimality in the lexicographic order (length, weight),
and `exists_isMinimalConjExpr` produces one by two applications of well-ordering
--- least length, then least weight among that length.  Its length is minimal in
the sense `GreendlingerMinimal` already uses
(`isMinimalConjProduct_of_isMinimalConjExpr`), so everything proved from the
factor count carries over unchanged.

## What the weight forbids

Two moves, each `GreendlingerSlide` proves is an identity, each strictly
shortening:

* `not_absorb_of_minimal` --- a conjugator that begins with the next factor's
  conjugator followed by that factor's whole rotation.  Reordering deletes the
  rotation from the conjugator and saves `|t'|`, which is positive because
  relators are nonempty.  So in a minimal expression **no rotation sits inside
  the next conjugator at that position**.

* `not_slide_of_minimal` --- the configuration the descent's bad case produces:
  the conjugators differ by `q`, the second rotation is `q ++ p`, the first
  inverted rotation is `p ++ p'`.  Swapping and re-conjugating to the meeting
  point saves `|q| - 2|p|`.  So in a minimal expression **the overhang `q` is at
  most twice the overlap `p`** --- and under `C'(1/6)`, `p` is a piece of
  `q ++ p`, which makes `|q|` more than five times `|p|`.  The two cannot both
  hold, so the configuration does not occur.

Neither statement mentions pieces: both are pure weight arithmetic.  The piece
bound enters only where they are used, in `GreendlingerRegime`.

Unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Expressions as data -/

/-- The element a list of conjugator-relator pairs spells. -/
def conjEval : List (FreeGroup α × List (α × Bool)) → FreeGroup α
  | [] => 1
  | (c, s) :: e => c * FreeGroup.mk s * c⁻¹ * conjEval e

@[simp] theorem conjEval_nil :
    conjEval ([] : List (FreeGroup α × List (α × Bool))) = 1 := rfl

@[simp] theorem conjEval_cons (c : FreeGroup α) (s : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    conjEval ((c, s) :: e) = c * FreeGroup.mk s * c⁻¹ * conjEval e := rfl

theorem conjEval_cons' (x : FreeGroup α × List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    conjEval (x :: e) = x.1 * FreeGroup.mk x.2 * x.1⁻¹ * conjEval e := by
  obtain ⟨c, s⟩ := x
  rfl

/-- Replacing the two leading factors by two whose product agrees leaves the
element unchanged. -/
theorem conjEval_replace_two {A B C D : FreeGroup α} {a b c d : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))}
    (h : A * FreeGroup.mk a * A⁻¹ * (B * FreeGroup.mk b * B⁻¹)
      = C * FreeGroup.mk c * C⁻¹ * (D * FreeGroup.mk d * D⁻¹)) :
    conjEval ((A, a) :: (B, b) :: e) = conjEval ((C, c) :: (D, d) :: e) := by
  simp only [← mul_assoc] at h
  simp only [conjEval_cons, ← mul_assoc]
  rw [h]

/-- Every relator occurring in the expression is symmetrized. -/
def ConjValid (R : Set (List (α × Bool)))
    (e : List (FreeGroup α × List (α × Bool))) : Prop :=
  ∀ x ∈ e, x.2 ∈ symmetrization R

theorem conjValid_nil (R : Set (List (α × Bool))) :
    ConjValid R ([] : List (FreeGroup α × List (α × Bool))) := by
  intro x hx
  simp at hx

theorem conjValid_cons_iff {R : Set (List (α × Bool))}
    {x : FreeGroup α × List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} :
    ConjValid R (x :: e) ↔ x.2 ∈ symmetrization R ∧ ConjValid R e := by
  constructor
  · intro h
    exact ⟨h x (List.mem_cons.mpr (Or.inl rfl)),
      fun y hy => h y (List.mem_cons.mpr (Or.inr hy))⟩
  · rintro ⟨hx, he⟩ y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hx
    · exact he y hy'

/-- The total conjugator length. -/
def conjWeight [DecidableEq α] (e : List (FreeGroup α × List (α × Bool))) : ℕ :=
  (e.map fun x => FreeGroup.norm x.1).sum

@[simp] theorem conjWeight_nil [DecidableEq α] :
    conjWeight ([] : List (FreeGroup α × List (α × Bool))) = 0 := rfl

@[simp] theorem conjWeight_cons [DecidableEq α] (c : FreeGroup α)
    (s : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool))) :
    conjWeight ((c, s) :: e) = FreeGroup.norm c + conjWeight e := by
  simp [conjWeight]

/-! ## The data and the count agree -/

theorem isConjProduct_iff_exists_conjExpr {R : Set (List (α × Bool))} :
    ∀ (n : ℕ) (g : FreeGroup α),
      IsConjProduct R n g ↔
        ∃ e : List (FreeGroup α × List (α × Bool)),
          ConjValid R e ∧ e.length = n ∧ conjEval e = g := by
  intro n
  induction n with
  | zero =>
      intro g
      constructor
      · intro h
        have hg : g = 1 := h
        exact ⟨[], conjValid_nil R, rfl, by rw [conjEval_nil, hg]⟩
      · rintro ⟨e, -, hlen, heval⟩
        have hnil : e = [] := List.length_eq_zero_iff.mp hlen
        subst hnil
        show g = 1
        rw [← heval, conjEval_nil]
  | succ n ih =>
      intro g
      constructor
      · rintro ⟨c, s, hs, h, hh, rfl⟩
        obtain ⟨e, hv, hlen, heval⟩ := (ih h).mp hh
        refine ⟨(c, s) :: e, conjValid_cons_iff.mpr ⟨hs, hv⟩, by simp [hlen], ?_⟩
        rw [conjEval_cons, heval]
      · rintro ⟨e, hv, hlen, heval⟩
        cases e with
        | nil =>
            rw [List.length_nil] at hlen
            exact absurd hlen (by omega)
        | cons x e' =>
            obtain ⟨hx, hv'⟩ := conjValid_cons_iff.mp hv
            have hlen' : e'.length = n := by
              rw [List.length_cons] at hlen
              omega
            refine ⟨x.1, x.2, hx, conjEval e',
              (ih (conjEval e')).mpr ⟨e', hv', hlen', rfl⟩, ?_⟩
            rw [← heval, conjEval_cons']

/-! ## Reading an expression backwards -/

theorem conjEval_append (e₁ e₂ : List (FreeGroup α × List (α × Bool))) :
    conjEval (e₁ ++ e₂) = conjEval e₁ * conjEval e₂ := by
  induction e₁ with
  | nil => rw [List.nil_append, conjEval_nil, one_mul]
  | cons x e₁ ih =>
      obtain ⟨c, s⟩ := x
      rw [List.cons_append, conjEval_cons, conjEval_cons, ih]
      simp only [← mul_assoc]

theorem conjWeight_append [DecidableEq α]
    (e₁ e₂ : List (FreeGroup α × List (α × Bool))) :
    conjWeight (e₁ ++ e₂) = conjWeight e₁ + conjWeight e₂ := by
  simp [conjWeight]

/-- The expression read backwards, with every relator inverted.  It spells the
inverse element, and `symmetrization` is closed under `invRev`, so it is again
an expression over the same relators. -/
def conjInv (e : List (FreeGroup α × List (α × Bool))) :
    List (FreeGroup α × List (α × Bool)) :=
  (e.map fun x => (x.1, FreeGroup.invRev x.2)).reverse

@[simp] theorem conjInv_nil :
    conjInv ([] : List (FreeGroup α × List (α × Bool))) = [] := rfl

theorem conjInv_cons (c : FreeGroup α) (s : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    conjInv ((c, s) :: e) = conjInv e ++ [(c, FreeGroup.invRev s)] := by
  simp [conjInv]

@[simp] theorem length_conjInv (e : List (FreeGroup α × List (α × Bool))) :
    (conjInv e).length = e.length := by
  simp [conjInv]

theorem conjEval_conjInv (e : List (FreeGroup α × List (α × Bool))) :
    conjEval (conjInv e) = (conjEval e)⁻¹ := by
  induction e with
  | nil => rw [conjInv_nil, conjEval_nil, inv_one]
  | cons x e ih =>
      obtain ⟨c, s⟩ := x
      rw [conjInv_cons, conjEval_append, ih, conjEval_cons, conjEval_cons,
        conjEval_nil, mul_one, mk_invRev_eq_inv]
      group

theorem conjValid_conjInv {R : Set (List (α × Bool))}
    {e : List (FreeGroup α × List (α × Bool))} (h : ConjValid R e) :
    ConjValid R (conjInv e) := by
  intro x hx
  simp only [conjInv, List.mem_reverse, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact invRev_mem_symmetrization (h y hy)

theorem conjWeight_conjInv [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) :
    conjWeight (conjInv e) = conjWeight e := by
  induction e with
  | nil => rfl
  | cons x e ih =>
      obtain ⟨c, s⟩ := x
      rw [conjInv_cons, conjWeight_append, ih, conjWeight_cons, conjWeight_cons,
        conjWeight_nil]
      omega

/-! ## Minimality in length, then weight -/

/-- A shortest expression which, among those of its length, has least total
conjugator length. -/
def IsMinimalConjExpr [DecidableEq α] (R : Set (List (α × Bool)))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) : Prop :=
  ConjValid R e ∧ conjEval e = g ∧
    (∀ e', ConjValid R e' → conjEval e' = g → e.length ≤ e'.length) ∧
    (∀ e', ConjValid R e' → conjEval e' = g → e'.length = e.length →
      conjWeight e ≤ conjWeight e')

/-- **Two well-orderings produce the minimum**: least length, then least weight
among that length. -/
theorem exists_isMinimalConjExpr [DecidableEq α] {R : Set (List (α × Bool))}
    {g : FreeGroup α}
    (h : ∃ e : List (FreeGroup α × List (α × Bool)),
      ConjValid R e ∧ conjEval e = g) :
    ∃ e, IsMinimalConjExpr R e g := by
  classical
  have hL : ∃ n, ∃ e : List (FreeGroup α × List (α × Bool)),
      ConjValid R e ∧ conjEval e = g ∧ e.length = n := by
    obtain ⟨e, hv, he⟩ := h
    exact ⟨e.length, e, hv, he, rfl⟩
  have hW : ∃ m, ∃ e : List (FreeGroup α × List (α × Bool)),
      ConjValid R e ∧ conjEval e = g ∧ e.length = Nat.find hL ∧
        conjWeight e = m := by
    obtain ⟨e, hv, he, hl⟩ := Nat.find_spec hL
    exact ⟨conjWeight e, e, hv, he, hl, rfl⟩
  obtain ⟨e, hv, he, hl, hw⟩ := Nat.find_spec hW
  refine ⟨e, hv, he, ?_, ?_⟩
  · intro e' hv' he'
    rw [hl]
    exact Nat.find_min' hL ⟨e', hv', he', rfl⟩
  · intro e' hv' he' hlen
    rw [hw]
    exact Nat.find_min' hW ⟨e', hv', he', by rw [hlen, hl], rfl⟩

/-- The length of a minimal expression is minimal in the sense the factor-count
argument uses, so everything `GreendlingerMinimal` proves applies to it. -/
theorem isMinimalConjProduct_of_isMinimalConjExpr [DecidableEq α]
    {R : Set (List (α × Bool))} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} (h : IsMinimalConjExpr R e g) :
    IsMinimalConjProduct R e.length g := by
  obtain ⟨hv, he, hlen, -⟩ := h
  refine And.intro ((isConjProduct_iff_exists_conjExpr e.length g).mpr
    ⟨e, hv, rfl, he⟩) ?_
  intro m hm hcon
  obtain ⟨e', hv', hlen', he'⟩ := (isConjProduct_iff_exists_conjExpr m g).mp hcon
  have := hlen e' hv' he'
  omega

/-- **Minimality is inherited by the backwards reading.**  Length and weight are
unchanged, and expressions for `g⁻¹` correspond to expressions for `g`. -/
theorem isMinimalConjExpr_conjInv [DecidableEq α] {R : Set (List (α × Bool))}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (h : IsMinimalConjExpr R e g) : IsMinimalConjExpr R (conjInv e) g⁻¹ := by
  obtain ⟨hv, he, hlen, hw⟩ := h
  refine ⟨conjValid_conjInv hv, by rw [conjEval_conjInv, he], ?_, ?_⟩
  · intro e' hv' he'
    rw [length_conjInv]
    have hb := hlen (conjInv e') (conjValid_conjInv hv')
      (by rw [conjEval_conjInv, he', inv_inv])
    rwa [length_conjInv] at hb
  · intro e' hv' he' hlen'
    rw [conjWeight_conjInv]
    have hb := hw (conjInv e') (conjValid_conjInv hv')
      (by rw [conjEval_conjInv, he', inv_inv])
      (by rw [length_conjInv, hlen', length_conjInv])
    rwa [conjWeight_conjInv] at hb

/-! ## What the weight forbids -/

/-- **No rotation inside the next conjugator.**  If the leading conjugator
begins with the next factor's conjugator followed by that factor's whole
rotation, reordering the two factors deletes the rotation and saves `|t'|`. -/
theorem not_absorb_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {c' t' q'' t : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk (c' ++ (t' ++ q'')), t) :: (FreeGroup.mk c', t') :: e) g)
    (hred : FreeGroup.IsReduced (c' ++ (t' ++ q''))) (ht' : t' ≠ []) : False := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  -- the reordered expression
  have hv2 : ConjValid R
      ((FreeGroup.mk c', t') :: (FreeGroup.mk (c' ++ q''), t) :: e) :=
    conjValid_cons_iff.mpr ⟨h3, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_absorb c' t' q'' t
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk c', t') :: (FreeGroup.mk (c' ++ q''), t) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk c', t') ::
      (FreeGroup.mk (c' ++ q''), t) :: e).length
      = ((FreeGroup.mk (c' ++ (t' ++ q'')), t) ::
        (FreeGroup.mk c', t') :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c' ++ (t' ++ q'')))
      = c'.length + (t'.length + q''.length) := by
    rw [norm_mk_of_isReduced hred]
    simp [List.length_append]
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c' ++ q''))
      ≤ c'.length + q''.length := by
    have := norm_mk_le_length (c' ++ q'')
    rwa [List.length_append] at this
  have hpos : 0 < t'.length := List.length_pos_iff.mpr ht'
  omega

/-- **No long overhang against a short overlap.**  In the configuration the
descent's bad case produces --- conjugators differing by `q`, second rotation
`q ++ p`, first inverted rotation `p ++ p'` --- swapping the two factors and
re-conjugating them to the meeting point saves `|q| - 2|p|`.  So a minimal
expression forces `|q| ≤ 2|p|`. -/
theorem overhang_le_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {c' q p p' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk (c' ++ q), FreeGroup.invRev p' ++ FreeGroup.invRev p)
        :: (FreeGroup.mk c', q ++ p) :: e) g)
    (hred : FreeGroup.IsReduced (c' ++ q)) : q.length ≤ 2 * p.length := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hrot : p ++ q ∈ symmetrization R := append_swap_mem_symmetrization h3
  have hv2 : ConjValid R
      ((FreeGroup.mk (c' ++ FreeGroup.invRev p), p ++ q)
        :: (FreeGroup.mk (c' ++ FreeGroup.invRev p),
          FreeGroup.invRev p' ++ FreeGroup.invRev p) :: e) :=
    conjValid_cons_iff.mpr ⟨hrot, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_slide c' q p p'
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk (c' ++ FreeGroup.invRev p), p ++ q)
        :: (FreeGroup.mk (c' ++ FreeGroup.invRev p),
          FreeGroup.invRev p' ++ FreeGroup.invRev p) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk (c' ++ FreeGroup.invRev p), p ++ q)
      :: (FreeGroup.mk (c' ++ FreeGroup.invRev p),
        FreeGroup.invRev p' ++ FreeGroup.invRev p) :: e).length
      = ((FreeGroup.mk (c' ++ q), FreeGroup.invRev p' ++ FreeGroup.invRev p)
        :: (FreeGroup.mk c', q ++ p) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hredc' : FreeGroup.IsReduced c' :=
    isReduced_of_infix ⟨[], q, by simp⟩ hred
  have hnorm : FreeGroup.norm (FreeGroup.mk (c' ++ q))
      = c'.length + q.length := by
    rw [norm_mk_of_isReduced hred, List.length_append]
  have hnormc' : FreeGroup.norm (FreeGroup.mk c') = c'.length :=
    norm_mk_of_isReduced hredc'
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c' ++ FreeGroup.invRev p))
      ≤ c'.length + p.length := by
    have hb := norm_mk_le_length (c' ++ FreeGroup.invRev p)
    rw [List.length_append, FreeGroup.invRev_length] at hb
    exact hb
  omega

/-- **The absorb move, mirrored.**  If the *second* conjugator begins with the
first followed by the first factor's inverted rotation, reordering deletes that
copy and saves `|t|`. -/
theorem not_absorb_inv_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {c t Z t' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t)
      :: (FreeGroup.mk (c ++ (FreeGroup.invRev t ++ Z)), t') :: e) g)
    (hred : FreeGroup.IsReduced (c ++ (FreeGroup.invRev t ++ Z)))
    (ht : t ≠ []) : False := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hv2 : ConjValid R
      ((FreeGroup.mk (c ++ Z), t') :: (FreeGroup.mk c, t) :: e) :=
    conjValid_cons_iff.mpr ⟨h3, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_absorb_inv c t Z t'
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk (c ++ Z), t') :: (FreeGroup.mk c, t) :: e) = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk (c ++ Z), t') :: (FreeGroup.mk c, t) :: e).length
      = ((FreeGroup.mk c, t)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev t ++ Z)), t') :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c ++ (FreeGroup.invRev t ++ Z)))
      = c.length + (t.length + Z.length) := by
    rw [norm_mk_of_isReduced hred]
    simp [FreeGroup.invRev_length]
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c ++ Z)) ≤ c.length + Z.length := by
    have hb := norm_mk_le_length (c ++ Z)
    rwa [List.length_append] at hb
  have hpos : 0 < t.length := List.length_pos_iff.mpr ht
  omega

/-- **The meet move.**  If the second conjugator overhangs the first by `y`,
and `y` is what the first inverted rotation begins with, swapping the factors
and re-conjugating the second to the meeting point saves `|y| - |v|`.  So a
minimal expression forces `|y| ≤ |v|`. -/
theorem overhang_le_of_minimal_meet [DecidableEq α] {R : Set (List (α × Bool))}
    {c y v u : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, FreeGroup.invRev v ++ FreeGroup.invRev y)
        :: (FreeGroup.mk (c ++ y), v ++ u) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ y)) : y.length ≤ v.length := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  have hv2 : ConjValid R
      ((FreeGroup.mk (c ++ FreeGroup.invRev v), v ++ u)
        :: (FreeGroup.mk c, FreeGroup.invRev v ++ FreeGroup.invRev y) :: e) :=
    conjValid_cons_iff.mpr ⟨h3, conjValid_cons_iff.mpr ⟨h1, h4⟩⟩
  have hmove := mk_palindrome_mul_meet c y v u
  simp only [mk_palindrome] at hmove
  have he2 : conjEval
      ((FreeGroup.mk (c ++ FreeGroup.invRev v), v ++ u)
        :: (FreeGroup.mk c, FreeGroup.invRev v ++ FreeGroup.invRev y) :: e)
      = g := by
    rw [← conjEval_replace_two hmove]
    exact he
  have hlen2 : ((FreeGroup.mk (c ++ FreeGroup.invRev v), v ++ u)
      :: (FreeGroup.mk c, FreeGroup.invRev v ++ FreeGroup.invRev y) :: e).length
      = ((FreeGroup.mk c, FreeGroup.invRev v ++ FreeGroup.invRev y)
        :: (FreeGroup.mk (c ++ y), v ++ u) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c ++ y)) = c.length + y.length := by
    rw [norm_mk_of_isReduced hred, List.length_append]
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c ++ FreeGroup.invRev v))
      ≤ c.length + v.length := by
    have hb := norm_mk_le_length (c ++ FreeGroup.invRev v)
    rw [List.length_append, FreeGroup.invRev_length] at hb
    exact hb
  omega

/-! ## The palindromic presentation is again minimal -/

/-- A reduced palindrome spells an element of length `2|c| + |t|`. -/
theorem norm_mk_palindrome [DecidableEq α] {c t : List (α × Bool)}
    (h : FreeGroup.IsReduced (palindrome c t)) :
    FreeGroup.norm (FreeGroup.mk (palindrome c t)) = 2 * c.length + t.length := by
  have hlen : (palindrome c t).length = c.length + t.length + c.length := by
    simp [palindrome, FreeGroup.invRev_length, Nat.add_assoc]
  rw [norm_mk_of_isReduced h, hlen]
  omega

/-- **The normal form never lengthens the conjugator.**  A conjugate spelled by
a reduced palindrome has `|c| ≤ norm x` for every `x` conjugating the relator to
it: the palindrome *is* the reduced word of the element, so its length is the
norm, and the norm of a conjugate is at most `2 norm x + |s|`. -/
theorem norm_conjugator_le [DecidableEq α] {x : FreeGroup α}
    {s c t : List (α × Bool)}
    (hred : FreeGroup.IsReduced (palindrome c t)) (hlen : t.length = s.length)
    (heq : x * FreeGroup.mk s * x⁻¹ = FreeGroup.mk (palindrome c t)) :
    c.length ≤ FreeGroup.norm x := by
  have h1 : FreeGroup.norm (FreeGroup.mk (palindrome c t))
      = 2 * c.length + t.length := norm_mk_palindrome hred
  have h2 : FreeGroup.norm (x * FreeGroup.mk s * x⁻¹)
      ≤ FreeGroup.norm (x * FreeGroup.mk s) + FreeGroup.norm x⁻¹ :=
    FreeGroup.norm_mul_le _ _
  have h3 : FreeGroup.norm (x * FreeGroup.mk s)
      ≤ FreeGroup.norm x + FreeGroup.norm (FreeGroup.mk s) :=
    FreeGroup.norm_mul_le _ _
  have h4 : FreeGroup.norm (FreeGroup.mk s) ≤ s.length := FreeGroup.norm_mk_le
  have h5 : FreeGroup.norm x⁻¹ = FreeGroup.norm x := FreeGroup.norm_inv_eq
  rw [heq, h1] at h2
  omega

/-- **A factor in palindromic normal form**, with its conjugator no longer than
the one it replaces. -/
theorem exists_palindrome_factor [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {s : List (α × Bool)} (hs : s ∈ symmetrization R) (x : FreeGroup α) :
    ∃ c t : List (α × Bool), t ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c t) ∧
      FreeGroup.mk c * FreeGroup.mk t * (FreeGroup.mk c)⁻¹
        = x * FreeGroup.mk s * x⁻¹ ∧
      FreeGroup.norm (FreeGroup.mk c) ≤ FreeGroup.norm x := by
  obtain ⟨c, k, hred, hnf⟩ := exists_conjugation_normalForm
    (symmetrization_isCyclicallyReduced hR hs)
    (ne_nil_of_mem_symmetrization hRne hs) x.toWord
  rw [FreeGroup.mk_toWord] at hnf
  refine ⟨c, s.rotate k, rotate_mem_symmetrization hs k, hred, ?_, ?_⟩
  · rw [← mk_palindrome]
    exact hnf.symm
  · have hredc : FreeGroup.IsReduced c :=
      isReduced_of_infix ⟨[], s.rotate k ++ FreeGroup.invRev c, by simp [palindrome]⟩
        hred
    rw [norm_mk_of_isReduced hredc]
    exact norm_conjugator_le hred (by rw [List.length_rotate]) hnf

/-- **The palindromic presentation of a minimal expression is again minimal.**
Each factor is replaced by its normal form, which spells the same element with a
conjugator no longer, so the length is unchanged and the weight cannot rise ---
and therefore, by minimality, cannot fall either. -/
theorem exists_palindromic_isMinimalConjExpr [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {x x' : FreeGroup α} {s s' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((x, s) :: (x', s') :: e) g) :
    ∃ c t c' t' : List (α × Bool),
      t ∈ symmetrization R ∧ t' ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c t) ∧
        FreeGroup.IsReduced (palindrome c' t') ∧
        IsMinimalConjExpr R
          ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g := by
  obtain ⟨hv, he, hlen, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  obtain ⟨c, t, ht, hredt, heqt, hnormt⟩ := exists_palindrome_factor hR hRne h1 x
  obtain ⟨c', t', ht', hredt', heqt', hnormt'⟩ :=
    exists_palindrome_factor hR hRne h3 x'
  rw [conjEval_cons, conjEval_cons] at he
  refine ⟨c, t, c', t', ht, ht', hredt, hredt',
    conjValid_cons_iff.mpr ⟨ht, conjValid_cons_iff.mpr ⟨ht', h4⟩⟩, ?_, ?_, ?_⟩
  · rw [conjEval_cons, conjEval_cons, heqt, heqt']
    exact he
  · intro e₀ hv₀ he₀
    have hb := hlen e₀ hv₀ he₀
    simpa using hb
  · intro e₀ hv₀ he₀ hlen₀
    have hb : conjWeight ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e)
        ≤ conjWeight ((x, s) :: (x', s') :: e) := by
      simp only [conjWeight_cons]
      omega
    refine le_trans hb (hweight e₀ hv₀ he₀ ?_)
    simpa using hlen₀

end SmallCancellationRouter
end GroupApproximation
