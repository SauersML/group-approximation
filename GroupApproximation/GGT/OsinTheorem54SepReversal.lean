import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# Reversing a path, and the symmetry of `d̂_λ`

Osin treats `Γ(G, X ⊔ ℋ)` as a graph, whose edges are unoriented: reversing a
path traverses the same edges, so it has the same components, and `d̂_λ` is
symmetric and `S(f,g;D) = S(g,f;D)` without argument.  A `RelLetter` word orients
the edges, and reversing it exchanges each letter for its inverse, so the
argument has to be made — and it needs `RelGenSet.base` to be closed under
inversion, which the structure does not require.  That hypothesis is free:
`GGT.OsinTheorem54SepSymmetric.exists_symmetric_base` supplies it, the failure
of symmetry being confined to the finite set `X ∩ H_λ`.

## What is proved

* `invLetter`, `revWord` --- the reversed word: invert each letter, keeping it on
  the same side of `X ⊔ ℋ`, and reverse the list.  `listVal_revWord`,
  `length_revWord` and `isLetter_of_mem_revWord` are its bookkeeping, the last
  needing the symmetry of the base.
* `avoidsFrom_revWord` --- **the reversed path avoids `Γ_{H_λ}` from the far end
  exactly when the original avoids it from the near end.**  The condition
  defining `AvoidsFrom` forbids reading a `λ`-letter at a vertex of `H_λ`; the
  reversed path reads the inverse letter at the *other* endpoint of the same
  edge, and when the letter is a `λ`-letter the two endpoints lie in `H_λ`
  together.  So the two conditions agree edge by edge, which is exactly the
  statement that the edge, not its orientation, is what `AvoidsFrom` reads.
* `relBall_inv` --- **`d̂_λ` is symmetric**.  With
  `OsinTheorem54SeparatingCosets.one_mem_relBall`, `relBall_mono_radius` and
  `relBall_mul`, this completes `d̂_λ` as a left-invariant metric on `H_λ`, which
  is what Osin's §4 uses it as throughout.

The reversed path is read from `1` rather than from `h` by
`avoidsFrom_smul_left`, `h` lying in `H_λ`; that is the same translation step
that makes `relBall_mul` work.

`SepData.sep_comm` needs one thing more than these: that the components of the
reversed word correspond, index by index, to those of the original, and that the
initial vertex of a component and its terminal vertex name the same coset.  The
second half is immediate, a component's span lying in `H_λ`; the first is index
arithmetic over `revWord` and is not done here.

## A duplication to merge

`GGT.HullSC.RelWord` carries the same construction under other names ---
`inv` and `revInv` in `GGT/HullSCSmallCancellation.lean`, with
`isCompOf_inv`, `isLetter_inv`, `revInv_cons`, `length_revInv`, `listVal_revInv`
and `inv_mem_of_mem_revInv` in `GGT/HullSCRelatorFamily.lean` --- built for
Hull's small-cancellation development.  It is not reused here because reaching
it means importing that whole development into Osin's §4--§5, which are
independent of it.  The construction belongs in
`GGT/WPDHyperbolicallyEmbedded.lean`, where `RelLetter` is defined and where both
lanes could take it from; hoisting it there is an edit to a file this lane does
not own.  Nothing below depends on which copy is used.

`relBall_inv` itself is not a duplicate.  `GGT/HullSCRelatorWord.lean` carries
`h ∉ relBall ρ ∧ h⁻¹ ∉ relBall ρ` as two separate conditions precisely because
the ball was not known to be closed under inversion; with a symmetric base it is,
and the second conjunct is redundant.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Inverting a letter -/

/-- **The letter labelling the reverse of the edge a letter labels**: the inverse
group element, on the same side of `X ⊔ ℋ`.

Keeping the side is the point.  A `λ`-letter reverses to a `λ`-letter, so the
component structure is preserved; an `X`-letter reverses to an `X`-letter, which
is where the base has to be closed under inversion. -/
def invLetter : RelLetter G Λ → RelLetter G Λ
  | RelLetter.base x => RelLetter.base x⁻¹
  | RelLetter.comp lam h => RelLetter.comp lam h⁻¹

theorem val_invLetter (a : RelLetter G Λ) :
    (invLetter a).val = (a.val)⁻¹ := by
  cases a <;> rfl

theorem isCompOf_invLetter (a : RelLetter G Λ) (lam : Λ) :
    (invLetter a).IsCompOf lam ↔ a.IsCompOf lam := by
  cases a <;> exact Iff.rfl

/-- Inverting a letter keeps it admissible, given a base closed under
inversion. -/
theorem isLetter_invLetter (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {a : RelLetter G Λ}
    (hlet : D.IsLetter a) : D.IsLetter (invLetter a) := by
  cases a with
  | base x => exact hsymm x hlet
  | comp lam h => exact inv_mem hlet

/-- **The value of a letter of a component lies in the family.**  A `λ`-letter
is `comp λ h` with `h ∈ H_λ`, and that `h` is its value. -/
theorem val_mem_fam_of_isCompOf (D : RelGenSet G Λ) {a : RelLetter G Λ} {lam : Λ}
    (hlet : D.IsLetter a) (hcomp : a.IsCompOf lam) : a.val ∈ D.fam lam := by
  cases a with
  | base x => exact hcomp.elim
  | comp mu y =>
      have hmu : mu = lam := hcomp
      show y ∈ D.fam lam
      have hy : y ∈ D.fam mu := hlet
      rwa [hmu] at hy

/-! ## Reversing a word -/

/-- **The word labelling the reverse of the path a word labels.** -/
def revWord (w : List (RelLetter G Λ)) : List (RelLetter G Λ) :=
  (w.map invLetter).reverse

theorem revWord_nil : revWord ([] : List (RelLetter G Λ)) = [] := rfl

theorem revWord_cons (a : RelLetter G Λ) (t : List (RelLetter G Λ)) :
    revWord (a :: t) = revWord t ++ [invLetter a] := by
  show ((a :: t).map invLetter).reverse
    = (t.map invLetter).reverse ++ [invLetter a]
  rw [List.map_cons, List.reverse_cons]

theorem length_revWord (w : List (RelLetter G Λ)) :
    (revWord w).length = w.length := by
  show ((w.map invLetter).reverse).length = w.length
  rw [List.length_reverse, List.length_map]

theorem listVal_singleton (a : RelLetter G Λ) :
    RelLetter.listVal [a] = a.val := by
  rw [listVal_cons, RelLetter.listVal_nil, mul_one]

/-- The reversed word spells the inverse. -/
theorem listVal_revWord (w : List (RelLetter G Λ)) :
    RelLetter.listVal (revWord w) = (RelLetter.listVal w)⁻¹ := by
  induction w with
  | nil => rw [revWord_nil, RelLetter.listVal_nil, inv_one]
  | cons a t ih =>
      rw [revWord_cons, listVal_append, ih, listVal_singleton, val_invLetter,
        listVal_cons, mul_inv_rev]

/-- The reversed word is admissible, given a base closed under inversion. -/
theorem isLetter_of_mem_revWord (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {w : List (RelLetter G Λ)}
    (hlet : ∀ b ∈ w, D.IsLetter b) : ∀ b ∈ revWord w, D.IsLetter b := by
  intro b hb
  have hb' : b ∈ (w.map invLetter).reverse := hb
  have hb'' : b ∈ w.map invLetter := List.mem_reverse.mp hb'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb''
  exact isLetter_invLetter D hsymm (hlet c hc)

/-! ## Reading a side backwards without assuming `X = X⁻¹`

Dahmani--Guirardel--Osin close the two fellow-travelling paths of Lemma
4.21(b) into a quadrilateral, whose fourth side is the second path read
backwards.  Reversing a `RelLetter` word inverts each letter *on its own side
of `X ⊔ ℋ`*, so `revWord` is admissible only when `X` is closed under
inversion --- the convention `X = X⁻¹` that Section 4 works under silently,
and which `RelGenSet` does not require.

The convention is not needed.  The reversed *path* is admissible whatever `X`
is, because the alphabet `X ⊔ ℋ` is symmetric: a base letter `x` whose inverse
is not a base letter has `x⁻¹ ∈ H λ` for some `λ`, and then `x ∈ H λ` too, so
the peripheral letter `comp λ x` labels the same edge and reverses to the
admissible `comp λ x⁻¹`.  Substituting letter by letter changes no vertex and
no length, so the substitute may replace the original as a side of a polygon.
-/

/-- **Every admissible letter has an admissible substitute of the same value
whose inverse letter is admissible too.**

A peripheral letter is its own substitute, a subgroup being closed under
inversion.  A base letter `x` with `x⁻¹ ∉ X` becomes `comp λ x` for a `λ` with
`x⁻¹ ∈ H λ`; such a `λ` exists because `X ⊔ ℋ` is symmetric and `x⁻¹` is not a
base letter, and `x ∈ H λ` follows since `H λ` is a subgroup. -/
theorem exists_isLetter_invLetter_of_isLetter (D : RelGenSet G Λ)
    {a : RelLetter G Λ} (ha : D.IsLetter a) :
    ∃ b : RelLetter G Λ, D.IsLetter b ∧ D.IsLetter (invLetter b) ∧
      b.val = a.val := by
  cases a with
  | comp lam y =>
      have hy : y ∈ D.fam lam := ha
      exact ⟨RelLetter.comp lam y, hy, inv_mem hy, rfl⟩
  | base x =>
      have hx : x ∈ D.base := ha
      by_cases hinv : x⁻¹ ∈ D.base
      · exact ⟨RelLetter.base x, hx, hinv, rfl⟩
      · have hxA : x ∈ D.alphabet.carrier := Set.mem_union_left _ hx
        have hinvA : x⁻¹ ∈ D.base ∪
            (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) :=
          D.symmetricGenerating.inv_mem x hxA
        rcases hinvA with hbaseMem | hfamMem
        · exact absurd hbaseMem hinv
        · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hfamMem
          have hlam' : x⁻¹ ∈ D.fam lam := hlam
          have hxlam : x ∈ D.fam lam := by
            have hxx := inv_mem hlam'
            rwa [inv_inv] at hxx
          exact ⟨RelLetter.comp lam x, hxlam, inv_mem hxlam, rfl⟩

/-- **Every admissible word has an admissible substitute reading the same path
whose reversal is admissible.**

The substitute has the same length and the same vertices from every
basepoint, so it is interchangeable with the original as a side of a polygon;
what it gains is that its reversal is again admissible.  This is what lets the
four-gon of Lemma 4.21(b) be formed over an arbitrary relative generating
set. -/
theorem exists_reversibleSubstitute (D : RelGenSet G Λ) :
    ∀ w : List (RelLetter G Λ), (∀ a ∈ w, D.IsLetter a) →
      ∃ w' : List (RelLetter G Λ),
        w'.length = w.length ∧
        (∀ a ∈ w', D.IsLetter a) ∧
        (∀ a ∈ revWord w', D.IsLetter a) ∧
        ∀ (v : G) (i : ℕ), vertex v w' i = vertex v w i := by
  intro w
  induction w with
  | nil =>
      intro _
      refine ⟨[], rfl, ?_, ?_, ?_⟩
      · intro c hc
        simp at hc
      · intro c hc
        rw [revWord_nil] at hc
        simp at hc
      · intro v i
        rfl
  | cons a t ih =>
      intro hlet
      obtain ⟨b, hbLet, hbInv, hbVal⟩ :=
        exists_isLetter_invLetter_of_isLetter D (hlet a List.mem_cons_self)
      obtain ⟨t', hlen, hlet', hrev', hvert'⟩ :=
        ih (fun c hc => hlet c (List.mem_cons_of_mem a hc))
      refine ⟨b :: t', ?_, ?_, ?_, ?_⟩
      · rw [List.length_cons, List.length_cons, hlen]
      · intro c hc
        rcases List.mem_cons.mp hc with hceq | hc'
        · rw [hceq]
          exact hbLet
        · exact hlet' c hc'
      · intro c hc
        rw [revWord_cons] at hc
        rcases List.mem_append.mp hc with hc1 | hc2
        · exact hrev' c hc1
        · rw [List.eq_of_mem_singleton hc2]
          exact hbInv
      · intro v i
        cases i with
        | zero => simp only [vertex_zero]
        | succ j =>
            rw [vertex_cons_succ, vertex_cons_succ, hbVal]
            exact hvert' (v * a.val) j

/-! ## Avoiding `Γ_{H lam}` is a property of the edge, not its orientation -/

/-- **The reversed path avoids `Γ_{H lam}` from the far end exactly when the
original avoids it from the near end.**

`AvoidsFrom` forbids reading a `lam`-letter at a vertex of `H lam`.  The
reversed path reads the inverse of that letter at the *other* endpoint of the
same edge; and when the letter is a `lam`-letter its value lies in `H lam`, so
the two endpoints lie in `H lam` together.  The two conditions therefore agree
edge by edge.

The admissibility hypothesis is used exactly there --- to know that the value of
a `lam`-letter lies in `H lam` --- and nowhere else. -/
theorem avoidsFrom_revWord (D : RelGenSet G Λ) (lam : Λ) :
    ∀ (w : List (RelLetter G Λ)), (∀ b ∈ w, D.IsLetter b) → ∀ v : G,
      (AvoidsFrom D.fam lam (revWord w) (v * RelLetter.listVal w)
        ↔ AvoidsFrom D.fam lam w v) := by
  intro w
  induction w with
  | nil =>
      intro _ v
      rw [revWord_nil, RelLetter.listVal_nil, mul_one]
  | cons a t ih =>
      intro hlet v
      have hla : D.IsLetter a := hlet a List.mem_cons_self
      have hlt : ∀ b ∈ t, D.IsLetter b :=
        fun b hb => hlet b (List.mem_cons_of_mem a hb)
      have hv2 : v * (a.val * RelLetter.listVal t) *
          RelLetter.listVal (revWord t) = v * a.val := by
        rw [listVal_revWord]
        group
      have hfirst : AvoidsFrom D.fam lam (revWord t)
            (v * (a.val * RelLetter.listVal t))
          ↔ AvoidsFrom D.fam lam t (v * a.val) := by
        rw [← mul_assoc]
        exact ih hlt (v * a.val)
      have hhead : AvoidsFrom D.fam lam [invLetter a] (v * a.val)
          ↔ ¬ (a.IsCompOf lam ∧ v ∈ D.fam lam) := by
        constructor
        · rintro ⟨hno, -⟩ hcon
          exact hno ⟨(isCompOf_invLetter a lam).mpr hcon.1,
            mul_mem hcon.2 (val_mem_fam_of_isCompOf D hla hcon.1)⟩
        · intro hno
          refine ⟨?_, trivial⟩
          rintro ⟨hc, hm⟩
          have hcomp : a.IsCompOf lam := (isCompOf_invLetter a lam).mp hc
          refine hno ⟨hcomp, ?_⟩
          have haval : a.val ∈ D.fam lam := val_mem_fam_of_isCompOf D hla hcomp
          have hstep := mul_mem hm (inv_mem haval)
          rwa [mul_assoc, mul_inv_cancel, mul_one] at hstep
      rw [revWord_cons, listVal_cons,
        avoidsFrom_append D.fam lam (revWord t) [invLetter a]
          (v * (a.val * RelLetter.listVal t)),
        hv2, hfirst, hhead]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1⟩

/-! ## `d̂_lam` is symmetric -/

/-- **`d̂_lam(1, h⁻¹) = d̂_lam(1, h)`**, in the form the balls record it.

Reverse the avoiding path to `h`: it avoids `Γ_{H lam}` read from `h` by
`avoidsFrom_revWord`, and reading it from `1` instead is harmless by
`avoidsFrom_smul_left`, `h` lying in `H lam`.  Its length is unchanged and it
spells `h⁻¹`.

With `one_mem_relBall`, `relBall_mono_radius` and `relBall_mul` this makes `d̂_lam`
a left-invariant metric on `H_lam`, which is what Osin's §4 treats it as.  The
hypothesis on the base is supplied for free by
`OsinTheorem54SepSymmetric.exists_symmetric_base`. -/
theorem relBall_inv (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {n : ℕ} {h : G}
    (hb : h ∈ D.relBall lam n) : h⁻¹ ∈ D.relBall lam n := by
  obtain ⟨hf, w, hlet, hval, hav, hlen⟩ := hb
  refine ⟨inv_mem hf, revWord w, isLetter_of_mem_revWord D hsymm hlet, ?_, ?_, ?_⟩
  · rw [listVal_revWord, hval]
  · have hrev := (avoidsFrom_revWord D lam w hlet 1).mpr hav
    rw [one_mul, hval] at hrev
    have hkey := avoidsFrom_smul_left hf (revWord w) 1
    rw [mul_one] at hkey
    exact hkey.mp hrev
  · rw [length_revWord]
    exact hlen

end OsinComponents
end GGT
end GroupApproximation
