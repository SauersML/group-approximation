import GroupApproximation.Sofic.GreendlingerLandingConfined
import GroupApproximation.Sofic.GreendlingerDeepOverrunCount

/-!
# A provenance-preserving residual for the non-confined landing

`StoppingAlternativeBetaSharp` is too strong because its block length is free:
it asks about blocks which the cascade never produces.  The corrected residual
below keeps the block attached to the actual cancellation split of the factor
which it meets.

If that factor keeps `P₂` and loses `M₂`, an incoming block of length `|M|`
which overruns `P₂` becomes the uniquely determined residual block

    |M| + |M₂| - |P₂|.

This is precisely the input of `landsInSharp_of_overrun`; no arbitrary block is
quantified.  The bridge below proves that this corrected residual implies
`NonConfinedBlockLands`.  Thus the remaining open statement is isolated after
one real cascade step, rather than hidden in the false stopping alternative.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## A measured, alignment-carrying cascade cursor -/

/-- If the tracked endpoint lies strictly inside the survivor of the current
palindrome, but past its leading conjugator, then the current residual word
really does open with that conjugator.  This is the precise (and only) place
where the opening premise used to construct an aligned cursor is obtained; it
must not be silently transported through an overrun step. -/
theorem exists_current_open_of_inside_survivor
    {c t P M B V : List (α × Bool)} {b : ℕ}
    (hpal : palindrome c t = P ++ M) (hword : V = P ++ B)
    (hc : c.length < b) (hinside : b < P.length) :
    ∃ Z : List (α × Bool), V = c ++ Z := by
  have hcpre : c <+: palindrome c t := by
    refine ⟨t ++ FreeGroup.invRev c, ?_⟩
    unfold palindrome
    simp only [List.append_assoc]
  have hPpre : P <+: palindrome c t := ⟨M, hpal.symm⟩
  have hcP : c <+: P :=
    List.prefix_of_prefix_length_le hcpre hPpre (by omega)
  obtain ⟨Z₀, hZ₀⟩ := hcP
  refine ⟨Z₀ ++ B, ?_⟩
  rw [hword, ← hZ₀, List.append_assoc]

/-- The concrete word eaten by an overrun is preserved, not merely its
length.  If `invRev L` is the incoming prefix and the current factor keeps
`P` while losing `M`, coverage of `P` produces the next incoming word
`invRev K ++ M`, whose inverse is exactly the prefix
`invRev M ++ K` of the tail.  Its length is the arithmetic residual used by
`AlignedCascadeSearch.overrun`.

This lemma is the provenance update needed by a well-founded cascade.  Keeping
only the number `|L| + |M| - |P|` loses the alignment information and is not
enough to build a later cursor. -/
theorem exists_residual_block_of_overrun
    {L P M B V : List (α × Bool)}
    (hin : FreeGroup.invRev L <+: P ++ B)
    (hcover : P.length ≤ L.length)
    (htail : V = FreeGroup.invRev M ++ B) :
    ∃ L₂ : List (α × Bool),
      FreeGroup.invRev L₂ <+: V ∧
        L₂.length = L.length + M.length - P.length := by
  have hPpre : P <+: P ++ B := ⟨B, rfl⟩
  have hlen : P.length ≤ (FreeGroup.invRev L).length := by
    rw [FreeGroup.invRev_length]
    exact hcover
  obtain ⟨K, hK⟩ :=
    List.prefix_of_prefix_length_le hPpre hin hlen
  refine ⟨FreeGroup.invRev K ++ M, ?_, ?_⟩
  · refine ⟨B.drop K.length, ?_⟩
    have hKB : K <+: B := by
      refine (List.prefix_append_right_inj P).mp ?_
      rw [hK]
      exact hin
    obtain ⟨C, hC⟩ := hKB
    have hdrop : B.drop K.length = C := by
      rw [← hC, drop_append_of_ge K K.length C le_rfl, Nat.sub_self,
        List.drop_zero]
    rw [htail, FreeGroup.invRev_append, FreeGroup.invRev_invRev, hdrop,
      List.append_assoc, hC]
  · have hlength := congrArg List.length hK
    simp only [FreeGroup.invRev_length, List.length_append] at hlength
    simp only [List.length_append, FreeGroup.invRev_length]
    omega

/-- A root-indexed position in the finite cancellation walk.

The root word and root block stay fixed while `e₁` grows and the normalized
current suffix `((c₃,t₃)::f)` shrinks.  `L` is the *concrete* block currently
read in that suffix.  The endpoint equation is the telescoping invariant which
relates its length to the original endpoint; it is strictly stronger than
remembering only a succession of natural-number residuals. -/
structure RootAlignedCascadePosition [DecidableEq α]
    (R : Set (List (α × Bool)))
    (V : List (α × Bool)) (b m : ℕ) where
  c₀ : List (α × Bool)
  t₀ : List (α × Bool)
  E : List (α × Bool)
  M : List (α × Bool)
  c₃ : List (α × Bool)
  t₃ : List (α × Bool)
  A : List (α × Bool)
  L : List (α × Bool)
  e₁ : List (FreeGroup α × List (α × Bool))
  f : List (FreeGroup α × List (α × Bool))
  g : FreeGroup α
  N : ℕ
  ht₀ : t₀ ∈ symmetrization R
  hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃)
  hmin : IsMinimalConjExpr R
    ((FreeGroup.mk c₀, t₀) ::
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g
  root_word : V =
    (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))).toWord
  root_split : V = A ++
    (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N
  root_orientation : FreeGroup.invRev M = c₀ ++ FreeGroup.invRev E
  source_suffix : E <:+ t₀
  root_block : FreeGroup.invRev M <+: V
  root_length : b = M.length
  current_block : FreeGroup.invRev L <+:
    (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord
  endpoint : b + N = A.length + L.length
  tail_lt : f.length < m

/-- Initialize the root-indexed walk at the actual adjacent factor.  The root
split is the zero drop, and the concrete current block is exactly the block
provided by the leading cancellation. -/
def RootAlignedCascadePosition.initial [DecidableEq α]
    {R : Set (List (α × Bool))}
    {c t c' t' E M B : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (ht : t ∈ symmetrization R)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (htail : (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B)
    (hM : M = E ++ FreeGroup.invRev c) (hEsuf : E <:+ t) :
    RootAlignedCascadePosition R
      (conjEval ((FreeGroup.mk c', t') :: f)).toWord M.length
      (f.length + 1) where
  c₀ := c
  t₀ := t
  E := E
  M := M
  c₃ := c'
  t₃ := t'
  A := []
  L := M
  e₁ := []
  f := f
  g := g
  N := 0
  ht₀ := ht
  hredp₃ := hredp'
  hmin := by simpa using hmin
  root_word := by simp only [List.nil_append]
  root_split := by simp only [List.drop_zero, List.nil_append]
  root_orientation := by
    rw [hM, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  source_suffix := hEsuf
  root_block := ⟨B, htail.symm⟩
  root_length := rfl
  current_block := ⟨B, htail.symm⟩
  endpoint := by simp
  tail_lt := by omega

/-- The concrete current block is no longer than the current residual word. -/
theorem RootAlignedCascadePosition.current_length_bound [DecidableEq α]
    {R : Set (List (α × Bool))}
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m) :
    S.L.length ≤
      (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord.length := by
  obtain ⟨C, hC⟩ := S.current_block
  have h := congrArg List.length hC
  simp only [List.length_append, FreeGroup.invRev_length] at h
  omega

/-- One overrun updates the root split and endpoint equation canonically.

There are two purely list-theoretic cases according to whether the root's
existing drop stops in the survivor `P` or beyond it.  In both cases the next
drop and survivor are explicit, and the residual word is the concrete witness
from `exists_residual_block_of_overrun`.  No choice made by the generic cascade
decomposition is used, so the endpoint equality is preserved exactly. -/
theorem RootAlignedCascadePosition.exists_overrun_transport [DecidableEq α]
    {R : Set (List (α × Bool))}
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    {P M₃ B : List (α × Bool)}
    (hstep : (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord = P ++ B)
    (htail : (conjEval S.f).toWord = FreeGroup.invRev M₃ ++ B)
    (hcover : P.length ≤ S.L.length) :
    ∃ (L₂ A₂ : List (α × Bool)) (N₂ : ℕ),
      FreeGroup.invRev L₂ <+: (conjEval S.f).toWord ∧
        L₂.length = S.L.length + M₃.length - P.length ∧
        V = A₂ ++ (conjEval S.f).toWord.drop N₂ ∧
        b + N₂ = A₂.length + L₂.length := by
  have hin : FreeGroup.invRev S.L <+: P ++ B := by
    rw [← hstep]
    exact S.current_block
  obtain ⟨L₂, hL₂pre, hL₂len⟩ :=
    exists_residual_block_of_overrun hin hcover htail
  have hB : B = (conjEval S.f).toWord.drop M₃.length :=
    by
      symm
      rw [htail, drop_append_of_ge (FreeGroup.invRev M₃) M₃.length B
        (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
        Nat.sub_self, List.drop_zero]
  rcases le_or_gt S.N P.length with hNP | hPN
  · refine ⟨L₂, S.A ++ P.drop S.N, M₃.length, hL₂pre, hL₂len, ?_, ?_⟩
    · rw [S.root_split, hstep, drop_append_of_le S.N P B hNP, hB,
        List.append_assoc]
    · have hdropLen : (P.drop S.N).length = P.length - S.N :=
        List.length_drop
      rw [List.length_append, hdropLen, hL₂len]
      omega
  · refine ⟨L₂, S.A, M₃.length + (S.N - P.length), hL₂pre, hL₂len, ?_, ?_⟩
    · rw [S.root_split, hstep,
        drop_append_of_ge P S.N B (by omega), hB, ← drop_add]
    · rw [hL₂len]
      omega

/-- A covered survivor advances the root-indexed walk to a genuinely shorter
normalized suffix.  The normal form is obtained at the actual next position of
the same minimal expression; the root word, concrete block, split, and endpoint
are then transported by `exists_overrun_transport`. -/
theorem RootAlignedCascadePosition.exists_next_of_overrun [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ [])
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    {P M₃ B : List (α × Bool)}
    (hstep : (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord = P ++ B)
    (htail : (conjEval S.f).toWord = FreeGroup.invRev M₃ ++ B)
    (hcover : P.length ≤ S.L.length) (hfne : S.f ≠ []) :
    ∃ S₂ : RootAlignedCascadePosition R V b m,
      S₂.f.length < S.f.length := by
  cases hf : S.f with
  | nil => exact (hfne hf).elim
  | cons x f₄ =>
      obtain ⟨x₄, s₄⟩ := x
      have hminOld : IsMinimalConjExpr R
          (((FreeGroup.mk S.c₀, S.t₀) ::
            (S.e₁ ++ [(FreeGroup.mk S.c₃, S.t₃)])) ++
              ((x₄, s₄) :: f₄)) S.g := by
        simpa [hf, List.append_assoc] using S.hmin
      obtain ⟨c₄, t₄, _ht₄, hredp₄, hminNew⟩ :=
        exists_palindromic_at hcyc hne hminOld
      obtain ⟨L₂, A₂, N₂, hL₂pre, _hL₂len, hsplit₂, hend₂⟩ :=
        S.exists_overrun_transport hstep htail hcover
      have hevalTail : conjEval ((FreeGroup.mk c₄, t₄) :: f₄)
          = conjEval ((x₄, s₄) :: f₄) := by
        have hnew := hminNew.2.1
        have hold := hminOld.2.1
        rw [conjEval_append] at hnew hold
        exact mul_left_cancel (hnew.trans hold.symm)
      let e₂ := S.e₁ ++ [(FreeGroup.mk S.c₃, S.t₃)]
      have hminNew' : IsMinimalConjExpr R
          ((FreeGroup.mk S.c₀, S.t₀) ::
            (e₂ ++ ((FreeGroup.mk c₄, t₄) :: f₄))) S.g := by
        dsimp [e₂]
        simpa [List.append_assoc] using hminNew
      have hrootWord : V =
          (conjEval (e₂ ++ ((FreeGroup.mk c₄, t₄) :: f₄))).toWord := by
        have hfull : conjEval
            (e₂ ++ ((FreeGroup.mk c₄, t₄) :: f₄)) =
            conjEval (S.e₁ ++ ((FreeGroup.mk S.c₃, S.t₃) :: S.f)) :=
          hminNew'.2.1.trans S.hmin.2.1.symm
        rw [hfull]
        exact S.root_word
      have hsplit₂' : V = A₂ ++
          (conjEval ((FreeGroup.mk c₄, t₄) :: f₄)).toWord.drop N₂ := by
        rw [hevalTail]
        simpa [hf] using hsplit₂
      have hL₂pre' : FreeGroup.invRev L₂ <+:
          (conjEval ((FreeGroup.mk c₄, t₄) :: f₄)).toWord := by
        rw [hevalTail]
        simpa [hf] using hL₂pre
      let S₂ : RootAlignedCascadePosition R V b m := {
        c₀ := S.c₀, t₀ := S.t₀, E := S.E, M := S.M,
        c₃ := c₄, t₃ := t₄, A := A₂, L := L₂, e₁ := e₂, f := f₄,
        g := S.g, N := N₂, ht₀ := S.ht₀, hredp₃ := hredp₄,
        hmin := hminNew', root_word := hrootWord, root_split := hsplit₂',
        root_orientation := S.root_orientation, source_suffix := S.source_suffix,
        root_block := S.root_block, root_length := S.root_length,
        current_block := hL₂pre', endpoint := hend₂,
        tail_lt := lt_trans (by rw [hf]; simp) S.tail_lt }
      refine ⟨S₂, ?_⟩
      dsimp [S₂]
      rw [hf]
      simp only [List.length_cons]
      omega

/-- A cursor at an actual factor of the non-confined cascade.

The first group of fields is exactly a `LandsInSharp` witness except for the
sharp bound on `i`.  The second group records why that bound holds: the
effective conjugator extends the original head conjugator by `y`, and the first
`i` letters of the current rotation also prefix the corresponding rotation of
the inverted original relator.  Minimality makes the two rotations distinct;
the metric condition then makes this common prefix a short piece.

The concrete termination measure is `f.length`: a transition replaces the
current factor by a later one and strictly decreases this tail.
-/
structure NonConfinedCascadeCursor [DecidableEq α]
    (R : Set (List (α × Bool))) (lam : ℚ)
    (V : List (α × Bool)) (b m : ℕ) where
  c₀ : List (α × Bool)
  t₀ : List (α × Bool)
  c₃ : List (α × Bool)
  t₃ : List (α × Bool)
  y : List (α × Bool)
  A : List (α × Bool)
  e₁ : List (FreeGroup α × List (α × Bool))
  f : List (FreeGroup α × List (α × Bool))
  g : FreeGroup α
  N : ℕ
  i : ℕ
  ht₀ : t₀ ∈ symmetrization R
  ht₃ : t₃ ∈ symmetrization R
  hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃)
  hminForward : IsMinimalConjExpr R
    ((FreeGroup.mk c₀, t₀) ::
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g
  hminTail : IsMinimalConjExpr R ((FreeGroup.mk c₃, t₃) :: f)
    (conjEval ((FreeGroup.mk c₃, t₃) :: f))
  tail_lt : f.length < m
  outer_split : V = A ++
    (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N
  N_conjugator : N ≤ c₃.length
  block_fit : b + N ≤ A.length + c₃.length + i
  effective : FreeGroup.mk (A ++ c₃.drop N) = conjEval e₁ * FreeGroup.mk c₃
  extends_head : A ++ c₃.drop N = c₀ ++ y
  y_prefix : y <+: FreeGroup.invRev t₀
  alignment : t₃.take i <+: (FreeGroup.invRev t₀).rotate y.length

/-- The invariant carried while the aligned walk has not yet certified that the
transported block stops at the current factor.  Unlike the old unrestricted
stopping predicate, every positional field is attached to the actual cascade
split and to the original head rotation.  A terminal step needs only the
strict tail decrease and the final block-fit inequality. -/
structure PartialAlignedCascadeState [DecidableEq α]
    (R : Set (List (α × Bool))) (lam : ℚ)
    (V : List (α × Bool)) (b m : ℕ) where
  c₀ : List (α × Bool)
  t₀ : List (α × Bool)
  c₃ : List (α × Bool)
  t₃ : List (α × Bool)
  y : List (α × Bool)
  A : List (α × Bool)
  e₁ : List (FreeGroup α × List (α × Bool))
  f : List (FreeGroup α × List (α × Bool))
  g : FreeGroup α
  N : ℕ
  i : ℕ
  ht₀ : t₀ ∈ symmetrization R
  ht₃ : t₃ ∈ symmetrization R
  hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃)
  hminForward : IsMinimalConjExpr R
    ((FreeGroup.mk c₀, t₀) ::
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g
  hminTail : IsMinimalConjExpr R ((FreeGroup.mk c₃, t₃) :: f)
    (conjEval ((FreeGroup.mk c₃, t₃) :: f))
  outer_split : V = A ++
    (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N
  N_conjugator : N ≤ c₃.length
  effective : FreeGroup.mk (A ++ c₃.drop N) = conjEval e₁ * FreeGroup.mk c₃
  extends_head : A ++ c₃.drop N = c₀ ++ y
  y_prefix : y <+: FreeGroup.invRev t₀
  alignment : t₃.take i <+: (FreeGroup.invRev t₀).rotate y.length

/-- Closing a partial state is honest: the two facts supplied here are exactly
the two facts intentionally absent from `PartialAlignedCascadeState`. -/
def PartialAlignedCascadeState.close [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V : List (α × Bool)} {b m : ℕ}
    (S : PartialAlignedCascadeState R lam V b m)
    (htail : S.f.length < m)
    (hfit : b + S.N ≤ S.A.length + S.c₃.length + S.i) :
    NonConfinedCascadeCursor R lam V b m where
  c₀ := S.c₀
  t₀ := S.t₀
  c₃ := S.c₃
  t₃ := S.t₃
  y := S.y
  A := S.A
  e₁ := S.e₁
  f := S.f
  g := S.g
  N := S.N
  i := S.i
  ht₀ := S.ht₀
  ht₃ := S.ht₃
  hredp₃ := S.hredp₃
  hminForward := S.hminForward
  hminTail := S.hminTail
  tail_lt := htail
  outer_split := S.outer_split
  N_conjugator := S.N_conjugator
  block_fit := hfit
  effective := S.effective
  extends_head := S.extends_head
  y_prefix := S.y_prefix
  alignment := S.alignment

/-- Build the partial cursor from the raw geometry of a root-indexed cascade.

In particular, this constructor does not accept `effective`, `extends_head`, or
`alignment` as independent assumptions.  They are consequences of the actual
cascade split, the opening of the selected suffix, and the transported root
block.  The bound `N ≤ |c₃|` is explicit because it is exactly what permits
the effective conjugator to be read without first rotating the landing
relator. -/
theorem partialAlignedCascadeState_of_root_geometry [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V c₀ t₀ c₃ t₃ E M A Z : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} {b m N i : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₀, t₀) ::
        (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g)
    (hV : V = (conjEval
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))).toWord)
    (ht₀ : t₀ ∈ symmetrization R)
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (hroot : V = A ++
      (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N)
    (hopen : (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord = c₃ ++ Z)
    (hNc : N ≤ c₃.length) (hZ : t₃.take i <+: Z)
    (hM : FreeGroup.invRev M = c₀ ++ FreeGroup.invRev E)
    (hEsuf : E <:+ t₀) (hMroot : FreeGroup.invRev M <+: V)
    (hlow : c₀.length ≤ A.length + (c₃.length - N))
    (hhigh : A.length + (c₃.length - N) + i ≤ M.length) :
    PartialAlignedCascadeState R lam V b m := by
  have ht₃ : t₃ ∈ symmetrization R :=
    hmin.1 (FreeGroup.mk c₃, t₃) (by simp)
  have hdrop :
      ((FreeGroup.mk c₀, t₀) ::
        (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))).drop (e₁.length + 1)
        = (FreeGroup.mk c₃, t₃) :: f := by
    rw [List.drop_succ_cons, List.drop_left]
  have hmin₃ := isMinimalConjExpr_drop (e₁.length + 1)
    ((FreeGroup.mk c₀, t₀) ::
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g hmin
  rw [hdrop] at hmin₃
  have htake : (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.take N
      = c₃.take N := by
    rw [hopen, take_append_of_le N c₃ Z hNc]
  have hPQ : FreeGroup.mk V = conjEval e₁ *
      FreeGroup.mk (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord := by
    rw [hV, FreeGroup.mk_toWord, FreeGroup.mk_toWord, conjEval_append]
  have heffective := mk_effectiveConjugator_of_split hroot htake rfl hPQ
  obtain ⟨y, hy, hyE⟩ :=
    exists_forward_containment hroot hopen hNc hM hMroot hlow (by omega)
  obtain ⟨y', hy', halign⟩ :=
    exists_forward_alignment hroot hopen hNc hZ hM hEsuf hMroot hlow hhigh
  have hyy : y = y' := List.append_cancel_left (hy.symm.trans hy')
  have halign' : t₃.take i <+: (FreeGroup.invRev t₀).rotate y.length := by
    rw [hyy]
    exact halign
  exact {
    c₀ := c₀, t₀ := t₀, c₃ := c₃, t₃ := t₃, y := y,
    A := A, e₁ := e₁, f := f, g := g, N := N, i := i,
    ht₀ := ht₀, ht₃ := ht₃, hredp₃ := hredp₃,
    hminForward := hmin, hminTail := hmin₃, outer_split := hroot,
    N_conjugator := hNc, effective := heffective,
    extends_head := hy,
    y_prefix := hyE.trans (invRev_prefix_of_suffix hEsuf), alignment := halign' }

/-- Root geometry together with the two terminal counting inequalities gives a
closed cursor.  This wrapper keeps callers from ever manufacturing the three
coincidence-sensitive fields by hand. -/
theorem nonConfinedCascadeCursor_of_root_geometry [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V c₀ t₀ c₃ t₃ E M A Z : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} {b m N i : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₀, t₀) ::
        (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g)
    (hV : V = (conjEval
      (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))).toWord)
    (ht₀ : t₀ ∈ symmetrization R)
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (hroot : V = A ++
      (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N)
    (hopen : (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord = c₃ ++ Z)
    (hNc : N ≤ c₃.length) (hZ : t₃.take i <+: Z)
    (hM : FreeGroup.invRev M = c₀ ++ FreeGroup.invRev E)
    (hEsuf : E <:+ t₀) (hMroot : FreeGroup.invRev M <+: V)
    (hlow : c₀.length ≤ A.length + (c₃.length - N))
    (hhigh : A.length + (c₃.length - N) + i ≤ M.length)
    (htail : f.length < m)
    (hfit : b + N ≤ A.length + c₃.length + i) :
    NonConfinedCascadeCursor R lam V b m :=
  (partialAlignedCascadeState_of_root_geometry hmin hV ht₀ hredp₃ hroot
    hopen hNc hZ hM hEsuf hMroot hlow hhigh).close htail hfit

/-- Close a root-indexed position when the concrete current block stops `i`
letters into the current rotation in the forward orientation.  Every cursor
field except the unavoidable forward-orientation inequality is derived from
the position. -/
theorem RootAlignedCascadePosition.closeForward [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V : List (α × Bool)} {b m i : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    {Z : List (α × Bool)}
    (hopen : (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord
      = S.c₃ ++ Z)
    (hNc : S.N ≤ S.c₃.length)
    (hLi : S.L.length = S.c₃.length + i)
    (hZ : S.t₃.take i <+: Z)
    (hlow : S.c₀.length ≤ S.A.length + (S.c₃.length - S.N)) :
    NonConfinedCascadeCursor R lam V b m := by
  have hhigh : S.A.length + (S.c₃.length - S.N) + i ≤ S.M.length := by
    rw [← S.root_length]
    omega
  have hfit : b + S.N ≤ S.A.length + S.c₃.length + i := by
    rw [S.endpoint, hLi]
  exact nonConfinedCascadeCursor_of_root_geometry S.hmin S.root_word S.ht₀
    S.hredp₃ S.root_split hopen hNc hZ S.root_orientation S.source_suffix
    S.root_block hlow hhigh S.tail_lt hfit

/-- The terminal inside-survivor case supplies the opening and rotation prefix
needed by `closeForward`.  There is deliberately no separate hypothesis that
the endpoint has not passed the end of the current rotation: `take i` saturates
there, so a putative full swallow aligns the whole current relator with the
root rotation and the cursor's piece argument rules it out.  The remaining
hypotheses are exactly the two forward-orientation facts: the root drop has not
entered the rotation and the effective landing conjugator is at least as long
as the protected one. -/
theorem RootAlignedCascadePosition.closeForward_of_inside [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    {P M₃ B : List (α × Bool)}
    (hpal : palindrome S.c₃ S.t₃ = P ++ M₃)
    (hstep : (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord
      = P ++ B)
    (hcL : S.c₃.length < S.L.length) (hinside : S.L.length < P.length)
    (hNc : S.N ≤ S.c₃.length)
    (hlow : S.c₀.length ≤ S.A.length + (S.c₃.length - S.N)) :
    NonConfinedCascadeCursor R lam V b m := by
  let i := S.L.length - S.c₃.length
  obtain ⟨Z, hopen⟩ :=
    exists_current_open_of_inside_survivor hpal hstep hcL hinside
  have hct : S.c₃ ++ S.t₃.take i <+: palindrome S.c₃ S.t₃ := by
    refine ⟨S.t₃.drop i ++ FreeGroup.invRev S.c₃, ?_⟩
    unfold palindrome
    rw [List.append_assoc, List.take_append_drop, List.append_assoc]
  have hPpre : P <+: palindrome S.c₃ S.t₃ := ⟨M₃, hpal.symm⟩
  have htake : (S.t₃.take i).length ≤ i := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have hctP : S.c₃ ++ S.t₃.take i <+: P :=
    List.prefix_of_prefix_length_le hct hPpre (by
      rw [List.length_append]
      dsimp [i]
      omega)
  have hctV : S.c₃ ++ S.t₃.take i <+:
      (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord :=
    hctP.trans ⟨B, hstep.symm⟩
  have hZ : S.t₃.take i <+: Z := by
    refine (List.prefix_append_right_inj S.c₃).mp ?_
    rw [← hopen]
    exact hctV
  exact S.closeForward (i := i) hopen hNc (by dsimp [i]; omega) hZ hlow

/-- If the concrete current block ends in the landing conjugator, the
root-indexed position is already a sharp landing at offset zero. -/
theorem RootAlignedCascadePosition.landsInSharp_of_shallow [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hne : ∀ r ∈ R, r ≠ [])
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    (hL : S.L.length ≤ S.c₃.length) (hNc : S.N ≤ S.c₃.length) :
    LandsInSharp R lam b V m := by
  have ht₃ : S.t₃ ∈ symmetrization R :=
    S.hmin.1 (FreeGroup.mk S.c₃, S.t₃) (by simp)
  have htpos : 0 < S.t₃.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hne ht₃)
  have hdrop :
      ((FreeGroup.mk S.c₀, S.t₀) ::
        (S.e₁ ++ ((FreeGroup.mk S.c₃, S.t₃) :: S.f))).drop
          (S.e₁.length + 1) = (FreeGroup.mk S.c₃, S.t₃) :: S.f := by
    rw [List.drop_succ_cons, List.drop_left]
  have hmin₃ := isMinimalConjExpr_drop (S.e₁.length + 1)
    ((FreeGroup.mk S.c₀, S.t₀) ::
      (S.e₁ ++ ((FreeGroup.mk S.c₃, S.t₃) :: S.f))) S.g S.hmin
  rw [hdrop] at hmin₃
  exact ⟨S.c₃, S.t₃, S.f, S.A, S.N, 0, S.tail_lt, S.root_split, ht₃,
    S.hredp₃, hmin₃, cast_zero_lt_lam_mul hlam0 htpos, by omega,
    by rw [S.endpoint]; omega⟩

/-- **A cursor is already a landing site.**  This is the payoff of carrying the
alignment rather than only the shorter tail.  The forward minimality argument
excludes coincidence of the two rotations; their aligned common prefix is
therefore a piece, and `C'(λ)` supplies the exact sharp offset inequality.
-/
theorem landsInSharp_of_nonConfinedCascadeCursor [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    {V : List (α × Bool)} {b m : ℕ}
    (S : NonConfinedCascadeCursor R lam V b m) :
    LandsInSharp R lam b V m := by
  have hmetric6 : MetricSmallCancellation R (1 / 6) :=
    metricSmallCancellation_of_le hlam hmetric
  have hi6 : 6 * S.i < S.t₃.length :=
    six_mul_intrusion_lt_of_forward hmetric6 S.hminForward S.ht₀ S.ht₃
      S.effective S.extends_head S.y_prefix S.alignment
  have hii : S.i ≤ S.t₃.length := by omega
  have hrotmem : (FreeGroup.invRev S.t₀).rotate S.y.length
      ∈ symmetrization R :=
    rotate_mem_symmetrization (invRev_mem_symmetrization S.ht₀) S.y.length
  have hne : S.t₃ ≠ (FreeGroup.invRev S.t₀).rotate S.y.length :=
    ne_rotate_invRev_of_minimal_forward S.hminForward S.effective
      S.extends_head S.y_prefix
  have hpiece : IsPiece (symmetrization R) (S.t₃.take S.i) :=
    isPiece_of_prefix_two S.ht₃ hrotmem hne
      (List.take_prefix S.i S.t₃) S.alignment
  have hi := hmetric (S.t₃.take S.i) hpiece S.t₃ S.ht₃
    (List.take_prefix S.i S.t₃)
  have hilength : (S.t₃.take S.i).length = S.i := by
    rw [List.length_take]
    omega
  rw [hilength] at hi
  exact ⟨S.c₃, S.t₃, S.f, S.A, S.N, S.i, S.tail_lt, S.outer_split,
    S.ht₃, S.hredp₃, S.hminTail, hi, by omega, S.block_fit⟩

/-- A finite, provenance-preserving cascade search. -/
inductive AlignedCascadeSearch [DecidableEq α]
    (R : Set (List (α × Bool))) (lam : ℚ) :
    List (α × Bool) → ℕ → ℕ → Prop
  | stop {V b m} (cursor : NonConfinedCascadeCursor R lam V b m) :
      AlignedCascadeSearch R lam V b m
  | landed {V b m} (landing : LandsInSharp R lam b V m) :
      AlignedCascadeSearch R lam V b m
  | overrun {V V₂ P M : List (α × Bool)} {b m m₂ : ℕ}
      (split : V = P ++ V₂.drop M.length)
      (covers : P.length ≤ b) (decreases : m₂ < m)
      (next : AlignedCascadeSearch R lam V₂
        (b + M.length - P.length) m₂) :
      AlignedCascadeSearch R lam V b m

/-- The terminal transition from the carried partial invariant. -/
def AlignedCascadeSearch.closePartial [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    {V : List (α × Bool)} {b m : ℕ}
    (S : PartialAlignedCascadeState R lam V b m)
    (htail : S.f.length < m)
    (hfit : b + S.N ≤ S.A.length + S.c₃.length + S.i) :
    AlignedCascadeSearch R lam V b m :=
  .stop (S.close htail hfit)

/-- One honest step of the root-indexed walk, once its two orientation
inequalities are available.  If the current block stops in the survivor, it
either stops in the conjugator or closes the aligned cursor (including the
full-rotation case, by saturation of `take`).  Otherwise the actual
cancellation split advances to a strictly shorter normalized suffix.

This packages the complete local trichotomy.  In particular, the recursive
branch carries a concrete `RootAlignedCascadePosition`; it does not replace the
block by an unrelated length. -/
theorem RootAlignedCascadePosition.search_or_next [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam)
    {V : List (α × Bool)} {b m : ℕ}
    (S : RootAlignedCascadePosition R V b m)
    {P M₃ B : List (α × Bool)}
    (hpal : palindrome S.c₃ S.t₃ = P ++ M₃)
    (hstep : (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord
      = P ++ B)
    (htail : (conjEval S.f).toWord = FreeGroup.invRev M₃ ++ B)
    (hNc : S.N ≤ S.c₃.length)
    (hlow : S.c₀.length ≤ S.A.length + (S.c₃.length - S.N)) :
    AlignedCascadeSearch R lam V b m ∨
      ∃ S₂ : RootAlignedCascadePosition R V b m,
        S₂.f.length < S.f.length := by
  by_cases hfne : S.f ≠ []
  · by_cases hcover : P.length ≤ S.L.length
    · exact Or.inr (S.exists_next_of_overrun hcyc hne hstep htail hcover hfne)
    · have hinside : S.L.length < P.length := by omega
      by_cases hshallow : S.L.length ≤ S.c₃.length
      · exact Or.inl (.landed
          (S.landsInSharp_of_shallow hlam0 hne hshallow hNc))
      · exact Or.inl (.stop
          (S.closeForward_of_inside hpal hstep (by omega) hinside hNc hlow))
  · have hf : S.f = [] := not_ne_iff.mp hfne
    by_cases hshallow : S.L.length ≤ S.c₃.length
    · exact Or.inl (.landed
        (S.landsInSharp_of_shallow hlam0 hne hshallow hNc))
    · let i := S.L.length - S.c₃.length
      have hopen :
          (conjEval ((FreeGroup.mk S.c₃, S.t₃) :: S.f)).toWord
            = S.c₃ ++ (S.t₃ ++ FreeGroup.invRev S.c₃) := by
        rw [hf]
        exact (toWord_conjEval_singleton S.hredp₃).trans (by
          unfold palindrome
          rw [List.append_assoc])
      have hZ : S.t₃.take i <+: S.t₃ ++ FreeGroup.invRev S.c₃ :=
        (List.take_prefix i S.t₃).trans ⟨FreeGroup.invRev S.c₃, rfl⟩
      exact Or.inl (.stop (S.closeForward (i := i) hopen hNc
        (by dsimp [i]; omega) hZ hlow))

/-- Structural consumption of a finite aligned search. -/
theorem landsInSharp_of_alignedCascadeSearch [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam) :
    ∀ {V : List (α × Bool)} {b m : ℕ},
      AlignedCascadeSearch R lam V b m → LandsInSharp R lam b V m := by
  intro V b m hsearch
  induction hsearch with
  | stop cursor =>
      exact landsInSharp_of_nonConfinedCascadeCursor hlam hmetric cursor
  | landed landing => exact landing
  | overrun split covers decreases next ih =>
      exact (landsInSharp_of_overrun split covers ih).mono (Nat.le_of_lt decreases)

/-- **The cascade has a genuine next factor.**  The empty-tail base case is
impossible: a singleton palindromic factor spells its palindrome verbatim, so
the incoming inverse block is confined to it.  This is the base case for an
induction on `f.length` in the non-confined branch. -/
theorem tail_ne_nil_of_nonConfined [DecidableEq α]
    {R : Set (List (α × Bool))}
    {c' t' M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))}
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (htail : (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hconf : ¬(FreeGroup.invRev M <+: palindrome c' t')) : f ≠ [] := by
  intro hf
  subst f
  apply hconf
  exact ⟨B', htail.symm.trans (toWord_conjEval_singleton hredp')⟩

/-- **One strict cascade descent.**  After non-confinement rules out the empty
tail, its head can be put in palindromic normal form without changing the tail
element.  The remaining list is strictly shorter than the old tail, providing
the concrete `Nat` measure for the successor case.
-/
theorem exists_next_palindromic_of_nonConfined [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ [])
    {c t c' t' M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (htail : (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B')
    (hconf : ¬(FreeGroup.invRev M <+: palindrome c' t')) :
    ∃ (c₂ t₂ : List (α × Bool))
      (f₂ : List (FreeGroup α × List (α × Bool))),
      t₂ ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c₂ t₂) ∧
        IsMinimalConjExpr R
          ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t')
            :: (FreeGroup.mk c₂, t₂) :: f₂) g ∧
        f₂.length < f.length ∧
        conjEval ((FreeGroup.mk c₂, t₂) :: f₂) = conjEval f := by
  have hfne : f ≠ [] := tail_ne_nil_of_nonConfined hredp' htail hconf
  cases f with
  | nil => exact absurd rfl hfne
  | cons x f₂ =>
      obtain ⟨x₂, s₂⟩ := x
      obtain ⟨c₂, t₂, ht₂, hredp₂, hmin₂⟩ :=
        exists_palindromic_thd hcyc hne hmin
      refine ⟨c₂, t₂, f₂, ht₂, hredp₂, hmin₂, by
        simp only [List.length_cons]
        omega, ?_⟩
      have h₁ := hmin₂.2.1
      have h₂ := hmin.2.1
      rw [conjEval_cons, conjEval_cons] at h₁ h₂
      have htailEq := mul_left_cancel (h₁.trans h₂.symm)
      exact mul_left_cancel htailEq

/-- **The corrected non-confined cascade residual.**  The survivor and loss are
the ones produced by the actual leading-cancellation split of the adjacent
factor, and the residual block is consequently fixed by that split.

Unlike `StoppingAlternativeBetaSharp`, this predicate cannot be queried with a
spectator block unrelated to the surrounding minimal expression.
-/
def NonConfinedCascadeProgress [DecidableEq α]
    (R : Set (List (α × Bool))) (lam : ℚ) : Prop :=
  ∀ (c t c' t' E M P' B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g →
    t ∈ symmetrization R → t' ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c' t') →
    palindrome c t = P' ++ M →
    (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B' →
    c.length < M.length → M.length ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c → E <:+ t → 0 < E.length →
    lam * (t.length : ℚ) ≤ (E.length : ℚ) →
    ¬(FreeGroup.invRev M <+: palindrome c' t') →
    AlignedCascadeSearch R lam
      (conjEval ((FreeGroup.mk c', t') :: f)).toWord M.length (f.length + 1)

/-- The shallow branch of the measured walk.  If the transported block stops
inside the conjugator of the normalized head of the remaining expression, the
head itself is already a sharp landing, at offset zero. -/
theorem landsInSharp_of_actual_shallow [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hne : ∀ r ∈ R, r ≠ [])
    {c t : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {b m : ℕ}
    (ht : t ∈ symmetrization R)
    (hred : FreeGroup.IsReduced (palindrome c t))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: f)
      (conjEval ((FreeGroup.mk c, t) :: f)))
    (hb : b ≤ c.length) (hm : f.length < m) :
    LandsInSharp R lam b
      (conjEval ((FreeGroup.mk c, t) :: f)).toWord m := by
  have htpos : 0 < t.length :=
    List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hne ht)
  exact landsInSharp_of_confined (i := 0) ht hred hmin
    (cast_zero_lt_lam_mul hlam0 htpos) (by omega) hm

/-- The corrected residual closes the original non-confined leaf.  The only
new work is showing that non-confinement forces the incoming block to cover the
actual survivor `P₂`; after that, `landsInSharp_of_overrun` is exactly the
cascade transport required by the conclusion.
-/
theorem nonConfinedBlockLands_of_cascadeProgress [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    (hprogress : NonConfinedCascadeProgress R lam) :
    NonConfinedBlockLands R lam := by
  intro c t c' t' E M P' B' f g hmin ht ht' hredp hredp' heq htail hlow
    hhigh hM hEt hEpos hlarge hconf
  exact landsInSharp_of_alignedCascadeSearch hlam hmetric
    (hprogress c t c' t' E M P' B' f g hmin ht ht' hredp hredp' heq htail
      hlow hhigh hM hEt hEpos hlarge hconf)

/-! ## The remaining genuine leaf -/

/-- The provenance-preserving cascade statement on the router alphabet.

This is now the sole non-confined obligation.  It is strictly narrower than the
refuted stopping alternative: `P₂`, `M₂`, and the residual block are fixed by
one cancellation step in the supplied minimal expression.
-/
theorem nonConfinedCascadeProgress_fin_two
    (R : Set (List (Fin 2 × Bool))) (lam : ℚ)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    NonConfinedCascadeProgress R lam := by
  intro c t c' t' E M P' B' f g hmin ht ht' hredp hredp' heq htail hlow
    hhigh hM hEt hEpos hlarge hconf
  obtain ⟨P₂, M₂, B₂, hpal₂, htail₂, hstep₂⟩ :=
    exists_tail_step_word (f := f) hredp'
  have hdrop₂ : B₂ = (conjEval f).toWord.drop M₂.length := by
    symm
    exact drop_invRev_block htail₂
  have hstep₂' : (conjEval ((FreeGroup.mk c', t') :: f)).toWord =
      P₂ ++ (conjEval f).toWord.drop M₂.length := by
    rw [hstep₂, ← hdrop₂]
  have hover : P₂.length ≤ M.length := by
    by_contra hnot
    apply hconf
    have hMpre : FreeGroup.invRev M
        <+: (conjEval ((FreeGroup.mk c', t') :: f)).toWord :=
      ⟨B', htail.symm⟩
    have hP₂pre : P₂
        <+: (conjEval ((FreeGroup.mk c', t') :: f)).toWord :=
      ⟨B₂, hstep₂.symm⟩
    have hMP : FreeGroup.invRev M <+: P₂ :=
      List.prefix_of_prefix_length_le hMpre hP₂pre (by
        rw [FreeGroup.invRev_length]
        omega)
    exact hMP.trans ⟨M₂, hpal₂.symm⟩
  have hbword : M.length + M₂.length - P₂.length ≤
      (conjEval f).toWord.length := by
    have hlen := congrArg List.length hstep₂
    have hlenTail := congrArg List.length htail₂
    have hlenBlock := congrArg List.length htail
    simp only [List.length_append, FreeGroup.invRev_length] at
      hlen hlenTail hlenBlock
    omega
  obtain ⟨c₂, t₂, f₂, ht₂, hredp₂, hmin₂, hf₂, heval₂⟩ :=
    exists_next_palindromic_of_nonConfined hcyc hne hmin hredp' htail hconf
  refine AlignedCascadeSearch.overrun hstep₂' hover (by omega) ?_
  by_cases hshallow : M.length + M₂.length - P₂.length ≤ c₂.length
  · apply AlignedCascadeSearch.landed
    have hminTail : IsMinimalConjExpr R ((FreeGroup.mk c₂, t₂) :: f₂)
        (conjEval ((FreeGroup.mk c₂, t₂) :: f₂)) := hmin₂.tail.tail
    have hland := landsInSharp_of_actual_shallow hlam0 hne ht₂ hredp₂
      hminTail hshallow hf₂
    rw [heval₂] at hland
    exact hland
  ·
    -- The remaining branch is the measured overrun walk: iterate the actual
    -- `exists_tail_step_word` decomposition until its first shallow suffix,
    -- carrying the original alignment data and decreasing the finite tail.
    sorry

/-- The premise-free non-confined theorem follows from the corrected cascade
residual, with no use of `StoppingAlternativeBetaSharp`.
-/
theorem nonConfinedBlockLands_fin_two_of_progress
    (R : Set (List (Fin 2 × Bool))) (lam : ℚ)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hne : ∀ r ∈ R, r ≠ []) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam) :
    NonConfinedBlockLands R lam :=
  nonConfinedBlockLands_of_cascadeProgress
    hlam hmetric
    (nonConfinedCascadeProgress_fin_two R lam hcyc hne hlam0 hlam hmetric)

end SmallCancellationRouter
end GroupApproximation
