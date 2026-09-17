import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.PermUnit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Action
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The ordered frame complex `X_n(A)`

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), tex l.424: "A
$(k-1)$-simplex ... is an ordered tuple $(v_1,\ldots,v_k)$ ... Faces delete a vector";
tex l.446: "The action of $G$ on ordered $k$-frames is transitive".

## Definition used

`IsFrame v` for `v : Fin k → (Fin n → A)`: there are `g ∈ GL_n(A)` and an injection
`e : Fin k ↪ Fin n` with `v i = g • e_{e i}`.  So `v` is a sub-family of the columns of an
invertible matrix.  This is equivalent to "the first `k` columns of some invertible matrix"
(`isFrame_iff_firstColumns`), which in turn is Khanh's `A^n = v_1 A ⊕ ... ⊕ v_k A ⊕ C` with
`C ≅ A^{n-k}`.  Using embeddings makes faces free (compose with an embedding) and makes
transitivity immediate (`IsFrame.exists_smul_eq`, all `k`, via a permutation unit).

`frameVertex`, `frameEdge`, `frameTri` are the 1-, 2- and 3-frames, with their faces and their
translates.  The complex itself (`Frame.VertexComplex`) lives on the frame vertices only: on the
full vector type `Fin n → A` it would not be connected (the zero vector lies on no edge frame),
so lane 10's `SimplyConnected` would be false there.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {n : ℕ}

/-- `v` is an ordered `k`-frame: it consists of distinct columns of an invertible matrix. -/
def IsFrame {k : ℕ} (v : Fin k → Fin n → A) : Prop :=
  ∃ g : (Matrix (Fin n) (Fin n) A)ˣ, ∃ e : Fin k ↪ Fin n,
    ∀ i, v i = g • (Pi.single (e i) 1 : Fin n → A)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.IsFrame

/-- Sub-families (in any order) of frames are frames. -/
theorem IsFrame.of_embedding {k k' : ℕ} {v : Fin k → Fin n → A} (hv : IsFrame v)
    (σ : Fin k' ↪ Fin k) (w : Fin k' → Fin n → A) (hw : ∀ i, w i = v (σ i)) : IsFrame w := by
  obtain ⟨g, e, he⟩ := hv
  exact ⟨g, σ.trans e, fun i => (hw i).trans (he (σ i))⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.IsFrame.of_embedding

theorem IsFrame.smul {k : ℕ} {v : Fin k → Fin n → A} (hv : IsFrame v)
    (h : (Matrix (Fin n) (Fin n) A)ˣ) : IsFrame (fun i => h • v i) := by
  obtain ⟨g, e, he⟩ := hv
  exact ⟨h * g, e, fun i => by rw [he i, mul_smul]⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.IsFrame.smul

theorem isFrame_single {k : ℕ} (e : Fin k ↪ Fin n) :
    IsFrame (fun i => (Pi.single (e i) 1 : Fin n → A)) :=
  ⟨1, e, fun i => (one_smul _ _).symm⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.isFrame_single

/-- `GL_n(A)` acts transitively on ordered `k`-frames, for every `k`. -/
theorem IsFrame.exists_smul_eq {k : ℕ} {v w : Fin k → Fin n → A} (hv : IsFrame v)
    (hw : IsFrame w) : ∃ h : (Matrix (Fin n) (Fin n) A)ˣ, ∀ i, h • v i = w i := by
  obtain ⟨g, e, he⟩ := hv
  obtain ⟨g', e', he'⟩ := hw
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e' e e'.injective e.injective
  refine ⟨g' * framePermUnit σ * g⁻¹, fun i => ?_⟩
  rw [he i, he' i, mul_smul, mul_smul, inv_smul_smul, framePermUnit_smul_single, ← hσ i,
    Equiv.symm_apply_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.IsFrame.exists_smul_eq

/-- Frames are exactly the families of the first `k` columns of invertible matrices. -/
theorem isFrame_iff_firstColumns {k : ℕ} (hk : k ≤ n) (v : Fin k → Fin n → A) :
    IsFrame v ↔ ∃ g : (Matrix (Fin n) (Fin n) A)ˣ,
      ∀ i, v i = g • (Pi.single (Fin.castLE hk i) 1 : Fin n → A) := by
  constructor
  · intro hv
    obtain ⟨h, hh⟩ := (isFrame_single (A := A) (Fin.castLEEmb hk)).exists_smul_eq hv
    exact ⟨h, fun i => (hh i).symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Fin.castLEEmb hk, hg⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.isFrame_iff_firstColumns

/-- Vertices of `X_n(A)`: unimodular vectors (1-frames). -/
def frameVertex (u : Fin n → A) : Prop := IsFrame ![u]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertex

/-- Ordered edges of `X_n(A)`: ordered 2-frames. -/
def frameEdge (u v : Fin n → A) : Prop := IsFrame ![u, v]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdge

/-- Ordered triangles of `X_n(A)`: ordered 3-frames. -/
def frameTri (u v w : Fin n → A) : Prop := IsFrame ![u, v, w]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri

theorem frameTri.edge01 {a b c : Fin n → A} (h : frameTri a b c) : frameEdge a b :=
  IsFrame.of_embedding h Fin.castSuccEmb _ (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri.edge01

theorem frameTri.edge12 {a b c : Fin n → A} (h : frameTri a b c) : frameEdge b c :=
  IsFrame.of_embedding h (Fin.succEmb 2) _ (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri.edge12

theorem frameTri.edge02 {a b c : Fin n → A} (h : frameTri a b c) : frameEdge a c :=
  IsFrame.of_embedding h (Fin.succAboveEmb (1 : Fin 3)) _ (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri.edge02

/-- The reversed ordered edge is again an ordered edge (a different cell). -/
theorem frameEdge.swap {a b : Fin n → A} (h : frameEdge a b) : frameEdge b a :=
  IsFrame.of_embedding h (Equiv.swap (0 : Fin 2) 1).toEmbedding _
    (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdge.swap

theorem frameEdge.vertex0 {a b : Fin n → A} (h : frameEdge a b) : frameVertex a :=
  IsFrame.of_embedding h Fin.castSuccEmb _ (fun i => by fin_cases i; rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdge.vertex0

theorem frameEdge.vertex1 {a b : Fin n → A} (h : frameEdge a b) : frameVertex b :=
  IsFrame.of_embedding h (Fin.succEmb 1) _ (fun i => by fin_cases i; rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdge.vertex1

theorem frameVertex.smul {u : Fin n → A} (h : frameVertex u) (g : (Matrix (Fin n) (Fin n) A)ˣ) :
    frameVertex (g • u) :=
  IsFrame.of_embedding (IsFrame.smul h g) (Function.Embedding.refl _) _
    (fun i => by fin_cases i; rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertex.smul

theorem frameEdge.smul {u v : Fin n → A} (h : frameEdge u v) (g : (Matrix (Fin n) (Fin n) A)ˣ) :
    frameEdge (g • u) (g • v) :=
  IsFrame.of_embedding (IsFrame.smul h g) (Function.Embedding.refl _) _
    (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameEdge.smul

theorem frameTri.smul {u v w : Fin n → A} (h : frameTri u v w)
    (g : (Matrix (Fin n) (Fin n) A)ˣ) : frameTri (g • u) (g • v) (g • w) :=
  IsFrame.of_embedding (IsFrame.smul h g) (Function.Embedding.refl _) _
    (fun i => by fin_cases i <;> rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameTri.smul

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
