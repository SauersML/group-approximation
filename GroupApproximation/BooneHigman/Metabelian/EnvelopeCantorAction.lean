import GroupApproximation.BooneHigman.Trees.TreeAut
import GroupApproximation.BooneHigman.V.Cantor
import Mathlib.Data.List.GetD
import GroupApproximation.Meta.AxiomGuard

/-!
# Tree automorphisms act faithfully on the Cantor set

A tree automorphism `g : TreeAut X` preserves lengths and prefixes of words, so it induces a map
on streams: the `n`-th letter of `g · x` is the `n`-th letter of `g • (x₀ … xₙ)`.

Route.  `firstWord_streamFun` says that the first `N` letters of `streamFun g x` are
`g • firstWord N x` (prefix preservation, `TreeAut.smul_prefix`).  From it `streamFun` is
multiplicative, hence a homomorphism `cantorHom : TreeAut X →* Equiv.Perm (Cantor X)`, and
`cantorHom_injective` recovers `g • w` as the first `|w|` letters of `g · (w a a a …)`.

This is the embedding of a self-similar group into its Röver–Nekrashevych group used in
Zaremsky's envelope (arXiv:2405.09722).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*}

theorem firstWord_eq_take {M N : ℕ} (h : M ≤ N) (x : Cantor X) :
    firstWord M x = (firstWord N x).take M := by
  refine List.ext_getElem ?_ ?_
  · simp only [List.length_take, length_firstWord]
    omega
  · intro n _ _
    simp [firstWord]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.firstWord_eq_take

/-- The action of a tree automorphism on streams, letter by letter. -/
def streamFun (g : TreeAut X) (x : Cantor X) : Cantor X :=
  fun n => (g • firstWord (n + 1) x).getD n (x n)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamFun

theorem firstWord_streamFun (g : TreeAut X) (x : Cantor X) (N : ℕ) :
    firstWord N (streamFun g x) = g • firstWord N x := by
  refine List.ext_getElem ?_ ?_
  · simp only [TreeAut.length_smul, length_firstWord]
  · intro k h₁ h₂
    have hk : k < N := by simpa using h₁
    have hlen : k < (g • firstWord (k + 1) x).length := by
      rw [TreeAut.length_smul, length_firstWord]
      omega
    have hpre : g • firstWord (k + 1) x <+: g • firstWord N x := by
      have h := TreeAut.smul_prefix g ((firstWord N x).take (k + 1))
        ((firstWord N x).drop (k + 1))
      rwa [List.take_append_drop, ← firstWord_eq_take (M := k + 1) (N := N) (by omega) x] at h
    calc (firstWord N (streamFun g x))[k]'h₁ = streamFun g x k := by simp [firstWord]
      _ = (g • firstWord (k + 1) x)[k]'hlen := List.getD_eq_getElem _ _ hlen
      _ = (g • firstWord N x)[k]'h₂ := hpre.getElem hlen

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.firstWord_streamFun

theorem streamFun_mul (g h : TreeAut X) (x : Cantor X) :
    streamFun (g * h) x = streamFun g (streamFun h x) := by
  funext n
  show ((g * h) • firstWord (n + 1) x).getD n (x n) =
    (g • firstWord (n + 1) (streamFun h x)).getD n (streamFun h x n)
  rw [firstWord_streamFun, mul_smul]
  have hn : n < (g • h • firstWord (n + 1) x).length := by
    rw [TreeAut.length_smul, TreeAut.length_smul, length_firstWord]
    omega
  rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hn]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamFun_mul

theorem streamFun_one (x : Cantor X) : streamFun 1 x = x := by
  funext n
  show ((1 : TreeAut X) • firstWord (n + 1) x).getD n (x n) = x n
  rw [one_smul]
  have hn : n < (firstWord (n + 1) x).length := by
    rw [length_firstWord]
    omega
  rw [List.getD_eq_getElem _ _ hn]
  simp [firstWord]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.streamFun_one

/-- The permutation of the Cantor set induced by a tree automorphism. -/
def cantorPerm (g : TreeAut X) : Equiv.Perm (Cantor X) where
  toFun := streamFun g
  invFun := streamFun g⁻¹
  left_inv x := by
    show streamFun g⁻¹ (streamFun g x) = x
    rw [← streamFun_mul, inv_mul_cancel, streamFun_one]
  right_inv x := by
    show streamFun g (streamFun g⁻¹ x) = x
    rw [← streamFun_mul, mul_inv_cancel, streamFun_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorPerm

/-- The action of `TreeAut X` on the Cantor set. -/
def cantorHom : TreeAut X →* Equiv.Perm (Cantor X) where
  toFun := cantorPerm
  map_one' := Equiv.ext fun x => streamFun_one x
  map_mul' g h := Equiv.ext fun x => streamFun_mul g h x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorHom

theorem cantorHom_apply (g : TreeAut X) (x : Cantor X) : cantorHom g x = streamFun g x := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorHom_apply

theorem firstWord_length_prepend (w : List X) (y : Cantor X) :
    firstWord w.length (prepend w y) = w := by
  refine List.ext_getElem (length_firstWord _ _) fun n _ h₂ => ?_
  simp only [firstWord, List.getElem_ofFn]
  exact prepend_getElem w y h₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.firstWord_length_prepend

/-- A tree automorphism is determined by its action on the Cantor set. -/
theorem cantorHom_injective [Nonempty X] : Function.Injective (cantorHom (X := X)) := by
  intro g h hgh
  obtain ⟨a⟩ := ‹Nonempty X›
  have e : ∀ (k : TreeAut X) (w : List X),
      k • w = firstWord w.length (cantorHom k (prepend w fun _ => a)) := by
    intro k w
    rw [cantorHom_apply, firstWord_streamFun, firstWord_length_prepend]
  exact TreeAut.ext fun w => by rw [e g w, e h w, hgh]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.cantorHom_injective

end GroupApproximation.BooneHigman.Metabelian.Envelope
