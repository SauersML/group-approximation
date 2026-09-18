import GroupApproximation.BooneHigman.Metabelian.EnvelopeCantorAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Tree automorphisms on prepended streams

Stream facts used for fragmentation in `V_X(H)` (`EnvelopeSimpleFragStep`):

* `frag_firstWord_prepend`: the first `|w| + N` letters of `w y` are `w` followed by the first
  `N` letters of `y`;
* `frag_eq_of_firstWord`: streams with the same long initial words are equal;
* `frag_cantorHom_prepend`: `g (c y) = (g • c) (g|_c y)` on the Cantor set, from
  `TreeAut.smul_append` and `firstWord_streamFun`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*}

theorem frag_firstWord_prepend (w : List X) (y : Cantor X) (N : ℕ) :
    firstWord (w.length + N) (prepend w y) = w ++ firstWord N y := by
  have e : prepend (w ++ firstWord N y) (dropN N y) = prepend w y := by
    rw [prepend_append, prepend_firstWord]
  have h := firstWord_length_prepend (w ++ firstWord N y) (dropN N y)
  rw [e, List.length_append, length_firstWord] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_firstWord_prepend

theorem frag_eq_of_firstWord {a b : Cantor X} (M : ℕ)
    (h : ∀ N, firstWord (M + N) a = firstWord (M + N) b) : a = b := by
  funext n
  have h1 : (fun i : Fin (M + (n + 1)) => a i) = fun i => b i :=
    List.ofFn_inj.mp (h (n + 1))
  exact congrFun h1 ⟨n, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_eq_of_firstWord

/-- A tree automorphism acts on the cone of `c` through its state at `c`. -/
theorem frag_cantorHom_prepend (g : TreeAut X) (c : List X) (y : Cantor X) :
    cantorHom g (prepend c y) = prepend (g • c) (cantorHom (TreeAut.state g c) y) := by
  refine frag_eq_of_firstWord c.length fun N => ?_
  have hR := frag_firstWord_prepend (g • c) (cantorHom (TreeAut.state g c) y) N
  rw [TreeAut.length_smul] at hR
  rw [hR, cantorHom_apply, cantorHom_apply, firstWord_streamFun, firstWord_streamFun,
    frag_firstWord_prepend, TreeAut.smul_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_cantorHom_prepend

end GroupApproximation.BooneHigman.Metabelian.Envelope
