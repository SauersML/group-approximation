import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegSpans
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Commute
import GroupApproximation.Meta.AxiomGuard

/-!
# The Nagao torus over an arbitrary field, up to constant symbols

k2-poly piece A5.2 (lane k2-field-b). The `F_p` chain (bh-met-92c/94x) uses the torus
`k2PolyDeg_torus p : F_pˣ →* St_I(F_p[X])`, `c ↦ C(h_mL(c))`. It is a monoid hom only because
Steinberg symbols vanish over `F_p` (`FieldK2.bruhatBigCell_h_mul_zmod`). Over an arbitrary field
`F` the same map is multiplicative only up to the constant symbol `C({c, c'})`. This file is the
layer every ported `Torus*`/`JRes*` file uses in place of `map_mul (k2PolyDeg_torus p …)`.

* `fieldTorus F m L hmL c = C(h_mL(c))`, with `fieldTorus_apply` (closed form `h_mL(C c)`).
* `fieldTorus_mul`: `t(c c') = C(symbol_mL(c, c')) · t(c') · t(c)`. This is exactly the definition
  of the symbol, `symbol(u, v) = h(u v) h(u)⁻¹ h(v)⁻¹`, pushed through `C`.
* `fieldTorus_conj_rootSpan`: the torus conjugates every root span of `St_I(F[X])` into itself.
  This is the `F_p` proof verbatim, since it never used multiplicativity.
* `constSymbol_commute_const`, `fieldTorus_commute_constSymbol`: a constant symbol commutes with
  every constant, in particular with the torus (`FieldK2.symbol_commute`, which needs a third
  index). Centrality in all of `St_I(F[X])` is A5.1 and is not claimed here.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.Metabelian.ElemFP
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_conj_mem)

variable {I : Type} [Fintype I] [DecidableEq I] (F : Type) [Field F]

/-- The field torus `c ↦ C(h_mL(c)) ∈ St_I(F[X])`. Over `F_p` this is `k2PolyDeg_torus p`. -/
noncomputable def fieldTorus (m L : I) (hmL : m ≠ L) (c : Fˣ) : SteinbergGroup I (Polynomial F) :=
  ringMap (I := I) (Polynomial.C : F →+* Polynomial F) (h m L hmL c)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus

variable {F}

/-- The field torus in closed form: `C(h_mL(c)) = h_mL(C c)`. -/
theorem fieldTorus_apply (m L : I) (hmL : m ≠ L) (c : Fˣ) :
    fieldTorus F m L hmL c =
      h m L hmL (Units.map (Polynomial.C : F →+* Polynomial F).toMonoidHom c) :=
  k2PolyDeg_ringMap_h _ m L hmL c

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus_apply

/-- `h(u v) = symbol(u, v) · h(v) · h(u)` in `St_I(F)`: the definition of the symbol, rearranged. -/
theorem h_mul_eq_symbol_mul (m L : I) (hmL : m ≠ L) (u v : Fˣ) :
    h m L hmL (u * v) = FieldK2.symbol m L hmL u v * h m L hmL v * h m L hmL u := by
  simp only [FieldK2.symbol]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.h_mul_eq_symbol_mul

/-- **Multiplicativity up to the constant symbol.** `t(c c') = C(symbol(c, c')) · t(c') · t(c)`.
Over `F_p` the symbol is `1` and this recovers `map_mul (k2PolyDeg_torus p …)` (up to the order of
the factors, which commute there). -/
theorem fieldTorus_mul (m L : I) (hmL : m ≠ L) (c c' : Fˣ) :
    fieldTorus F m L hmL (c * c') =
      ringMap (I := I) (Polynomial.C : F →+* Polynomial F) (FieldK2.symbol m L hmL c c') *
        fieldTorus F m L hmL c' * fieldTorus F m L hmL c := by
  simp only [fieldTorus, h_mul_eq_symbol_mul m L hmL c c', map_mul]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus_mul

/-- The field torus conjugates every root span of `St_I(F[X])` into itself. -/
theorem fieldTorus_conj_rootSpan (m L n : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)
    (q : I → I → Prop) (c : Fˣ) {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ rootSpan (R := Polynomial F) q) :
    fieldTorus F m L hmL c * g * (fieldTorus F m L hmL c)⁻¹ ∈
      rootSpan (R := Polynomial F) q := by
  rw [fieldTorus_apply]
  refine rootSpan_conj_mem (fun k l hkl b hq => ?_) hg
  obtain ⟨b', hb'⟩ := k2PolyDeg_h_conj_exists m L k l hmL hkl ⟨n, hmn, hLn⟩
    (Units.map (Polynomial.C : F →+* Polynomial F).toMonoidHom c) b
  rw [hb']
  exact x_mem_rootSpan hkl b' hq

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus_conj_rootSpan

/-- A constant symbol commutes with every constant `C(g)`, `g ∈ St_I(F)` (third index `k`). -/
theorem constSymbol_commute_const (m L k : I) (hmL : m ≠ L) (hmk : m ≠ k) (hLk : L ≠ k)
    (u v : Fˣ) (g : SteinbergGroup I F) :
    Commute (ringMap (I := I) (Polynomial.C : F →+* Polynomial F) (FieldK2.symbol m L hmL u v))
      (ringMap (I := I) (Polynomial.C : F →+* Polynomial F) g) :=
  (FieldK2.symbol_commute m L k hmL hmk hLk u v g).map _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.constSymbol_commute_const

/-- A constant symbol commutes with the field torus. -/
theorem fieldTorus_commute_constSymbol (m L k : I) (hmL : m ≠ L) (hmk : m ≠ k) (hLk : L ≠ k)
    (u v c : Fˣ) :
    Commute (ringMap (I := I) (Polynomial.C : F →+* Polynomial F) (FieldK2.symbol m L hmL u v))
      (fieldTorus F m L hmL c) :=
  constSymbol_commute_const m L k hmL hmk hLk u v (h m L hmL c)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus_commute_constSymbol

end GroupApproximation.BooneHigmanLinear.K2Poly
