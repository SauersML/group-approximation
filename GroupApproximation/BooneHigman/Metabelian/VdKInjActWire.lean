import GroupApproximation.BooneHigman.Metabelian.VdKInjActInj
import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectWire
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's injectivity action, part 4: the residual and the reduction

Lane `bh-met-91o`.  Parts 1–3 carry out van der Kallen's action argument in Steinberg words.

* `St_{n+1}(R)` acts on `St_n(R) × R^{n+1}` by `(h, u) · x_{ij}(a) = (h · c(u, x_{ij}(a)), u M)`.
* The action is defined on generators, and every Steinberg relator is checked
  (`vdkInjAct_genPerm_kills`).  The checks reduce exactly to the three families of
  `vdkInjAct_IsCocycle c`.
* If `c` is based at `e_last` (`vdkInjAct_IsBased c`), the fibre over `e_last` is `St_n(R)`, and
  `stab g` acts on it by right multiplication by `g⁻¹`.  So `stab g = 1` forces `g = 1`
  (`vdkInjAct_K2Stab_injective_of_cocycle`, for every commutative `R` and every `n`).

## Residual: `vdkInjAct_CocycleStatement`

A based row cocycle exists: a function `c(u, x_{ij}(a)) ∈ St_n(R)` on rows `u ∈ R^{n+1}` and roots
of `St_{n+1}(R)`, `n = r + 3`, satisfying the finite list of relator checks
`vdkInjAct_IsCocycle` and the normalisation `vdkInjAct_IsBased`.  Every item is an identity of
explicit Steinberg words in `St_n(R)`.

**LOUD (strength).**  The reduction `vdkInjAct_transitiveInj_of_cocycle` is proved.  The residual
is **not** logically weaker than the target.  Modulo Step A (the open
`vdkInjCoset_RowStabStatement`: the stabiliser of `e_last` in `St_{n+1}(R)` is the parabolic
image), it is **equivalent** to it.  Given the target and Step A, choose a section `s` of the
orbit map `g ↦ e_last M_g` with `s(e_last) = 1`.  Let `c(u, g)` be the `St_n(R)`-component of
`s(u) g s(u M_g)⁻¹` in the parabolic `P ≅ Rⁿ ⋊ St_n(R)`; on rows outside the orbit, let it be `1`.
This `c` is a based cocycle.  That construction is `VdKInjActTruth.lean`.

It is strictly smaller in **proof content**.  The action on pairs, all the relator
bookkeeping, and the base-point injectivity are proved here for every commutative ring.  What
remains is the construction of the row cocycle.  This is the combinatorial core of van der Kallen's
paper, where `c` is written down using a stable-range decomposition of `u`.

**Truth.**  It holds by van der Kallen's theorem together with Step A (see above).  Neither is
assumed.  The route avoids row extension, `vdkInj_DiagStatement`, homotopy invariance, excision
and surjectivity statements.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Residual** (lane `bh-met-91o`): for commutative `R` with `sr(R) ≤ r` (elementary
transitivity on unimodular rows given), there is a based row cocycle for `St_{r+4}(R)` with
values in `St_{r+3}(R)`.  LOUD: equivalent to `vdkInjDirect_TransitiveInjStatement` modulo
`vdkInjCoset_RowStabStatement`; smaller in proof content only. -/
def vdkInjAct_CocycleStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkInjDirect_RowTransitive R r →
      ∃ c : vdkInjAct_Cocycle (r + 3) R, vdkInjAct_IsCocycle c ∧ vdkInjAct_IsBased c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_CocycleStatement

/-- **Endpoint**: the frontier `vdkInjDirect_TransitiveInjStatement` from the residual. -/
theorem vdkInjAct_transitiveInj_of_cocycle (h : vdkInjAct_CocycleStatement) :
    vdkInjDirect_TransitiveInjStatement := by
  intro R _ r hsr htr
  obtain ⟨c, hc, hb⟩ := h R r hsr htr
  exact vdkInjAct_K2Stab_injective_of_cocycle hc hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_transitiveInj_of_cocycle

/-- **Endpoint**: `vdkStab_InjStabStatement` from the residual. -/
theorem vdkInjAct_injStab_of_cocycle (h : vdkInjAct_CocycleStatement) :
    vdkStab_InjStabStatement :=
  vdkInjDirect_injStab_of_transitive (vdkInjAct_transitiveInj_of_cocycle h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_injStab_of_cocycle

end GroupApproximation.BooneHigman.Metabelian.ElemFP
