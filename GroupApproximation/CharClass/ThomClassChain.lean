import GroupApproximation.CharClass.ThomFreeModule

/-!
# The Thom class, named

`ThomFreeModule.lean` proves the linear algebra: given Leray–Hirsch bases for
`H^*(P(E ⊕ 1))` and `H^*(P(E))` and the two equations describing the restriction on
them, the kernel of the restriction is free of rank one on
`thomGenerator = ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`, and a map injective with that image has a
unique element over it.

This file gives that element a name and records its three properties, so that when
`cc-projective`'s Leray–Hirsch lands the Thom class is a term rather than an
existential.  Everything is stated over the Leray–Hirsch data as *hypotheses*, exactly
as the lead's split prescribes: nothing here waits on the ladder, and when the ladder
lands these instantiate.

## Main results

* `thomClass` — the unique class over `ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`.
* `jm_thomClass`, `thomClass_unique` — its defining property and its uniqueness.
* `existsUnique_smul_thomClass` — `H^{*}(P(E⊕1), P(E⊕1) ∖ Z)` is free of rank one on it,
  which is the isomorphism `H^{k+2r}(pair) ≅ H^k(X)` of the program note.
-/

namespace GroupApproximation.CharClass

variable {R : Type*} [CommRing R] {M M' P : Type*}
variable [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable [AddCommGroup P] [Module R P]
variable {r : ℕ}

section ThomClass

variable (b : Module.Basis (Fin (r + 1)) R M) (b' : Module.Basis (Fin r) R M')
variable (c : Fin r → R) {ρ : M →ₗ[R] M'}
variable (hcast : ∀ i : Fin r, ρ (b (Fin.castSucc i)) = b' i)
variable (hlast : ρ (b (Fin.last r)) = -∑ i, c i • b' i)
variable (jm : P →ₗ[R] M) (hinj : Function.Injective jm)
variable (hrange : LinearMap.range jm = LinearMap.ker ρ)

/-- **The Thom class**: the unique class of the pair restricting to
`ξ^r + γ₁ ξ^{r−1} + ⋯ + γ_r`. -/
noncomputable def thomClass : P :=
  (existsUnique_lift (w := thomGenerator b c) jm hinj hrange
    (map_thomGenerator b b' c hcast hlast)).choose

/-- The defining property of the Thom class. -/
theorem jm_thomClass :
    jm (thomClass b b' c hcast hlast jm hinj hrange) = thomGenerator b c :=
  (existsUnique_lift (w := thomGenerator b c) jm hinj hrange
    (map_thomGenerator b b' c hcast hlast)).choose_spec.1

/-- Nothing else restricts to the Chern relation. -/
theorem thomClass_unique (v : P) (hv : jm v = thomGenerator b c) :
    v = thomClass b b' c hcast hlast jm hinj hrange :=
  (existsUnique_lift (w := thomGenerator b c) jm hinj hrange
    (map_thomGenerator b b' c hcast hlast)).choose_spec.2 v hv

/-- **The relative cohomology of the pair is free of rank one on the Thom class.**  This
is the isomorphism `H^{k+2r}(P(E⊕1), P(E⊕1) ∖ Z) ≅ H^k(X)` of §1.4 item 5. -/
theorem existsUnique_smul_thomClass (x : P) :
    ∃! a : R, x = a • thomClass b b' c hcast hlast jm hinj hrange :=
  existsUnique_smul_of_injective_of_range b b' c hcast hlast jm hinj hrange
    (jm_thomClass b b' c hcast hlast jm hinj hrange) x

end ThomClass

end GroupApproximation.CharClass
