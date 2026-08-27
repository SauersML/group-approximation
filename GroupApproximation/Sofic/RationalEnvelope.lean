import GroupApproximation.Sofic.LinearResidual

/-!
# One representation realizes the whole hidden kernel

Theorems 53.1 and 53.2.  For a perfect finite lamp the invisible kernel is the
entire lamp subgroup, and the dossier observes that this whole kernel is already
the kernel of a *single* explicit four-dimensional rational representation:
compose the split quotient `W_K ↠ G_*` with the faithful
`ρ_* : G_* ↪ GL₄(ℚ)` of Section 39.7.  Two consequences are recorded there --
the kernel of that one map is all five residuals at once, and its image is the
*same* fixed matrix group for the whole infinite alternating-lamp family.

The point is worth isolating because it sounds paradoxical: a group can fail to
be linear over every field precisely because of a subgroup that is itself
already cut out by one small linear representation.  There is no tension.  The
representation is not faithful on `W_K`; it is faithful on the quotient, and the
whole failure is concentrated in what it forgets.

## What this file proves

The mechanism, abstractly, with no dependence on the concrete family:

* `ker_comp_of_injective` -- if `ρ` is injective then inflating it along `q`
  has kernel exactly `ker q`.  So *whatever* the split quotient's kernel is, one
  representation realizes it; no property of the lamp is used.
* `ker_comp_eq_of_ker_eq` -- consequently, if `ker q` is known to be the common
  residual, the composite's kernel is that residual on the nose.
* `range_comp_eq_range` -- if `q` is surjective the composite's image is `ρ`'s
  image, *independently of the source*.  This is what makes the image the same
  fixed subgroup for every member of a family sharing one visible quotient.
* `exists_unique_factorization` -- every homomorphism killing `ker q` factors
  uniquely through `q`, which is the universal property 53.2 states for the
  envelope.

## What this file does not prove

It does not construct `ρ_*`, and it does not assert that the concrete
`G_* ↪ GL₄(ℤ[1/2])` of Section 39.7 is faithful -- that is a statement about the
explicit affine matrix model, tracked separately.  What is isolated here is the
part that is pure group theory, so that the concrete instance needs only the
faithfulness of one named matrix representation and nothing else.

Stated for an arbitrary group target rather than `GL₄(ℚ)`, since nothing in the
argument sees the dimension or the field.
-/

namespace GroupApproximation

namespace RationalEnvelope

universe u v w

variable {W : Type u} [Group W] {P : Type v} [Group P] {M : Type w} [Group M]

/-- **The envelope principle (53.1).**  Inflating a *faithful* representation of
the quotient along the quotient map has kernel exactly the quotient's kernel.

No hypothesis on `q` beyond being a homomorphism, and none at all on the
kernel: the whole content is that `ρ` separates points of `P`. -/
theorem ker_comp_of_injective (q : W →* P) (ρ : P →* M)
    (hρ : Function.Injective ρ) :
    (ρ.comp q).ker = q.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro h
    have : ρ (q x) = ρ 1 := by rw [h, map_one]
    exact hρ this
  · intro h
    rw [h, map_one]

/-- The form the dossier uses: when the split quotient's kernel is the common
invisible residual `R`, one representation has kernel exactly `R`. -/
theorem ker_comp_eq_of_ker_eq (q : W →* P) (ρ : P →* M)
    (hρ : Function.Injective ρ) {R : Subgroup W} (hR : q.ker = R) :
    (ρ.comp q).ker = R := by
  rw [ker_comp_of_injective q ρ hρ, hR]

/-- **The image does not depend on the source (53.1, second clause).**  If `q`
is surjective the inflated representation has the same image as `ρ` itself --
so an entire family of groups sharing one visible quotient has one and the same
matrix image, the differences living entirely inside the kernels. -/
theorem range_comp_eq_range (q : W →* P) (hq : Function.Surjective q)
    (ρ : P →* M) :
    (ρ.comp q).range = ρ.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨q x, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨x, rfl⟩ := hq p
    exact ⟨x, rfl⟩

/-- **The universal property (53.2).**  Every homomorphism out of `W` that kills
the kernel of `q` factors through `q`, uniquely because `q` is surjective.

Combined with `ker_comp_of_injective`, this is what lets the four-dimensional
envelope stand in for the visible quotient: any target that cannot see the
invisible kernel sees only what the envelope already records. -/
theorem exists_unique_factorization (q : W →* P) (hq : Function.Surjective q)
    {T : Type*} [Group T] (f : W →* T) (hf : q.ker ≤ f.ker) :
    ∃! g : P →* T, g.comp q = f := by
  refine ⟨(QuotientGroup.lift q.ker f hf).comp
      (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom, ?_, ?_⟩
  · refine MonoidHom.ext fun x => ?_
    show QuotientGroup.lift q.ker f hf
        ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q x)) = f x
    have hsymm : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q x)
        = QuotientGroup.mk x := by
      apply (QuotientGroup.quotientKerEquivOfSurjective q hq).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hsymm]
    rfl
  · intro g hg
    refine MonoidHom.ext fun p => ?_
    obtain ⟨x, rfl⟩ := hq p
    have h1 : g (q x) = f x := congrArg (fun h : W →* T => h x) hg
    have h2 : ((QuotientGroup.lift q.ker f hf).comp
        (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom) (q x)
        = f x := by
      show QuotientGroup.lift q.ker f hf
          ((QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q x)) = f x
      have hsymm : (QuotientGroup.quotientKerEquivOfSurjective q hq).symm (q x)
          = QuotientGroup.mk x := by
        apply (QuotientGroup.quotientKerEquivOfSurjective q hq).injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [hsymm]
      rfl
    rw [h1, h2]

/-- The packaged statement: one faithful representation of the visible quotient
realizes the invisible kernel exactly, has a source-independent image, and is
universal among targets blind to that kernel. -/
theorem envelope (q : W →* P) (hq : Function.Surjective q) (ρ : P →* M)
    (hρ : Function.Injective ρ) :
    (ρ.comp q).ker = q.ker ∧ (ρ.comp q).range = ρ.range :=
  ⟨ker_comp_of_injective q ρ hρ, range_comp_eq_range q hq ρ⟩

end RationalEnvelope

end GroupApproximation
