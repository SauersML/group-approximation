import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# The conditions (W1), (W2), (W3) on a word of `X ⊔ ℋ`

Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and rotating
families* (arXiv:1111.7048), Lemma 4.21, and Hull, *Small cancellation in
acylindrically hyperbolic groups* (arXiv:1308.4345), §5, which quotes them
verbatim:

> **(W1)** `W` contains no subwords of the form `xy` where `x, y ∈ X`.
>
> **(W2)** If `W` contains `h ∈ H_λ` for some `λ`, then `d̂_λ(1, h) ≥ 50C`,
> where `C` is the constant from Lemma C.
>
> **(W3)** If `W` contains a subword `h₁xh₂` (respectively, `h₁h₂`) where
> `x ∈ X`, `h₁ ∈ H_λ` and `h₂ ∈ H_μ`, then either `λ ≠ μ` or the element of `G`
> represented by `x` does not belong to `H_λ` (respectively, `λ ≠ μ`).

They are stated here **separately**, one `Prop` each, so that a consumer needing
only two of them does not have to produce the third; the two printed halves of
(W3) stay together because they are one condition in the source.

## The renderings, and why each is the faithful one

* A *subword* is read as a run of consecutive positions, so each condition is a
  statement about `w[i]?` and its successors.  That is the form the relator
  lane already uses (`HullSCRelatorSeparation2AlignedClose`), and `getElem?`
  rather than `getElem` with a proof is what makes "if there is a next letter"
  free rather than a side condition.
* (W2)'s `d̂_λ(1,h) ≥ 50C` becomes `h ∉ D.relBall lam R` for a radius `R` the
  predicate carries.  This repository has no `d̂` norm --- a lower bound on it is
  expressible only as falling outside a ball --- and the negative form is the
  one consumers want: `relBall_mono_radius` turns it into a lower bound on
  whatever radius a bound hands back, which is exactly the step that converts
  `Σ ℓ̂ ≤ Kn` into a bound on the number of isolated components.
* `R` is a parameter rather than `50 ·` a constant fixed inside, because the
  constant of Lemma C is not uniform in the side count in this tree.  See
  `GGT/HullYiLemmaC.lean`: a consumer at a fixed side count picks `R` after
  receiving `C(n)`, so the threshold belongs to the consumer.

## What (W2) buys immediately

`ne_one_of_isWTwo`: every `λ`-letter of a `(W2)` word has value `≠ 1`, because
`1` lies in every relative ball.  That is the hypothesis single-letter polygon
sides need, so a `(W2)` word supplies its own geodesic clause.

## Connectors across two paths

Lemma 4.21(b) pairs a component of `p` with a component of `q`, and states the
pairing at the components' **starts**.  Hull's `yi` consumes it at both ends: his
`e₀` joins `(u₁)₋` to `(v₁)₋` and his `eᵢ` joins `(uᵢ)₊` to `(vᵢ)₊`, and the
argument that `c = Lab(e₀) = Lab(e₁) = ⋯` is what lands the connecting element in
`E(f₁) ∩ ⋯ ∩ E(f_k)`.  `endConnector_mem_fam` is the passage from one to the
other, so a statement of 4.21(b) need carry only the start form.

## Non-vacuity

`hullShape t a b` is the shape of Hull's own relator at one block --- one
`X`-letter, then subgroup letters of alternating index --- and it satisfies all
three conditions (`isWOne_hullShape`, `isWTwo_hullShape`,
`isWThree_hullShape`).  Hull's `W ≡ t⁻¹h₁^{m₁}h₂^{l₁}…h₁^{m_n}h₂^{l_n}` is this
shape extended, with `t` adjoined to `X` **as a letter**: every `h_i^{m}` is a
single letter of the coned subgroup `⟨h_i⟩`, and the whole base part is the one
letter `t⁻¹`.  A word carrying a long base prefix is not of this shape and is
not a `W`-word --- (W1) fails, and so does (W4), which allows only one
`X`-letter in the entire word.
-/

namespace GroupApproximation
namespace GGT
namespace WWord

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The three conditions -/

/-- **(W1)**: no two consecutive letters are both letters of `X`. -/
def IsWOne (w : List (RelLetter G Λ)) : Prop :=
  ∀ (i : ℕ) (x y : G), w[i]? = some (RelLetter.base x) →
    w[i + 1]? = some (RelLetter.base y) → False

/-- **(W2)**: every subgroup letter is deeper than `R` in its own relative
metric. -/
def IsWTwo (D : RelGenSet G Λ) (R : ℕ) (w : List (RelLetter G Λ)) : Prop :=
  ∀ (i : ℕ) (lam : Λ) (h : G), w[i]? = some (RelLetter.comp lam h) →
    h ∉ D.relBall lam R

/-- **(W3)**: two subgroup letters that are adjacent, or separated by one
`X`-letter, are not connectable --- distinct indices in the first case, and in
the second either distinct indices or a separating letter outside the
subgroup. -/
def IsWThree (D : RelGenSet G Λ) (w : List (RelLetter G Λ)) : Prop :=
  (∀ (i : ℕ) (lam mu : Λ) (h₁ h₂ : G), w[i]? = some (RelLetter.comp lam h₁) →
      w[i + 1]? = some (RelLetter.comp mu h₂) → lam ≠ mu) ∧
    (∀ (i : ℕ) (lam mu : Λ) (h₁ h₂ x : G),
      w[i]? = some (RelLetter.comp lam h₁) →
        w[i + 1]? = some (RelLetter.base x) →
          w[i + 2]? = some (RelLetter.comp mu h₂) →
            lam ≠ mu ∨ x ∉ D.fam lam)

/-! ## What (W2) gives for free -/

/-- **A `(W2)` word has no trivial subgroup letter.**  The identity lies in
every relative ball, so a letter outside one is not the identity.  This is the
clause a single-letter polygon side needs to be geodesic. -/
theorem ne_one_of_isWTwo {D : RelGenSet G Λ} {R : ℕ}
    {w : List (RelLetter G Λ)} (hw : IsWTwo D R w) {i : ℕ} {lam : Λ} {h : G}
    (hi : w[i]? = some (RelLetter.comp lam h)) : h ≠ 1 := by
  intro h1
  refine hw i lam h hi ?_
  rw [h1]
  exact OsinComponents.one_mem_relBall D lam R

/-! ## Non-vacuity: the shape of Hull's relator -/

/-- **One block of Hull's relator**: a single `X`-letter followed by subgroup
letters of alternating index. -/
def hullShape (t a b : G) : List (RelLetter G Bool) :=
  [RelLetter.base t, RelLetter.comp false a, RelLetter.comp true b]

omit [Group G] in
theorem getElem?_hullShape_zero (t a b : G) :
    (hullShape t a b)[0]? = some (RelLetter.base t) := rfl

omit [Group G] in
theorem getElem?_hullShape_one (t a b : G) :
    (hullShape t a b)[1]? = some (RelLetter.comp false a) := rfl

omit [Group G] in
theorem getElem?_hullShape_two (t a b : G) :
    (hullShape t a b)[2]? = some (RelLetter.comp true b) := rfl

omit [Group G] in
theorem length_hullShape (t a b : G) : (hullShape t a b).length = 3 := rfl

omit [Group G] in
theorem isWOne_hullShape (t a b : G) : IsWOne (hullShape t a b) := by
  intro i x y h1 h2
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h2
  have hlen : (hullShape t a b).length = 3 := length_hullShape t a b
  have hi : i < 2 := by omega
  interval_cases i
  · simp [hullShape] at h1 h2
  · simp [hullShape] at h1 h2

theorem isWTwo_hullShape (D : RelGenSet G Bool) (R : ℕ) {t a b : G}
    (ha : a ∉ D.relBall false R) (hb : b ∉ D.relBall true R) :
    IsWTwo D R (hullShape t a b) := by
  intro i lam h hi
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
  have hlen : (hullShape t a b).length = 3 := length_hullShape t a b
  have hi3 : i < 3 := by omega
  interval_cases i
  · simp [hullShape] at hi
  · simp [hullShape] at hi
    obtain ⟨hlam, hval⟩ := hi
    subst hlam
    subst hval
    exact ha
  · simp [hullShape] at hi
    obtain ⟨hlam, hval⟩ := hi
    subst hlam
    subst hval
    exact hb

theorem isWThree_hullShape (D : RelGenSet G Bool) (t a b : G) :
    IsWThree D (hullShape t a b) := by
  have hlen : (hullShape t a b).length = 3 := length_hullShape t a b
  constructor
  · intro i lam mu h₁ h₂ h1 h2
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h2
    have hi : i < 2 := by omega
    interval_cases i
    · simp [hullShape] at h1
    · simp [hullShape] at h1 h2
      obtain ⟨hlam, -⟩ := h1
      obtain ⟨hmu, -⟩ := h2
      subst hlam
      subst hmu
      decide
  · intro i lam mu h₁ h₂ x h1 _ h3
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp h3
    have hi : i < 1 := by omega
    interval_cases i
    · simp [hullShape] at h1

/-! ## Connectors across two paths -/

/-- **The end-connector of a matched pair lies in the family**, given the
start-connector.

A component's span lies in its own family member
(`OsinComponents.span_mem_fam_of_isComp`), so if two components start in the
same coset of `H lam` they end in it too:

    x_kp⁻¹ * y_kq = (x_ip⁻¹ * x_kp)⁻¹ * (x_ip⁻¹ * y_iq) * (y_iq⁻¹ * y_kq),

a product of three elements of `H lam`.  This is why a statement of Lemma
4.21(b) need pair the components only at their starts. -/
theorem endConnector_mem_fam (D : RelGenSet G Λ) {lam : Λ} {vp vq : G}
    {p q : List (RelLetter G Λ)} (hp : ∀ a ∈ p, D.IsLetter a)
    (hq : ∀ a ∈ q, D.IsLetter a) {ip kp iq kq : ℕ}
    (hcp : OsinComponents.IsComp lam p ip kp)
    (hcq : OsinComponents.IsComp lam q iq kq)
    (hstart : (OsinComponents.vertex vp p ip)⁻¹ * OsinComponents.vertex vq q iq
      ∈ D.fam lam) :
    (OsinComponents.vertex vp p kp)⁻¹ * OsinComponents.vertex vq q kq
      ∈ D.fam lam := by
  have hsp : (OsinComponents.vertex vp p ip)⁻¹ * OsinComponents.vertex vp p kp
      ∈ D.fam lam := OsinComponents.span_mem_fam_of_isComp D vp hp hcp
  have hsq : (OsinComponents.vertex vq q iq)⁻¹ * OsinComponents.vertex vq q kq
      ∈ D.fam lam := OsinComponents.span_mem_fam_of_isComp D vq hq hcq
  have hprod : (OsinComponents.vertex vp p kp)⁻¹ * OsinComponents.vertex vq q kq
      = ((OsinComponents.vertex vp p ip)⁻¹ * OsinComponents.vertex vp p kp)⁻¹ *
        (((OsinComponents.vertex vp p ip)⁻¹ * OsinComponents.vertex vq q iq) *
          ((OsinComponents.vertex vq q iq)⁻¹ *
            OsinComponents.vertex vq q kq)) := by
    group
  rw [hprod]
  exact mul_mem (inv_mem hsp) (mul_mem hstart hsq)

end WWord
end GGT
end GroupApproximation
