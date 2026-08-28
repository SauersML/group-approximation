import GroupApproximation.GGT.OsinComponents

/-!
# Penetration, separating cosets, and why `sep` is well defined

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Definition 4.3,
verbatim:

> We say that a path `p` in `Γ(G, X ⊔ ℋ)` *penetrates* a coset `xH_λ` for some
> `λ ∈ Λ` if `p` decomposes as `p₁ a p₂`, where `p₁, p₂` are possibly trivial,
> `a₋ ∈ xH_λ`, and `a` is an `H_λ`-component of `p`.  If, in addition,
> `d̂_λ(a₋,a₊) > D`, then we say that `p` *essentially penetrates* the coset
> `xH_λ`.
>
> If some `f, g ∈ G` are joined by a geodesic path `p` in `Γ(G, X ⊔ ℋ)` that
> essentially penetrates `xH_λ`, we call `xH_λ` an *(f,g,D)-separating coset*.
> The set of all `(f,g,D)`-separating cosets is denoted by `S(f,g;D)`.

## The quantifier, and why it matters here

The definition asks for **some** geodesic, not every one.  So `S(f,g;D)` is a
union over all geodesics from `f` to `g`, and its finiteness is *not* immediate:
nothing in the definition stops different geodesics from contributing different
cosets.  What rules that out is Osin's Lemma 4.8:

> For any `f, g ∈ G`, `⪯` is a linear order on `S(f,g;D)` and every geodesic `p`
> from `f` to `g` penetrates all `(f,g,D)`-separating cosets according to the
> order `⪯`.

Once *every* geodesic penetrates *all* of them, a single geodesic bounds the
whole set: each separating coset is the coset of the initial vertex of one of
that geodesic's components, and a word of length `n` has at most `n` of those.
That is `sepSet_finite`, and it is what makes an `ℕ`-valued `sep` --- the first
field of `GGT.OsinEnlargement.SepData` --- well defined.  Getting this order of
dependency wrong is the trap the team lead flagged: finiteness first, then
`sep`.

Only the "every geodesic penetrates all of them" half of Lemma 4.8 is carried
in `LemmaFourEight`; the linear order `⪯` is not needed for finiteness and is
left to the module that builds it, which is where Lemma 5.9's consecutive-coset
statement will want it.

## What is proved

* `listVal_cons`, `vertex_length` --- a word read from `v` ends at
  `v * listVal w`, so `IsGeodesicWord` and the component vocabulary of
  `GGT/OsinComponents.lean` describe the same path.
* `sepSet_finite` --- **`S(f,g;D)` is finite**, from `LemmaFourEight` and any
  one geodesic between the endpoints.

## What is named, not proved

* `LemmaFourEight` --- Osin's Lemma 4.8, above.
* `ExistsGeodesicWord` --- every pair of group elements is joined by a geodesic
  *word over `RelLetter`*.  `WordMetric.exists_isWord_length_eq` already gives a
  realizing `List G` of the right length; lifting it to `List (RelLetter G Λ)`
  is a choice, for each letter, of which side of `X ⊔ ℋ` it is read from.  That
  is routine and deliberately not done here: it is bookkeeping about the letter
  type rather than about Osin's geometry, and doing it inline would put a
  `Classical.choice` in the middle of a module whose subject is something else.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Words and their endpoints -/

theorem listVal_cons (a : RelLetter G Λ) (t : List (RelLetter G Λ)) :
    RelLetter.listVal (a :: t) = a.val * RelLetter.listVal t := by
  show ((a :: t).map RelLetter.val).prod = a.val * (t.map RelLetter.val).prod
  rw [List.map_cons, List.prod_cons]

/-- A word read from `v` ends at `v * listVal w`.  This is what identifies the
`vertex` indexing of `GGT/OsinComponents.lean` with the path whose label is
`w`. -/
theorem vertex_length (v : G) (w : List (RelLetter G Λ)) :
    vertex v w w.length = v * RelLetter.listVal w := by
  induction w generalizing v with
  | nil =>
      show vertex v ([] : List (RelLetter G Λ)) 0 = v * RelLetter.listVal []
      rw [vertex_nil, RelLetter.listVal_nil, mul_one]
  | cons a t ih =>
      show vertex v (a :: t) (t.length + 1) = v * RelLetter.listVal (a :: t)
      rw [vertex_cons_succ, ih, listVal_cons, mul_assoc]

/-- **A geodesic word from `f` to `g`**: a word in the letters of
`X ⊔ ℋ` spelling `f⁻¹g` whose length realises `d_{X⊔ℋ}(f,g)`. -/
def IsGeodesicWord (D : RelGenSet G Λ) (f g : G)
    (w : List (RelLetter G Λ)) : Prop :=
  (∀ a ∈ w, D.IsLetter a) ∧ f * RelLetter.listVal w = g ∧
    w.length = wordDist D.alphabet.carrier f g

theorem IsGeodesicWord.vertex_length_eq {D : RelGenSet G Λ} {f g : G}
    {w : List (RelLetter G Λ)} (h : IsGeodesicWord D f g w) :
    vertex f w w.length = g := by
  rw [vertex_length]
  exact h.2.1

/-! ## Penetration -/

/-- **Osin, Definition 4.3**, first half: the path `w` read from `v` penetrates
the coset of the initial vertex of its component `[i,k)`. -/
def Penetrates (lam : Λ) (w : List (RelLetter G Λ)) (i k : ℕ) : Prop :=
  IsComp lam w i k

/-- **Osin, Definition 4.3**, second half: the penetration is *essential* when
the component's endpoints are more than `Dc` apart in `d̂_λ`, i.e. when the
element they span is outside the `d̂_λ`-ball of radius `Dc`. -/
def EssentiallyPenetrates (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (v : G)
    (w : List (RelLetter G Λ)) (i k : ℕ) : Prop :=
  IsComp lam w i k ∧ (vertex v w i)⁻¹ * vertex v w k ∉ D.relBall lam Dc

/-- **Osin's `S(f,g;D)`**: the cosets essentially penetrated by *some* geodesic
from `f` to `g`. -/
def sepSet (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G) :
    Set (G ⧸ D.fam lam) :=
  {c | ∃ (w : List (RelLetter G Λ)) (i k : ℕ),
    IsGeodesicWord D f g w ∧ EssentiallyPenetrates D lam Dc f w i k ∧
      c = QuotientGroup.mk (vertex f w i)}

/-- **Osin, Lemma 4.8**, the half finiteness needs: *every* geodesic from `f`
to `g` penetrates *all* the `(f,g,D)`-separating cosets.  The linear order `⪯`
of the full statement is not carried here. -/
def LemmaFourEight (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) : Prop :=
  ∀ (f g : G) (w : List (RelLetter G Λ)), IsGeodesicWord D f g w →
    ∀ c ∈ sepSet D lam Dc f g, ∃ i k : ℕ,
      EssentiallyPenetrates D lam Dc f w i k ∧
        c = QuotientGroup.mk (vertex f w i)

/-- Every pair of elements is joined by a geodesic word over `RelLetter`.
Routine from `WordMetric.exists_isWord_length_eq`; see the module docstring. -/
def ExistsGeodesicWord (D : RelGenSet G Λ) : Prop :=
  ∀ f g : G, ∃ w : List (RelLetter G Λ), IsGeodesicWord D f g w

/-! ## Finiteness -/

/-- **`S(f,g;D)` is finite.**  By Lemma 4.8 every separating coset is the coset
of the initial vertex of a component of one fixed geodesic, and a word of
length `n` has fewer than `n + 1` indices, so the whole set is the image of a
finite set of indices. -/
theorem sepSet_finite {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) (f g : G) {w : List (RelLetter G Λ)}
    (hw : IsGeodesicWord D f g w) : (sepSet D lam Dc f g).Finite := by
  refine Set.Finite.subset
    ((Set.finite_Iio w.length).image
      (fun i : ℕ => (QuotientGroup.mk (vertex f w i) : G ⧸ D.fam lam))) ?_
  intro c hc
  obtain ⟨i, k, hpen, hceq⟩ := h48 f g w hw c hc
  obtain ⟨hik, hkw, -, -, -⟩ := hpen.1
  exact ⟨i, by simp only [Set.mem_Iio]; omega, hceq.symm⟩

/-- The separating-coset count, once Lemma 4.8 has made the set finite.  This
is the `sep` field of `GGT.OsinEnlargement.SepData`. -/
noncomputable def sepCard (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G) :
    ℕ :=
  (sepSet D lam Dc f g).ncard

end OsinComponents
end GGT
end GroupApproximation
