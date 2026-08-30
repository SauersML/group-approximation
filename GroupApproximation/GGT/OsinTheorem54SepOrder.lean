import GroupApproximation.GGT.OsinTheorem54SepFourGonGeneral
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# The order on the separating cosets

Osin's `⪯`, built from the ordering half of Lemma 4.8, together with the facts
that make it an order.  This is the vocabulary Lemma 5.9 is stated in;
"consecutive separating cosets" has no meaning without it.

`SepLT D lam Dc f g c c'` says some geodesic from `f` to `g` penetrates `c`
before `c'`.  The ordering half of `LemmaFourEight` is what makes that
independent of the geodesic, so the relation deserves the name.

## What is proved here

* `penetratesAt_unique` --- **a geodesic penetrates each coset at most once.**
  This is the no-backtracking content, and it needs no new input: two
  penetrations of one coset put the two component starts in a common coset,
  hence `Connected`, and `not_connected_of_isCompStart_of_geodesic` forbids that
  on a geodesic.  Irreflexivity follows.
* `sepLT_irrefl`, `sepLT_trans`, `sepLT_total` --- a strict linear order on
  `S(f,g;D)`.  Transitivity and totality use both halves of 4.8: the penetration
  half to realise all the cosets in one geodesic, the ordering half to move a
  comparison from one geodesic to another.
* `SepSucc` --- the successor relation, `c'` immediately after `c`.

## Model tests

*Degenerate.*  `Λ = Unit`, `G = ℤ`, `H = ⊥`: geodesics carry no components, so
`S(f,g;D)` is empty and everything here is vacuous.  Nothing to check and
nothing false.

*Non-degenerate.*  `G = ⟨a⟩ * ⟨b⟩`, `H = ⟨a⟩`, `X = {b^±1}`.  Here `d̂_H(1,h)` is
infinite for `h ≠ 1` --- an `H`-avoiding path out of `1` must start with `b^±1`,
and no product of `b`-letters and `a`-powers avoiding `H`-vertices reduces to a
single `a`-syllable --- so `relBall () N = {1}` and every component with
nontrivial span is essential.  Take `f = 1`, `g = aba`.  The word
`[comp a, base b, comp a]` is geodesic (`aba` is not a letter, and there is no
two-letter factorisation over `X ⊔ H`), with vertices `1, a, ab, aba`.  Its two
components are `[0,1)` and `[2,3)`, of cosets `H` and `abH`, both essential.  So

  `S(1, aba; Dc) = {H, abH}`,

two elements, penetrated at indices `0` and `2`, so `H < abH` --- a strict order
on a two-element set, as it should be.  They are consecutive, and the gap runs
from vertex `a` to vertex `ab`, spelling `b`: a single `X`-letter, so
`sepSet(a, ab) = ∅` and `b ∈ Y`.  That is Lemma 5.9's conclusion, holding in the
smallest model where it says anything.

## Lemma 5.9, the next target

Stated here rather than declared, because it is **provable and not a leaf**:

> for `c` and `c'` consecutive in `S(f,g;D)`, penetrated by a geodesic `w` at
> components `[i,k)` and `[j,l)`, the segment between them has
> `sepSet D lam Dc (vertex f w k) (vertex f w j) = ∅`.

The argument is the penetration half of 4.8 turned on the sub-geodesic: a coset
separating the gap would be essentially penetrated by the sub-path, hence by `w`
itself at an index strictly between `i` and `j`, contradicting consecutiveness.
What it needs beyond what is here is that a sub-word of a geodesic word is a
geodesic word, and that a component of a sub-word is a component of the whole ---
the same maximality transfer as `isComp_fourGon_of_isComp_side_of_end`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin's `⪯`**: some geodesic from `f` to `g` penetrates `c` before `c'`.
The ordering half of `LemmaFourEight` makes this independent of the geodesic. -/
def SepLT (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G)
    (c c' : G ⧸ D.fam lam) : Prop :=
  ∃ w : List (RelLetter G Λ), IsGeodesicWord D f g w ∧ ∃ i j : ℕ,
    PenetratesAt D lam Dc f w i c ∧ PenetratesAt D lam Dc f w j c' ∧ i < j

/-- **A geodesic penetrates each coset at most once.**

Two penetrations of one coset put their component starts in a common coset of
`H_lam`, so they are `Connected`; and no two distinct components of a geodesic
word are connected. -/
theorem penetratesAt_unique {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ} {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w)
    {c : G ⧸ D.fam lam} {i j : ℕ}
    (hi : PenetratesAt D lam Dc f w i c) (hj : PenetratesAt D lam Dc f w j c) :
    i = j := by
  by_contra hne
  obtain ⟨⟨ki, hEPi⟩, hci⟩ := hi
  obtain ⟨⟨kj, hEPj⟩, hcj⟩ := hj
  refine not_connected_of_isCompStart_of_geodesic D hw ⟨ki, hEPi⟩ ⟨kj, hEPj⟩
    hne ?_
  refine connected_of_mk_eq_mk ?_
  rw [← hci, ← hcj]

/-- **Irreflexivity**, from uniqueness of the penetration index. -/
theorem sepLT_irrefl {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ} {f g : G}
    {c : G ⧸ D.fam lam} : ¬ SepLT D lam Dc f g c c := by
  rintro ⟨w, hw, i, j, hPi, hPj, hij⟩
  have heq := penetratesAt_unique hw hPi hPj
  omega

/-- **Totality on `S(f,g;D)`.**  Both cosets are realised in one geodesic by the
penetration half of 4.8, and distinct cosets get distinct indices because the
index determines the coset. -/
theorem sepLT_total {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) {f g : G} {c c' : G ⧸ D.fam lam}
    (hc : c ∈ sepSet D lam Dc f g) (hc' : c' ∈ sepSet D lam Dc f g)
    (hne : c ≠ c') :
    SepLT D lam Dc f g c c' ∨ SepLT D lam Dc f g c' c := by
  obtain ⟨w, hw⟩ := existsGeodesicWord D f g
  obtain ⟨i, ki, hEPi, hci⟩ := h48.1 f g w hw c hc
  obtain ⟨j, kj, hEPj, hcj⟩ := h48.1 f g w hw c' hc'
  have hPi : PenetratesAt D lam Dc f w i c := ⟨⟨ki, hEPi⟩, hci⟩
  have hPj : PenetratesAt D lam Dc f w j c' := ⟨⟨kj, hEPj⟩, hcj⟩
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact Or.inl ⟨w, hw, i, j, hPi, hPj, hlt⟩
  · refine absurd ?_ hne
    rw [hci, hcj, heq]
  · exact Or.inr ⟨w, hw, j, i, hPj, hPi, hgt⟩

/-- **Transitivity.**  The third coset is realised in the first geodesic by the
penetration half, and the ordering half moves the second comparison onto that
geodesic. -/
theorem sepLT_trans {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) {f g : G} {c c' c'' : G ⧸ D.fam lam}
    (hc'' : c'' ∈ sepSet D lam Dc f g)
    (h1 : SepLT D lam Dc f g c c') (h2 : SepLT D lam Dc f g c' c'') :
    SepLT D lam Dc f g c c'' := by
  obtain ⟨w, hw, i, j, hPi, hPj, hij⟩ := h1
  obtain ⟨w', hw', j', k', hPj', hPk', hjk⟩ := h2
  obtain ⟨m, km, hEPm, hcm⟩ := h48.1 f g w hw c'' hc''
  have hPm : PenetratesAt D lam Dc f w m c'' := ⟨⟨km, hEPm⟩, hcm⟩
  refine ⟨w, hw, i, m, hPi, hPm, ?_⟩
  have hjm : j < m :=
    (h48.2 f g w' w hw' hw c' c'' j' k' j m hPj' hPk' hPj hPm).mp hjk
  omega

/-- **The successor relation**: `c'` comes immediately after `c`, with no
separating coset strictly between.  This is what "consecutive" means in
Lemma 5.9. -/
def SepSucc (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ) (f g : G)
    (c c' : G ⧸ D.fam lam) : Prop :=
  SepLT D lam Dc f g c c' ∧
    ∀ c'' ∈ sepSet D lam Dc f g,
      ¬ (SepLT D lam Dc f g c c'' ∧ SepLT D lam Dc f g c'' c')

end OsinComponents
end GGT
end GroupApproximation
