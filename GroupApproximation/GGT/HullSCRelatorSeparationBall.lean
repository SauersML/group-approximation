import GroupApproximation.GGT.HullSCRelatorWord

/-!
# The relative-metric ball calculus Olshanskii's separation runs on

Osin, *Acylindrically hyperbolic groups*, §4, after Dahmani--Guirardel--Osin,
Definition 4.25; the vocabulary is `GGT.RelGenSet.relBall` and `GGT.AvoidsFrom`
of `GGT/WPDHyperbolicallyEmbedded.lean`.

Three facts about `d̂` are used by every step of Hull's §6, and none of them is
in the repository yet.

* `avoidsFrom_map_base` -- **a word of base letters traverses no edge of
  `Γ_{H λ}`**, from any vertex.  `GGT.AvoidsFrom` forbids reading a `λ`-letter at
  a vertex of `H λ`, and a base letter is never a `λ`-letter, so the condition
  holds letter by letter with nothing to check.
* `mem_relBall_of_wordNorm_le` -- **a short element of the family is a shallow
  one**: if `x ∈ H λ` and `|x|_X ≤ n` then `d̂_λ(1,x) ≤ n`.  This is the step that
  turns the `eps`-bound the piece condition carries -- a bound in the word metric
  of the base -- into a bound in the relative metric, which is the metric the
  depth clause of `C(eps, mu, rho)` is stated in.  It needs the base to generate,
  which for Hull's relative generating set it does: `E.rel.base` is
  `A.alphabet.carrier`.
* `relBall_mono`, `notMem_relBall_of_le` -- **the ball grows with its radius**.
  This is what lets a relator be chosen deep at a radius larger than the one the
  statement was handed: depth at `max rho rho'` implies depth at `rho`, so the
  separation estimate may raise the radius to whatever its geometry needs and
  still meet the clause it was asked for.

`GGT.RelGenSet.IsHyperbolicallyEmbedded.locallyFinite` makes every `relBall`
finite, which is what makes the exponent design of
`GGT/HullSCRelatorSeparationGaps.lean` possible.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section Ball

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A word of base letters traverses no edge of `Γ_{H λ}`**, read from any
vertex.  `GGT.RelLetter.IsCompOf lam (base g)` is `False`, so the clause
`GGT.AvoidsFrom` imposes at each letter is vacuous. -/
theorem avoidsFrom_map_base (H : Λ → Subgroup G) (lam : Λ) (l : List G) (v : G) :
    GGT.AvoidsFrom H lam (l.map GGT.RelLetter.base) v := by
  induction l generalizing v with
  | nil => exact trivial
  | cons g t ih => exact ⟨fun h => h.1, ih (v * g)⟩

/-- **The relative ball grows with its radius.** -/
theorem relBall_mono {D : GGT.RelGenSet G Λ} {lam : Λ} {m n : ℕ} (hmn : m ≤ n) :
    D.relBall lam m ⊆ D.relBall lam n := by
  intro x hx
  rw [GGT.RelGenSet.mem_relBall] at hx ⊢
  obtain ⟨hfam, w, hlet, hval, havoid, hlen⟩ := hx
  exact ⟨hfam, w, hlet, hval, havoid, le_trans hlen hmn⟩

/-- **Depth at a large radius is depth at a small one.**  This is the direction
the relator is chosen along: the estimate may demand a radius larger than the
one `C(eps, mu, rho)` names, and the deep letters it produces are still deep for
`rho`. -/
theorem notMem_relBall_of_le {D : GGT.RelGenSet G Λ} {lam : Λ} {m n : ℕ}
    (hmn : m ≤ n) {x : G} (hx : x ∉ D.relBall lam n) : x ∉ D.relBall lam m :=
  fun hmem => hx (relBall_mono hmn hmem)

/-- **A short element of the family is a shallow one**: an element of `H λ`
spelled by at most `n` letters of the base lies in the `d̂_λ`-ball of radius `n`.

The word realizing `|x|_X` is read as a word of base letters, which is
admissible because its letters are letters of the base, spells `x` by
`listVal_map_base`, and traverses no edge of `Γ_{H λ}` by
`avoidsFrom_map_base`.

The hypothesis that the base generates is not decoration: `wordNorm` is an
infimum over a set of lengths that is empty when the element has no word at all,
and `sInf ∅ = 0`, so without it `|x|_X ≤ n` would hold vacuously for every `x`
outside `⟨X⟩`.  For Hull's relative generating set the hypothesis is free --
`E.rel.base` is `A.alphabet.carrier`, a symmetric generating set. -/
theorem mem_relBall_of_wordNorm_le {D : GGT.RelGenSet G Λ} {lam : Λ} {x : G}
    {n : ℕ} (hbase : IsSymmetricGeneratingSet D.base) (hx : x ∈ D.fam lam)
    (hn : wordNorm D.base x ≤ n) : x ∈ D.relBall lam n := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hbase x
  rw [GGT.RelGenSet.mem_relBall]
  refine ⟨hx, l.map GGT.RelLetter.base, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact hl.letters g hg
  · rw [listVal_map_base]
    exact hl.prod_eq
  · exact avoidsFrom_map_base D.fam lam l 1
  · rw [List.length_map, hlen]
    exact hn

end Ball

/-! ## Hull's relative generating set has a generating base -/

/-- **The base of the core is a symmetric generating set.**  It is Hull's
alphabet, by `HypEmbeddedCore.base_eq`, so `mem_relBall_of_wordNorm_le` applies
to it with no side condition. -/
theorem isSymmetricGeneratingSet_base {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G}
    (E : HypEmbeddedCore A N) : IsSymmetricGeneratingSet E.rel.base := by
  rw [E.base_eq]
  exact A.alphabet.symmetricGenerating

end HullSC
end GroupApproximation
