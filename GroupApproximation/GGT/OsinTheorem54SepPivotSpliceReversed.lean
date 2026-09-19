import GroupApproximation.GGT.OsinTheorem54SepPivotSplice
import GroupApproximation.GGT.OsinTheorem54SepCommIndex

/-!
# The pivot splice, read from the far end

Osin's Lemma 4.9 uses its construction twice.  Cosets entered before the pivot
go to `S(f,h;D)`; cosets entered after it go to `S(g,h;D)`, and for those he
writes only "arguing as above".  The second reading is the first one run in the
reversed path, and that is what this module does: every hypothesis is turned
round by the reversal vocabulary of `GGT/OsinTheorem54SepCommIndex.lean`, and
`sepSet_of_essentiallyPenetrates_of_lt_pivot` is applied to the reversed
configuration.

Three things reverse, and each has its lemma already:

* the geodesic (`isGeodesicWord_revWord`), from `g` to `f`;
* the component, to the indices `[|p| - k, |p| - i)` (`isComp_revWord`), so an
  index `n` past the pivot `m` becomes an index `|p| - (n+1)` BEFORE
  `|p| - (m+1)` --- the order of penetration is reversed with the path, which is
  exactly what the first reading needs;
* the span, to its inverse, which `relBall_inv` says `d̂_λ` does not see.  So the
  penetration stays essential and, again, no constant is spent.

The pivot's index on the second geodesic is not asked of the caller.  It is
Lemma 4.6 again --- `entrance_eq_of_isComp` on the two geodesics leaving `g` ---
so the caller supplies a component of `q` at whatever index it has, and the
matching is done here.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin's Lemma 4.9 construction, second reading.**

`p` is a geodesic from `f` to `g` whose component at `[n, n+1)` essentially
penetrates a coset of `H_λ`; a coset of `H_μ` is entered EARLIER on `p`, at
`m < n`, and is penetrated by the geodesic `q` from `g` to `h`.  Then the coset
penetrated at `n` separates `g` from `h`.

Everything is stated in `p`'s own coordinates, read from `f`: the caller never
has to compute a reversed index. -/
theorem sepSet_of_essentiallyPenetrates_of_pivot_lt (D : RelGenSet G Λ)
    (lam mu : Λ) (Dc : ℕ) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {f g h : G}
    {p q : List (RelLetter G Λ)} (hp : IsGeodesicWord D f g p)
    (hq : IsGeodesicWord D g h q) {n m j : ℕ} (hmn : m < n)
    (hess : EssentiallyPenetrates D lam Dc f p n (n + 1))
    (hpiv : IsComp mu p m (m + 1)) (hpivq : IsComp mu q j (j + 1))
    (hcos : (QuotientGroup.mk (vertex f p m) : G ⧸ D.fam mu)
      = QuotientGroup.mk (vertex g q j)) :
    (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam) ∈ sepSet D lam Dc g h := by
  obtain ⟨hcomp, hdeep⟩ := hess
  have hnp : n + 1 ≤ p.length := hcomp.2.1
  have hmp : m + 1 ≤ p.length := hpiv.2.1
  -- the reversed path, and its vertices in the original coordinates
  have hvrev : ∀ i : ℕ, vertex g (revWord p) (p.length - i) = vertex f p i := by
    intro i
    rw [← hp.2.1]
    exact vertex_revWord_of_end p f i
  have hprev : IsGeodesicWord D g f (revWord p) := isGeodesicWord_revWord D hsymm hp
  -- the two components, reversed
  have hcomprev : IsComp lam (revWord p) (p.length - (n + 1))
      (p.length - (n + 1) + 1) := by
    have hidx : p.length - n = p.length - (n + 1) + 1 := by omega
    rw [← hidx]
    exact isComp_revWord lam p hcomp
  have hpivrev : IsComp mu (revWord p) (p.length - (m + 1))
      (p.length - (m + 1) + 1) := by
    have hidx : p.length - m = p.length - (m + 1) + 1 := by omega
    rw [← hidx]
    exact isComp_revWord mu p hpiv
  -- the pivot coset, named from `g` on both sides
  have hcospiv : (QuotientGroup.mk (vertex g (revWord p) (p.length - (m + 1)))
      : G ⧸ D.fam mu) = QuotientGroup.mk (vertex g q j) := by
    rw [hvrev (m + 1)]
    exact (mk_vertex_eq_of_isComp D f hp.1 hpiv).symm.trans hcos
  -- Lemma 4.6 places the pivot at the same index on `q`
  have hjeq : p.length - (m + 1) = j :=
    entrance_eq_of_isComp D mu hprev hq hpivrev hpivq hcospiv
  subst hjeq
  -- essentiality survives, the span having only changed sign
  have hdeeprev : (vertex g (revWord p) (p.length - (n + 1)))⁻¹ *
      vertex g (revWord p) (p.length - (n + 1) + 1) ∉ D.relBall lam Dc := by
    have hidx : p.length - (n + 1) + 1 = p.length - n := by omega
    rw [hidx, hvrev (n + 1), hvrev n]
    intro hmem
    refine hdeep ?_
    have hinv := relBall_inv D lam hsymm hmem
    rwa [mul_inv_rev, inv_inv] at hinv
  have hmain := sepSet_of_essentiallyPenetrates_of_lt_pivot D lam mu Dc hprev hq
    (by omega : p.length - (n + 1) < p.length - (m + 1))
    ⟨hcomprev, hdeeprev⟩ hpivrev hpivq hcospiv
  rw [hvrev (n + 1)] at hmain
  rw [mk_vertex_eq_of_isComp D f hp.1 hcomp]
  exact hmain

end OsinComponents
end GGT
end GroupApproximation
