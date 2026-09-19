import GroupApproximation.GGT.OsinTheorem54SepLemma48
import GroupApproximation.GGT.OsinTheorem54SepGeodesicRuns

/-!
# Lemma 4.5 in the coordinates Lemma 4.9 uses it

Lemma 4.9 opens by fixing geodesics `r` from `f` to `h` and `q` from `h` to `g`
and saying that every coset of `S(f,g;D)` is penetrated by at least one of them.
That is Lemma 4.5, and this module restates it at a penetration INDEX of the
fixed geodesic `p` from `f` to `g`, which is the form the two splices consume.

Two conversions happen here, once, so that the counting argument never has to
do them.

* On the `r` side the index is the same, by Lemma 4.6: `p` and `r` leave the
  same point, so they enter the coset after the same number of letters
  (`penetratesAt_index_eq`).  The disjunct therefore names the component of `r`
  at `n` itself, not at some index of its own.
* On the `q` side there is no common origin --- `q` runs from `h` --- so the
  disjunct is stated for `revWord q`, which runs from `g`, the point the second
  splice leaves from.  `isComp_revWord` moves the component and
  `mk_vertex_revWord_eq` says the reversed path names the same coset.

Both disjuncts are also stated with the component's end at `n + 1`: on a
geodesic a component is a single letter (`isComp_eq_succ_of_isGeodesicWord`),
so nothing is lost and the splices get the shape they want.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin's Lemma 4.5, at an index of `p`.**  The coset `p` penetrates at `n`
is penetrated by `r` --- at the same index --- or by `q` read backwards from
`g`. -/
theorem pivot_dichotomy (D : RelGenSet G Λ) (lam : Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {C Dc : ℕ}
    (hbnd : ∀ (n : ℕ), n ≤ 6 → ∀ (v : G) (u : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon D 1 0 n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu (C * n))
    (hDc : C * 4 ≤ Dc) {f g h : G} {p r q : List (RelLetter G Λ)}
    (hp : IsGeodesicWord D f g p) (hr : IsGeodesicWord D f h r)
    (hq : IsGeodesicWord D h g q) {n : ℕ} (hcomp : IsComp lam p n (n + 1))
    (hc : (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
      ∈ sepSet D lam Dc f g) :
    (IsComp lam r n (n + 1) ∧ (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
        = QuotientGroup.mk (vertex f r n))
      ∨ (∃ j : ℕ, IsComp lam (revWord q) j (j + 1) ∧
        (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)
          = QuotientGroup.mk (vertex g (revWord q) j)) := by
  rcases penetrates_of_mem_sepSet D lam hsymm hbnd hDc hr hq hc with
    ⟨a, b, hab, hmk⟩ | ⟨a, b, hab, hmk⟩
  · left
    have hb : b = a + 1 := isComp_eq_succ_of_isGeodesicWord D lam hr hab
    subst hb
    have hidx : n = a :=
      penetratesAt_index_eq D lam
        (c := (QuotientGroup.mk (vertex f p n) : G ⧸ D.fam lam)) (Dc := Dc)
        hp hr ⟨⟨n + 1, hcomp⟩, rfl⟩ ⟨⟨a + 1, hab⟩, hmk.symm⟩
    subst hidx
    exact ⟨hab, hmk.symm⟩
  · right
    have hb : b = a + 1 := isComp_eq_succ_of_isGeodesicWord D lam hq hab
    subst hb
    have hql : a + 1 ≤ q.length := hab.2.1
    refine ⟨q.length - (a + 1), ?_, ?_⟩
    · have hidx : q.length - a = q.length - (a + 1) + 1 := by omega
      rw [← hidx]
      exact isComp_revWord lam q hab
    · have hkey := mk_vertex_revWord_eq D lam h hq.1 hab
      rw [hq.2.1] at hkey
      exact hmk.symm.trans hkey.symm

end OsinComponents
end GGT
end GroupApproximation
