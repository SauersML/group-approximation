import GroupApproximation.GGT.HullSCRelatorSeparation2ApplyIface

/-!
# The four-gon's quasi-geodesic clause, from its two long sides

The polygon clause `hqg` quantifies over all four sides of
`py ++ u ++ pz ++ revWord u'`, and the composition has to produce it.  Only two
of the four say anything: the long sides `u` and `u'` are pieces of the relator
and their clause is the block count.  The other two are the base spellings of
the separation's `y` and `z`, and for them the clause is arithmetic --- a side
shorter than the constant satisfies it with no geometry at all, since the
distance it is compared against is a natural number.

That is the whole of this module, and it is where the constant's size is
decided.  `bn` must be at least the length of each short side, so at least
`eps + 2` once the spellings are padded, which is why the block-count constant
`cnt` is chosen after `eps` and not before it.  The relative metric is what
forces this: a short element can lie in `H λ`, where its relative norm is `1`
while its base spelling has length `eps`, so no bound smaller than `|py|` can
serve.

The two long sides are read off their own clause by transport.  Side one is a
left translate of `u` by `listVal py`, and the word metric is left invariant.
Side three is `revWord u'`, whose vertices are those of `u'` in reverse order
and translated (`GGT.OsinComponents.vertex_revWord`), so its clause is `u'`'s
read backwards --- which is why the hypothesis is stated for every pair of
indices rather than for prefixes.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

section FourGonQG

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The quasi-geodesic clause, from the count in naturals.**  The clause is
stated over the reals with `mu = 1`; the count that produces it is a statement
about natural numbers, and this is the cast between them. -/
theorem qgClause_of_le {a d bn : ℕ} (h : a ≤ d + bn) :
    ((a : ℕ) : ℝ) / 1 - (bn : ℝ) ≤ ((d : ℕ) : ℝ) := by
  rw [div_one]
  have hcast : ((a : ℕ) : ℝ) ≤ ((d : ℕ) : ℝ) + (bn : ℝ) := by exact_mod_cast h
  linarith

/-- **The four-gon's quasi-geodesic clause from the two long sides.**

The two short sides are covered by their length: `bn` bounds them, and the
distance is a natural number, so the clause holds there with nothing said about
the geometry. -/
theorem fourGonQG_of_sides (D : GGT.RelGenSet G Λ)
    {py pz u u' : List (GGT.RelLetter G Λ)} {bn : ℕ}
    (hpylen : py.length ≤ bn) (hpzlen : pz.length ≤ bn)
    (hu : ∀ x y : ℕ, x ≤ y → y ≤ u.length →
      y - x ≤ wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u x)
        (GGT.OsinComponents.vertex (1 : G) u y) + bn)
    (hu' : ∀ x y : ℕ, x ≤ y → y ≤ u'.length →
      y - x ≤ wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex (1 : G) u' x)
        (GGT.OsinComponents.vertex (1 : G) u' y) + bn) :
    ∀ t : ℕ, t < 4 → ∀ z y : ℕ,
      GGT.OsinComponents.fourGonCut py u pz u' t ≤ z → z ≤ y →
      y ≤ GGT.OsinComponents.fourGonCut py u pz u' (t + 1) →
      ((y - z : ℕ) : ℝ) / 1 - (bn : ℝ)
        ≤ ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
            (GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) : ℕ) : ℝ) := by
  intro t ht z y hz hzy hy
  have key : y - z ≤ wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex (1 : G)
        (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') z)
      (GGT.OsinComponents.vertex (1 : G)
        (py ++ u ++ pz ++ GGT.OsinComponents.revWord u') y) + bn := by
    interval_cases t
    · have hy0 : y ≤ py.length := hy
      omega
    · have hz1 : py.length ≤ z := hz
      have hy1 : y ≤ py.length + u.length := hy
      obtain ⟨a, ha⟩ : ∃ a, z = py.length + a := ⟨z - py.length, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, y = py.length + b := ⟨y - py.length, by omega⟩
      subst ha
      subst hb
      have hbu : b ≤ u.length := by omega
      have hv : ∀ k : ℕ, k ≤ u.length →
          GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
              (py.length + k)
            = GGT.RelLetter.listVal py *
              GGT.OsinComponents.vertex (1 : G) u k := by
        intro k hk
        have h1 : py.length + k ≤ ((py ++ u) ++ pz).length := by
          rw [List.length_append, List.length_append]
          omega
        have h2 : py.length + k ≤ (py ++ u).length := by
          rw [List.length_append]
          omega
        rw [GGT.OsinComponents.vertex_append_of_le ((py ++ u) ++ pz)
            (GGT.OsinComponents.revWord u') 1 (py.length + k) h1,
          GGT.OsinComponents.vertex_append_of_le (py ++ u) pz 1
            (py.length + k) h2,
          GGT.OsinComponents.vertex_append_add py u 1 k, one_mul,
          GGT.OsinComponents.vertex_eq_mul_vertex_one u
            (GGT.RelLetter.listVal py) k]
      rw [hv a (by omega), hv b hbu,
        wordDist_left_invariant D.alphabet.carrier]
      have hab := hu a b (by omega) hbu
      omega
    · have hz2 : py.length + u.length ≤ z := hz
      have hy2 : y ≤ py.length + u.length + pz.length := hy
      omega
    · have hz3 : py.length + u.length + pz.length ≤ z := hz
      have hy3 : y ≤ py.length + u.length + pz.length + u'.length := hy
      obtain ⟨a, ha⟩ : ∃ a, z = py.length + u.length + pz.length + a :=
        ⟨z - (py.length + u.length + pz.length), by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, y = py.length + u.length + pz.length + b :=
        ⟨y - (py.length + u.length + pz.length), by omega⟩
      subst ha
      subst hb
      have hbu : b ≤ u'.length := by omega
      have hv : ∀ k : ℕ, k ≤ u'.length →
          GGT.OsinComponents.vertex (1 : G)
              (py ++ u ++ pz ++ GGT.OsinComponents.revWord u')
              (py.length + u.length + pz.length + k)
            = GGT.RelLetter.listVal ((py ++ u) ++ pz) *
              (GGT.RelLetter.listVal u')⁻¹ *
                GGT.OsinComponents.vertex (1 : G) u' (u'.length - k) := by
        intro k hk
        have hlen : ((py ++ u) ++ pz).length
            = py.length + u.length + pz.length := by
          rw [List.length_append, List.length_append]
        have hk' : u'.length - (u'.length - k) = k := by omega
        have hrev := GGT.OsinComponents.vertex_revWord u'
          (GGT.RelLetter.listVal ((py ++ u) ++ pz)) (u'.length - k)
        rw [hk'] at hrev
        rw [show py.length + u.length + pz.length + k
              = ((py ++ u) ++ pz).length + k from by rw [hlen],
          GGT.OsinComponents.vertex_append_add ((py ++ u) ++ pz)
            (GGT.OsinComponents.revWord u') 1 k, one_mul, hrev]
      rw [hv a (by omega), hv b hbu,
        wordDist_left_invariant D.alphabet.carrier,
        wordDist_comm D.alphabet.symmetricGenerating]
      have hab := hu' (u'.length - b) (u'.length - a) (by omega) (by omega)
      omega
  exact qgClause_of_le key

end FourGonQG

end HullSC
end GroupApproximation
