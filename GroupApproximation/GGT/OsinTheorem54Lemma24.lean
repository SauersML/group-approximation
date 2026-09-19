import GroupApproximation.GGT.OsinSeparatingCosets

/-!
# Osin's Lemma 2.4 at a Cayley graph, proved

`GGT/OsinSeparatingCosets.lean` reduces Osin's Theorem 5.4 to two inputs:
`SepDataStatement`, the separating-coset construction of *Acylindrically
hyperbolic groups* §4--§5, and `OsinLemma24`, the passage from a bound at pairs
at *one* distance to acylindricity.  This module discharges the second one, and
records why it had to be restated before it could be discharged.

## `OsinLemma24` as written is not Osin's Lemma 2.4

Osin's Lemma 2.4 is stated for a hyperbolic space in the sense of his §2, where
--- as throughout that literature --- hyperbolic spaces are geodesic.
`OsinLemma24` quantifies over an arbitrary `PseudoMetricSpace` instead, and with
geodesicity dropped the statement proves far too much.  Its hypothesis asks for
*some* `R > 0` at which the two-point count is bounded, and on a space whose
distance function never takes the value `R` that hypothesis is vacuously true.
A Cayley graph has an integer-valued vertex metric, so `R = 1/2` is such a value
for every alphabet at once, and `isAcylindrical_of_osinLemma24` is the
consequence: `OsinLemma24` would make **every** isometric action on a hyperbolic
Cayley graph acylindrical.

`osinTheorem54_of_osinLemma24` is what that costs.  Theorem 5.4 would hold with
`Y = X`, its own hypothesis supplying clause (b) --- and the enlargement of `X`
to `Y` is not a convenience but a necessity, by the counterexample Osin gives
immediately before Theorem 5.4 and quotes in the docstring of `OsinTheorem54`:
for `G = (K × ℤ) * H` with `K` infinite and `H` nontrivial and `X = K ∪ {x}`,
one has `H ↪_h (G,X)` while the action on `Γ(G, X ⊔ H)` is not acylindrical.
So `OsinLemma24` is false, and no lane should spend effort on it.

The failure is exactly the missing geodesic: on a geodesic space every value in
`[0, diam]` is a distance, so the vacuous reading is unavailable, and Osin's
proof --- take a point of `[x,z]` at distance `R` from `x` --- is available.

## What replaces it

`isAcylindrical_cayley_of_exactCore` is Lemma 2.4 in the form the chain uses it,
at a Cayley graph, unconditionally.  Its hypothesis is `SepData.AcylindricalCore`
verbatim: for each `m` a radius `R` and a bound `N` such that at most `N`
elements `k` have `|k|_A ≤ m` and `|z⁻¹kz|_A ≤ m`, for every `z` with `|z|_A = R`
exactly.

The proof is Osin's, with the discrete geodesic of a Cayley graph in place of a
geodesic segment.  Two steps:

* `exists_geodesic_vertex` --- a geodesic word for `z` of length `|z|_A ≥ R`
  splits at position `R`, and its prefix `p` satisfies `|p|_A = R` and
  `|p|_A + |p⁻¹z|_A = |z|_A`; that is, `p` is a vertex *on* a geodesic from `1`
  to `z`, at distance exactly `R` from `1`.
* `dist_smul_le_of_gromovProduct_eq_zero` --- **the whole geometric content**:
  if `(x|y)_w = 0` and `k` moves both `x` and `y` by at most `ε`, then `k` moves
  `w` by at most `ε + 2δ`.  One application of the four-point condition to
  `(x, k·w, y)` based at `w` makes one of `(x|k·w)_w`, `(k·w|y)_w` at most `δ`,
  and either one bounds `d(w, k·w)` by a triangle inequality that cancels
  `d(x,w)` or `d(y,w)` against itself.  No geodesic and no stability theorem is
  used, only the four-point condition.

With `dist_smul_le_of_gromovProduct_eq_zero` at `w = p`, the set the conclusion
counts is contained in the set the hypothesis counts at `p`, and
`OsinEnlargement.isAcylindrical_cayley_of_basepoint` removes the quantifier over
the first vertex.

`osinTheorem54_of_sepDataStatement` is then Theorem 5.4 from `SepDataStatement`
alone.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The geometric step -/

section Displacement

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **Displacement at an interior point of a geodesic.**

If `(x|y)_w = 0` --- so that `w` lies on a geodesic from `x` to `y`, in the
coarse sense that `d(x,w) + d(w,y) = d(x,y)` --- and `k` moves both `x` and `y`
by at most `ε`, then `k` moves `w` by at most `ε + 2δ`.

The four-point condition at `w` applied to `x`, `k·w`, `y` gives
`min ((x|k·w)_w) ((k·w|y)_w) ≤ (x|y)_w + δ = δ`.  In the first case
`d(x,w) + d(w,k·w) - d(x,k·w) ≤ 2δ` while
`d(x,k·w) ≤ d(x,k·x) + d(k·x,k·w) = d(x,k·x) + d(x,w)`, and `d(x,w)` cancels;
the second case is the same computation at `y`.

This is the step Osin's Lemma 2.4 takes with a geodesic segment.  Nothing here
needs a geodesic: only a point at which the Gromov product of the two endpoints
vanishes, and a Cayley graph has one at every integer distance. -/
theorem dist_smul_le_of_gromovProduct_eq_zero {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X) {x y w : X}
    (hw : gromovProduct x y w = 0) {k : G} {ε : ℝ}
    (hx : dist x (k • x) ≤ ε) (hy : dist y (k • y) ≤ ε) :
    dist w (k • w) ≤ ε + 2 * δ := by
  have h4 := hδ w x (k • w) y
  rw [hw] at h4
  have hmin : min (gromovProduct x (k • w) w) (gromovProduct (k • w) y w) ≤ δ := by
    linarith
  have hcomm : dist w (k • w) = dist (k • w) w := dist_comm w (k • w)
  rcases min_le_iff.mp hmin with h | h
  · unfold gromovProduct at h
    have h1 : dist x (k • w) ≤ dist x (k • x) + dist (k • x) (k • w) :=
      dist_triangle x (k • x) (k • w)
    have h2 : dist (k • x) (k • w) = dist x w := hiso k x w
    rw [h2] at h1
    rw [hcomm]
    linarith
  · unfold gromovProduct at h
    have h1 : dist (k • w) y ≤ dist (k • w) (k • y) + dist (k • y) y :=
      dist_triangle (k • w) (k • y) y
    have h2 : dist (k • w) (k • y) = dist w y := hiso k w y
    have h3 : dist (k • y) y = dist y (k • y) := dist_comm (k • y) y
    have h4' : dist y w = dist w y := dist_comm y w
    rw [h2, h3] at h1
    rw [hcomm]
    linarith

end Displacement

/-! ## A vertex at a prescribed distance along a geodesic -/

section Prefix

variable {G : Type u} [Group G]

/-- **The prefix of a geodesic word.**  A word of length `|z|_A` spelling `z`
splits at position `R ≤ |z|_A` into a prefix spelling `p` and a suffix spelling
`p⁻¹z`.  The prefix has at most `R` letters and the suffix at most `|z|_A - R`,
while the two lengths add to at least `|z|_A`, so both bounds are equalities.

In `Γ(G,A)` this says `p` is a vertex on a geodesic from `1` to `z` at distance
exactly `R` from `1`, which is what makes the Gromov product `(1|z)_p` vanish. -/
theorem exists_geodesic_vertex (A : Alphabet G) {z : G} {R : ℕ}
    (hR : R ≤ wordNorm A.carrier z) :
    ∃ p : G, wordNorm A.carrier p = R ∧
      wordNorm A.carrier p + wordNorm A.carrier (p⁻¹ * z)
        = wordNorm A.carrier z := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq A.symmetricGenerating z
  have hRlen : R ≤ l.length := by rw [hlen]; exact hR
  have hsplit : l.take R ++ l.drop R = l := List.take_append_drop R l
  have hlensum : (l.take R).length + (l.drop R).length = l.length := by
    have h := congrArg List.length hsplit
    rwa [List.length_append] at h
  have hlt : (l.take R).length = R := by
    rw [List.length_take]
    omega
  have hwordp : IsWord A.carrier (l.take R) (l.take R).prod :=
    ⟨fun x hx => hl.letters x (List.take_subset R l hx), rfl⟩
  have hwordq : IsWord A.carrier (l.drop R) (l.drop R).prod :=
    ⟨fun x hx => hl.letters x (List.drop_subset R l hx), rfl⟩
  have hprod : (l.take R).prod * (l.drop R).prod = z := by
    rw [← List.prod_append, hsplit, hl.prod_eq]
  have hinv : ((l.take R).prod)⁻¹ * z = (l.drop R).prod := by
    rw [← hprod]
    group
  have hple : wordNorm A.carrier (l.take R).prod ≤ (l.take R).length :=
    wordNorm_le_length hwordp
  have hqle : wordNorm A.carrier (l.drop R).prod ≤ (l.drop R).length :=
    wordNorm_le_length hwordq
  have hsub : wordNorm A.carrier z
      ≤ wordNorm A.carrier (l.take R).prod
        + wordNorm A.carrier (l.drop R).prod := by
    rw [← hprod]
    exact wordNorm_mul_le A.symmetricGenerating _ _
  refine ⟨(l.take R).prod, by omega, ?_⟩
  rw [hinv]
  omega

end Prefix

/-! ## Osin's Lemma 2.4, at a Cayley graph -/

section Lemma24

variable {G : Type u} [Group G]

/-- **Osin, Lemma 2.4, in the direction the chain uses it, proved.**

> The action of a group `G` on a hyperbolic space `S` is acylindrical if and
> only if for every `ε > 0` there exist `R, N > 0` such that for every two
> points `x, z` satisfying `d(x,z) = R`, we have
> `♯{g ∈ G | max{d(x,gx), d(z,gz)} ≤ ε} ≤ N`.

Stated at `Γ(G,A)` and in the word metric, which is where the separating-coset
argument delivers it, and with the exact-distance condition at integer radius
--- `SepData.AcylindricalCore` verbatim.

Given `ε`, take the bound of the hypothesis at `m = ⌈ε⌉ + ⌈ε + 2δ⌉` and the
radius `R` it returns.  For `z` with `|z|_A ≥ R`, `exists_geodesic_vertex` gives
a vertex `p` with `|p|_A = R` and `(1|z)_p = 0`, and
`dist_smul_le_of_gromovProduct_eq_zero` moves every `k` that displaces `1` and
`z` by at most `ε` into the set the hypothesis counts at `p`.  The quantifier
over the first vertex is removed by `isAcylindrical_cayley_of_basepoint`. -/
theorem isAcylindrical_cayley_of_exactCore (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A))
    (hcore : ∀ m : ℕ, ∃ R N : ℕ, 0 < R ∧ ∀ z : G,
      wordDist A.carrier 1 z = R →
        {k : G | wordDist A.carrier 1 k ≤ m ∧
            wordDist A.carrier 1 (z⁻¹ * k * z) ≤ m}.Finite ∧
          {k : G | wordDist A.carrier 1 k ≤ m ∧
            wordDist A.carrier 1 (z⁻¹ * k * z) ≤ m}.ncard ≤ N) :
    IsAcylindrical G (Cayley A) := by
  refine isAcylindrical_cayley_of_basepoint A ?_
  intro ε _
  obtain ⟨R, N, -, hRN⟩ := hcore (⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊)
  refine ⟨(R : ℝ), N, ?_⟩
  intro z hz
  -- the two ceiling bounds
  have hceil1 : ε ≤ ((⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊ : ℕ) : ℝ) := by
    have h1 : ε ≤ (⌈ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) ≤ ((⌈ε + 2 * δ⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  have hceil2 : ε + 2 * δ ≤ ((⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊ : ℕ) : ℝ) := by
    have h1 : ε + 2 * δ ≤ (⌈ε + 2 * δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (0 : ℝ) ≤ ((⌈ε⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    linarith
  -- the vertex on a geodesic at distance exactly `R` from the basepoint
  have hRz : R ≤ wordDist A.carrier 1 z := by exact_mod_cast hz
  rw [wordDist_one_left] at hRz
  obtain ⟨p, hpR, hpsum⟩ := exists_geodesic_vertex A hRz
  have hpdist : wordDist A.carrier 1 p = R := by
    rw [wordDist_one_left]
    exact hpR
  obtain ⟨hfin, hcard⟩ := hRN p hpdist
  -- the three distances at the three vertices
  have hxW : dist (Cayley.base A) (Cayley.of A p)
      = ((wordNorm A.carrier p : ℕ) : ℝ) := by
    have h := dist_val A (Cayley.base A) (Cayley.of A p)
    simp only [Cayley.val_base, Cayley.val_of, inv_one, one_mul,
      wordDist_one_left] at h
    exact h
  have hWy : dist (Cayley.of A p) (Cayley.of A z)
      = ((wordNorm A.carrier (p⁻¹ * z) : ℕ) : ℝ) := by
    have h := dist_val A (Cayley.of A p) (Cayley.of A z)
    simp only [Cayley.val_of, wordDist_one_left] at h
    exact h
  have hxy : dist (Cayley.base A) (Cayley.of A z)
      = ((wordNorm A.carrier z : ℕ) : ℝ) := by
    have h := dist_val A (Cayley.base A) (Cayley.of A z)
    simp only [Cayley.val_base, Cayley.val_of, inv_one, one_mul,
      wordDist_one_left] at h
    exact h
  have hcast : ((wordNorm A.carrier p : ℕ) : ℝ)
      + ((wordNorm A.carrier (p⁻¹ * z) : ℕ) : ℝ)
      = ((wordNorm A.carrier z : ℕ) : ℝ) := by exact_mod_cast hpsum
  have hgp : gromovProduct (Cayley.base A) (Cayley.of A z) (Cayley.of A p)
      = 0 := by
    unfold gromovProduct
    rw [hxW, hxy, dist_comm (Cayley.of A z) (Cayley.of A p), hWy]
    linarith
  -- the inclusion of the two counted sets
  have hsub : {k : G | ((wordDist A.carrier 1 k : ℕ) : ℝ) ≤ ε ∧
        ((wordDist A.carrier 1 (z⁻¹ * k * z) : ℕ) : ℝ) ≤ ε}
      ⊆ {k : G | wordDist A.carrier 1 k ≤ ⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊ ∧
        wordDist A.carrier 1 (p⁻¹ * k * p) ≤ ⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊} := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨?_, ?_⟩
    · have : ((wordDist A.carrier 1 k : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊ : ℕ) : ℝ) := le_trans hk1 hceil1
      exact_mod_cast this
    · have hk1' : dist (Cayley.base A) (k • Cayley.base A) ≤ ε := by
        have h := dist_smul_val A (Cayley.base A) k
        simp only [Cayley.val_base, inv_one, one_mul, mul_one] at h
        rw [h]
        exact hk1
      have hk2' : dist (Cayley.of A z) (k • Cayley.of A z) ≤ ε := by
        have h := dist_smul_val A (Cayley.of A z) k
        simp only [Cayley.val_of] at h
        rw [h]
        exact hk2
      have hdisp : dist (Cayley.of A p) (k • Cayley.of A p) ≤ ε + 2 * δ :=
        dist_smul_le_of_gromovProduct_eq_zero hδ (isIsometricAction_cayley A)
          hgp hk1' hk2'
      have hval := dist_smul_val A (Cayley.of A p) k
      simp only [Cayley.val_of] at hval
      rw [hval] at hdisp
      have : ((wordDist A.carrier 1 (p⁻¹ * k * p) : ℕ) : ℝ)
          ≤ ((⌈ε⌉₊ + ⌈ε + 2 * δ⌉₊ : ℕ) : ℝ) := le_trans hdisp hceil2
      exact_mod_cast this
  exact ⟨hfin.subset hsub, le_trans (Set.ncard_le_ncard hsub hfin) hcard⟩

end Lemma24

/-! ## Theorem 5.4 from the separating-coset data alone -/

section Assembly

variable {G : Type u} [Group G]

/-- **Clause (b) of Theorem 5.4 from the residue, with no citation.**  The
replacement for `SepData.isAcylindrical_of_core`, which routes through
`OsinLemma24`. -/
theorem SepData.isAcylindrical_of_core' {D : RelGenSet G Unit} (S : SepData D)
    (hcore : S.AcylindricalCore) :
    IsAcylindrical G (Cayley S.enlarged.alphabet) := by
  obtain ⟨δ, hδ⟩ := S.emb.hyperbolic
  exact isAcylindrical_cayley_of_exactCore S.enlarged.alphabet hδ hcore

end Assembly

/-- **Osin's Theorem 5.4 from `SepDataStatement` alone.**  The separating-coset
data supplies `Y`, clause (a) through its `emb` field, and clause (b) through
`SepData.isAcylindrical_of_core'`.  `OsinLemma24` does not appear. -/
theorem osinTheorem54_of_sepDataStatement (h : SepDataStatement.{u}) :
    OsinTheorem54.{u} := by
  intro G _inst D hD
  obtain ⟨S, hcore⟩ := h G D hD
  exact ⟨S.enlarged, S.base_subset, S.fam_eq, S.emb,
    S.isAcylindrical_of_core' hcore⟩

/-! ## Why `OsinLemma24` had to be replaced rather than proved -/

section Refutation

variable {G : Type u} [Group G]

/-- **`OsinLemma24` makes every isometric action on a hyperbolic Cayley graph
acylindrical.**

Its hypothesis asks for one radius `R > 0` at which the two-point count is
bounded.  The vertex metric of `Γ(G,A)` is integer-valued, so no pair of
vertices is at distance `1/2`, and the hypothesis holds at `R = 1/2` with `N = 0`
for every `ε` at once.

On a geodesic space, which is what Osin's Lemma 2.4 is stated for, every value
below the diameter is a distance and this reading is unavailable.  Dropping
geodesicity is what makes the transcription false. -/
theorem isAcylindrical_of_osinLemma24 (h24 : OsinLemma24.{u}) (A : Alphabet G)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A)) :
    IsAcylindrical G (Cayley A) := by
  refine h24 G (Cayley A) δ hδ (isIsometricAction_cayley A) ?_
  intro ε _
  refine ⟨1 / 2, 0, by norm_num, ?_⟩
  intro x z hxz
  exfalso
  rw [Cayley.dist_eq] at hxz
  rcases Nat.eq_zero_or_pos
      (wordDist A.carrier (Cayley.val x) (Cayley.val z)) with h0 | h0
  · rw [h0] at hxz
    norm_num at hxz
  · have h0' : 1 ≤ wordDist A.carrier (Cayley.val x) (Cayley.val z) := h0
    have h1 : (1 : ℝ)
        ≤ ((wordDist A.carrier (Cayley.val x) (Cayley.val z) : ℕ) : ℝ) := by
      exact_mod_cast h0'
    rw [hxz] at h1
    norm_num at h1

end Refutation

/-- **What `OsinLemma24` would cost.**  Theorem 5.4 would hold with `Y = X`: its
own hypothesis carries the hyperbolicity of `Γ(G, X ⊔ ℋ)`, and
`isAcylindrical_of_osinLemma24` would then carry clause (b).

The enlargement of `X` to `Y` is not a convenience.  Osin gives the
counterexample immediately before Theorem 5.4 --- `G = (K × ℤ) * H` with `K`
infinite and `H` nontrivial, `X = K ∪ {x}` --- and it is quoted in the docstring
of `OsinTheorem54`.  So `OsinLemma24` is false, and the reduction it appears in
is not a route to Theorem 5.4;
`osinTheorem54_of_sepDataStatement` is. -/
theorem osinTheorem54_of_osinLemma24 (h24 : OsinLemma24.{u}) :
    OsinTheorem54.{u} := by
  intro G _inst D hD
  obtain ⟨δ, hδ⟩ := hD.hyperbolic
  exact ⟨D, subset_rfl, rfl, hD, isAcylindrical_of_osinLemma24 h24 D.alphabet hδ⟩

end OsinEnlargement
end GGT
end GroupApproximation
