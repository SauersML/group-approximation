import GroupApproximation.GGT.OsinTheorem54SepReversal

/-!
# The block count against a second side, as an injection

The count of `GGT/HullSCRelatorSeparation2QuasiGeodesic.lean` --- item 2 of the
Ledger --- is three steps, and only one of them is geometric.  Written out at a
two-sided figure `u ++ revWord q`, with `u` the piece of the relator and `q` a
geodesic between its endpoints:

1. each component of `u` is connected to some OTHER component of the figure,
   because a deep component is not isolated;
2. the one it is connected to lies on the far side, because no two components
   of `u` are connected to each other;
3. distinct components of `u` reach distinct components of `q`, for the same
   reason, so their number is at most the number of components of `q`.

Steps 2 and 3 are this module, and they are unconditional: no relator, no
design, no geometry --- `GGT.OsinComponents.connected_trans` and a counting
argument over `Finset.card_le_card_of_injOn` are the whole content.  Step 1 is
the hypothesis `hother`, and it is where the debt sits.

## Why the target is the far side's COMPONENTS and not its letters

Because the chain can only consume `mu = 1`.  Counting one index at a time and
bounding each count by `|q|` gives `k_false + k_true ≤ 2|q|`, which is the
quasi-geodesic clause at `mu = 2`, and
`GGT/HullSCRelatorSeparation2ApplyQG.lean` and everything above it are stated
at `mu = 1`.  The two counts have to share the far side rather than each take
all of it, and they do: the injection lands on a `lam`-component start of `q`,
a position starts a component of at most one index
(`GGT.OsinComponents.not_isCompStart_of_ne`), so the two targets are disjoint
subsets of `|q|` positions and the two counts ADD to at most `|q|`.  That is
what `card_add_card_le_of_subset_range` is for, and it is why the target of the
injection is a `Finset` the caller supplies rather than `Finset.range q.length`.

## What this does NOT close

Both remaining inputs are stated here by name, so that neither can be lost:

* `hother`, step 1, is the isolated-component bound at the figure.  Every form
  of that bound in this development consumes `IsQuasiGeodesicPolygon`, which by
  its definition asks the (mu, b) lower bound of EVERY side --- one of which is
  the relator piece.  Discharging `hother` that way assumes what the count
  proves.
* `hsep`, the side separation, is asked at every pair of positions of `u`, so at
  index separations up to `|ms|`.  The design supplies it only inside a window
  `W` fixed before the exponent list
  (`HullSC.exists_separated_exponents_window`), and the geometric route
  `HullSC.index_close_of_connected` takes the quasi-geodesic clause as a
  hypothesis --- again what the count proves.

So this module is the socket and not the count.  It is written because its two
hypotheses are what any source for item 2 has to supply, whatever route that
source takes, and because the arithmetic between them and the count should not
have to be redone when it arrives.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u v

section CountBigon

variable {G : Type u} [Group G] {Λ : Type v}

/-- **A position starts a component of at most one index.**

The first letter of a component of index `lam` is a `lam`-letter, and a letter
carries one index: `RelLetter.IsCompOf` is `False` at a base letter and pins the
index at a component letter. -/
theorem not_isCompStart_of_ne {lam mu : Λ} (hne : lam ≠ mu)
    {w : List (RelLetter G Λ)} {y : ℕ} (hlam : IsCompStart lam w y) :
    ¬ IsCompStart mu w y := by
  intro hmu
  obtain ⟨k, hk⟩ := hlam
  obtain ⟨k', hk'⟩ := hmu
  have hyw : y < w.length := lt_of_lt_of_le hk.1 hk.2.1
  have h1 : (w[y]'hyw).IsCompOf lam := hk.2.2.1 y (le_refl y) hk.1 hyw
  have h2 : (w[y]'hyw).IsCompOf mu := hk'.2.2.1 y (le_refl y) hk'.1 hyw
  obtain ⟨a, ha⟩ : ∃ a : RelLetter G Λ, w[y]'hyw = a := ⟨_, rfl⟩
  rw [ha] at h1 h2
  cases a with
  | base g => simp only [RelLetter.IsCompOf] at h1
  | comp b g =>
      simp only [RelLetter.IsCompOf] at h1 h2
      exact hne (h1.symm.trans h2)

/-- **A component of the near side is connected to a component of the FAR
side.**

The component it is connected to is some other component of the figure; the
side separation excludes every position of `u`, and a component start lies
inside the figure, whose length is `|u| + |q|`. -/
theorem crossConnected_of_sideSeparated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (u q : List (RelLetter G Λ))
    (hsep : ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
      IsCompStart lam (u ++ revWord q) x →
      IsCompStart lam (u ++ revWord q) y →
      ¬ Connected D.fam lam v (u ++ revWord q) x y)
    {x y : ℕ} (hx : x < u.length)
    (hxc : IsCompStart lam (u ++ revWord q) x) (hne : y ≠ x)
    (hyc : IsCompStart lam (u ++ revWord q) y)
    (hcon : Connected D.fam lam v (u ++ revWord q) x y) :
    u.length ≤ y ∧ y < u.length + q.length := by
  have hlen : (u ++ revWord q).length = u.length + q.length := by
    rw [List.length_append, length_revWord]
  obtain ⟨k, hk⟩ := id hyc
  have hyk : y < k := hk.1
  have hkW : k ≤ (u ++ revWord q).length := hk.2.1
  refine ⟨?_, by omega⟩
  by_contra hlt
  exact hsep x hx y (by omega) (Ne.symm hne) hxc hyc hcon

/-- **Positions of the near side reaching a target set are at most as many as
the target.**

The assignment is injective because two positions reaching one position of the
far side are connected to each other, which the separation forbids. -/
theorem card_le_card_of_crossConnected (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (u q : List (RelLetter G Λ)) (S Q : Finset ℕ)
    (hcross : ∀ x ∈ S, ∃ y ∈ Q,
      Connected D.fam lam v (u ++ revWord q) x (u.length + y))
    (hsep : ∀ x ∈ S, ∀ z ∈ S, x ≠ z →
      ¬ Connected D.fam lam v (u ++ revWord q) x z) :
    S.card ≤ Q.card := by
  classical
  have hchoice : ∀ x : ℕ, ∃ y : ℕ, x ∈ S →
      y ∈ Q ∧ Connected D.fam lam v (u ++ revWord q) x (u.length + y) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨y, hyQ, hy⟩ := hcross x hx
      exact ⟨y, fun _ => ⟨hyQ, hy⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using hchoice
  have hmaps : Set.MapsTo f (↑S : Set ℕ) (↑Q : Set ℕ) := by
    intro x hx
    exact Finset.mem_coe.mpr (hf x (Finset.mem_coe.mp hx)).1
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro x hx z hz hfxz
    have hxS : x ∈ S := Finset.mem_coe.mp hx
    have hzS : z ∈ S := Finset.mem_coe.mp hz
    by_contra hne
    refine hsep x hxS z hzS hne ?_
    have hcx : Connected D.fam lam v (u ++ revWord q) x (u.length + f x) :=
      (hf x hxS).2
    have hcz : Connected D.fam lam v (u ++ revWord q) z (u.length + f z) :=
      (hf z hzS).2
    rw [← hfxz] at hcz
    exact connected_trans hcx (connected_symm hcz)
  exact Finset.card_le_card_of_injOn f hmaps hinj

/-- **The count, from non-isolation and the side separation.**

`hother` is step 1 --- each counted position is connected to another component
of the figure --- and it is the only thing here that is not bookkeeping.  `hQ`
says the target collects the far side's `lam`-components; taking it as a
parameter is what lets the two indices share `q`. -/
theorem card_le_card_of_sideSeparated (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (u q : List (RelLetter G Λ)) (S Q : Finset ℕ)
    (hSu : ∀ x ∈ S, x < u.length)
    (hSc : ∀ x ∈ S, IsCompStart lam (u ++ revWord q) x)
    (hother : ∀ x ∈ S, ∃ y : ℕ, y ≠ x ∧
      IsCompStart lam (u ++ revWord q) y ∧
      Connected D.fam lam v (u ++ revWord q) x y)
    (hsep : ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
      IsCompStart lam (u ++ revWord q) x →
      IsCompStart lam (u ++ revWord q) y →
      ¬ Connected D.fam lam v (u ++ revWord q) x y)
    (hQ : ∀ y : ℕ, y < q.length →
      IsCompStart lam (u ++ revWord q) (u.length + y) → y ∈ Q) :
    S.card ≤ Q.card := by
  refine card_le_card_of_crossConnected D lam v u q S Q ?_ ?_
  · intro x hx
    obtain ⟨y, hne, hyc, hcon⟩ := hother x hx
    obtain ⟨h1, h2⟩ := crossConnected_of_sideSeparated D lam v u q hsep
      (hSu x hx) (hSc x hx) hne hyc hcon
    have hy : y = u.length + (y - u.length) := by omega
    refine ⟨y - u.length, hQ (y - u.length) (by omega) ?_, ?_⟩
    · rw [← hy]
      exact hyc
    · rw [← hy]
      exact hcon
  · intro x hx z hz hne
    exact hsep x (hSu x hx) z (hSu z hz) hne (hSc x hx) (hSc z hz)

/-- **A deep component of the near side is connected to another component of
the figure.**

The isolated-component bound in CONTRAPOSITIVE, which is the only way this
argument ever uses it: an isolated component's span lies in
`relBall lam (C * n)`, the design's depth clause puts the span outside a ball at
least that big, so the component is not isolated --- and at a position already
known to start a component, that is exactly the witness `hother` asks for.

Nothing is ever proved isolated, so nothing has to be known about the far side.
A `lam`-letter of the far side whose vertex lands in the component's coset is
not an obstacle here; it is the conclusion. -/
theorem other_of_deep (D : RelGenSet G Λ) (lam : Λ) (v : G)
    {w : List (RelLetter G Λ)} {C n rho : ℕ}
    (hbound : ∀ i k : ℕ, IsComp lam w i k → IsIsolated D.fam lam v w i →
      (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (C * n))
    (hrho : C * n ≤ rho) {i k : ℕ} (hcomp : IsComp lam w i k)
    (hdeep : (vertex v w i)⁻¹ * vertex v w k ∉ D.relBall lam rho) :
    ∃ y : ℕ, y ≠ i ∧ IsCompStart lam w y ∧ Connected D.fam lam v w i y := by
  by_contra hno
  have hiso : IsIsolated D.fam lam v w i := by
    refine ⟨⟨k, hcomp⟩, ?_⟩
    intro j hji hcs hconn
    exact hno ⟨j, hji, hcs, hconn⟩
  exact hdeep (relBall_mono_radius D lam hrho (hbound i k hcomp hiso))

/-- **The count, from the bound and the depth clause.**

The join: `other_of_deep` at the two-sided figure discharges `hother`,
and `card_le_card_of_sideSeparated` does the rest.  `hScomp` is what the design
supplies --- each counted position starts a component whose span is deep --- and
`hbound` is the isolated-component bound at `n = 2`, the only geometric input
left in the count. -/
theorem card_le_card_of_deep (D : RelGenSet G Λ) (lam : Λ) (v : G)
    (u q : List (RelLetter G Λ)) (S Q : Finset ℕ) {C rho : ℕ}
    (hbound : ∀ i k : ℕ, IsComp lam (u ++ revWord q) i k →
      IsIsolated D.fam lam v (u ++ revWord q) i →
      (vertex v (u ++ revWord q) i)⁻¹ * vertex v (u ++ revWord q) k
        ∈ D.relBall lam (C * 2))
    (hrho : C * 2 ≤ rho)
    (hSu : ∀ x ∈ S, x < u.length)
    (hScomp : ∀ x ∈ S, ∃ k : ℕ, IsComp lam (u ++ revWord q) x k ∧
      (vertex v (u ++ revWord q) x)⁻¹ * vertex v (u ++ revWord q) k
        ∉ D.relBall lam rho)
    (hsep : ∀ x : ℕ, x < u.length → ∀ y : ℕ, y < u.length → x ≠ y →
      IsCompStart lam (u ++ revWord q) x →
      IsCompStart lam (u ++ revWord q) y →
      ¬ Connected D.fam lam v (u ++ revWord q) x y)
    (hQ : ∀ y : ℕ, y < q.length →
      IsCompStart lam (u ++ revWord q) (u.length + y) → y ∈ Q) :
    S.card ≤ Q.card := by
  refine card_le_card_of_sideSeparated D lam v u q S Q hSu ?_ ?_ hsep hQ
  · intro x hx
    obtain ⟨k, hcomp, -⟩ := hScomp x hx
    exact ⟨k, hcomp⟩
  · intro x hx
    obtain ⟨k, hcomp, hdeep⟩ := hScomp x hx
    exact other_of_deep D lam v hbound hrho hcomp hdeep

/-- **Two disjoint targets inside the far side leave `mu = 1` intact.**

The two indices' counts add to at most `|q|`, which is the arithmetic the
quasi-geodesic clause of this development is stated at. -/
theorem card_add_card_le_of_subset_range {n : ℕ} {Q₀ Q₁ : Finset ℕ}
    (h₀ : Q₀ ⊆ Finset.range n) (h₁ : Q₁ ⊆ Finset.range n)
    (hd : Disjoint Q₀ Q₁) : Q₀.card + Q₁.card ≤ n := by
  have hcard : (Q₀ ∪ Q₁).card = Q₀.card + Q₁.card :=
    Finset.card_union_of_disjoint hd
  have hle := Finset.card_le_card (Finset.union_subset h₀ h₁)
  rw [Finset.card_range, hcard] at hle
  exact hle

end CountBigon

end OsinComponents
end GGT
end GroupApproximation
