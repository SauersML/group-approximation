import GroupApproximation.GGT.OsinSeparatingCosets

/-!
# Components of a path in `Γ(G, X ⊔ ℋ)`, and Osin's Lemma 4.2

The chain below `GGT.OsinEnlargement.SepDataStatement` is: construct the
separating cosets, which needs the order `⪯` of Osin's Lemma 4.8, which needs
*penetration* (his Definition 4.3), which needs *components* (his
Definition 4.1).  This module supplies the component vocabulary, once, against
the `RelLetter` / `AvoidsFrom` / `relBall` layer of
`GGT/WPDHyperbolicallyEmbedded.lean` --- which is already faithful to Osin's
Definition 2.8 and Dahmani--Guirardel--Osin's Definition 2.1, and is not
restated here.

## The definitions, from the source

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Definition 4.1:

> An `H_λ`-component `p` of `q` is called *isolated* in `q` if it is not
> connected to any other component of `q`.

A path is a word `w` read from a vertex `v`, so a component is an index at
which a maximal run of `λ`-letters begins (`IsCompStart`), and two components
are *connected* when their initial vertices lie in the same left coset of
`H λ` (`Connected`), which is the same thing as the two runs labelling edges of
one copy `gH_λ` of `Γ(H_λ, H_λ)`.

## What is proved

* `vertex_smul` --- the vertex map is `G`-equivariant.  Everything in Osin's §4
  is left-invariant, and this is the fact that makes it so; it is what will
  eventually give `SepData.sep_smul`.
* `Connected` is reflexive, symmetric and transitive (`connected_refl`,
  `connected_symm`, `connected_trans`) --- it is the restriction to component
  starts of the coset equivalence, so "connected to some other component" is a
  genuine equivalence class, and `isolated` means the class is a singleton.
* `not_isolated_of_connected` --- two distinct connected component starts are
  both non-isolated, which is the form the counting arguments use.

## The named input

`IsolatedComponentBound` is Osin's Lemma 4.2, which he introduces as *"a
simplified version of [16, Proposition 4.13]"* with `[16]` Dahmani--Guirardel--
Osin, i.e. their §4.2 "Isolated components in geodesic polygons":

> For every `μ ≥ 1` and `b ≥ 0` there is `C = C(μ,b) > 0` such that for any
> `n`-gon `p` with `(μ,b)`-quasi-geodesic sides in `Γ(G, X ⊔ ℋ)`, any `λ`, and
> any isolated `H_λ`-component `a` of `p`, we have `d̂_λ(a₋,a₊) ≤ Cn`.

It is the constant `C` in Osin's `D ≥ 3C`, hence the constant that defines his
`Y`.  This module does not prove it: it needs quasi-geodesic polygons in
`Γ(G, X ⊔ ℋ)`, which the repository does not have.  It is stated in the
one-component form the separating-coset construction consumes, with the polygon
hypothesis carried as an abstract predicate, so that a later module can supply
the polygon theory without this statement changing.

## A model test

Dahmani--Guirardel--Osin, Example 2.2(b): `G = H × ℤ` with `X = {x}` a
generator of the `ℤ` factor.  Then `Γ(G, X ⊔ H)` is quasi-isometric to a line,
so clauses (a) and (b) of `↪_h` hold, while `d̂(h₁,h₂) ≤ 3` for all
`h₁, h₂ ∈ H` --- the path `x, h₁⁻¹h₂, x⁻¹` avoids `Γ_H` --- so clause (c) fails
whenever `H` is infinite.  This is the example showing the three clauses are
independent rather than merely that (c) can fail, and any component vocabulary
should be checked against it before it is trusted.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Vertices of a path -/

/-- The vertex reached after reading the first `i` letters of `w` from `v`. -/
def vertex (v : G) : List (RelLetter G Λ) → ℕ → G
  | _, 0 => v
  | [], _ + 1 => v
  | a :: t, i + 1 => vertex (v * a.val) t i

@[simp] theorem vertex_zero (v : G) (w : List (RelLetter G Λ)) :
    vertex v w 0 = v := by
  cases w <;> rfl

@[simp] theorem vertex_nil (v : G) (i : ℕ) :
    vertex v ([] : List (RelLetter G Λ)) i = v := by
  cases i <;> rfl

@[simp] theorem vertex_cons_succ (v : G) (a : RelLetter G Λ)
    (t : List (RelLetter G Λ)) (i : ℕ) :
    vertex v (a :: t) (i + 1) = vertex (v * a.val) t i := rfl

/-- **The vertex map is `G`-equivariant.**  Left translation carries the path
read from `v` to the path read from `a * v`, so every notion defined from
vertices below is left-invariant. -/
theorem vertex_smul (a v : G) (w : List (RelLetter G Λ)) (i : ℕ) :
    vertex (a * v) w i = a * vertex v w i := by
  induction w generalizing v i with
  | nil => simp
  | cons b t ih =>
      cases i with
      | zero => simp
      | succ j =>
          rw [vertex_cons_succ, vertex_cons_succ, mul_assoc, ih]

/-! ## Components -/

/-- **`[i,k)` is an `H lam`-component of `w`**: a maximal run of `lam`-letters.
Every letter in the range is a `lam`-letter, the letter before `i` is not, and
the letter at `k` --- if there is one --- is not.  A component of a path is a
*run* of letters, not a single edge, which is why both endpoints are carried:
its endpoints in Osin's notation are `a₋ = vertex v w i` and
`a₊ = vertex v w k`. -/
def IsComp (lam : Λ) (w : List (RelLetter G Λ)) (i k : ℕ) : Prop :=
  i < k ∧ k ≤ w.length ∧
    (∀ (j : ℕ), i ≤ j → j < k → ∀ hj : j < w.length,
      (w[j]'hj).IsCompOf lam) ∧
    (∀ (j : ℕ), i = j + 1 → ∀ hj : j < w.length,
      ¬ (w[j]'hj).IsCompOf lam) ∧
    (∀ hk : k < w.length, ¬ (w[k]'hk).IsCompOf lam)

/-- **`i` starts an `H lam`-component of `w`.**  Components are indexed by
where they start, which is what makes `Connected` and `IsIsolated` below
statements about indices. -/
def IsCompStart (lam : Λ) (w : List (RelLetter G Λ)) (i : ℕ) : Prop :=
  ∃ k : ℕ, IsComp lam w i k

/-- **Two components are connected**: their initial vertices lie in the same
left coset of `H lam`, so the two runs label edges of one copy of
`Γ(H_lam, H_lam)`. -/
def Connected (H : Λ → Subgroup G) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (i j : ℕ) : Prop :=
  (vertex v w i)⁻¹ * vertex v w j ∈ H lam

theorem connected_refl (H : Λ → Subgroup G) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (i : ℕ) : Connected H lam v w i i := by
  show (vertex v w i)⁻¹ * vertex v w i ∈ H lam
  rw [inv_mul_cancel]
  exact one_mem _

theorem connected_symm {H : Λ → Subgroup G} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j : ℕ} (h : Connected H lam v w i j) :
    Connected H lam v w j i := by
  have h1 : ((vertex v w i)⁻¹ * vertex v w j)⁻¹ ∈ H lam := inv_mem h
  have h2 : ((vertex v w i)⁻¹ * vertex v w j)⁻¹
      = (vertex v w j)⁻¹ * vertex v w i := by group
  rw [h2] at h1
  exact h1

theorem connected_trans {H : Λ → Subgroup G} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j k : ℕ} (hij : Connected H lam v w i j)
    (hjk : Connected H lam v w j k) : Connected H lam v w i k := by
  have h1 : ((vertex v w i)⁻¹ * vertex v w j) *
      ((vertex v w j)⁻¹ * vertex v w k) ∈ H lam := mul_mem hij hjk
  have h2 : ((vertex v w i)⁻¹ * vertex v w j) *
        ((vertex v w j)⁻¹ * vertex v w k)
      = (vertex v w i)⁻¹ * vertex v w k := by group
  rw [h2] at h1
  exact h1

/-- **Connectedness is left-invariant**, because the vertex map is. -/
theorem connected_smul {H : Λ → Subgroup G} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j : ℕ} (a : G) :
    Connected H lam (a * v) w i j ↔ Connected H lam v w i j := by
  show (vertex (a * v) w i)⁻¹ * vertex (a * v) w j ∈ H lam ↔
    (vertex v w i)⁻¹ * vertex v w j ∈ H lam
  rw [vertex_smul, vertex_smul]
  have h : (a * vertex v w i)⁻¹ * (a * vertex v w j)
      = (vertex v w i)⁻¹ * vertex v w j := by group
  rw [h]

/-- **Osin's Definition 4.1.**  A component is isolated when it is connected to
no other component of the same path. -/
def IsIsolated (H : Λ → Subgroup G) (lam : Λ) (v : G)
    (w : List (RelLetter G Λ)) (i : ℕ) : Prop :=
  IsCompStart lam w i ∧
    ∀ j : ℕ, j ≠ i → IsCompStart lam w j → ¬ Connected H lam v w i j

/-- Two distinct connected components are both non-isolated.  This is the shape
the counting arguments use: isolatedness fails in pairs. -/
theorem not_isolated_of_connected {H : Λ → Subgroup G} {lam : Λ} {v : G}
    {w : List (RelLetter G Λ)} {i j : ℕ} (hne : i ≠ j)
    (hi : IsCompStart lam w i) (hj : IsCompStart lam w j)
    (hc : Connected H lam v w i j) :
    ¬ IsIsolated H lam v w i ∧ ¬ IsIsolated H lam v w j := by
  constructor
  · rintro ⟨-, hiso⟩
    exact hiso j (Ne.symm hne) hj hc
  · rintro ⟨-, hiso⟩
    exact hiso i hne hi (connected_symm hc)

/-! ## Osin's Lemma 4.2 -/

/-- **Osin, Lemma 4.2**, which he states as *"a simplified version of
[16, Proposition 4.13]"* with `[16]` Dahmani--Guirardel--Osin --- their §4.2,
"Isolated components in geodesic polygons":

> For every `μ ≥ 1` and `b ≥ 0` there is `C = C(μ,b) > 0` such that for any
> `n`-gon `p` with `(μ,b)`-quasi-geodesic sides in `Γ(G, X ⊔ ℋ)`, any `λ ∈ Λ`,
> and any isolated `H_λ`-component `a` of `p`, we have `d̂_λ(a₋,a₊) ≤ Cn`.

`IsQuasiGeodesicPolygon` is carried abstractly: this repository has no polygon
theory in `Γ(G, X ⊔ ℋ)`, and pinning the predicate down here would freeze a
definition before anything can be checked against it.  What the separating-coset
construction consumes is only the conclusion --- a bound on `d̂_λ` of an isolated
component in terms of the number of sides --- and that is what is stated.

The constant this proposition provides is the `C` in Osin's `D ≥ 3C`, hence the
constant defining `Y = {y | S(1,y;D) = ∅}`.  So it sits at the bottom of the
chain under `GGT.OsinEnlargement.SepDataStatement`. -/
def IsolatedComponentBound
    (IsQuasiGeodesicPolygon :
      ℝ → ℝ → ℕ → G → List (RelLetter G Λ) → Prop)
    (D : RelGenSet G Λ) : Prop :=
  ∀ μ b : ℝ, 1 ≤ μ → 0 ≤ b → ∃ C : ℕ, 0 < C ∧
    ∀ (n : ℕ) (v : G) (w : List (RelLetter G Λ)),
      IsQuasiGeodesicPolygon μ b n v w →
      ∀ (lam : Λ) (i k : ℕ), IsComp lam w i k →
        IsIsolated D.fam lam v w i →
          (vertex v w i)⁻¹ * vertex v w k ∈ D.relBall lam (C * n)

end OsinComponents
end GGT
end GroupApproximation
