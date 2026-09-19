import GroupApproximation.GGT.DGOPolygonBaseCaseTower
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# The isolated-component bound at a general `μ`, and why Morse does not reduce
it to `μ = 1`

`GGT/DGOPolygonBaseCaseTower.lean` proves the isolated-component bound at
`μ = 1` for polygons of at most six sides, from a symmetric base and four-point
hyperbolicity alone.  Ledger item 2 (`hcount`) needs the same bound at `μ = 4`,
because Dahmani--Guirardel--Osin's Lemma 4.21(1) delivers `(4,1)` and no
consumer takes a multiplicative defect.  `IsolatedComponentBoundAt` below is
that statement with `μ` freed; `isolatedComponentBoundAt_one` discharges its
`μ = 1` instance from the tower at statement time.

## The reduction that does not work, and it fails at every `μ`

The tower's own docstring points at the route: "A base case at general `μ` ---
Dahmani--Guirardel--Osin's Lemma 4.15, quasi-geodesic stability at
`θ = ϰ(μ,b) + 2δ`, inside their 4.16 --- instantiates the same binder and gives
the same conclusion at `(μ,b)`".  Quasi-geodesic stability *is* available here:
`GGT.Hyperbolic.morseLemma` discharges `Hyperbolic.MorseLemma` unconditionally.
So the obvious reduction is to Morse the `(μ,b)` sides onto geodesics, apply the
`μ = 1` bound to the resulting figure, and absorb the displacement.

**That reduction is refuted, and not by a corner case.**
`DGOIsolatedComponentBoundFourGon.span_mem_relBall_of_sideZero` carries the
component as **side 0** and asks its quasi-geodesic clause only of the other
sides, so a Morse replacement would leave the component's own letters alone ---
which is what makes the reduction look clean.  The obstruction is elsewhere, in
`IsIsolated`, which is a condition on the **whole** word:

* the component's span `(vertex v w i)⁻¹ * vertex v w k` lies in `H lam`
  (`OsinComponents.span_mem_fam_of_isComp`);
* every element of every `H lam` is a **letter**, since
  `RelGenSet.alphabet` is `X ∪ ⋃ lam, H lam`;
* so the component's two endpoints are at `wordDist ≤ 1` in `Γ(G, X ⊔ ℋ)`
  (`wordDist_component_le_one` below).

The complementary arc runs from `vertex v w k` back to `vertex v w i`, between
those same two vertices.  Replacing it by a geodesic therefore replaces it by a
path of length at most one: a **single `lam`-letter**, whose start vertex lies in
the same `H lam`-coset as the component's.  That letter starts a `lam`-component
`Connected` to the original one, so `IsIsolated D.fam lam v w' i` **fails** for
the replaced word `w'`, and the `μ = 1` theorem does not apply to it.

Nothing in that argument mentions `μ`.  The reduction would fail at `μ = 1` too,
which is exactly why the `μ = 1` case is proved directly, by the thinness
argument on the given polygon, rather than by geodesic-ising anything.  Coning
off makes the peripheral cosets have diameter one, so a geodesic *prefers* the
very coset the component lives in; the figure collapses onto the component's own
edge and takes the isolation hypothesis with it.

## What this leaves

The general-`μ` base case has to be proved the way Dahmani--Guirardel--Osin
prove 4.16: rerun the thinness argument with the `(μ,b)` constants in place,
with 4.15 used *inside* it to bound how far a quasi-geodesic side strays, and
never as a replacement of one figure by another.  `morseLemma_univ` is still the
right ingredient; what is wrong is the shape of its use.

The two facts below are stated because they are the whole of the obstruction,
and because a later attempt at this reduction should trip over them rather than
rediscover them.  The refutation is not itself formalised as "replacement
destroys isolation": that would need the replacement construction written down,
which is a large object to build in order to record a negative.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## 1.  The target -/

/-- **The isolated-component bound at `(μ, b)` for `n`-gons.**

`∃ C` sits outside the polygon quantifiers, so the radius is uniform in the
figure --- which is what every consumer spends.  `μ` is a real because
`IsQuasiGeodesicPolygon` takes it there; `b` and `n` are naturals because the
chain's own pair is `(1, ((|p| + c : ℕ) : ℝ))` and the tower is stated at a
natural `b`. -/
def IsolatedComponentBoundAt (D : RelGenSet G Λ) (mu : ℝ) (b n : ℕ) : Prop :=
  ∃ C : ℕ, ∀ (v : G) (u : List (RelLetter G Λ)),
    IsQuasiGeodesicPolygon D mu (b : ℝ) n v u →
      ∀ (nu : Λ) (i k : ℕ), IsComp nu u i k → IsIsolated D.fam nu v u i →
        (vertex v u i)⁻¹ * vertex v u k ∈ D.relBall nu C

/-- **The `μ = 1` instance, discharged.**  The tower proves exactly this, at
`C = 15 · (25 · (δ + b + 1)) · n`, from a symmetric base and four-point
hyperbolicity. -/
theorem isolatedComponentBoundAt_one (D : RelGenSet G Λ)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ} (b n : ℕ) (hn : n ≤ 6)
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    IsolatedComponentBoundAt D 1 b n :=
  ⟨15 * (25 * (δ + b + 1)) * n,
    isolatedComponentBound_of_fourPointHyperbolic_at D hsymm b hδ n hn⟩

/-! ## 2.  The obstruction -/

/-- **Every element of every peripheral subgroup is a letter.**  This is the
whole content of coning off, and it is what makes the obstruction generic. -/
theorem mem_alphabet_of_mem_fam (D : RelGenSet G Λ) (lam : Λ) {g : G}
    (h : g ∈ D.fam lam) : g ∈ D.alphabet.carrier := by
  show g ∈ D.base ∪ ⋃ mu : Λ, (D.fam mu : Set G)
  exact Or.inr (Set.mem_iUnion.mpr ⟨lam, h⟩)

/-- **A component's endpoints are adjacent in `Γ(G, X ⊔ ℋ)`.**

This is the fact that refutes the Morse reduction: the complementary arc joins
these two vertices, so any geodesic replacing it has length at most one and is a
single `lam`-letter in the component's own coset. -/
theorem wordDist_component_le_one (D : RelGenSet G Λ) {lam : Λ} (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) :
    wordDist D.alphabet.carrier (vertex v w i) (vertex v w k) ≤ 1 :=
  wordDist_le_one_of_mem_fam D (span_mem_fam_of_isComp D v hlet hcomp)

/-- **A component's endpoints are `Connected`.**  The second half of the
obstruction: the replacement letter starts at `vertex v w k`, which lies in the
same `H lam`-coset as `vertex v w i`, so it starts a component connected to the
original and `IsIsolated` fails for the replaced word. -/
theorem connected_endpoints_of_isComp (D : RelGenSet G Λ) {lam : Λ} (v : G)
    {w : List (RelLetter G Λ)} (hlet : ∀ a ∈ w, D.IsLetter a) {i k : ℕ}
    (hcomp : IsComp lam w i k) : Connected D.fam lam v w i k :=
  span_mem_fam_of_isComp D v hlet hcomp

end OsinComponents
end GGT
end GroupApproximation
