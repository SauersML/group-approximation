import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-disjoint supports give a commutator witness, part 1: upstream interfaces

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex, so there is no tex line).  Infrastructure lane `sk-flip-07`.

The witness theorem of `InfraNonDisjWit` uses three results authored by parallel lanes that are
not yet on disk.  They are stated here as `Statement`s whose shapes are exactly the lane
signatures, so that each is discharged by `fun X .. => <lane theorem> ..` once it lands.

* `NonDisjWitDisplacedStatement` (lane `sk-flip-01`, `exists_isClopen_displaced_common`): a point
  moved by `f` and by `k` has a clopen neighbourhood `W` with `W ∩ f W = ∅` and `W ∩ k W = ∅`.
  TRUE: separate `x` from `f x` and from `k x` by open sets (Hausdorff), intersect the
  neighbourhood of `x` with the `f`- and `k`-preimages of the neighbourhoods of `f x`, `k x`, and
  shrink to a clopen set (clopen basis of a compact Hausdorff totally disconnected space).
* `NonDisjWitCommLocalStatement` (lane `sk-flip-02`, `commutator_commutator_eq_of_displaced`): if
  `a, b` are supported in `W` and `W ∩ g W = ∅` then `⁅⁅a, g⁆, b⁆ = ⁅a, b⁆`.
  TRUE: `⁅a, g⁆ = a * c` with `c = g a⁻¹ g⁻¹` supported in `g W`; homeomorphisms supported in
  disjoint sets commute (each preserves its support set), so `c b c⁻¹ = b` and
  `⁅a c, b⁆ = a c b c⁻¹ a⁻¹ b⁻¹ = a b a⁻¹ b⁻¹`.
* `NonDisjWitNonMetabelianStatement` (lane `sk-flip-05`, `exists_nonMetabelian_supportedIn`): for
  a minimal homeomorphism of a Cantor space, every nonempty open `W` supports `a, b, c, d ∈ [[T]]`
  with `⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1`.
  TRUE: minimality on an infinite Hausdorff space gives aperiodicity, hence a clopen `V ≠ ∅` with
  `V, T V, …, T^4 V ⊆ W` pairwise disjoint; permuting the levels embeds `S_5` into `[[T]]` with
  support in `W`, and `S_5` is not metabelian (`A_5` is perfect).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Lane `sk-flip-01` interface: a common displaced clopen neighbourhood of a point moved by two
homeomorphisms (see the module docstring for why it is true). -/
def NonDisjWitDisplacedStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (f k : X ≃ₜ X) (x : X), f x ≠ x → k x ≠ x →
      ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ Disjoint W (f '' W) ∧ Disjoint W (k '' W)

/-- Lane `sk-flip-02` interface: commutator localisation for elements supported in a set
displaced by `g` (see the module docstring for why it is true). -/
def NonDisjWitCommLocalStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (a b g : X ≃ₜ X) (W : Set X),
    SupportedIn a W → SupportedIn b W → Disjoint W (g '' W) → ⁅⁅a, g⁆, b⁆ = ⁅a, b⁆

/-- Lane `sk-flip-05` interface: local non-metabelianity of `[[T]]` for a minimal homeomorphism of
a Cantor space (see the module docstring for why it is true). -/
def NonDisjWitNonMetabelianStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X), IsMinimalHomeo T →
      ∀ W : Set X, IsOpen W → W.Nonempty →
        ∃ a b c d : topologicalFullGroup T,
          SupportedIn (a : X ≃ₜ X) W ∧ SupportedIn (b : X ≃ₜ X) W ∧
            SupportedIn (c : X ≃ₜ X) W ∧ SupportedIn (d : X ≃ₜ X) W ∧ ⁅⁅a, b⁆, ⁅c, d⁆⁆ ≠ 1

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.NonDisjWitDisplacedStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.NonDisjWitCommLocalStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.NonDisjWitNonMetabelianStatement
