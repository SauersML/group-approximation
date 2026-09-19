---
rg: 2
id: simple-inputs-in-wobbling-hosts-are-dense-schreier-realizations
kind: claim
title: An infinite simple group lies in the full group of a free Λ-subshift, faithfully on every invariant subset, iff one of its nontrivial Schreier quotients has a coarsely dense injective Lipschitz realization in Λ, and the subshift is then effectively closed from WP(G) alone
distinct_from:
  translation-like-inputs-embed-in-full-groups-over-a-fixed-group: that treats FREE (translation-like) realizations, where freeness gives faithfulness on every invariant subset; this treats arbitrary, non-free realizations of simple inputs, where faithfulness has to come from simplicity plus coarse density of the moved set.
  translation-like-hosts-are-capped-by-separation-profiles: its Consequence 4 states the non-free escape as "faithful on Λ × N with bounded displacement, effectively closed when the action is computable"; this corrects that item. Faithfulness on minimal subsystems needs coarse density of moved points, and effectivity comes from WP(G) through a density condition, not from computability of the action.
---

**ESTABLISHED** (lane proof, bh-gate-u-wobble; elementary; not reviewed; no priority claimed). This is
gate U of the master route (`research/artifacts/gq-bh-synthesis-master-route.md`, v3, Track B), in the
non-free form that bh-invent-09 isolated.

## Setting

- `Λ` is a finitely generated group. `Cay(Λ)` uses right multiplication by a finite generating set, with
  word metric `d`.
- `G` is an infinite, finitely generated, simple group with finite symmetric generating set `S`.
- An *R-realization* of `G` on `Λ` is a right action of `G` on the *set* `Λ` in which every `s ∈ S` moves
  every point at most `R`. The *moved set* `M` is the set of points moved by some `s ∈ S`. The realization
  is *R₀-dense* if every ball of radius `R₀` in `Λ` meets `M`.
- `X_G^(R,R₀) ⊆ (B_Λ(R)^S)^Λ` is the set of move tables `x` (as in the setting of
  `translation-like-inputs-embed-in-full-groups-over-a-fixed-group`) satisfying:
  - (T1) each `φ_s^x` is a bijection with inverse `φ_(s⁻¹)^x`;
  - (T2) `φ_w^x = id` for every relator `w` of `G`;
  - (T3′) every `R₀`-ball contains a position `v` with `x(v)_s ≠ e` for some `s`.

  Condition (T3) (fixed-point freeness) is *not* imposed.

## Theorem 1 (dense Schreier realizations)

The following are equivalent.
1. **(host form)** There are `R, R₀`, a nonempty effectively closed Λ-subshift `X` and an embedding
   `G ↪ [[Λ ⋉ (X × Y)]]`, for `Y` any free Λ-subshift, that is faithful on every nonempty closed
   Λ-invariant subset, in particular on every minimal subsystem.
2. **(action form)** `G` has an `R₀`-dense `R`-realization on `Λ` for some `R, R₀`.
3. **(Schreier form)** There are proper subgroups `K_i < G` and maps `ι_i : K_i\G → Λ` with pairwise
   disjoint images whose union is `R₀`-dense. Each `ι_i` is injective, and `R`-Lipschitz from the Schreier
   graph `K_i\Cay(G, S)` (right cosets, edges `K_i g — K_i g s`) to `Cay(Λ)`.

Moreover, in 1 one may take `X = X_G^(R,R₀)`. It is effectively closed whenever `WP(G)` is decidable,
**whether or not** the realization in 2 is computable. Only its nonemptiness uses 2.

## Proof

**2 ⇔ 3.** Decompose the realization into `G`-orbits. The orbits meeting `M` are exactly the nontrivial
transitive `G`-sets, since a point fixed by all of `S` is fixed by `G`. So they are `K_i\G` with `K_i`
proper, and the inclusions are injective and `R`-Lipschitz on Schreier graphs. Conversely, transport the
actions onto the images and let `G` act trivially elsewhere. Every point of each `K_i\G` is moved by some
generator (again because `K_i` is proper), so the moved set is the union of the images, which is
`R₀`-dense.

**2 ⇒ 1.** The move table `x(v)_s = v⁻¹(v·s)` of the realization lies in `X_G^(R,R₀)`, so that subshift is
nonempty.
- **Effectivity.** It is Λ-invariant and closed. (T1) and (T3′) forbid finitely many patterns. (T2)
  forbids an r.e. list of patterns when `WP(G)` is decidable, since the relators are then r.e., and
  `WP(Λ)` is decidable for the Λ used here.
- **Faithfulness.** Let `Z ⊆ X_G^(R,R₀) × Y` be nonempty, closed and invariant, and pick `(x, y) ∈ Z`.
  - As in Theorem 2 of `translation-like-inputs-embed-in-full-groups-over-a-fixed-group`, the Λ-orbit of
    `(x, y)` is a copy of Λ (freeness of `Y`), and `σ_s` acts on it as `φ_s^x` acts on Λ. So `G` acts on
    that orbit through the action encoded by `x`.
  - By (T3′), `x` has a nonidentity move, so that action is nontrivial. `G` is simple, so it is faithful,
    and hence `G` acts faithfully on `Z`.

**1 ⇒ 2.** Take `(x, y)` in the host. Its orbit carries an `R`-realization, encoded by `x`.
- Suppose that for every `R₀` some `R₀`-ball misses the moved set.
- Translating these balls to the identity and passing to a limit, compactness gives `x′` in the orbit
  closure of `x` with no nonidentity move, so `x′ = id*`, the identity table.
- Then `G` acts trivially on the nonempty closed invariant set `{id*} × Y`, which contradicts 1.
- So the moved set of `x` is `R₀`-dense for some `R₀`. `∎`

## Corollaries

1. **Monotonicity.** Suppose there is an injective, Lipschitz, coarsely surjective map
   `Cay(Λ) → Cay(Λ′)`, for example when `Λ ≤ Λ′` has finite index. Then every simple `G` with a dense
   realization on `Λ` has one on `Λ′`.
2. **Free realizations and QI classes.** Let `Λ` be nonamenable and `Γ` any finitely generated group
   quasi-isometric to `Λ`.
   - Whyte's theorem (recalled, not re-read) gives a bijection `β : Γ → Λ` at bounded distance from a
     quasi-isometry.
   - Then `λ·γ = β(β⁻¹(λ)γ)` is a free action with displacement at most `L|γ| + C`, so it is
     translation-like, and `Γ` lies in the host of
     `translation-like-inputs-embed-in-full-groups-over-a-fixed-group`.
   - **Calibrations.**
     - `Λ = F₂ × F₂` hosts every cocompact lattice in a product of two trees. That includes the
       finitely presented *simple* Burger–Mozes groups, which are infinite simple inputs over one fixed
       Farrell–Jones scaffold.
     - A torsion-free vertex-regular Ã₂ lattice hosts every cocompact lattice of its building, and these
       are infinite *Kazhdan* groups (Ã₂ lattices have (T); recalled).
3. **Correction to Consequence 4 of `translation-like-hosts-are-capped-by-separation-profiles`.**
   - A faithful bounded-displacement action on `Λ × N` is not enough for gate U: minimal subsystems can
     collapse to `{id*}`, which is exactly the failure of density.
   - The orbit closure of a computable configuration need not be effectively closed.
   - The correct non-free interface for simple inputs is Theorem 1, a coarsely dense realization. Its host
     subshift is effectively closed from `WP(G)` alone.

## Lesson for general BH

For a simple input, gate U over a fixed scaffold Λ is a pure question in coarse geometry. Some nontrivial
Schreier quotient `K\Cay(G)` of the input must embed injectively and Lipschitz into Λ, densely enough that
no invariant subset of the host forgets the input. Simplicity then supplies faithfulness everywhere, and
the input's word problem supplies effectivity. The designer is free to pick the stabilizer `K`, and so to
make the Schreier graph far smaller and tamer than the Cayley graph. That is the only way monsters, which
contain expanders, can pass the separation cap.
