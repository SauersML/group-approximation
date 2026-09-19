---
rg: 2
id: grigorchuk-envelope-emitter-reduces-to-ie-prime-for-grigorchuk
kind: claim
title: The branch set at the emitter of Grigorchuk's finitely presented envelope is, up to finite index and a trivially acting kernel, finitely many free orbits of the Grigorchuk group; so a finite-type (IE′) blow-up of that emitter exists only if the Grigorchuk group itself, up to commensurability, has an SFT compactification, and the branch envelope hands the emitter problem back to its input
distinct_from:
  stabilizer-engines-embed-in-every-branch-compactification: that treats the free-product emitter of Z/2 * S, whose branch set is the free S-orbit S; this treats the ascending-HNN emitter of Grigorchuk's envelope, with a fixed end and a homogeneous branch set G/φ(G), and identifies that set with free orbits of G through level-one sections.
  finite-type-branch-blow-ups-are-sft-compactifications: that gets SFT compactifications from metric seeds (Cannon cones) for hyperbolic S; this shows that the Grigorchuk envelope needs the same object for the Grigorchuk group, where no seed mechanism is known.
---

**ESTABLISHED** for items 1–3 (lane proof, bh-e3prime, 2026-09-18; elementary; not reviewed).
Item 4 is **OPEN**. The answer to the coordinator's test is: *not yet a concrete (IE′) instance*,
and exactly why.

## Setting

- `G = ⟨a, c, d⟩` is the first Grigorchuk group, with `b = cd` and wreath recursion `ψ`.
- `φ` is Lysionok's substitution, and `ψ(φ(g)) = (θ(g), g)`, where `θ : G -> ⟨a, d⟩ ≅ D_8` has
  `θ(a) = d`, `θ(c) = θ(d) = a`, and hence `θ(b) = 1` (`grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter`,
  item 2).
- `H = G*_φ = ⟨G, t | t^(-1) g t = φ(g)⟩` is Grigorchuk's finitely presented envelope, and `T` its
  Bass–Serre tree with base vertex `v_0 = G`.

## Statement

1. **The emitter.**
   - Each vertex has exactly one *up-edge* (the translate of `[v_0, t v_0]`, stabilizer `G`).
   - Each vertex has the *down-edges* `h [v_0, t^(-1) v_0]` for `h ∈ G/φ(G)`, with stabilizer
     `φ(G)`. These are infinitely many.
   - `H` fixes the end `ω = lim t^n v_0`.
   - So the engine lives on a compact open *horoball* reduction avoiding `ω`, as for `BS(1,2)` and
     the odometer. Its emitters are the vertex points, and the branch set at `v_0` is the `G`-set
     `G/φ(G)`.
2. **The branch set is `G` through sections.** Put `S_1 = St_G(1)`, of index 2. Then
   `G/φ(G) = S_1/φ(G) ⊔ a·S_1/φ(G)`, and the map `(x, y) ↦ x θ(y)^(-1)` induces an
   `S_1`-isomorphism
   `S_1/φ(G) ≅ O`, where `O ⊆ G` is the orbit of `1` under the action `g·z = g|_0 · z · θ(g|_1)^(-1)` of `g ∈ S_1`.
   - On the finite-index subgroup `L_0 = {g ∈ S_1 : g|_1 ∈ ker θ}`, this action is left
     multiplication by `g|_0`.
   - The section map `L_0 -> G`, `g ↦ g|_0`, has finite-index image `G_0`, and its kernel acts
     trivially.
   - `O` is `L_0`-invariant, so it is a union of right cosets `G_0 z`. As an `L_0`-set, the branch set
     is therefore finitely many free orbits of `G_0` under left multiplication.
3. **Reduction.**
   - A finite-type blow-up of this emitter, in the sense of the parent nodes, is a `G`-equivariant
     compactification `K` of `G/φ(G)` in which `G/φ(G)` is an isolated dense orbit and which is
     conjugate to the orbit closure of that point in an SFT.
   - Restricting to `L_0` and dividing out the trivially acting kernel changes an SFT only by
     finite-index recoding. So such `K` exists only if `G_0` (a finite-index subgroup of `G`) has an SFT containing
     finitely many isolated free orbits whose union is dense. The SFT is pushed forward along
     `L_0 -> G_0`, whose kernel acts trivially on the orbit closure. The converse (inducing back to a
     `G`-compactification of `G/φ(G)`) is not claimed. That is (IE′) for the
     Grigorchuk group, up to commensurability.
   - Finite remainders are excluded by the two-defect argument of part 3(a) of
     `stabilizer-engines-embed-in-every-branch-compactification`, adapted to remainders indexed by a
     finite quotient (lane check, not written out). `G` is one-ended, because a finitely generated infinite
     torsion group fixes a vertex in every tree action (Serre) and so does not split over a finite
     subgroup (Stallings).
   - So by part 3(a) of `finite-type-branch-blow-ups-are-sft-compactifications`, the remainder must be
     infinite and clopen-indecomposable.
4. **Open: (IE′) for the Grigorchuk group.** No seed mechanism is known.
   - The Cannon distance-gradient seed of `finite-type-branch-blow-ups-are-sft-compactifications` needs
     (TP): cones determined by bounded tails, hence finitely many cone types. Then the geodesic language
     would be regular for that generating set. This lane expects that to fail for a group of
     intermediate growth, but did not prove it.
   - Strongly aperiodic SFTs on `G` are recalled from the literature (Barbieri), not re-read. They are
     the opposite object: no isolated points.

## Proof

**Item 1.**
- `t^(-1) G t = φ(G) <= G` gives `Stab([v_0, t^(-1) v_0]) = G ∩ φ(G) = φ(G)`. The down-edges at
  `v_0` are its `G`-translates, indexed by `G/φ(G)`, which is infinite.
- `t φ(G) t^(-1) = G` gives `G <= t G t^(-1)`, so `G` fixes `t v_0`, and `[v_0, t v_0]` is the only
  edge of its type at `v_0`.
- Iterating, `G <= t^n G t^(-n)`, so `G` fixes the up-ray `(t^n v_0)`. Every vertex stabilizer fixes
  its up-ray, and all up-rays are cofinal, so `H` fixes their common end `ω`.
- The reduction to the clopen set of ends and blow-up points below `v_0` avoids `ω`.

**Item 2.**
- `φ(G) <= S_1`, and `ψ(S_1)` has finite index in `G × G`. It contains `ψ(φ(G)) = graph(θ)`.
- `(x, y) ↦ x θ(y)^(-1)` is constant exactly on the left cosets of `graph(θ)` in `G × G`, and it is
  equivariant for the action `(x, y)·z = x z θ(y)^(-1)`.
- The map is injective on cosets: equal values force `ψ(g^(-1)g') ∈ graph(θ) = ψ(φ(G))`, and `ψ` is
  injective on `S_1`. So it identifies `S_1/φ(G)` with the orbit `O` of `1`.
- For `g ∈ L_0`, `θ(g|_1) = 1`, so `g` acts as `z ↦ g|_0 z`.
- `L_0` has finite index in `S_1` because `ker θ` has finite index in `G`. Its image under `g ↦ g|_0`
  has finite index in `G`, because `ψ(S_1)` has finite index in `G × G`. The kernel acts trivially by
  the formula.
- `G_0` acts on `G` with `[G : G_0]` free orbits.

**Item 3.**
- **Finite index.** For `N <= G` of finite index, `N`-SFTs and `G`-SFTs correspond by the usual
  induction/restriction. The isolated `G/φ(G)`-orbit becomes finitely many isolated `L_0`-orbits.
  The trivially acting kernel is invisible to cylinder sets.
- **Remainder.** The remainder statements are the cited parent parts, applied to the one-ended group
  `G_0`.

## Consequence for the gates

- **The branch envelope creates no room at its emitter.** Blowing up the emitter of Grigorchuk's
  finitely presented envelope requires (as a necessary condition) (IE′) for the Grigorchuk group itself, up to commensurability.
  So the emitter the branch data forced (`grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter`)
  cannot be repaired by the finite-type blow-up engine without first solving the input's own emitter
  problem.
- **This is a general feature of self-replicating envelopes.** The argument uses only
  `ψ(φ(g)) = (θ(g), g)` with `θ` of finite image, and that `ψ(St(1))` has finite index in `G × G`
  with first projection onto `G` (regular branch and self-replicating). So every substitution envelope of
  this form has, as branch set, finitely many free orbits of the input group through level-one
  sections.
- **The live (IE′) instances stay metric** (`Z`, `Z^2`, free and surface groups).
  - The question for branch inputs is now: does a self-replicating group have an SFT with an isolated
    free orbit, built from its own self-similarity rather than from a metric? That is (IE′)-branch.
  - A positive answer for `G` would give a concrete finite-type blow-up over a branch input, and a
    negative answer would close branch inputs at the emitter.

## Lesson for general BH

**A substitution envelope hands its emitter back to its input.** When a self-replicating group is
finitely presented by an ascending substitution HNN extension `ψ(φ(g)) = (θ(g), g)`, the branch set
at the resulting emitter is the input group itself, acting through level-one sections, up to finite
index. So the blow-up engine can repair that emitter only if the input already has an SFT
compactification.

Finite presentation of branch data therefore moves the problem to (IE′) for the same group; it does
not shrink it. For one-ended torsion inputs the missing object is a seed not built from a metric: an
SFT whose isolated free orbit is pinned down by self-similarity. No such seed is known for any
branch group.
