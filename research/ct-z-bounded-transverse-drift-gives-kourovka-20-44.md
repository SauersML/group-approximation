---
rg: 2
id: ct-z-bounded-transverse-drift-gives-kourovka-20-44
kind: claim
title: "Kourovka 20.44 holds wherever the slope drift stays within bounded distance of a positive ray: in a totally consumable subgroup of CT(Z), orbits whose drift lies within distance f of some positive ray meet [−Π^(D+2f), Π^(D+2f)); so 20.44 holds for every finitely generated G ≤ CT(Z) whose slope cocycle is cohomologous, through a locally constant transfer, to a positive-ray cocycle (for example every rcwa-conjugate of an integer-ray group), and every counterexample needs infinitely many orbits whose drift is unbounded transverse to every positive ray, the one phenomenon behind both the trapped (Mahler-type) sweeping and the 3x+1 group G_T"
distinct_from:
  ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups: that is the case f = 0 (drift exactly on a ray) plus the join monotonicity; this allows bounded transverse drift and gives the cohomological form.
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that needs every slope in one γ^Z; this needs the cocycle only up to a bounded coboundary.
  ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails: that handles trapped groups with a frozen tail; this shows that bounded transverse drift never occurs in a totally consumable trapped orbit, so trapped hardness is exactly unbounded drift.
---

**ESTABLISHED** (lane proof, bh-2044-tc, 2026-09-19; **not reviewed**). Elementary. No priority
claimed. Kourovka 20.44 (S. Kohl) stays **OPEN**.
- **Credit.** The tail and corner framework is bh-free-58's; the orbit-local form is
  `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups`.
- **Scope.** Aimed at the slope lattices with `dim C_Λ ≤ 1`, which Kohl's `G_T` does not reach.
  It avoids the Mahler-type part by isolating it.

## Setting

Notation is as in `ct-z-frozen-tails-anywhere-give-kourovka-20-44`: `G = ⟨S⟩ ≤ CT_P(Z)`, depth `D`,
`Π = ∏_{p ∈ P ∪ {2}} p`, degrees in `N^k`, tails `σ^n`, and TC = no frozen degree anywhere in `Ẑ`.

**Drift.**
- For `x ∈ Z` and `h ∈ G`, the degree cocycle `c(h, x) = ν(slope of h at x) ∈ Z^k` shifts every
  tail of `x` left unread along `h`.
- The **drift set** of `x` is `Δ_x = {c(h, x) : h ∈ G}`.
- For `v ∈ N^k`, put `δ_v(x) = sup_(c ∈ Δ_x) min_(t ∈ Z) ‖c − t v‖_∞`, the transverse drift of
  `x` off the ray `Z v`. Then `δ(x) = min_(v ∈ N^k) δ_v(x) ∈ N ∪ {∞}`.
- Along an orbit, `c(h, gx) = c(hg, x) − c(g, x)`, so `δ(gx) ≤ 2δ(x)`. So "bounded transverse
  drift" is a property of the orbit.

## Theorem C

Let `G ≤ CT(Z)` be finitely generated and TC, and let `f ∈ N`.
1. Every orbit containing a point `x` with `δ(x) ≤ f` meets `[−Π^(D+2f), Π^(D+2f))`. So `G` has
   at most `2Π^(D+2f)` such orbits.
2. **Kourovka 20.44 follows** for every finitely generated `G ≤ CT(Z)` with a uniform `f` such that
   all but finitely many orbits contain a point with `δ(x) ≤ f`:
   - a frozen degree anywhere gives a transversal of positive lower density
     (`ct-z-frozen-tails-anywhere-give-kourovka-20-44`);
   - otherwise item 1 applies.

*Proof of 1.* Take `x ≥ 0` with `δ_v(x) ≤ f`, `v ∈ N^k`.
- **`v ≠ 0`.** If `v = 0`, every drift is bounded by `f`. Then the tail at `(D + f)·1` always sits
  at a degree `≥ D·1`, is never read, and is frozen, against TC.
- **Start.** Put `K_s = s v + (D + f)·1`, and choose `s ≥ 0` with `m_(K_s) > x`, so
  `σ^(K_s) x = 0`.
- **Reading.** By TC some word reads that tail. Let `w = h′x` be the configuration just before the
  reading move.
  - The tail then sits at `K′ = K_s + c(h′, x)`, and `c(h′, x) = t v + e` with `t ∈ Z` and
    `‖e‖_∞ ≤ f`. So `K′ = (s + t) v + (D + f)·1 + e`.
  - The reading piece has `d(λ) ≤ D·1` and `d(λ) ≰ K′`. If `s + t ≥ 0`, then
    `K′ ≥ (D + f)·1 + e ≥ D·1`, since `v ≥ 0`. So `s + t < 0`, and `K′ ≤ (D + 2f)·1`.
  - Tracking keeps the unread tail `0`, so `w = ρ_(K′)(w) ∈ [0, m_(K′)) ⊆ [0, Π^(D+2f))`, and
    `w` is in the orbit of `x`.
- **Negative `x`.** Choose `m_(K_s) ≥ |x|`, so the tail is `−1`, and get `w ∈ [−Π^(D+2f), 0)`. ∎

With `f = 0` this is Theorem A of `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups`.

## Corollary C1 (cohomological form)

Suppose the slope cocycle of `G` is cohomologous to a positive-ray cocycle through a locally
constant transfer. That is, there are `v ∈ N^k` and a locally constant `β : Ẑ → Z^k` with
`c(g, x) − β(gx) + β(x) ∈ Z v` for all generators `g` and all `x`. Then Kourovka 20.44 holds for
`G`.

*Proof.*
- The relation passes to all of `G` by the cocycle identity.
- `β` takes finitely many values on the compact `Ẑ`. So `δ_v(x) ≤ 2 max ‖β‖_∞` for every `x`.
- Apply Theorem C. ∎

**Example: rcwa-conjugates.** Let `φ` be an rcwa permutation of Z, and let `H` be a group of rcwa
permutations whose slopes lie in `γ^Z`, `γ` an integer. Suppose `G = φ H φ^(−1)` is a finitely
generated subgroup of CT(Z).
- The slope of `φhφ^(−1)` at `x` is the slope of `h` at `φ^(−1)x`, times `β(φhφ^(−1)x)/β(x)`,
  where `β(y)` is the slope of `φ` at `φ^(−1)y`. This `β` is locally constant, since `φ` has
  finitely many affine pieces.
- So Corollary C1 gives 20.44 for `G`.
- The global slope lattice of `G` can be large, since `β` may take any values. It can even contain
  `Z e_2 ⊕ Z e_3`, the lattice of `G_T`.
- This fits the Lesson of the orbit-slope node: hardness is not a property of the lattice.

## Corollary C2 (the class dim C_Λ ≤ 1)

- **Tube lattices** (`C_Λ = R_(≥0) v′`, `rank Λ ≥ 2`).
  - As in `ct-z-kourovka-20-44-is-graded-by-orbit-slope-groups`, `Λ ∩ R^A = Z v′`, where
    `A = supp v′`. The projection `π_B` to the other coordinates maps `Λ/Z v′` injectively onto a
    cone-avoiding lattice.
  - So `δ_(v′)(x) < ∞` iff the trapped part `π_B c(h, x)` stays bounded along the orbit.
  - Theorem C then gives: **in a TC tube group, orbits with bounded trapped drift are finitely many,
    for each bound.**
- **Trapped lattices** (`C_Λ = 0`).
  - Bounded transverse drift never occurs in a TC orbit.
  - If `c = t v + e` stays in a cone-avoiding `Λ` with `t` unbounded, then `v` lies in
    `span(Λ) ∩ R^k_(≥0) = 0`. So the drift is bounded, and the tail at `(D+f)·1` is frozen.
  - So Theorem C says nothing new for trapped groups. Their totally consumable orbits are exactly
    the orbits with unbounded trapped drift.

## Where 20.44 stays open: one phenomenon

Every counterexample to 20.44 is TC (frozen-tails node) and has infinitely many orbits with
unbounded transverse drift (Theorem C, for every `f`). This single condition covers all three
known sources of difficulty:
- **trapped sweeping**, where tails walk across ever larger level sets (the Mahler-type analogy of
  `ct-z-totally-consumable-core-of-kourovka-20-44`);
- **tube sweeping**, which is unbounded trapped drift inside a tube;
- **Kohl's `G_T`**, whose 3x+1 trajectories multiply by `3^k/2^L`. This drift `(−L, k)` has mixed
  signs, which is transverse to every positive ray; this is an explanation, not a claim.

  If `G_T` had bounded transverse drift, Theorem C would force finitely many orbits, which is the
  open 3x+1 finiteness statement. So nothing here proves or refutes it.

The part of `dim C_Λ ≤ 1` that avoids Mahler-type questions is exactly bounded trapped drift. The
rest of the class is the trapped sweeping phenomenon, in pure or tube form.

**Next steps (open).**
- A positive theorem for unbounded trapped drift would need a new mechanism. Descent works in the
  explicit groups `E_γ`, but it is not forced by total consumption.
- bh-free-58 already records the cheap-end form of descent on the `(3/2)^Z` ray, heuristically, in
  `ct-p-z-mixed-ray-frozen-tails-force-finite-orbits`: a tail read at the contracting end gives
  `|w| ≲ |x|^(log 2/log 3)`. The open case is the expanding end.
- One sharp test: rank-one mixed rays `(a/b)^Z` in which every piece has slope `≤ 1` on `N_0` near
  its orbit minimum.

## Lesson for general BH

**The obstruction to controlling orbits of arithmetic groups is unbounded drift transverse to
every positive ray, and it is a cohomological invariant, not a lattice one.**
- Bounded coboundaries, and so rcwa conjugation, never create it.
- Positive-ray drift, even up to bounded error, gives a finite window of orbit representatives.
- The Mahler-type sweeping of trapped lattices and the 3x+1 group are two faces of the same
  unbounded transverse drift.
- For hosts: if the slope cocycle of an embedded subgroup can be cobounded onto a positive ray,
  its orbits are tame, whatever slopes the host uses.
