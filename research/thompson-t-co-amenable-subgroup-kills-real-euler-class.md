---
rg: 2
id: thompson-t-co-amenable-subgroup-kills-real-euler-class
kind: claim
title: "Thompson's T has a co-amenable subgroup H on which the real Euler class vanishes (equivalently, the preimage of H in T-bar has a homomorphism to R sending z to 1)"
distinct_from:
  thompson-t-euler-class-splits-over-almost-invariant-space: that allows any nonsingular T-space; this is its special case X = T/H with counting measure, reduced to a statement about subgroups
  thompson-t-orbits-carry-no-invariant-means: that shows point stabilizers (e.g. F) are not co-amenable in T; this asks for a co-amenable subgroup of a different kind
artifacts: []
---

**Statement.** There is a subgroup `H ≤ T` with both properties:
- `H` is co-amenable in `T`: `T/H` carries a `T`-invariant mean, or equivalently `ℓ²(T/H)` has
  almost invariant vectors.
- The preimage `H̄ ≤ T̄` has a homomorphism `u : H̄ → R` with `u(z) = 1`. Equivalently,
  `e_R|_H = 0` in `H²(H, R)`, where `e_R` is the real Euler class.

**Status.** OPEN.

## Role

This implies `thompson-t-euler-class-splits-over-almost-invariant-space` (proof below), and so
`lifted-thompson-t-is-a-t-menable`.

`H = T` is excluded, because `T̄` is perfect.

**Proof of the implication.** Take `X = T/H = T̄/H̄` with counting measure. Choose a section
`σ : T̄/H̄ → T̄`, and set `β(g, y) = u(σ(gy)^{-1} g σ(y))`. The argument lies in `H̄`.
- The cocycle identity holds by telescoping.
- `β(z, y) = u(σ(y)^{-1} z σ(y)) = u(z) = 1`, since `z` is central.
- The Koopman representation is the quasi-regular representation `ℓ²(T/H)`. It has almost
  invariant vectors iff `H` is co-amenable (Eymard; standard). ∎

## Forced shape (established)

**(D1) `H` has no finite orbit on `S^1`.**

Suppose `H` preserves a finite set. Then a finite-index subgroup `H' ≤ H` fixes a point of `S^1`.
- `H'` is co-amenable in `T`: average an invariant mean on `T/H` over the fibres of
  `T/H' → T/H`, each of size `[H : H']`.
- `u|_{H̄'}` still sends `z` to `1`.
- So `X' = T/H'` is a witness for (MT) with an equivariant map `tH' ↦ t·p` to `S^1`, which
  contradicts (F2) of `thompson-t-euler-class-splits-over-almost-invariant-space`.

This excludes `F` and all point and finite-set stabilizers.

**(D2) `H` is nonamenable, and the induced `β` is not uniformly integrable.**
- `H` is nonamenable because `T` is nonamenable, and a co-amenable amenable subgroup would
  make `T` amenable.
- The induced `β` is not uniformly integrable along any almost invariant sequence, by (F1).

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): isolated; (D1) and (D2) proved. No candidate `H`
  was tested.
  - *Candidate: `H = PSL_2(Z) ≤ T`.*
    - `PSL_2(Z)` embeds in `T`, acting on `S^1` by the Minkowski-conjugated projective action.
      Its preimage in `T̄` is recalled as `B_3`, whose abelianization is `Z`. The centre
      generator `Δ²` maps to `6`, so `u = ab/6` works, and `H` satisfies (D1) and (D2). The
      identification of the preimage with `B_3` was not rechecked verbatim.
    - So "is `PSL_2(Z)` co-amenable in `T`?" is a single falsifiable question. A yes proves
      `lifted-thompson-t-is-a-t-menable`.
  - *Test for a no.* Suppose `H` preserves a probability measure `λ` on a compact `T`-space `Y`
    that carries no `T`-invariant probability. Then `H` is not co-amenable, because integrating
    `t_*λ` against an invariant mean on `T/H` would give a `T`-invariant probability. For
    `PSL_2(Z)`, the space `Y = S^1` gives nothing, since the action is nonelementary.
- 2026-09-18 (swarm-0917-w10-w10-nv-last1): **the `PSL_2(Z)` candidate is refuted.**
  - `psl2z-is-almost-malnormal-and-not-co-amenable-in-thompson-t` shows that
    `Λ = Φ(PSL_2(Z))` is almost malnormal in `T`, with `|Λ ∩ gΛg^{-1}| ≤ |B(g)|!`, where `B(g)`
    is the rational breakpoint set of `g ∉ Λ` in the model `T = PPSL_2(Z)`.
  - The general lemma `nonamenable-almost-malnormal-subgroups-are-not-co-amenable` then says:
    `ℓ²(T/Λ)` splits as the base point plus quasi-regular representations of `Λ` over finite
    stabilizers. The Kesten gap of `Λ` confines almost invariant vectors to the base point, which
    any `g ∉ Λ` moves by `√2`.
  - Invariant: the breakpoint set. The class dies where `Λ ∩ gΛg^{-1}` must permute `B(g)`.
  - The kill covers every conjugate of `Λ` and every subgroup of one. It applies to any
    isomorphism `PPSL_2(Z) → T`, including the Minkowski one. The recalled identification of
    the preimage with `B_3` plays no role.
  - Forced shape, new: **(D3)** `H` is contained in no conjugate of `Λ`. More generally, `H` is
    contained in no proper nonamenable subgroup with amenable self-intersections.
  - Surviving shape: `H` has no finite orbit (D1), is nonamenable (D2), is not inside a conjugate
    of `Λ` (D3), and `T/H` is an infinite amenable coset space.
  - Whether `T` has *any* proper co-amenable subgroup remains open. A no would kill this node,
    and with it this discrete route to `lifted-thompson-t-is-a-t-menable`.
- 2026-09-18 (swarm-0917-w10-w10-nv-follow): the decomposition was sharpened, and a barrier
  proved. No candidate was decided. Everything is through
  `thompson-t-amenable-actions-are-free-off-fixed-points` (ESTABLISHED).
  - *Barrier.* A witness `H` is proper, since `T̄` is perfect. By item 1 of that claim (Dudko--Medynets
    character rigidity for `T`), every invariant mean on `T/H` is then essentially free, so `T` is
    sofic and hence `F` is sofic. The routes are:
    - `thompson-t-fixed-point-free-amenable-action-from-euler-subgroup`;
    - `thompson-t-sofic-from-fixed-point-free-amenable-action`;
    - `thompson-f-sofic-from-t-sofic`.

    So this node is at least as hard as `thompson-f-is-sofic`. Its prerequisite
    `thompson-t-has-a-fixed-point-free-amenable-action` can fail on its own, and if it fails
    this node is false.
  - *New forced shape.* Beyond (D1)–(D2), and past any finite-index reduction:
    - (D4) for each finite `P ⊆ T \ {e}`, mean-almost every conjugate `tHt^(-1)` misses `P`;
    - (D5) `H` is not confined;
    - (D6) `H` fixes no finitely additive probability on the algebra of dyadic half-open arcs.

    (D6) contains the w9 "test for a no" for `Y = S^1`, (D1), and the amenable half of (D2).
  - *Sharper test for a no.* `H` is not co-amenable exactly when
    `T/H = A_1 ∪ ... ∪ A_l ∪ Fix(p_1) ∪ ... ∪ Fix(p_k)` with the `g_jA_j, h_jA_j` pairwise
    disjoint (Elek--Szabó Theorem 3, via item 1). A paradoxical decomposition modulo finitely
    many fixed sets is enough.
- 2026-09-18 (swarm-0917-w11-w11-nv-break): bounded-cohomology constraint on every witness. This
  node stays OPEN.
  - *Result.* See `thompson-t-co-amenable-subgroups-see-all-bounded-euler-powers`, ESTABLISHED
    by route `thompson-t-co-amenable-bounded-euler-powers-proof`. For every co-amenable `H ≤ T`,
    `(e_b|_H)^n ≠ 0` for all `n`.
    - The proof is a transfer through the invariant mean, together with `H^*_b(T) = R[e_b]`.
  - *(D3') New forced shape.* A witness `H` makes `φ = rot − u` a homogeneous quasimorphism on
    `H` with `[δφ] = −e_b|_H` and all cup powers nonzero. So `H` must avoid all of the following:
    - boundedly acyclic groups, including `F` and `F^k`;
    - groups with a finite-index subgroup fixing a point, which reproves (D1);
    - every action conjugate or semi-conjugate into an action of a Lie group locally isomorphic
      to `SL_2(R)`, by Hartnick–Ott `H^4_cb = 0`. This strictly contains the wave-10 exclusion
      (D3) of `PSL_2(Z)`, and also excludes all Fuchsian and Schottky subgroups of `T`;
    - free groups whose class is `Δ`-decomposable or Brooks (Amontova–Bucher).
  - *Reduction.* A free co-amenable `H ≤ T` automatically has `e_R|_H = 0`. Such an `H` would
    exist only if some class in `H²_b(F_r)` had all cup powers nonzero, which is open (Hofmann
    2024).
    - So the free route to this node goes through the cup-product problem for free groups.
    - A proof that such cup powers always vanish would force every witness to be non-free, and to
      avoid every `SL_2(R)`-type action.
  - *Calibration.* `T̄` acting through `T` has `e_R = 0` and all `e_b^n ≠ 0`. So (A) alone cannot
    refute this node.
- 2026-09-18 (swarm-0917-w12-w12-nv-last1): the candidate `H = PSL_2(Z)` is refuted, together
  with every subgroup of every stabilizer of a quad-complete lamination. The node stays OPEN.
  - *Forced shape (D4).* A co-amenable `H` fixes no `τ ∈ Tri_D`, a non-crossing,
    quad-complete chord system with endpoints in a countable `T`-invariant set `D`. This is
    `thompson-t-quad-complete-laminations-carry-no-invariant-mean`, Part 4.
  - (D4) contains the forced shape (D3) that swarm-0917-w10 found on the bus (`H` lies in no
    conjugate of `PSL_2(Z)`). The Minkowski-conjugated `PSL_2(Z)` fixes the dyadic Farey
    tessellation `τ_0`.
  - *Obstruction.* This is sharp quad-diagonal exclusivity. An invariant mean makes both
    diagonals of a quad equal in mean, through five monotone nested moves, while exactly one of
    them is present at each point.
  - The test above, which looks for an `H`-invariant probability on a compact space, is
    replaced by the test "does `H` fix a quad-complete lamination?". The new test needs no
    compact space and no spectral estimate.
  - *Still open.* Candidates `H` whose orbits on chord systems contain no quad-complete fixed
    point, for example stabilizers of laminations with non-triangular gaps. Not tested.
- 2026-09-18 (swarm-0917-w12-w12-nv-break, reframing): ESTABLISHED
  `thompson-t-co-amenable-subgroups-meet-copies-of-f` (route `...-proof`). This node
  stays OPEN, with two new forced shapes.
  - *Principle.* Restrict the `T`-invariant mean on `T/H` to a test subgroup `K`. The stabilizer of
    `gH` is `K ∩ gHg^{-1}`. If all of these are amenable, then `K` is amenable.
  - *(D-F) Reduction to `F`.* Take `K = F`. Then `F ∩ gHg^{-1}` is the stabilizer in `H` of the
    dyadic point `g^{-1}(0)`. Suppose some witness `H` has amenable stabilizers at dyadic points.
    Such a witness proves `F` amenable. This covers every `H` all of whose `F_2`-free subgroups are
    amenable, by Brin–Squier; linear and hyperbolic witnesses are examples. If `F` is nonamenable,
    every witness contains a nonamenable subgroup that fixes an open arc pointwise (take
    `K = F[1/4,3/4]`). Invariant: amenability of point stabilizers. Step where the witness dies:
    restriction of the mean to `F`.
  - *(D-Λ) The candidate `PSL_2(Z)` is refuted unconditionally,* independently of the w10
    almost-malnormality argument recorded on the live bus.
    - Test subgroup: `K = π^{-1}(Λ) ≤ C_T(r_{1/2})`, the double-cover lift, which is
      nonamenable.
    - Lifts of hyperbolic elements have 4 or 0 fixed points and infinite order, so they lie in no
      conjugate of `Λ`.
    - Subgroups of `PSL_2(Z)` without hyperbolic elements are amenable.
    - So `K ∩ gΛg^{-1}` is amenable for every `g`, and no subgroup of any conjugate of `Λ` is
      co-amenable.
  - *Left open.* The measurable analogue for (MT): `F` does not act Zimmer-amenably on a witness
    `X` unless `F` is amenable. It needs Kuhn's weak-containment theorem, which is not imported.
