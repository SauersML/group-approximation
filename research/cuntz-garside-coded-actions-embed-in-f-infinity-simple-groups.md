---
rg: 2
id: cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups
kind: claim
title: A group acting faithfully by global bisections on the boundary of a Li-Garside category with finite unit groups, with no open set trapped beyond a loop and a minimal effective boundary groupoid, embeds in a simple group of type F_infinity; the host class is closed under finite-index overgroups
distinct_from:
  cuntz-stabilized-garside-full-groups-are-f-infinity: that is the finiteness half with trivial units; this adds finite unit groups, simplicity, the embedding and closure under finite-index overgroups, packaged as one host theorem.
  finitely-coded-cantor-actions-give-type-a-hosts: that needs a degree map with (UFP*) and assumes finite presentation; this needs neither, proves F_infinity, and yields simple hosts rather than type (A) actions.
  torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups: that is one application (free cubulations); this is the general interface that application instantiates.
---

**ESTABLISHED** through `cuntz-garside-coded-actions-host-proof` (lane proof, not
independently reviewed; X. Li, arXiv:2110.04505v2 and 2209.08087v2, read at source; no priority
claimed).
- The finite-unit extension of the Cuntz theorem is new here.
- It needs a referee pass. The trivial-unit core, `cuntz-stabilized-garside-full-groups-are-f-infinity`,
  was internally refereed with the Q1.15 chain.

## Statement

**Data.**
- `𝔠` satisfies the standing hypotheses of Li's `intro:Gars` (as in
  `cuntz-stabilized-garside-full-groups-are-f-infinity`).
- `𝔠` is right cancellative, so (F) holds.
- Every unit group `𝔠*(v,v)` is **finite**.
- `X ⊆ Ω_∞(𝔠)` is closed and invariant.
- `𝒢 = I_l ⋉ X`, `v_0` is an object, and `Y = X(v_0) ∩ X` has no isolated points.
- `G_2` is the Cuntz groupoid on `C = {x,y}^ℕ`.

**Conditions.**
- **(C1) Coding.** The data above.
- **(C2) Resynchronization.** A group `G` acts faithfully on `Y` by global compact open
  bisections of `𝒢|_Y`.
- **(C3) (Acyc).** For every object `v` and every non-unit `σ ∈ 𝔠(v,v)`, the set
  `∩_m σ^m·X(v)` has empty interior in `X`.
- **(C4) Dynamics.** `𝒢|_Y` is Hausdorff, effective and minimal.

**Theorem.** Assume (C1)–(C4), and put `S = F((𝒢 × G_2)|_{Y × C})`. Then:
1. `S` is of type `F_∞`. This needs only (C1) and (C3).
2. `S` is simple, perfect and integrally acyclic.
3. `g ↦ g × id` embeds `G` in `S`.
4. `S ≀ Q ≤ S` for every finite group `Q`. So the class of groups that embed in `S` is closed
   under finite-index overgroups, via the normal core and Krasner–Kaloujnine.

## What each condition asks of a geometric input

This is the anatomy of the cubulated case, `cubulated-groups-embed-in-f-infinity-simple-groups`.
Each condition was supplied by one feature of a CAT(0) cube complex, and by nothing else.

| Condition | Supplied, for cube complexes, by | Used for |
|---|---|---|
| (C1) disjoint mcms | median joins of geodesics from every vertex | Li's lcms in the bisection category |
| (C1) finite objects, Garside heights | the finite local state (a vertex, its adjacent walls, a label) and Niblo–Reeves heights | Witzel's criterion |
| (C1) finite units | properness and cocompactness (finite cube stabilizers) | `lem:Stab` |
| (C2) | "leaving a wall's carrier is permanent", so promises (flags) propagate like crossings | every element is a global bisection |
| (C3), (C4) | free exits: `G * F_r` with an exit edge at every vertex, and trivial exit stabilizers | no open set beyond a loop; topological freeness; minimality |

What is **not** used:
- curvature beyond these combinatorial facts;
- specialness, hyperbolicity or residual finiteness;
- Li's loop condition (`t<d`), a degree map, or a Perron condition.

## Consequences for non-cubulated inputs

- **Median joins are more than Li needs.** Li needs disjoint mcms, not joins. The median joins
  used here come from the median-graph structure of the 1-skeleton, and an infinite Kazhdan
  group has no proper action on a median graph (Niblo–Reeves; Chatterji–Druţu–Haglund). So Kazhdan inputs
  must enter through non-median codings with disjoint mcms, such as grid codings with
  `k`-graph combinatorics.
- **Euclidean buildings, all types (done 2026-09-19).** The box orbit categories of
  `euclidean-building-lattices-lie-in-permutational-bh-class` satisfy (C1)–(C4) with no
  rescaling: see `euclidean-building-lattices-embed-in-f-infinity-simple-groups`. (C3) is
  "shadows shrink", proved with a uniform box measure. This covers Ã₂, C̃_n and G̃₂, including
  the Kazhdan non-residually-finite C̃₂ lattices.
- **Correction (2026-09-19): no promise moves are needed for buildings.** The earlier text
  here proposed seed codings with promise moves for C̃_n. That is unnecessary. Sector codings of
  chambers at infinity resynchronize by themselves, because that boundary is closed and
  generic. Promise moves are needed only when the natural boundary contains non-generic limit
  points, as the Roller boundary does.

## Lesson for general BH

For simple `F_∞` hosts, a geometric group has to supply exactly **a finite-state coding of
its boundary whose prefix order has disjoint mcms, and, where that boundary is not closed,
promise moves that make codings from different base points resynchronize.** The rest is free:
- the Cuntz factor supplies merge packing, and with it finiteness;
- free exits supply topological freeness, (Acyc) and minimality;
- Li's Corollary D and Matui supply simplicity.

So the question "does class `𝒞` satisfy Boone–Higman?" becomes, for geometric classes, "do its
spaces have a finite-state, promise-closed prefix order with disjoint mcms?" Median geometry is
one sufficient answer. It is not the only one, and it is the one that excludes Kazhdan groups.

## Referee (bh-ref-q115-b, 2026-09-19): PASS, with one credit correction

I checked `cuntz-garside-coded-actions-host-proof` adversarially, concentrating on the
finite-unit step.

**Credit.** Units are native to Li's framework, so "the finite-unit extension is new here"
should be narrowed.
- Li's finiteness theorem already allows units. It is stated for `𝐅(I_l ⋉ ∂Ω)` "of type `F_n` if
  `ℭ*(𝔳,𝔳)` is of type `F_n` for all `𝔳`" (arXiv:2110.04505v2, TeX l.619, read at source).
- `lem:Stab`, (F), (3_Γ) and `cor:thmA` are Li's, with units. Li also notes verbatim that
  "Condition (F) is for example satisfied if ℭ is cancellative".
- Dehornoy's criterion is quoted verbatim by Li: "𝔖∪ℭ* generates ℭ and 𝔖♯ is closed under mcms
  and right divisors (see [13], Chapter IV, Proposition 2.25)".
- What is new is running the pure-hole Cuntz datum, Lemma L and the (Acyc) height with units, in
  place of Li's (`t<d`).

**Checks.**
- **(U1).** Pure holes are carried to pure holes by `𝔠₂* = 𝔠* × {1}`.
  - `u a_i = a'_i u'_i` keeps norms, so (3_Γ) holds.
  - (4_Γ) applies to `ω u^{-1}`, and `c_k ∈ mcm ⊆ 𝔖₂^♯` gives (5_Γ).
  - One must use an `=*`-transversal of `𝔖₂`, since `(u,x) =* (1,x)`. U1 does so.
- **(U2).** `([u_i,U_i])_i` is a unit of `𝐂_𝐗` by (1_𝔛), and invertible morphisms have unit
  components by `lem:aU=bU`.
- **(U3).**
  - Doubling on unit classes uses `δ_{τ'}` for any `τ' ∈ [τ]`.
  - The merge `α = δ_τ·(id ⊔ [u^{-1},uτ])` is an atom, since atoms are closed under right unit
    multiplication. It lies in `Div(Δ)`: `Δ(τ) = δ_τρ = α·((id ⊔ [u,τ])ρ)`.
  - Pigeonhole is over `|𝒯(*)|` classes.
- **(U4).** A cycle gives `U_0 = σU_0` with `σ` a non-unit, by left cancellation. The height
  increments are those of the trivial-unit case.
- **(U5).** The unit groups are finite.
- **Items 2–4.** The product of effective groupoids is effective, since an open subset of the
  isotropy contains a product of open bisections. Uniqueness of the bisection `β_g` under
  effectiveness makes `g ↦ β_g` a homomorphism. The prefix-code wreath and Krasner–Kaloujnine
  are correct.

No gap found. The Euclidean-building application added in 37f53166d2 is outside this review.

## Referee (bh-ref-q11, 2026-09-19): PASS (second referee of the finite-unit steps)

(U1)–(U5) and items 2–4 check; the details are in the Referee section of `cubulated-groups-embed-in-f-infinity-simple-groups`.
- One addition to (U1): `𝔠*𝔖 ⊆ 𝔖^♯` is automatic, because `𝔖^♯` is closed under right divisors and `εs` right-divides `s`. So no hypothesis is needed for units to carry pure holes to pure holes.
- I agree with bh-ref-q115-b's credit correction.
- The Euclidean-building application is outside this review.
