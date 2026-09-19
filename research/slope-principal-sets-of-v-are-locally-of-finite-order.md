---
rg: 2
id: slope-principal-sets-of-v-are-locally-of-finite-order
kind: claim
title: For a subgroup of Thompson's group V, every element has a power that is the identity on a neighbourhood of any slope-principal closed invariant set, and this fails in 2V for the baker map
distinct_from:
  slope-principal-minimal-sets-of-nv-subgroups-carry-measures: that asks for an invariant measure on a slope-principal minimal set of a subgroup of nV; this proves a torsion rigidity statement about the elements, for n = 1 only, and gives no measure.
  nv-point-germ-groups-embed-in-zn-by-slope: that is pointwise, about germs at a fixed point and about one canonical self-compression; this is a statement about whole orbits, proved from it by an itinerary and a recurrence argument, and it is false for n >= 2.
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that assumes the element is conjugate to a proper power of itself and concludes that its periodic set is open in C^n; this assumes only that the fixed points inside one closed invariant set have zero slope, concludes that the set consists of periodic points, and holds only for n = 1.
  minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal: that is the open Kazhdan half, asserting slope-principality; this takes slope-principality as a hypothesis and draws a torsion consequence from it.
artifacts:
  - research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md
  - research/artifacts/slope-principal-v-locally-finite-order-attempt-2026-09-18.md
---

Notation as in Section 0 of `research/artifacts/kazhdan-nv-measure-criterion-2026-09-17.md`:
bricks `[v] ⊆ C^n`, canonical charts, `g` canonical on a brick, the slope cocycle
`s(g,x) = |w| - |w'| ∈ Z^n`. A closed `G`-invariant `Z ⊆ C^n` is **slope-principal** if
`s(g,z) = 0` whenever `g ∈ G`, `z ∈ Z` and `gz = z`.

**OPEN** (demoted 2026-09-18 at landing: two of three referee lenses refuted the
node as first written — Theorem B asserted that `S × C` is `b`-invariant, which is
false for every aperiodic minimal subshift `S`, and the Zorn step of Theorem B was
applied to that set. The repair recommended by both lenses has been applied below and
to the route, but has not itself been refereed. Theorem A was found sound by all three
lenses. See Attempts.) There is no route into this claim; the proof is kept as the
attempt artifact
`research/artifacts/slope-principal-v-locally-finite-order-attempt-2026-09-18.md`.
The only intended graph input is `nv-point-germ-groups-embed-in-zn-by-slope`, items 1
and 4; no external import beyond the two standard facts named in Corollary 2.

**Theorem A (`n = 1`).** Let `G <= V` and let `Z ⊆ C` be a nonempty closed
`G`-invariant slope-principal set. Then for every `g ∈ G` there are `q >= 1` and a
clopen `W ⊇ Z` with `g^q|_W = id`. In particular every point of `Z` is a periodic point
of `g`, and the restriction `G|_Z` is a torsion group.

**Theorem B (`n >= 2`).** Theorem A fails for `n >= 2`. Brin's baker map `b ∈ 2V`,
`b(0w,y) = (w,0y)`, `b(1w,y) = (w,1y)`, has constant slope `(1,-1)` and countable
periodic set. For any aperiodic minimal subshift `S ⊆ C`, the set `S × C` is closed and
only **forward** `b`-invariant (`b(S × C) ⊊ S × C`; genuine invariance would force `S`
to be the full shift). Take instead its maximal invariant subset
`Y = ⋂_{k >= 0} b^k(S × C)`, a nested intersection of nonempty compacta: `Y` is nonempty,
closed, satisfies `b(Y) = Y`, and contains no periodic point of `b`. Concretely
`Y = {(u,v) : (v_k…v_1)u ∈ S for all k >= 0}`, the natural extension of `(S,σ)`; under
`(u,v) ↦ …v_2v_1.u_1u_2…` the map `b` is the two-sided shift and `Y` the two-sided
subshift of `S`. Every `⟨b⟩`-minimal subset `M` of `Y` is slope-principal for `⟨b⟩`
vacuously, while `b|_M` has infinite order.

**Corollaries of Theorem A.**
1. The germ groupoid of `G` on a slope-principal `Z ⊆ C` is principal and is generated
   by bisections of finite order, and `Σ_{j<q} s(g, g^j z) = 0` for all `z ∈ Z`.
2. If a minimal slope-principal `Z ⊆ C` carries no `G`-invariant probability measure,
   then `G|_Z` is non-amenable, hence not locally finite, so some finitely generated
   `H <= G` has infinite torsion image `H|_Z`, a quotient of a free product of finite
   cyclic groups. So the `n = 1` case of
   `slope-principal-minimal-sets-of-nv-subgroups-carry-measures` is equivalent to the
   Burnside-type claim `locally-torsion-subgroups-of-v-have-measured-minimal-sets`.

**What this says about the split.** The route
`kazhdan-nv-measured-minimal-sets-via-slope-principality` puts all of property (T) into
`minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal` and calls the other half
`(T)`-free. Corollary 2 shows the `(T)`-free half is not the cheap half: at `n = 1`,
where the flagship statement is already known through `thompson-v-has-haagerup-property`,
that half implies a Burnside-type theorem about germ groups of `V`. Theorem B shows the
`n = 1` mechanism cannot be transported: for `n >= 2` a slope-principal minimal set can
carry infinite-order elements with no periodic points in it at all, so the germ
trichotomy of `nv-point-germ-groups-embed-in-zn-by-slope` is vacuous there.

**Correction to a recorded failure mode.** The bullet "a free group whose minimal set
has only saddle fixed points" in
`research/slope-principal-minimal-sets-of-nv-subgroups-carry-measures.md` is not a way
the claim can fail: a saddle fixed point has `s ≠ 0`, so a minimal set containing one is
not slope-principal. After Theorem A the surviving shapes of a counterexample are listed
in Section 5 of the artifact.

## Attempts

- 2026-09-18 (lane `e2-w2-nv-kazhdan-halves`, wave `swarm-0917`, symbolic-dynamics,
  inverter). Node created with a direct-proof route; **demoted to OPEN at landing**
  because two of three referee lenses refuted it. The proof is kept as the attempt
  artifact `research/artifacts/slope-principal-v-locally-finite-order-attempt-2026-09-18.md`
  (Steps 0-4) together with
  `research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md`.
  - **What was refuted (lenses 1 and 3, independently and in the same place).** Step 4
    (Theorem B) asserted "`S × C` is closed, `b`-invariant (`σS = S`)". That is false,
    and false for *every* aperiodic minimal `S`, not for a bad choice. With
    `b(x,y) = (σx, x_1y)` one has
    `b(S × C) = {x : 0x ∈ S} × [0] ∪ {x : 1x ∈ S} × [1]`, so `b(S × C) = S × C` would
    force every point of `S` to admit both left extensions inside `S`, hence
    `|L_{n+1}| = 2|L_n|`, entropy `log 2`, i.e. `S` the full shift — never aperiodic
    minimal. Explicitly, in the Fibonacci subshift `11` is not a factor, so for `u ∈ S`
    beginning with `1` the point `(u,1y) ∈ S × C` has `b^{-1}(u,1y) = (1u,y) ∉ S × C`.
    `σS = S` gives only forward invariance. Two things broke: the stated Theorem B was
    literally false, and "a `⟨b⟩`-minimal `M ⊆ S × C` exists by Zorn" had no starting
    element, since the poset is that of nonempty closed `K` with `b(K) = K`.
  - **Repair applied (recommended verbatim by both refuting lenses; not refereed).**
    Replace `S × C` by its maximal invariant subset `Y = ⋂_{k >= 0} b^k(S × C)`, a nested
    intersection of nonempty compacta with `b(Y) = Y`; equivalently the natural extension
    `{(u,v) : (v_k…v_1)u ∈ S for all k}`, on which `b` is conjugate to the two-sided shift
    of the two-sided subshift of `S`. The *conclusion* of Theorem B, the class-kill at
    `n >= 2` and the dimension split are untouched by the correction. The correction has
    been made here, in the attempt artifact, in
    `research/artifacts/slope-principal-torsion-rigidity-2026-09-18.md` Section 4, and in
    `slope-principal-minimal-sets-carry-measures-for-n-at-least-2`.
  - **What survived all three lenses.** Theorem A in full: Step 0's induction
    (sub-brick rule, `F_{t+1} = g(F_t) ∩ B_{i_{t+1}}`, `s(g^t,x) = |E_t| - |F_t|`);
    Step 1's recurrence and its three exhaustive sign cases at `n = 1`, including the
    cocycle flip `s(g^τ,p) = -s(g^{-τ},p)` at a fixed point; Step 2's pigeonhole over the
    `N` table cones and the canonical self-compression of `B_i`; Step 3's relative
    openness of `P_Z`, the inheritance of slope-principality by `Z \ P_Z` (only
    `⟨g⟩`-invariance is used, so its non-`G`-invariance is harmless) and the
    lcm/compactness assembly; and Corollary 2's equivalence with
    `locally-torsion-subgroups-of-v-have-measured-minimal-sets` in both directions.
    Lens 2 (hypotheses and citations) recorded *survives*: both uses of item 4 and the
    use of item 1 of `nv-point-germ-groups-embed-in-zn-by-slope` match the source
    quantifiers exactly, and the group hypothesis on `Z` is genuinely consumed (item 4
    is applied to `g^{-τ}` and to `h^{-1}`, so forward invariance alone would not do).
  - **Calibration probes reported by lens 3, all passed.** The dyadic odometer in
    `Aut(T_2)` has zero slope, no periodic points and infinite order, so Theorem A's
    conclusion is false there; the proof does use what separates `V`, namely the finite
    table (Step 0) and the pigeonhole over its `N` cones (Step 2), which is exactly the
    step that dies for an automaton with no finite table.
  - **Residual nits, none load-bearing.** Corollary 2 uses "amenable ⇒ invariant measure
    on a compact space" and "locally finite ⇒ amenable", declared as standard facts, so
    the earlier "no external import" tag was too strong; Theorem B needs the existence
    of an aperiodic minimal subshift (Fibonacci/Sturmian), named but not formally cited;
    Step 1 should read `τ >= max(T,1)` rather than `τ >= T`, which recurrence supplies.
  - **To restore.** Re-referee the corrected Theorem B and re-create the direct-proof
    route from the attempt artifact.
