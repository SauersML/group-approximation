---
rg: 2
id: greedy-cube-codings-rsg-proof
kind: route
title: Pairwise crossing of separating hyperplanes at a vertex gives the Markov property; free action gives canonical similarities in G; gates to carriers give heights, and (NA) makes carrier entry uniform, so the surface-case Lemmas A–E give a finite nucleus
target: greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
requires:
  - closed-surface-groups-contracting-rsg-via-bowen-series
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-partials`, lane proof, not reviewed.

**Notation.**
- For a vertex `x` and `ω ∈ ∂X`, `S(x,ω)` is the set of edges at `x` whose hyperplanes separate `x` from `ω`.
- `H^±` are the halfspaces of a hyperplane `H`, and `N(H)` is its carrier.
- Distances are combinatorial: the number of separating hyperplanes.

**Step 1 (Markov, no hypothesis).**
- **The quarter lemma.** Let `H, L` be distinct hyperplanes dual to edges at `x`, not crossing, with `x ∈ H^-∩L^-`.
  The neighbours of `x` across `H` and across `L` lie in `H^+∩L^-` and `H^-∩L^+`. So the empty quarter is `H^+∩L^+`.
- **Consequences.**
  - The hyperplanes of `S(x,ω)` pairwise cross, since an ultrafilter picks pairwise intersecting halfspaces; this is
    Niblo–Reeves.
  - If `ω ∈ H^+`, every edge at `x` whose hyperplane does not cross `H` lies outside `S(x,ω)`.
- **The greedy step.** Let `e = min S(x,ω)` with hyperplane `H`, and let `x_1` be the far end of `e`. The edges at `x`
  crossing `H` span squares with `e`, so they correspond to edges at `x_1` with the same hyperplanes.
- **So the image of a piece is a union of pieces.**
  `{ω : S(x,ω) = S} = ⋃ { {ω : S(x_1,ω) = S'} : e^{-1} ∉ S', S' ∩ cross(H) = S∖{e} }`.
  The edges at `x_1` not coming from `x` are free.
- **Translating back.** Translating by the unique `g` with `g x_1 = rep(x_1)` (the action is free) gives the state
  graph `𝒢`, and the map is injective on each piece.
- **Nonempty.** Cylinders are `u_w(piece)`, with `u_w ∈ G` the unique element carrying the representative to the end
  vertex. So they are nonempty whenever the word is admissible.

**Step 2 (RSG).** Cylinders with the same end state `(r,S)` are `u_w(A_{r,S})` and `u_{w'}(A_{r,S})`, and
`u_{w'}u_w^{-1} ∈ G` is the canonical similarity between them.

**Step 3 (under (NA): coding homeomorphism and finite nucleus).**
- **Lemma A.** Greedy paths cross only hyperplanes separating the current vertex from `ω`, and never recross. So they
  are geodesic, and they converge to the Gromov image `ζ(ω)`, since `X` is quasi-isometric to `G`.
- **Lemma C.**
  - *Heights.* Let `H` be a hyperplane with `ζ ∈ Λ(H)`, or with the target in `H^+`. The height of a vertex `y` on the
    `H^-` side is `d(y, N(H))`, which counts the hyperplanes separating `y` from `N(H)` (gate property). None of these
    crosses `H`.
  - *They are crossed.* By (NA) their limit sets miss `Λ(H)`, so they separate `y` from the target and are crossed
    eventually. Hyperplanes not separating `y` from `N(H)` and disjoint from `H` are never crossed, by the quarter lemma.
    So the height decreases to 0, and the ray enters `N(H)`.
  - *Uniform time.* A geodesic from near the quasiconvex `N(H)` to a point of `Λ(H)` or of `H^+` stays near `N(H)` until
    it reaches it. By (NA) each separating `K` diverges from `N(H)`, and cocompactness bounds the region beyond `K`
    near `N(H)`. So the entry time is within `K_1` for `c_1`-close rays.
- **Injectivity.**
  - Ultrafilters with different `ζ` are separated by Lemma A.
  - Ultrafilters with the same `ζ` differ on a hyperplane `H` with `ζ ∈ Λ(H)`. By (NA) the sides of the other
    hyperplanes are determined by `ζ`. The common ray enters `N(H)`, where the state records the side of `H`.
  - Continuity, surjectivity and equivariance are as in `right-angled-h3-reflection-rsg-via-greedy-roller-coding`,
    Step 2.
- **Lemmas D and E** of `closed-surface-groups-contracting-rsg-via-bowen-series` apply verbatim, with hyperplanes for
  walls and edges for faces. They bound `d(x_0, k x_0)` for the local actions `k = u_v^{-1} h u_w` uniformly, so the
  nucleus is finite.

**Step 4 (with (IRR)).** A single recurrent component is an irreducible core
(`sft-irreducible-core-iff-unique-recurrent-component`). With Steps 2–3 this makes `G` a contracting RSG. ∎

**For the referee.**
- The uniform-time claim in Lemma C, which uses quasiconvexity of carriers, (NA) and cocompactness.
- Whether the fibres of `∂X → ∂G` over points of several limit sets are handled by the state records of successive
  carriers.
