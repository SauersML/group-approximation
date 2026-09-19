---
rg: 2
id: f-dyadic-orbit-geometry-cannot-force-extensive-amenability
kind: claim
title: A transitive amenable action on the dyadic rationals with the same orbit metric as Thompson's F, up to bi-Lipschitz identity, is not extensively amenable, so no coarse-geometric or wobbling criterion can prove extensive amenability of F on the dyadics, and the gate is order preservation
distinct_from:
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open confinement hole, equivalent to the root; this kills every proof of it that uses only the bi-Lipschitz class of the orbital graph of F on D, and it leaves the hole OPEN.
  thompson-f-dyadic-action-is-extensively-amenable: that is extensive amenability of F on D, open; this shows that the Schreier graph of F on D, up to bi-Lipschitz bijection, also carries a transitive amenable action that is not extensively amenable.
  lodha-moore-breakpoint-orbit-is-hereditarily-amenable-not-ea: that calibrator is a piecewise projective group on Q sharing germ and finiteness data with F; this calibrator shares the orbit metric itself (bi-Lipschitz via the identity of D) and is built inside the wobbling group, so it kills a different class (geometry of the orbit, not local germ data).
  pl-ea-calibrators-are-nonamenable-interval-groups: that shows a PL counter-calibration exists iff PL_+([0,1]) has a nonamenable subgroup; this finds a non-PL calibrator with the same orbit geometry and proves that every order-preserving bounded-displacement calibrator lies in PL_+([0,1]), which puts it back under that dichotomy.
  f-dyadic-action-is-not-recurrent: that shows the Schreier graph of F on D is not recurrent, so the recurrence criterion does not apply; this shows no criterion that sees only the graph up to bi-Lipschitz equivalence can apply.
  thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs: that bars recurrent wobbling hosts for F; this shows that the wobbling group of the dyadic Schreier graph of F itself does not act extensively amenably.
artifacts:
  - experiments/f-dyadic-wobbling-calibrator-2026-09-17/wobbling_tree.py
---

**ESTABLISHED** through `f-dyadic-orbit-geometry-cannot-force-ea-proof`. It has
not been independently reviewed. The only imports are Definition 1.1 and Lemma 2.1 of
Juschenko–Matte Bon–Monod–de la Salle, the inverted-orbit proposition of the same paper, and Brin–Squier.
All of them are already graph nodes.

**Setting.**
- `D` is the set of dyadic rationals in `(0,1)`.
- `Γ_D` is the Schreier graph of `F = ⟨x_0, x_1⟩` acting on `D`, with edges `t — x_i^{±1} t`, and `d` is
  its path metric.
- For a binary word `w`, `.w` is the dyadic `Σ_i w_i 2^{-i}`.
- The blocks are `A = 01`, `B = 011`, `C = 0111`. A block word `u = c_1 ⋯ c_k` is *reduced* if no two
  adjacent blocks are equal.
- `φ(u) = .u1` (the concatenated blocks followed by `1`), and `Y = {φ(u) : u reduced}`. Then
  `φ(∅) = 1/2` and `Y ⊂ [1/4, 1/2]`.
- `Γ = Z/2 * Z/2 * Z/2 = ⟨s_A, s_B, s_C⟩` is a nonamenable group; it contains a free subgroup of rank 2.
- For `c ∈ {A, B, C}` the involution `σ_c` of `D` is the identity off `Y`, and on `Y` it is
  `φ(c u') ↦ φ(u')` and `φ(u) ↦ φ(c u)` when `u` does not begin with `c`.
- `G = ⟨x_0, x_1, σ_A, σ_B, σ_C⟩ ≤ Sym(D)`.
- The wobbling group `W(Γ_D)` is the group of bijections `h` of `D` with `sup_t d(t, h t) < ∞`.
  `W^+(Γ_D)` is its subgroup of order-preserving elements.

1. **Free tree inside the orbit.** `φ` is injective. `u ↦ φ(u)` is a Lipschitz map from the 3-regular
   tree (the Cayley graph of `Γ`) into `Γ_D`: `d(φ(u), φ(c u)) ≤ L` for every reduced `u` and
   every `c` with `cu` reduced. Here `L` is the maximum of the word lengths of six explicit elements of
   `F`, one for each edge type `c' → cc'`, and of the three root distances `d(1/2, φ(c))`. The
   distances actually realised, measured by exact BFS, are at most 9.
2. **The calibrator.** `G ≤ W(Γ_D)`. The identity of `D` is a bi-Lipschitz bijection, with constants
   `1` and `L`, from `Γ_D` to the Schreier graph of `G` with respect to `{x_0^{±1}, x_1^{±1}, σ_A, σ_B, σ_C}`.
   `G ↷ D` is transitive and amenable, but **not extensively amenable**.
3. **Class kill.** Let `P` be any property of transitive actions of finitely generated groups that depends
   only on the Schreier graph up to bi-Lipschitz bijection of the vertex sets. Quasi-isometry invariance
   is enough. If `P` implies extensive amenability, then `F ↷ D` does not have `P`. In particular:
   - (a) `W(Γ_D) ↷ D`, and any group of bounded-displacement permutations of `D` that contains `G`, is
     not extensively amenable. The Juschenko–Monod pattern (prove that the wobbling group or a full
     group acts extensively amenably, then restrict to `F`) cannot work on `Γ_D` when pieces may be
     arbitrary. Recurrence of a host graph is already excluded by `f-dyadic-action-is-not-recurrent`.
   - (b) This rules out every criterion whose hypothesis is a bi-Lipschitz invariant of `Γ_D`, up to
     constants: recurrence, growth, resistance growth, isoperimetric or Følner profile,
     return-probability decay class. Any such criterion would also apply to `G ↷ D`. The Liouville
     property is not a rough-isometry invariant and is not covered.
   - (c) For the walk `μ_G` that is uniform on `{x_0^{±1}, x_1^{±1}, σ_A, σ_B, σ_C}`, the inverted
     orbit fails the hole's statement: there is `ε > 0` with `P(|O_n| < ε n) ≤ e^{−ε n}` for all large
     `n`, and `−(1/n) log E 2^{−|O_n|}` does not tend to `0`. The walk on `G` has the same orbit geometry
     and the same `x_0`, `x_1` steps as a walk on `F`. So exactly the hole's rare-event confinement
     fails there.
4. **Order gate.** Every `h ∈ W^+(Γ_D)` extends to a homeomorphism of `[0,1]` that agrees, on each of
   finitely many intervals, with a single element of the finite ball `B_F(R)`, where
   `R = sup_t d(t, h t)`. So `W^+(Γ_D) ≤ PL_+([0,1])`, and `W^+(Γ_D)` has no non-abelian free subgroup
   (`pl-plus-interval-has-no-non-abelian-free-subgroups`).
   If `H ≤ W^+(Γ_D)` acts transitively on `D` but not extensively amenably, then `H` is a nonamenable
   subgroup of `PL_+([0,1])`. This is alternative (b) of item 4 of
   `pl-ea-calibrators-are-nonamenable-interval-groups`. So an order-preserving calibrator of the type in
   item 2 is at least as hard to build as a nonamenable subgroup of `PL_+([0,1])`.
   The σ's are unavoidable: `G` is not order-preserving, and it contains the free group of `Γ`.

**Precise obstruction.** The invariant is the orbital graph `Γ_D` up to bi-Lipschitz equivalence. Its
coarse class is shared by `F ↷ D` and `G ↷ D`. The dying step is any implication of the form "orbit
graph of `F` in class `C` ⇒ `F ↷ D` is extensively amenable". Such an implication would make `G ↷ D`
extensively amenable, which is false by item 2.

What survives is data invisible to coarse geometry. By item 4, the cheapest such datum is that the
acting maps preserve the order of `D`. So any proof of the hole must use that `F` acts by
homeomorphisms, or finer structure (PL germs, relations of `F`). Inside the order-preserving world the
question becomes the known PL dichotomy.

**Scope.** The hole `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` and the root stay OPEN.
Item 2 is a new calibrator, and items 3–4 are the class kill and the gate. The construction is the
standard way a free tree is planted inside a nonamenable orbit. What is new is that it fits inside the
bounded-displacement group of the dyadic orbit of `F` and keeps the action amenable.
