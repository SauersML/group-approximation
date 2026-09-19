---
rg: 2
id: hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs
kind: claim
title: A hyperbolic right-angled Coxeter group whose nerve L has at least three vertices, a connected complement graph, and no simplex whose vertex stars cover L is isomorphic to a contracting RSG, and so is every group commensurable with it
distinct_from:
  greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs: that is the conditional theorem for any cocompact cubulation, with (NA) and (IRR) as hypotheses; this proves (NA) for every hyperbolic RACG and reduces (IRR) to three conditions on the nerve.
  right-angled-reflection-groups-in-h3-are-contracting-rsgs: that is the case where L is the boundary of the dual of a compact right-angled polyhedron in H³ (dodecahedron, Löbell L(n)); this covers every hyperbolic RACG with a spread nerve, in every dimension.
  closed-surface-groups-are-contracting-rsgs: that proves the surface case through the Bowen–Series map; the right-angled n-gon groups, n ≥ 5, are instances here, so this gives a second, Bowen–Series-free proof for every closed surface group.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this answers it for every group commensurable with a hyperbolic RACG with a spread nerve.
---

**ESTABLISHED** by `hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof` (lane `bh-partials`, 2026-09-19; lane
proof, **not reviewed**; no priority claimed).

## Statement

Let `L` be a finite flag simplicial complex with vertex set `S`, and `W = W_L` the right-angled Coxeter group
`⟨S | s², (st)² for {s,t} an edge of L⟩`. Let `𝒩` be the complement graph on `S` (join `s ≠ t` when they are not
adjacent in `L`), and `St(s)` the set of vertices adjacent or equal to `s`.

Assume:
- **(H)** `W` is hyperbolic, i.e. `L` has no induced 4-cycle (Moussong; recalled);
- **(0)** `|S| ≥ 3`;
- **(a) spread:** for every simplex `σ` of `L`, `S ≠ ⋃_{s∈σ} St(s)`;
- **(b)** `𝒩` is connected.

Then:
1. `W` is isomorphic to a contracting RSG. The coding space is the Roller boundary of its Davis cube complex. The states
   are the nonempty simplices of `L`, and `σ → τ` exactly when `s_0 = min σ ∉ τ` and `τ ∩ lk(s_0) = σ ∖ {s_0}`.
2. Every finite-index subgroup of `W`, and every group commensurable with `W`, is isomorphic to a contracting RSG.
   (Corrected 2026-09-19: the first version also assumed an odd cycle **(c)** in `𝒩`. That condition is automatic, by an
   odd loop through an edge simplex; see `contracting-rsgs-pass-to-finite-index-subgroups-via-loops`.)

(a) and (0) imply that `W` is non-elementary with trivial finite radical.

## Instances

- **Right-angled `n`-gon groups, `n ≥ 5`** (`L = C_n`).
  - (a): the stars of an edge `{i, i+1}` are `{i−1, …, i+2}`.
  - (b): the complement of `C_n` is connected.
  - Every closed hyperbolic surface group is commensurable with the pentagon group, so this reproves
    `closed-surface-groups-are-contracting-rsgs`.
- **Compact right-angled polyhedra in H³**, with `L` the dual of the face structure. The dodecahedron and the Löbell
  polyhedra `L(n)`, `n ≥ 5` (two `n`-gons and `2n` pentagons) are checked in
  `right-angled-reflection-groups-in-h3-are-contracting-rsgs`. So is every group commensurable with them, including
  closed hyperbolic 3-manifold groups.
- **Higher dimensions.** Any flag no-square triangulation satisfying (a)–(b), for example the nerves of compact
  right-angled polytopes in H⁴. Such polytopes exist (the 120-cell); the check was not done here.

## What remains of Question 1.1

- **Covered.** Hyperbolic groups commensurable with RACGs that have spread nerves. That includes surface
  groups and the 3-manifold groups commensurable with the reflection groups of the right-angled dodecahedron and the
  Löbell polyhedra.
- **Not covered.**
  - Hyperbolic groups that are only virtually special, i.e. only quasiconvex subgroups of RACGs. This includes most
    closed hyperbolic 3-manifold groups (Agol). For their own cubulations, (NA) and (IRR) of
    `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs` are open.
  - Kazhdan hyperbolic groups, which have no cubulation.

## Lesson for general BH

- **Coxeter structure gives (NA) for free.** Two disjoint walls with an infinite common stabilizer would give an
  infinite-order element commuting with the product of the two reflections. In a hyperbolic group that product must
  then share a power with the element, which is impossible because the product translates the walls.
- **The rest is a finite check on the nerve.** Irreducibility of the greedy coding is (a) + (b), and coset refinement for
  subgroups is automatic, since an odd loop through an edge simplex kills the parity.
- **Where this leaves Question 1.1 for cubulated groups.** Transferring the result along Haglund–Wise's embedding of a
  virtually special group into a RACG is exactly what fails, because being a contracting RSG passes to overgroups of
  finite index, not to subgroups. That transfer is now the precise gap for cubulated hyperbolic groups.
