# Ideas lane: growth and hyperbolic roots (2026-09-14)

Targets:
- `fp-group-of-intermediate-growth-exists`;
- `non-residually-finite-hyperbolic-group`;
- `nonsofic-hyperbolic-group`;
- `one-ended-hyperbolic-groups-contain-surface-subgroups`.

Every idea below names the smallest decisive test and a kill criterion. "Not on main" means we
grepped `origin/main:research` for the idea's key terms and read the root's attempt list. It does
not mean the idea is absent from the literature.

## Ideas

**S1. Girth surfaces in GHB_2(7).**
- *Idea.* By CCKW Theorem 3.1(i), `G = G_{HB_2}(7)` acts simply transitively on the chambers of a
  CAT(−1) complex `Y` built from (3,4,4) triangles. Its vertex links are coset graphs of girth
  6, 8, 8. Glue `T` hyperbolic (3,4,4) triangles into a closed surface in which every vertex has
  exactly girth-many triangles. Label each side by a nontrivial element of its edge group, and ask
  that the word around every vertex be trivial in its vertex group. Every link walk is then a
  girth cycle, so the developing map is a local isometry into `Y`. Hence `π_1(S)` embeds as a
  quasiconvex surface subgroup.
- *Not on main.* The root lists Kahn–Markovic, Calegari–Walker, Wilton and Kahn–Labourie–Mozes
  coverage; none covers a non-Lie Kazhdan hyperbolic group. `git grep` finds no periodic-plane
  or building surface argument. The closest literature is Kangaslampi–Vdovina (arXiv:1409.1401),
  whose computer search found no genus-2 periodic apartments for most of 23 torsion-free
  triangular-building lattices. Kangaslampi (arXiv:1410.4655) found surface subgroups in 3 of
  the 23 by another method. Neither treats GHB_2(7), whose links are not generalized polygons.
- *Smallest decisive test.* Enumerate every girth surface with `T = 24` (genus 2 when
  orientable), then solve the label CSP exactly.
- *Kill.* No labelling on any `T = 24` surface, together with a heuristic count showing larger `T`
  is out of reach. That would give a calibrated barrier, not nonexistence.
- *Verdict.* PROMISING. Executed below.

**S2. Torus-twisted orbifold planes.**
- *Idea.* The scalings `a ↦ a^s, b ↦ b^t, c ↦ c^u` with `(s,t,u) ∈ (F_7^×)^3` preserve every
  vertex relator: they are torus actions on U_3(7) and U_4(7). So `G ⋊ (F_7^×)^3` acts on `Y`.
  Look for girth planes with orbifold symmetry, which shrinks the CSP by the symmetry order.
- *Not on main.* No node uses automorphisms of GHB_2(7).
- *Quick kill.* There is no order-4 rotation about a type-1 or type-2 vertex. If
  `(g,h)^4 = 1` with `h` in a group of exponent 6, then `h^2 = 1`, so `(g,h)^2 = (g h(g), 1)` lies
  in a 7-group and has order ≤ 2, hence is trivial. Reflections in both sides at a type-0 vertex
  are impossible too: a product of two involutions of the abelian torus has order ≤ 2, but an
  order-3 rotation needs a torus part of order 3. What survives is the sphere with four order-3
  cone points, of index 4 in `Δ⁺(3,4,4)`. Its torsion-free index-3 subgroup gives genus-2 surfaces
  with `T = 24`, so S1's exhaustive search already covers it.
- *Verdict.* ALIVE, as an accelerator for `T ≥ 72` only.

**S3. Cone-angle ≥ 2π surfaces.**
- *Idea.* Allow vertex degree `2k > 2m_i`, provided link points at circle distance `≥ π` have link
  distance `≥ π`. The same proof still gives a local isometry.
- *Quick kill.* The links are small. In the type-0 link (49 + 49 vertices, degree 7, girth 6),
  43 of the 49 same-type vertices lie within distance 2 of a given one. So every antipodal pair on
  an 8-walk is rejected with probability about 7/8. In the type-1 link, 259 of 343 opposite-type
  vertices lie within distance 3. The expected number of solutions per corner is strictly worse
  than for girth surfaces.
- *Verdict.* DEAD as a search strategy. The theorem generalizes; the search does not improve.

**S4. Arithmetic uniform lattices in SO(2n,1) via totally geodesic 3-manifolds.**
- *Idea.* The root lists all uniform lattices in `SO(2n,1)` as uncovered. In even dimension every
  arithmetic lattice is expected to be of simplest type. Restricting the anisotropic form to a
  rational 4-dimensional subspace would give a cocompact totally geodesic hyperbolic
  3-manifold subgroup, and Kahn–Markovic then gives a surface subgroup.
- *Not on main.* `git grep "totally geodesic"` finds no surface-subgroup use.
- *Test.* Source-check (a) that simplest type is the only arithmetic type in even dimension and
  (b) that the restricted form stays anisotropic.
- *Kill.* Either fact fails at source.
- *Verdict.* PROMISING as cheap coverage, but only for arithmetic lattices. Not executed here;
  it is a literature task.

**S5. Bounded-folding SAT search for one atoroidal `φ ∈ Out(F_3)`.**
- *Idea.* By `automorphism-immersion-representatives-have-finite-order`, only the bounded-folding
  criterion of arXiv:1212.2618 remains for hyperbolic free-by-cyclic groups. Encode "boundedly
  `f`-folded fatgraph of size ≤ N" as a SAT instance.
- *Test.* One rose representative with `N ≤ 12`.
- *Kill.* UNSAT up to `N = 12` for three representatives.
- *Verdict.* ALIVE. It needs a new encoder and was not started.

**R1. Quasiconvex non-separability through S1.**
- *Idea.* Residual finiteness of all hyperbolic groups is known to force separability of
  quasiconvex subgroups. That is a Dehn-filling theorem of Agol–Groves–Manning, not source-checked
  in this lane; main cites these authors only for cubulation. A girth surface subgroup
  `Σ ≤ GHB_2(7)` is a concrete quasiconvex subgroup to test.
- *Test.* Compute `ψ(Σ) ≤ Sp_4(F_7)`.
- *Kill.* A finite computation can only exhibit separating quotients, never non-separability.
- *Verdict.* DEAD as a decisive route; it yields evidence only.

**R2. Orbit-cycle indices evaluated on girth surfaces.**
- *Idea.* By `ghb7-centre-survival-iff-unbounded-orbit-cycle-indices`, centre survival is decided
  by whether `sup_N m_ω(N)` is infinite. A girth surface supplies integer 2-cycles in every `N\Y`,
  so it might bound `m_ω(N)`.
- *Quick kill.* Let `S_N = φ^{-1}(N)\S̃`. It maps to `N\Y`, and its class pushes forward to
  `d_N · [S_K → K\Y]` with `d_N = [φ^{-1}K : φ^{-1}N]`. So the surface gives only
  `m_ω(N) | d_N · ω(S_K)`, and `d_N` is unbounded as `N` shrinks. A uniform bound would need, for
  each `N`, a girth surface with group inside `N` and bounded `ω`-value. That is a separability-type
  statement, not a finite test.
- *Verdict.* DEAD as a decisive route. The first landed version of this artifact claimed the bound
  `m_ω(N) ≤ |ω(S)|`; that claim was wrong and is withdrawn.

**R3. Deligne-type finite central extensions of hyperbolic groups.**
- *Quick kill.* A finite central extension of a hyperbolic group is hyperbolic. So a non-residually
  finite one is itself a non-RF hyperbolic group, and the idea is circular.
- *Verdict.* DEAD.

**R4. Kac–Moody lattices above GHB_2(7).**
- *Idea.* The KMS group maps to a Kac–Moody group over `F_7`, whose lattices are simple and not
  residually finite.
- *Quick kill.* Those lattices are irreducible lattices in a product of two buildings. They
  contain quasi-flats, so they are not hyperbolic.
- *Verdict.* DEAD.

**N1. Nonsoficity from a stable hyperbolic group with a non-RF finite central extension.**
- *Quick kill.* That extension is hyperbolic and not residually finite, so the route reduces to
  `non-residually-finite-hyperbolic-group` plus stability. The circularity is the same as in R3.
- *Verdict.* DEAD.

**N2. Sofic-profile obstruction from girth surfaces.**
- *Idea.* Sofic approximations of `G` restricted to `Σ` are approximations of a surface group.
  Surface groups are LEF, which rules out any obstruction coming from `Σ` alone.
- *Verdict.* DEAD.

**G1. Presentable quotients of the Lysenok HNN extension.**
- *Idea.* `grigorchuk-hnn-extension-is-fp-amenable-non-ea` gives a finitely presented
  `G_L = <𝔊, t | t g t^{-1} = σ(g)>`. Look for finitely presented quotients `Q` of intermediate
  growth.
- *Quick kill.* Let `Q` be a finitely presented quotient of `G_L` and `N` the image of 𝔊. Since 𝔊
  is just-infinite (`grigorchuk-group-is-just-infinite-torsion-not-fp`), `N` is finite or `N ≅ 𝔊`.
  Let `M = ∪_k t^{-k} N t^k`, the normal closure of `N` (the union ascends because `tNt^{-1} ≤ N`).
  - If `t` has finite order `n` modulo `M`, then `t^n ∈ t^{-K} N t^K =: N'` for some `K`. So `t^n`
    normalizes `N'`, the union stabilizes, and `M = N' ≅ N` has finite index in `Q`. If `N ≅ 𝔊`,
    then 𝔊 is finitely presented, which is false. Otherwise `Q` is finite.
  - If `Q/M ≅ Z` and `Q` has intermediate growth, then `M` is finitely generated
    (`intermediate-growth-z-quotient-kernels-fg-intermediate`). The union stabilizes, so `M` is a
    conjugate of `N` and `N` is normal in `Q`. `N ≅ 𝔊` contradicts
    `grigorchuk-group-is-a-normal-subgroup-of-no-fp-group`; `N` finite makes `Q` virtually cyclic.

  So no finitely presented quotient of `G_L` has intermediate growth.
- *Verdict.* DEAD.

**G2. Growth truncations of branch groups.**
- *Idea.* `fp-intermediate-growth-iff-subexponential-truncation` asks for a finitely generated
  `Q` of intermediate growth and an `n` with `P_n(Q)` subexponential. Take `Q = G_ω` and test
  `P_n(G_ω)` for a free subsemigroup at small `n`.
- *Quick kill.* `P_n(G_ω)` is a finitely presented cover of `G_ω`. By
  `fp-covers-of-grigorchuk-groups-are-large` such covers are large, so they have exponential growth.
- *Verdict.* DEAD for every `G_ω` covered by that node. The truncation criterion needs a `Q`
  outside the Grigorchuk families.

**G3. Nekrashevych fragmentations of dihedral groups.**
- *Idea.* These are finitely generated simple groups of intermediate growth. Test finite
  presentability of their contracting self-similar models by a Dehn-function bound.
- *Kill.* There is no decisive finite test. Finite growth data cannot certify either finite
  presentability or its failure.
- *Verdict.* DEAD as a test; ALIVE as a literature question.

## Quick-kill summary

PROMISING: S1 (executed) and S4 (literature). ALIVE: S2, S5, G3 (literature). DEAD: S3, R1, R2,
R3, R4, N1, N2, G1, G2.

## Execution: S1

**Result.** `GHB_2(7)` contains a quasiconvex genus-2 surface subgroup. It is landed as follows:
- the criterion, with a complete proof: `ghb7-girth-surfaces-give-surface-subgroups` and route
  `ghb7-girth-surfaces-give-surface-subgroups-proof`;
- the certified instance: `ghb7-contains-a-genus-two-surface-subgroup` and its `-proof` route;
- the code and data: `experiments/ghb7-girth-surfaces/`.

**Criterion.** A girth surface is a closed surface tiled by (3,4,4) triangles, whose vertices have
6, 8, 8 triangles, with labels in the edge groups and trivial vertex words. For any such surface,
the developing map `S̃ → Y` is a local isometric embedding: every link walk is a girth cycle, hence
`d_π`-isometric. It is therefore an isometric embedding, which gives the injective quasiconvex
`φ : π_1(S) → G`.

Sources, all read at source:
- CCKW Theorem 3.1(i),(v);
- Bridson–Haefliger Definition I.5.6, Theorems I.7.39 and I.7.50, Proposition I.8.19,
  Proposition II.1.4(1),(2), Theorems III.H.1.7 and III.H.1.9.

**Calibration.** Recorded in `experiments/ghb7-girth-surfaces/search-t24.log` and the output of
`intersections.py`.
- Vertex group orders are 343, 2401, 2401, and the edge groups have order 7.
- `ψX_i ∩ ψX_j = ψ<g_k>`, and the triple intersection is trivial.
- Closed alternating words with nonzero exponents, counted by length 2/4/6/8, are 0/0/180/4896 in
  `X_0` and 0/0/0/936 in `X_1` and `X_2`. So the link girths are 6, 8, 8, matching `cckwLinkGirths`.
- Every scaling `(s,t) ∈ (F_7^×)^2` extends to an automorphism of each vertex group, which confirms
  S2's premise.
- On two planted instances the CSP solver recovered the planted labelling. Surface 25 gave 12 and 2
  solutions, and the planted one was found both times.

**Enumeration.** Orderly generation with canonical BFS relabelling found 72 isomorphism classes of
girth surfaces with `T = 24`, 8 of them orientable. The search took 31,981 nodes. Every class has
`χ = −2`.

**Label CSP.** The solver is bitset constraint propagation over the closed-word tables.
- 10 of the 72 classes carry labellings.
- Six of the eight orientable classes (25, 29, 31, 43, 65, 67) each reached the cap of 20 solutions.
- The orientable classes 42 and 51 have no labelling. That search was exhaustive, at 1,493,563 and
  1,151,155 nodes.
- Four non-orientable classes also have labellings.
- Every solution was re-checked by raw matrix products.

**Independent verification.** `verify_certificate.py` shares no code with the search. It re-checked
the six orientable certificates:
- the involutions, transitivity, and free orbits of sizes 6, 8, 8;
- orientability and `χ = −2`;
- the labels, and every vertex word equal to `I` in `SL_4(F_7)`;
- the eleven relators for `ψ(a), ψ(b), ψ(c)`.

All checks passed (`verify-genus2.log`).

**Exact counts.** These come from an uncapped rerun (`sol24-all.log` on MSI), which stopped after
class 65 when MSI went down.
- Orientable classes: 25 has 5,184 labellings, 29 has 1,944, 31 has 3,456, 43 has 6,912 and 65 has
  116,640. Classes 42 and 51 have none.
- Non-orientable classes: 17 has 216, 36 has 2,592 and 53 has 432.

Every count is a multiple of `216 = 6^3`. The torus scalings of S2 map labellings to labellings,
and they act freely because every exponent is nonzero. So labellings come in free orbits of size 216.

**Heuristic, for calibration only.**
- The naive independence estimate for `T = 24` is `6^{−36} · 180^4 · 936^6 ≈ 0.07` per surface.
- On an oriented surface each exponent enters the abelianized vertex conditions of its two endpoints
  with opposite signs. That gives three linear dependencies and raises the estimate to about 23.
- The observed orientable counts, from 0 to 116,640, are far from Poisson with mean 23. So the
  heuristic misses structure: the torus orbits, and whatever obstructs classes 42 and 51 (not
  identified here).

**What this does not do.**
- It gives surface subgroups of one group, not a general theorem.
- The criterion works verbatim for any triangle of finite groups with trivial face group, link
  girths `2m_i` and `Σ 1/m_i < 1`, provided a finite quotient injective on the vertex groups is
  available for checking. Other `G_{HB_2}(q)` and Kac–Moody–Steinberg groups are the next targets.

## Surviving ideas, ranked after execution

1. **S1-family (best next execution).**
   - *Idea.* Run the same girth-surface search, with the independent verifier, on the other hyperbolic
     generalized triangle groups with property (T) constructed in CCKW (arXiv:2011.09276), using
     their presentations in the MSI text extract. Then test whether a counting argument over random
     girth surfaces gives existence for every triangle of finite groups with trivial face group and
     `Σ 1/m_i < 1`.
   - *Kill.* An instance with no girth surface for `T ≤ 48`.
2. **S4.** Import surface subgroups for arithmetic uniform lattices in `SO(2n,1)` through totally
   geodesic 3-manifolds and Kahn–Markovic. This is a literature pin, not new mathematics.
3. **S5.** SAT encoding of bounded folding for one atoroidal `φ ∈ Out(F_3)`.
4. **S2.** Torus-twisted orbifold planes, as an accelerator for `T ≥ 72`.
5. **G3.** Finite presentability of Nekrashevych fragmentations; a literature question only.
