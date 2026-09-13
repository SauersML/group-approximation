# Quantum rigidity beyond first order: group shifts, Bieri–Strebel, and gluing

Lane `ex2-labbe-quantum-rigidity`, 2026-09-13. Unreviewed. Part 3. Parts 1 and 2:
- `research/artifacts/quantum-rigidity-walls-and-commutator-ideal-2026-09-13.md`;
- `research/artifacts/labbe-shift-wall-rigidity-2026-09-13.md`.

It supports:
- `antipodal-one-sided-group-shift-configurations-are-walls`;
- `group-shift-crossed-product-fp-from-lamp-group-fp`;
- the Attempts of `wall-rigid-z2-sft-is-quantum-rigid`.

## 1. Group shifts

Let `p` be prime and `X ⊆ (F_p^m)^(Z^2)` a group shift, i.e. a closed shift-invariant subgroup. It is an SFT.
Write `M` for its Pontryagin dual. `M` is a finitely generated `F_p[Z^2]`-module, and `X = Hom(M, F_p)`. For a
unit vector `v`, put `X_v^+ = {c ∈ X : c(n) = 0 whenever <n, v> <= 0}`.

**Proposition G1 (antipodal one-sidedness gives walls).** If `X_v^+ != 0` and `X_(-v)^+ != 0` for some `v`,
then `X` is not `D`-wall-rigid for any `D`. So `X` is not quantum rigid over any field.

*Proof.* Take nonzero `c_+ ∈ X_v^+` and `c_- ∈ X_(-v)^+`. Translate by lattice vectors `g_±` with
`±<g_±, v> >= L`, so the supports lie in `<n,v> > L` and `<n,v> < -L`. Then `y = σ^(g_+) c_+ + σ^(g_-) c_-` is
in `X`. The difference set `Δ(0, y) = supp y` has two nonempty parts at distance `>= 2L`. For `2L > 2D` this is
a wall certificate. By `sft-wall-rigidity-iff-idempotent-commutator-ideal`, `X` is not `D`-quantum rigid.
Every scale fails. QED

**Proposition G2 (lamp groups).** Let `k` be a field with `char k != p` containing a primitive `p`-th root of
unity, and put `G = M ⋊ Z^2`. Then `LC(X, k) ⋊ Z^2 ≅ k[G]`. If `G` is finitely presented, then `X` is
`D`-quantum rigid for some `D`.

*Proof.* Locally constant functions on the compact group `X` are finite combinations of characters, whose
group is `M`. Since `μ_p ⊆ k` and `p` is invertible, this gives `LC(X, k) ≅ k[M]`, equivariantly for the
shift. So the crossed product is `k[M] ⋊ Z^2 = k[G]`. A finite presentation of `G` gives one of `k[G]`: add
`g g^(-1) = 1` for the generators. Apply `sft-crossed-product-fp-iff-quantum-rigid`. QED

**Corollary G3 (conditional on two recalled facts).** Let `k` be as in G2. Suppose the following two facts,
recalled and not re-read:
1. **Duality.** Bieri–Strebel's invariant `Σ^c_M` consists of the directions `v` with `X_v^+ != 0`.
2. **Bieri–Strebel (Proc. LMS 1980).** `M ⋊ Z^2` is finitely presented iff `Σ^c_M` contains no antipodal
   pair.

Then for group shifts, `D`-wall-rigid for some `D` ⇔ quantum rigid ⇔ `M ⋊ Z^2` is finitely presented.

*Proof.* If `Σ^c_M` has an antipodal pair, G1 gives walls at every scale. Otherwise the group is finitely
presented, and G2 gives rigidity, hence wall rigidity. QED

**Reading.** For algebraic shifts the local-to-global principle `wall-rigid-z2-sft-is-quantum-rigid` is
(conditionally) the Bieri–Strebel theorem.
- Walls play the role of antipodal points of `Σ^c`: the easy direction, via superposition.
- The hard direction of Bieri–Strebel propagates relations using one-sided finite generation in every
  direction.
- Calibration: for a principal module `F_p[Z^2]/(f)`, `Σ^c` is the set of outer normals of edges of the Newton
  polygon (recalled). So wall rigidity is "no two parallel edges". Ledrappier's triangle passes, and the
  square `1 + x + y + xy` fails, matching part 1.

**Where Labbé's shift sits.** It has fault lines in four directions, so `X_v^+`-type asymmetric pairs exist on
both sides in those directions. Yet superposition is unavailable, and it has no walls (part 2). Condition 2 of
G3 is false for it, while wall rigidity holds. So the Bieri–Strebel mechanism for the hard direction cannot be
transplanted: its propagation step uses one-sided determinism, which Labbé's shift lacks in four directions.

## 2. Gluing classical pieces

A *piecewise-classical family* consists of:
- a set `S` of tilings in `Ω`, and `W = k^(S)`, with diagonal operators `Δ(z)` reading `T_s(z)`;
- a cover of `Z^2` by regions `Q_i` whose pairwise overlaps (bands) have width `> 2D`, with every `D`-ball
  inside one region;
- gauges `U_i ∈ GL(W)` with `E(z) = U_i Δ(z) U_i^(-1)` on `Q_i`.

Consistency on a band `b = Q_i ∩ Q_j` says `g_(ij) = U_i^(-1) U_j` lies in the Levi group
`L(β_b) = ⊕_blocks GL(block)`. Here `β_b` is the partition of `S` by restriction to `b`. Each `D`-ball lies in
one region, so every such family satisfies (Q1)–(Q3).

**Lemma P1.** If two equivalence relations on a set have union the complete relation, one of them is complete.

*Proof.* Take `x, y` in different classes of the first. Then `x ~_2 y`. For any `z`:
- if `z` is not first-equivalent to `x`, then `z ~_2 x`;
- otherwise `z` is not first-equivalent to `y`, so `z ~_2 y ~_2 x`.

So `~_2` is complete. QED

**Proposition P2 (tree covers).** Let `Ω` be `D`-wall-rigid, and let the adjacency graph of the cover be a
tree, each band separating the plane into the two unions of regions on its sides. Then every piecewise-classical
family on that cover commutes.

*Proof.*
1. **The band blocks.** Let `b` separate sides `H_1` and `H_2`, and let `s, t` lie in one block of `β_b`. Wall
   rigidity forbids `s, t` from differing on both sides. So the relations "agree on `H_1`" and "agree on
   `H_2`", restricted to the block, cover all pairs.
2. **Splitting the transition.** By P1, one relation is complete on the block, so the block lies inside a
   single partition class of that side. Then `GL(block)` commutes with `Δ(z)` for all `z` on that side. So
   `g = V_1 V_2^(-1)`, where `V_1` collects the blocks complete on side 1 and `V_2^(-1)` the rest. Each `V_i`
   commutes with the diagonal operators on its side.
3. **Induction.** Absorb `V_1` into the gauges of all regions on side 1, and `V_2` into those on side 2. This
   removes the transition at `b` without changing the family. Inducting over the edges of the tree makes all
   gauges equal, so the family is conjugate to `Δ` and commutes. QED

**Cycles are where freedom lives.** On an annular cover, a band does not separate, and P2 fails as a proof.
Hand checks in dimension 3 (regions with frames, bands fixing one line) found the following:
- **Loops.** In every case checked, three- and four-step loops of frame rotations close trivially, or produce
  two extracted tilings agreeing on two bands and differing on both arcs between them, which is a wall.
- **Triangles.** Glued through a scalar ray, the extracted tilings include `(a,a',a')` and `(b,b',b'')`. They
  agree on the two bands bounding `Q_1` and differ on both sides, which is again a wall.
- **Band ends.** At a coarse vertex, a frame-changing band `(L, Π)` can meet only bands of its own type. A
  complementary band forces the two adjacent frames to share a second line and then to coincide. So
  frame-changing bands run to infinity or close up.

These are case checks, not a theorem. They support dimension `>= 4` as the natural threshold, as for the magic
square, but do not exclude Kochen–Specker-type triads in dimension 3 on non-simply-connected arrangements.

**For Labbé's shift (heuristic).** Tilings agreeing on a thick unbounded band have equal torus points, because
the orbit along the band sees every boundary direction. So the Levi blocks of bands sit inside fibres, and a
piecewise-classical family splits as a direct sum over torus points. Within one fibre the differences are at
most four concurrent fault lines, which cross near their common point, so the family commutes. Making "equal
torus points" rigorous for a half-strip along a rational direction needs care: the orbit along a lattice ray
fills a closed circle, not the torus.

## 3. What the crux now is

- **General.** A wall-rigid SFT failing rigidity would need a genuinely non-piecewise-classical family. Its
  local frames change at every scale, with no gauge region carrying a constant classical decomposition. In
  constraint-game terms it is contextuality on a planar arrangement of contexts (balls). For XOR games with
  each variable in two contexts, planarity excludes contextuality (Arkhipov's theorem, recalled). Our contexts
  overlap heavily, so that theorem does not apply.
- **Labbé.** Wall-rigid, not Bieri–Strebel tame, with fault networks in four directions crossing. Its quantum
  rigidity decides which invariant governs presentations of tiling algebras. Either answer is new.
- **Literature.** Web search was exhausted and the arXiv API returned HTTP 429 from MSI on 2026-09-13. No
  literature on operator-valued tilings or finite presentation of Steinberg algebras of `Z^2`-SFTs was found
  or checked. Novelty is claimed only relative to this graph.
