---
rg: 2
id: pure-braid-zero-twist-cones-p5-salvetti-morse-certificates
kind: route
title: "Bestvina–Brady Morse certificates on the Salvetti complex prove Sigma^2(P_5) on open cones meeting c_12 = 0 and c_123 = 0"
target: pure-braid-open-zero-twist-cones-lie-in-sigma-two-of-p5
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
artifacts:
  - experiments/pure-braid-translated-jump-loci-2026-09-17/salvetti_morse.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/cert_n5_m2_t5c01.json
  - experiments/pure-braid-translated-jump-loci-2026-09-17/cert_n5_m2_t5c123w.json
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert_n5_m2_t5c01.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/verify_cert_n5_m2_t5c123w.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/antistar_check.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/antistar_check_n5.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin_t5c01.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/margin_t5c123w.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/check_chars.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/check_chars_certified.log
  - experiments/pure-braid-translated-jump-loci-2026-09-17/fast_morse.py
  - experiments/pure-braid-translated-jump-loci-2026-09-17/climb3.py
---

The proof uses the Bux–Gonzalez criterion (BG) and the Morse Lemma (ML). Both are
stated in `germ-complex-and-bux-gonzalez-morse-inputs`. It applies them to the
universal cover of the Salvetti complex, with an explicit integer Morse function. The
exact computation is in the artifacts. The search code (`climb3.py`, `fast_morse.py`)
only proposes certificates. The verifier (`verify_cert.py` over `salvetti_morse.py`)
recomputes everything from the face rule, so correctness does not depend on the search.

Work with `n = 5`. Strands are `0..4` in the code and `1..5` in the claim.

## Step 0. The Salvetti model (import)

**The complex.** `Sal` is the Salvetti complex of the real braid arrangement
`{x_i = x_j}` in `R^5`.

- Chambers `C` are the permutations.
- Faces `F` are ordered set partitions.
- The cells are `<C,F>` for every face `F` and every chamber `C` in `star(F)`. The
  dimension is `5 - #blocks(F)`, and the vertex set is `star(F)`.
- The face rule is `<D,G> <= <C,F>` iff `G` refines `F` and `D = G∘C`.
- `Sal` is a finite regular CW complex with 1920 cells, and it is homotopy equivalent
  to `M = {z in C^5 : z_i != z_j}`.

This is Salvetti, *Topology of the complement of real hyperplanes in C^N*, Invent.
Math. 88 (1987) 603–618. That paper was **not re-read verbatim this session**. The
homotopy type is confirmed through the quotient, quoted verbatim from
Paolini–Salvetti, arXiv:1907.11795, §2.1:

> "As shown in [Sal87, Sal94], the orbit configuration space YW has the homotopy type
> of a CW complex XW, with one |T|-cell cT for every T in ∆W ={T⊆S| the standard
> parabolic subgroup WT is finite}."

> "The 1-cells are oriented in such a way that c{s} corresponds to the generator s of
> the fundamental group GW"

> "In the literature, the CW complex XW is usually called the Salvetti complex of W."

`S_5` acts freely on `Sal` by `w·<C,F> = <wC, wF>`, and this action preserves the face
rule. It has `1920/120 = 16 = 2^4` orbits, which is one cell for each `T ⊆ S` with
`|S| = 4`. This matches `X_W` for `W = S_5`.

**The action of `P_5`.** Let `Y` be the universal cover of `Sal`. Then `P_5 = π_1(M)`
acts on `Y` freely, cellularly and cocompactly, with quotient `Sal`. The complex `Y` is
simply connected, and that is all Step 4 needs. `P_5` is finitely presented because
`Sal` is a finite complex, so it has type `F_2`.

**The meridian.** The embedding of the 1-skeleton sends the edge `<C,G>` to a path from
`x_C` to `x_{C'}`, where:

- `C'` is the chamber across the wall `ij` of `G`;
- the real part moves along the segment;
- the imaginary part stays in the chamber `C`.

So the loop `<C,G>` followed by `<C',G>` winds once, positively, around `z_i = z_j`. It
winds zero times around every other hyperplane, because the real part of `z_k - z_l`
keeps its sign. This loop therefore represents the meridian class `[A_ij]`, whose
classes form the standard basis of `H_1(P_5)`. The orientation convention does not
matter, because of Step 4(c).

## Step 1. The cocycle

Let `a` be an integer vector indexed by pairs. Define a 1-cochain `d` on `Sal` by
`d(<C,G>) = a_ij / 2`, where the edge `<C,G>` is oriented from `C` across the wall `ij`.

- **`d` is a cocycle.** The boundary of a 2-cell `<C,F>` consists of two minimal
  galleries in `star(F)` from `C` to the opposite chamber. Both are made of edges
  `<E,G>` with `E = G∘C`, so both are oriented away from `C`. Each crosses every wall
  of `F` exactly once, so `d` sums to the same value on both.
- **`[d] = χ`.** The meridian loop has value `a_ij/2 + a_ij/2 = a_ij`. So `[d]` is the
  character `χ = Σ a_ij ω_ij`.

## Step 2. Heights

Pull `d` back to `Y` and choose a primitive `h_d` on the vertices. Set
`H(x) = 2K·h_d(x) + η(C(x))`. Here:

- `C(x)` is the chamber under the vertex `x`;
- `K` and the integer vector `η` are read from the certificate file.

**Equivariance.** Deck transformations fix `C(x)`. So `H(g x) = H(x) + 2Kχ(g)`, and
`2Kχ` is a positive multiple of `χ`.

**Heights inside a cell.** Let `σ` be a lift of `<C',F>` with base vertex `x'` over
`C'`, and let `x_D` be its vertex over `D`. Join them by a minimal gallery in `σ`. Its
edges are oriented away from `C'`, by the face rule. So

`H(x_D) - H(x') = K·Σ_{ij separating C', D} a_ij + η(D) - η(C') = f_{C'}(D) - f_{C'}(C')`.

This `f` is exactly the function computed by `salvetti_morse.sepval` and
`verify_cert.py`. So the order of the vertex heights in every lifted cell is the order
the certificate computes. All heights are integers.

`verify_cert.py` checks that every one of the 1920 cells of `Sal` has a **unique**
lowest vertex. The lifts of cells at a vertex `x` over `C` correspond bijectively,
preserving order, to the cells of `Sal` containing `C`. This holds because `Sal` is
regular and closed cells lift homeomorphically.

## Step 3. The Morse function and its ascending links

**The Morse function.** Let `Y'` be the barycentric subdivision of `Y`, which is a
simplicial complex because `Y` is regular. Set

`h(σ̂) = H(low(σ)) + ε·dim σ`, with `ε = 1/10`,

and extend `h` affinely over simplices. Here `low(σ)` is the lowest vertex of `σ`.

Adjacent vertices `σ̂ < ρ̂` of `Y'` have `|h(σ̂) - h(ρ̂)| >= ε`:

- if `low(σ) = low(ρ)`, the difference is `ε·(dim ρ - dim σ) >= ε`;
- otherwise the two lowest vertices are distinct vertices of `ρ` with distinct integer
  heights, so the difference is at least `1 - 4ε > ε`.

So `(h, s)` with `s` constant is a Morse function in the sense of ML.

**(a) Chamber vertices.** Let `x` lie over `C`. The link of `x` in `Y'` is the order
complex of the cells `σ ∋ x` with `dim σ >= 1`.

- If `low(σ) = x`, then `h(σ̂) > H(x)`, so `σ̂` is ascending.
- Otherwise `H(low σ) <= H(x) - 1`, so `h(σ̂) < H(x)`, and `σ̂` is descending.

So the ascending link is the order complex of
`Asc(C) = {<C',F> ∋ C : dim >= 1, C is the unique argmin of f_{C'} on star(F)}`.

For both certificates, `verify_cert.py` recomputes all 120 posets `Asc(C)` in exact
arithmetic. For each one it:

- finds reduced `H_0 = H_1 = 0` over `F_1000003` and over `F_32003`;
- shows `π_1 = 1` by reducing an edge-path presentation of the order complex to the
  empty presentation.

The results are in `verify_cert_n5_m2_t5c01.log` and `verify_cert_n5_m2_t5c123w.log`,
which contain 120 lines ending in "pi1 trivial" and the verdict "VERIFIED". So every
chamber vertex has a 1-connected ascending link.

**(b) Barycentres of cells of positive dimension.** Let `σ` be such a cell and
`v = low(σ)`. The link of `σ̂` is the join of the order complex of the proper faces of
`σ` with the order complex of the cofaces of `σ`.

| Neighbour of `σ̂` | Height | Ascending? |
| --- | --- | --- |
| Proper face `τ` with `v ∉ τ` | `h >= H(v) + 1 > H(v) + 4ε >= h(σ̂)` | yes |
| Proper face `τ ∋ v` | `h = H(v) + ε dim τ < h(σ̂)` | no |
| Coface `ρ` with `low(ρ) = v` | `h(ρ̂) > h(σ̂)` | yes |
| Other coface `ρ` | `h(ρ̂) <= H(v) - 1 + 4ε < h(σ̂)` | no |

So the ascending link is `A_v(σ) * B`, where:

- `A_v(σ)` is the order complex of the proper faces of `σ` that miss `v` (the antistar
  of `v` in `∂σ`);
- `B` is the order complex of the cofaces with the same lowest vertex, possibly empty.

A join with a nonempty 1-connected factor is 1-connected. `antistar_check.py 5 one`
checks every cell `<id,F>` of positive dimension. These cells represent all cells modulo
the free `S_5`-action.

- The command checks one vertex `v` of each cell.
- One vertex suffices. The face poset of `<id,F>` is `{G : G refines F}`, ordered by
  refinement. The Young subgroup of the blocks of `F` fixes `F`, preserves refinement,
  and acts transitively on `star(F)`. So all the antistars `A_v` of one cell are
  isomorphic.
- The command finds that `A_v` is nonempty, has `H̃_0 = H̃_1 = 0`, and has `π_1 = 1`
  when `dim >= 2`. The result is in `antistar_check_n5.log`, which ends in
  "ANTISTARS OK".
- For `dim σ = 1`, `A_v` is a point.
- Running without `one` checks every vertex. For `n = 4` that run also prints
  "ANTISTARS OK".

This check replaces the classical fact that the antistar of a vertex in the boundary of
a polytope is a ball.

So every vertex of `Y'` has a 1-connected ascending link.

## Step 4. Conclusion

**(a) The filtration is 1-connected.** Apply ML to `Y'` with `p = -∞`, `q = t`,
`r = +∞` and `k = 2`. The pair `(Y', Y'_{t<=h})` is 2-connected. Since `Y'` is simply
connected, the exact homotopy sequence shows that every `Y'_{t<=h}` is simply
connected. So the filtration is essentially 1-connected.

**(b) BG gives `Σ^2`.** Apply BG with `m = 2` to `G = P_5`, which has type `F_2` and
acts on the 1-connected complex `Y'`. The stabilizers are trivial and the action is
cocompact. The height `h` is `2Kχ`-equivariant. BG gives `[χ] ∈ Σ^2(P_5)`.

**(c) The sign.** Complex conjugation of `M`, with a real base point, induces an
automorphism `φ` of `P_5` that acts as `-id` on `H_1`. So `Σ^2(P_5) = -Σ^2(P_5)`, and
the orientation convention of Step 0 does not matter.

**(d) Openness.** Let `a'` be real with `|a' - a|_∞ < r`. Every strict inequality
`f_{C'}(D) > f_{C'}(low)` survives, because it changes by at most `w·K·|a' - a|_∞`,
where `w` is the number of walls separating exactly one of `D`, `low` from `C'`.
`margin.py` computes `r = min (f(D) - f(low)) / (wK)` over all cells and vertices. So
the lowest-vertex assignment, the posets `Asc(C)` and the antistars are all unchanged.

Steps 1–4 then go through with real heights. Take `ε` as one tenth of the smallest gap
between the lowest vertex and any other vertex of a cell. There are finitely many
`P_5`-orbits of cells, so this gap is positive. This needs no import of the openness
of `Σ^m`.

The radii are `29867/2000000` for `chi_1` (`margin_t5c01.log`) and `42251/1000000` for
`chi_2` (`margin_t5c123w.log`). `Σ^2` is a set of rays, so positive multiples are
included.

**(e) The characters.** `check_chars_certified.log` records the twist data:

- `chi_1` has the unique vanishing twist `c_12`;
- `chi_2` has the unique vanishing twist `c_123`;
- both Aomoto complexes are acyclic in degrees `<= 2`.

Every point of the two open balls meets the stated hyperplane on a relatively open set.

## Gaps

- The combinatorial cell model (`<C,F>`, the face rule, and regularity) is cited from
  Salvetti 1987 without a verbatim quote from that paper. The quoted Paolini–Salvetti
  text certifies only the homotopy type of the quotient.
- The proof is computer-assisted. No human has checked the certificate data.

Status: UNREVIEWED (swarm-0917 worker w20-z-last1, 2026-09-17).
