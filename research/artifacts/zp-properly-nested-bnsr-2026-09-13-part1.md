# Zaremsky Problem 1.18: properly nested BNSR invariants — part 1

Lane z1-18-nested-bnsr, 2026-09-13. Root: `zaremsky-1-18-properly-nested-bnsr-invariants`.
Status: analysis and reductions. Nothing here answers the problem. Imports marked
"(to verify)" have not been read from their sources yet.

## 0. The problem and the reading

Zaremsky, *Some open problems* (July 12, 2026), §1 Problem 18, verbatim: "Does there exist a
group G of type F∞ such that the BNSR-invariants Σ1(G) ⊋ Σ2(G) ⊋ · · · are all properly nested?"

- `S(G) = (Hom(G,R) \ {0})/R_{>0}` is a sphere of dimension `r − 1`, where `r = rank G^{ab}`.
- `Σ^m(G)` is the homotopical invariant. It is open in `S(G)`, and `Σ^1 ⊇ Σ^2 ⊇ ⋯`.
- For a nonzero character `χ`, its **level** is `ℓ(χ) = min{m : [χ] ∉ Σ^m(G)}` (`∞` if
  `[χ] ∈ Σ^∞`). Then `Σ^{m−1}(G) ⊋ Σ^m(G)` iff some character has level exactly `m`.
- **Problem 1.18 asks for a group of type `F_∞` realizing every level `m ≥ 2`.** Level 1
  must also be realized, for `Σ^0 = S ⊋ Σ^1`, but the problem's chain starts at `Σ^1 ⊋ Σ^2`,
  so what it needs is the levels `2, 3, 4, …`.
- The complements `S \ Σ^m` are compact and increase with `m`. Realizing infinitely many
  levels means infinitely many distinct compact sets in a sphere of fixed dimension.

## 1. Verified background (read from arXiv:1502.02620, Zaremsky, "On the Σ-invariants of generalized Thompson groups and Houghton groups")

- **Citation 1.2 there, attributed to [BGK10]:** "Let G be a group of type F_m and N a normal
  subgroup containing [G,G]. Then N is of type F_m if and only if for every χ∈Hom(G,ℝ) with
  χ(N)=0 we have [χ]∈Σ^m(G)."
- **Theorem A there:** "For any n,m≥2, we have Σ^m(F_n)=Σ^2(F_n)", for the generalized
  Thompson groups `F_n = F_{n,∞}`. The same paper records `Σ^m(F_2)` for all `m` from [BGK10]
  and `Σ^2(F_n)` from [Koc12]. So the Thompson groups `F_{n,∞}` have infinite cohomological
  dimension, are of type `F_∞`, and still realize no level above 2.
- **Houghton groups:** `H_n` is of type `F_{n−1}` but not `F_n`. Theorem 6.1 there gives lower
  bounds for `Σ^m(H_n)` from the action on a CAT(0) cube complex; Conjecture 6.2 says the
  bound is sharp. Houghton groups are not `F_∞`, so they are not candidates.

## 2. Proposition 1: finite cohomological dimension forces a constant tail

**Statement.** Let `G` be of type `F_∞` with `cd G = d < ∞`. Then
`Σ^m(G) = Σ^{max(2,d)}(G)` for every `m ≥ max(2,d)`. In particular no level exceeds
`max(2,d)`, and `G` does not answer Problem 1.18.

**Proof, from two imports (to verify).**
- (a) Novikov criterion (Sikorav for `m = 1`, Bieri in general): for `G` of type `FP_m`,
  `[χ] ∈ Σ^m(G;Z)` iff `Tor_i^{ZG}(\widehat{ZG}_{−χ}, Z) = 0` for `0 ≤ i ≤ m`.
- (b) Bieri–Renz: `Σ^m(G) = Σ^2(G) ∩ Σ^m(G;Z)` for `m ≥ 2`.

A group of type `F_∞` is of type `FP_∞`; with `cd G = d`, `Z` has projective dimension `d`
over `ZG`. So `Tor_i^{ZG}(M, Z) = 0` for every right module `M` and every `i > d`.

By (a), `[χ] ∈ Σ^d(G;Z)` already gives the vanishing of all `Tor_i`, `i ≥ 0`, so
`Σ^m(G;Z) = Σ^d(G;Z)` for all `m ≥ d`. Then (b) gives
`Σ^m(G) = Σ^2 ∩ Σ^m(G;Z) = Σ^2 ∩ Σ^d(G;Z) = Σ^{max(2,d)}(G)` for `m ≥ max(2,d)`. ∎

A second route to the homological half avoids (a). Use the Bieri–Renz valuation criterion
(a chain endomorphism of a finite-type free resolution that raises `v_χ` in degrees ≤ m).
Replace the length-`d` projective resolution by a free one whose tail is 2-periodic, built
from a splitting `P ⊕ Q ≅ free`. The tail's comparison maps have bounded valuation loss, so
a high power of a degree-≤`d` push extends to all degrees. This is written only as an
outline here.

**Consequence.** Every answer to Problem 1.18 has infinite cohomological dimension. The
known infinite-dimensional `F_∞` examples with computed invariants (`F`, `F_{n,∞}`) stop at
level 2 (§1).

## 3. Proposition 2: levels through coabelian subgroups

From Citation 1.2 (§1): if `G` is of type `F_∞`, and for each `k ≥ 1` some normal
`N_k ⊇ [G,G]` is of type `F_k` but not `F_{k+1}`, then `Σ^k(G) ⊋ Σ^{k+1}(G)` for every `k`.

**Proof.** `S(G, N_k) ⊆ Σ^k(G)`, and `S(G,N_k) ⊄ Σ^{k+1}(G)`. ∎

So Problem 1.18 follows from one lattice `Z^r = G^{ab}` whose sublattices carry coabelian
subgroups of every finiteness level. The converse fails only when a level is realized
solely at irrational characters.

## 4. Calibration: long finite chains, and chain length is not bounded by the rank

Tool (to verify against Meier–Meinert–VanWyk 1998, cited as [MMV98] in 1502.02620). Let
`A_Γ` be a right-angled Artin group and `χ` a character. `L(χ)` is the full subcomplex of
the flag complex on the vertices with `χ(v) ≠ 0`. Then `χ ∈ Σ^m(A_Γ)` iff, for every dead
simplex `σ` (including `σ = ∅`, `dim ∅ = −1`), `lk(σ) ∩ L(χ)` is `(m − 2 − dim σ)`-acyclic.

Sanity checks: `Σ^1(F_2) = ∅`, and a character on `Z` lies in `Σ^∞`.

- **`F_2^n`.** A character nonzero on exactly `j` factors has level `j`.
  - Both generators of each supported factor live: `L(χ)` is the octahedral `(j−1)`-sphere.
  - One generator of a supported factor dies: the dead simplex of all such generators has an
    empty link intersection, which gives the same bound.
  - So `S ⊋ Σ^1 ⊋ ⋯ ⊋ Σ^n = ∅`: a proper chain of length `n`, then constant.
- **Blocks `B_n = F_2^n ⋊ ⟨t⟩`, `t` permuting the factors cyclically.** `Hom(B_n,R) = R^3`
  (a diagonal `ψ` plus `c = χ(t)`). Pass to the finite-index subgroup `F_2^n × ⟨t^n⟩`, a
  RAAG with cone vertex `t^n`.
  - If `c ≠ 0`, the cone vertex lives, every `lk(σ) ∩ L(χ)` is a cone, and `χ ∈ Σ^∞`.
  - If `c = 0` and `ψ ≠ 0`, `χ` has level `n`.
  - Transfer to finite-index subgroups: `[χ] ∈ Σ^m(G)` iff `[χ|_H] ∈ Σ^m(H)` (to verify).
- **Products.** Take `G_k = B_1 × B_2 × B_4 × ⋯ × B_{2^{k−1}}`, of rank `3k`. A character with
  all `c_i = 0` supported on the blocks `i ∈ S` has level `Σ_{i∈S} 2^i` (links in joins add
  acyclicity). Any `c_i ≠ 0` puts it in `Σ^∞`. Every level `1, …, 2^k − 1` occurs, so
  `G_k` has the proper chain `S ⊋ Σ^1 ⊋ ⋯ ⊋ Σ^{2^k−1} = Σ^∞`, of length `2^k − 1`, at rank
  `3k`. Here `cd G_k = 2^k − 1 + k`, consistent with Proposition 1.

**Lesson.** A negative answer cannot come from the rank of the abelianization alone. The
levels were produced by *weights* (orbit sizes) together with *killers* (central elements
whose nonvanishing sends a character into `Σ^∞`).

## 5. Why the obvious mechanisms stall

1. **Convex and join rules.** Suppose the complements are generated from finitely many atomic
   bad pieces by spherical joins or convex hulls, with levels adding. Carathéodory's theorem
   in `R^r` then bounds the number of atoms in a minimal decomposition by `r`, so the levels
   are bounded by `r · max weight`. Products, metabelian groups under the `m`-tame
   conjecture, and S-arithmetic Borel subgroups all fit this pattern.
2. **Germ characters.** For Thompson-like groups the characters are logarithms of germs at
   global fixed points. Self-embeddings (conjugations into subintervals, doubling maps) act on
   germ characters by projections or permutations, which have finite orbits. A tree splitting
   with edge group `≅ G` can raise levels by one per step only along an infinite orbit, and
   there is none.
3. **Permutational wreath products of type `F_∞`.** Bartholdi–Cornulier–Kochloukova (to
   verify) give `A ≀_X F`, with `X` the dyadic rationals in `(0,1)`, of type `F_∞` when `A`
   is, because the stabilizers of `k`-tuples are `F^{k+1}`.
   - The restricted characters are supported on the two boundary pieces plus the lamp
     coordinates, and the middle pieces carry the zero character.
   - Heuristically the level of a configuration of `k` lamps is controlled by small `k`, so
     only finitely many levels appear. This is a heuristic, not a computation.

## 6. An architecture that would answer yes (and 1.13 no)

Keep the character space fixed, say `R^2 ⊕ R^2` (lamp directions plus killer directions).
Look for infinitely many blocks `P_n ≤ G` such that:
- block `n` is killed exactly off a line `ker c_n`, where `c_n` is the value of a killer
  element `z_n` centralizing the block's free-group part;
- `c_1, c_2, …` are pairwise non-proportional, e.g. `z_n` of abelianization class `(1, n)`;
- block `n` activates at level `n`, e.g. `n` permuted free factors with diagonal characters;
- "locality" holds: a character's level is the minimum over the blocks it activates.

Then `S \ Σ^m` is the finite set of directions `{ker c_j ∩ (ψ ≠ 0) : j ≤ m}`, which grows
forever. Its union accumulates at the direction of `(0,1)`, so `Σ^∞(G)` would not be open
there either (Problem 1.13, peer z1-13-sigma-inf).

**The missing pieces.**
- A finitely generated `G` of type `F_∞` containing the blocks compatibly. Cocompactness
  forces the blocks to come from a self-similar or oligomorphic structure, not from infinitely
  many orbits.
- An exact local-to-global computation of `Σ^m` for that `G`, in both directions. The Meinert
  criterion for actions on complexes (stabilizer restrictions in `Σ^{m−dim σ}` imply
  `χ ∈ Σ^m`) gives only one direction.

## 7. Next targets

1. Read the sources for imports (a), (b), (c), the finite-index transfer, and MMV98. Then
   promote Proposition 1 to an established obstruction claim with a proof route.
2. Find the computed `Σ^m` of the Stein groups `F_{2,3}` (Spahn–Zaremsky) and of
   Lodha–Moore groups: do they exceed level 2? Also look for any computation of `Σ^m` for
   permutational wreath products.
3. Look for a group realizing §6 with blocks generated by an oligomorphic action whose
   stabilizers are products carrying killers in infinitely many directions.
