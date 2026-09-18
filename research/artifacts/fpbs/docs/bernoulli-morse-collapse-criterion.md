# Measured Morse matchings of the Cayley 2-complex and the Bernoulli cost

Written 2026-09-17 by swarm worker `swarm-0917-w4-fp-cycle-tail`. This is a written deduction over one imported
identity. Nobody has refereed it or checked it formally.

## 0. Why this matters

`fpbs-bernoulli-cycle-tail-compactness` is equivalent to `C(b) = 1 + beta_1^(2)(Gamma)`. All of its present
sufficient conditions control a tail:

- Corollary 6.1 of `cost-cycle-structure.md` needs `T_L -> 0` uniformly;
- inequality (6.4) there needs a uniformly bounded mean reduced circulation mass.

Both start from an arbitrary near-minimizing graphing and repair it by surgery. That is why cycle lengths have to be
controlled.

This note starts instead from the Cayley graphing `Phi_S` and deletes edges along an integral structure: a
well-founded matching of relator 2-cells to boundary edges. It needs no bound on mass or length. Recovery trees only
have to be finite almost surely, and König's lemma turns that into generation.

The resulting quantity, the *Morse deficit* `m(P)` of a finite presentation, is monotone in the presentation. Its
limit over the full presentations `P_L` is exactly the subgraphing cost excess. The target then splits into
prerequisites that can each fail on their own (Section 5).

## 1. Setting

- `Gamma` is an infinite group with a finite generating set `S`.
- `P = <S | R>` is a presentation, where `R` is a finite list of words in `S^{+-1}` with repetitions allowed.
- `b` is the Bernoulli action `Gamma -> ([0,1]^Gamma, mu)`, which is essentially free.
- `R_b` is its orbit relation.
- `Phi_S` is the graphing `{x -> s.x : s in S}`, with `c(Phi_S) = |S|`.
- An *edge* is a pair `(x, s)` in `X x S`. It joins `x` and `s.x`. Let `nu = mu x counting` on `X x S`.

**Cells.** A *cell* is a pair `(x, r)` in `X x R`.

- Its boundary path is the closed path in the Schreier graph of `Phi_S` that starts at `x` and reads `r`.
- *Convention.* A path *reads* the word `s_1^{e_1} ... s_k^{e_k}` when it visits the points
  `x_i = (s_1^{e_1} ... s_i^{e_i})^{-1}.x`. Step `i` then crosses one `s_i`-edge. Under the orbit identification
  `gamma -> gamma^{-1}.x`, this is the usual Cayley-graph path. With this convention, the path reading `r` is closed
  iff `r = 1` in `Gamma`, by freeness.
- `bd(x, r)` is the list of edges it traverses, each edge being a Borel function of `x`.

**Morse matching.** A *Morse matching* for `P` is a Borel partial map `M : D -> X x S`, with `D` a subset of `X x R`,
satisfying (M1)–(M3):

- **(M1)** `M(c)` lies in `bd(c)` and is traversed exactly once by the boundary path of `c`.
- **(M2)** `M` is injective. Write `E_M` for its image, the set of *removed* edges.
- **(M3)** `M` is well-founded. For `e` in `E_M` with `c = M^{-1}(e)`, the *children* of `e` are the edges of
  `bd(c)`, other than `e`, that lie in `E_M`. Almost surely no orbit carries an infinite chain `e_0, e_1, ...` in
  which each `e_{j+1}` is a child of `e_j`.

**Mass and deficit.** The *mass* is `mu(M) = sum_{r in R} mu(D_r)`, where `D_r = {x : (x, r) in D}`. The *Morse
deficit* of `P` is

```text
m(P) = z(Phi_S) - sup_M mu(M),
```

where `z` is the finite-cycle dimension of `fpbs-graphing-cost-betti-cycle-dimension-identity`. By that identity,
`z(Phi_S) = |S| - 1 - beta_1^(2)(Gamma)`.

**Imported identity (I).** `fpbs-graphing-cost-betti-cycle-dimension-identity`: for a bounded-degree graphing `Phi`
with infinite components generating `R`, `c(Phi) = 1 + beta_1^(2)(R) + z(Phi)`, and `z(Phi) >= 0`. For a free action
of `Gamma`, `beta_1^(2)(R) = beta_1^(2)(Gamma)`.

## 2. Theorem A (Morse sufficiency)

**Theorem A.** Let `M` be a Morse matching for a presentation `P` on `S`, and let `Phi' = Phi_S \ E_M`. Then:

- (a) `Phi'` generates `R_b`;
- (b) `c(Phi') = |S| - mu(M)`;
- (c) `C(b) <= |S| - mu(M)`, and `mu(M) <= z(Phi_S)`.

So `m(P) >= 0`. If `m(P) = 0`, then `C(b) = 1 + beta_1^(2)(Gamma)`.

**Proof of (b).**

- Partition `D` Borel-wise into pieces `D_{r,i}`: cells of type `r` whose matched edge is the `i`-th letter of `r`.
- On `D_{r,i}`, the map `M` is `(x, r) -> (g_{r,i}.x, s_{r,i})` for a fixed `g_{r,i}` in `Gamma` and a fixed
  `s_{r,i}` in `S`. So `M` preserves measure on each piece.
- Because `M` is injective, `nu(E_M) = sum mu(D_{r,i}) = mu(M)`.
- Therefore `c(Phi') = sum_s mu{x : (x, s) not in E_M} = |S| - nu(E_M)`.

**Proof of (a).**

- *The recovery tree is finite.* Fix a removed edge `e`. Its *recovery tree* `T(e)` has root `e`, and the children
  of a node are the children defined in (M3). Every node has at most `k_max - 1` children, where `k_max` is the
  longest relator length. By (M3), almost surely `T(e)` has no infinite branch, so by König's lemma it is finite.
  (The orbits carrying an infinite chain form a null set, contained in a Gamma-invariant null Borel set, which is
  discarded.)
- *Induction on height.* We prove that the endpoints of `e` are `R_{Phi'}`-equivalent, by induction on the height of
  `T(e)`. Let `c = M^{-1}(e)`. By (M1), the boundary path of `c` with `e` deleted is a path joining the endpoints of
  `e`. Each edge on it is either in `Phi'` or a child of `e`. A child has a strictly lower tree, so by induction its
  endpoints are `R_{Phi'}`-equivalent. Hence the endpoints of `e` are `R_{Phi'}`-equivalent.
- *Conclusion.* Every edge of `Phi_S` joins `R_{Phi'}`-equivalent points, so `R_{Phi'}` contains `R_{Phi_S} = R_b`.

**Proof of (c).**

- The first inequality holds because `Phi'` is a generating graphing.
- `Phi'` has bounded degree, and its components are infinite, because it generates `R_b` and `Gamma` is infinite.
  So (I) gives `|S| - mu(M) = c(Phi') >= 1 + beta_1^(2)(Gamma)`.
- (I) applied to `Phi_S` gives `z(Phi_S) = |S| - 1 - beta_1^(2)(Gamma)`, hence `mu(M) <= z(Phi_S)`.
- If `m(P) = 0`, then `C(b) <= 1 + beta_1` by (c), and `C(b) >= 1 + beta_1` by (I). QED.

**Remark (the second Betti number).**

- For a finite presentation, Atiyah's l2 Euler characteristic of the simply connected Cayley 2-complex `K_P~` gives
  `z(Phi_S) = |R| - beta_2^(2)(K_P~)`.
- So the unmatched cells always have density at least `beta_2^(2)(K_P~)`. They carry the l2 2-cycles.
- This remark is not used in any proof.

**Consequences.**

- If `m(P) = 0`, `Gamma` also has fixed price: every free action `a` satisfies `1 + beta_1 <= C(a) <= C(b)`, by (I)
  and Abért–Weiss maximality (`fpbs-bernoulli-maximal-cost`).
- No length or mass control enters anywhere. Recovery trees may have infinite expected size. This is the difference
  from (6.4) of `cost-cycle-structure.md`.
- Theorem A never uses that `R` presents `Gamma`. It only uses that each word in `R` is trivial in `Gamma`. So it
  holds for every finitely generated `Gamma` and every finite list `R` of trivial words.

## 3. Theorem B (monotone deficit and the subgraphing limit)

Let `P_L` be the list of all words of length at most `L` in `S^{+-1}` that are trivial in `Gamma`, one cell type per
word. Let `C_sub(S)` be the infimum of `c(Phi')` over Borel subgraphings `Phi'` of `Phi_S` that generate `R_b`.

**Theorem B.** Let `Gamma` be infinite and finitely generated by `S`.

- (i) If `R` is contained in `R'`, then `m(R') <= m(R)`.
- (ii) `lim_{L -> infinity} m(P_L) = C_sub(S) - 1 - beta_1^(2)(Gamma)`. The sequence is nonincreasing.
- (iii) Consequently `C(b) = 1 + beta_1` follows from `inf_L m(P_L) = 0`, and in particular from `m(R) = 0` for a
  single finite list `R`.

**Proof of (i).** A Morse matching for `R` is a Morse matching for `R'`, with the same cells, boundaries and children.
The value `z(Phi_S)` depends only on `S`.

**Proof of (ii), lower bound.** For any Morse matching `M` for `P_L`, Theorem A(a,b) gives
`|S| - mu(M) >= C_sub(S)`. Therefore

```text
m(P_L) >= |S| - 1 - beta_1 - (|S| - C_sub(S)) = C_sub(S) - 1 - beta_1.
```

**Proof of (ii), upper bound.**

- *Setup.* Let `Phi'` be a generating subgraphing of `Phi_S`, and let `E'` be its complement.
- *The recovery word.* Take a removed edge `e = (x, s)` in `E'`. Let `w(e)` be the shortlex-least word among the
  shortest words read along a `Phi'`-path from `s.x` back to `x`. This is a Borel choice, and its length `l(e)` is
  finite almost surely, because `Phi'` generates.
- *The cell.* Let `r(e)` be the word that traverses `e` and then reads `w(e)`. It labels a closed path, so it is
  trivial in `Gamma`, and it has length `l(e) + 1`.
- *The matching.* Set `E'_L = {e in E' : l(e) <= L - 1}`, and define `M_L(x, r(e)) = e` on `E'_L`.
  - (M1) holds, because `w(e)` uses only `Phi'`-edges and `e` is not one of them.
  - (M2) holds, because the cell `(x, r(e))` determines `x` and its first letter, and those determine `e`.
  - The boundary edges other than `e` lie in `Phi'`, which is disjoint from `E'_L`. So there are no children,
    and (M3) holds trivially: recovery depth is one.
- *Mass.* By Theorem A(b), `mu(M_L) = nu(E'_L)`. By monotone convergence, `nu(E'_L) -> nu(E') = |S| - c(Phi')`.
  Hence `lim m(P_L) <= |S| - 1 - beta_1 - (|S| - c(Phi')) = c(Phi') - 1 - beta_1`. Take the infimum over `Phi'`.
  The limit exists by (i).

**Proof of (iii).** Combine (ii) with `C(b) <= C_sub(S)` and (I). QED.

**Reading of Theorem B.**

- Over the full presentations `P_L`, depth-one matchings with long relators already realise the subgraphing cost.
- The content of a fixed finite presentation is that long relators must be replaced by deep recovery trees built
  from short cells.
- So `m(R)` versus `lim m(P_L)` is the combinatorial form of the interchange of limits in `L` and `n` that
  `cost-cycle-structure.md` Section 4 identifies with the cost–Betti gap. The difference is that the approximating
  graphings are now restricted to subgraphings of one Cayley graphing.

## 4. Calibrations

**4.1 `Z^2 = <a, b | [a, b]>`, where `z = 1`.**

- *Naive matchings fail.* Matching every square to its right `b`-edge is not well-founded: the left `b`-edge is a
  child, which gives an infinite leftward chain. Matching every square to its top `a`-edge fails the same way.
- *Sparse columns work.* Keep the `b`-edge `(x, b)` iff `x(1_Gamma) < eps`. Match each square to its right `b`-edge
  when that edge is not kept.
  - The chain of a removed `b`-edge runs leftward through distinct points, each testing an independent coordinate.
    So it stops within `N` steps except with probability `(1 - eps)^N`, and (M3) holds.
  - The mass is `1 - eps`, so `m(P) = 0`.
  - Recovery trees are geometric here, but their size plays no role.

**4.2 Products, and `F_2 x F_2` with `beta_2 = 1`.**

*The general product.*

- *Setup.*
  - `Gamma = Gamma_1 x Gamma_2`, with finite generating sets `S_1` and `S_2`, `S = S_1 ⊔ S_2`.
  - Fix `c` in `S_2` and `a` in `S_1`, both of infinite order.
  - `R` consists of the commutators `[s, c]` for `s` in `S_1` and `[a, t]` for `t` in `S_2 \ {c}`.
  - As in 4.1, each edge is kept independently with probability `eps`, using the coordinate at `1_Gamma`.
- *The matching.*
  - Match the cell `[s, c]` to its `s`-edge on the far side from `c`, when that edge is not kept. The only possible
    child is an `s`-edge at a point that differs by a power of `c`.
  - Match the cell `[a, t]` to its `t`-edge on the far side from `a`, when that edge is not kept. Its possible
    children are two `S_1`-edges and one `t`-edge at a point that differs by a power of `a`.
- *Why (M3) holds.*
  - Children of `S_1`-edges are `S_1`-edges. So an infinite chain is eventually a chain of `S_1`-edges along a
    `c`-line, or else it is a chain of `t`-edges along an `a`-line.
  - Both kinds of chain stop almost surely, because `a` and `c` have infinite order and the coordinates they test are
    independent.
- *Mass and cost.* The mass is `(|S| - 1)(1 - eps)`, so `C(b) <= 1 + (|S| - 1) eps`. This recovers Gaboriau's fixed
  price one for these products.

*The case `F_2 x F_2`.*

- Take the generators `<a, b> x <c, d>`. The relators `[a, c]`, `[b, c]`, `[a, d]` are matched as above, and `[b, d]`
  is never matched.
- The standard presentation has `|R| = 4` and `z = 3`.
- The Cayley complex is the product of two 4-valent trees, with `beta_2^(2) = beta_1^(2)(F_2)^2 = 1`.
- So `m(P) = 0`, and the unmatched `[b, d]`-cells have density exactly `beta_2 = 1`. The bound in the Remark of
  Section 2 is attained.

**4.3 Proposition C (the proper-power ceiling).**

*Statement.* Suppose `R` contains `w^m`, where `w` has order exactly `m` in `Gamma`, and the closed path reading
`w^m` traverses each edge once. Then every Morse matching has `mu(D_{w^m}) <= 1/m`.

*Proof.*

- The cells `(w^{-j}.x, w^m)`, for `j = 0, ..., m-1`, are distinct, by freeness. They share one boundary cycle.
- Suppose two of them, `c != c'`, are matched, to `e = M(c)` and `e' = M(c')`. By injectivity `e != e'`. Then `e'`
  is a child of `e` and `e` is a child of `e'`, which is an infinite chain and contradicts (M3).
- So `sum_{j < m} 1_{D_{w^m}}(w^{-j}.x) <= 1`. Integrating with the measure-preserving map `x -> w^{-1}.x` gives
  `m mu(D_{w^m}) <= 1`. QED.

*Application to one-relator groups.*

- Let `Gamma = <S | w^m>` be infinite. By the imported `one-relator-group-cost-equals-first-l2-betti-plus-one`,
  `beta_1 = |S| - 1 - 1/m`, so `z(Phi_S) = 1/m`.
- The ceiling is therefore *exactly sharp*. `m(P) = 0` says: almost every boundary cycle carries one matched cell,
  and the choice is well-founded.
- By Theorem A this would give Bernoulli cost `|S| - 1/m`, which is fixed price for one-relator groups. That is open;
  Remark 3.6 of Poulin–Wróbel explains why their cutting method cannot give it.
- So Morse attainment is a concrete Borel combinatorics target for this class.

## 5. The decomposition, and what is open

For an infinite, finitely generated `Gamma` with a finite generating set `S`, let `Target(Gamma)` be the statement
`C(b) = 1 + beta_1^(2)(Gamma)`. It is equivalent to tail compactness for `Gamma`. Consider:

- **(Q1) Fixed-list attainment.** Some finite list `R` of trivial words has `m(R) = 0`.
- **(Q2) Depth compactness.** For some finite `R`, `m(R) = lim_L m(P_L)`. Deep recovery trees on short cells do as
  well as long relators.
- **(Q3) Subgraphing attainment.** `C_sub(S) = C(b)`. The Bernoulli cost is approached by subgraphings of one Cayley
  graphing.

**Established here.**

- (Q1) implies `Target(Gamma)` and fixed price (Theorem A).
- `inf_L m(P_L) = 0` is equivalent to `C_sub(S) = 1 + beta_1`, which is equivalent to `Target(Gamma)` together with
  (Q3) (Theorem B).
- Therefore `Target(Gamma)`, (Q2) and (Q3) together imply (Q1). Conversely, (Q1) implies `Target(Gamma)`.

**Why each prerequisite can fail on its own.**

- (Q3) is a statement about the Cayley graphing, independent of cost–Betti. We know no reference either way.
- (Q2) is a statement about Borel matchings for a fixed finite `R`, and is independent of costs of other graphings.
- (Q1) with `R` a finite presentation is the finitary form that attack lanes can work on directly: factor-of-iid
  well-founded matchings, as in Section 4.

**Not established.**

- None of (Q1)–(Q3) is proved for Kazhdan groups, for one-relator groups, or in general.
- `fpbs-bernoulli-cycle-tail-compactness` remains OPEN.
