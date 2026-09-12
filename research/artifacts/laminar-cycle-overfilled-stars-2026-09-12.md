# Laminar cycle configurations: overfilled stars

Lane `w5-laminar-cycle`, 2026-09-12. Target: `leavitt-units-have-laminar-finite-subgroup-defect`.
Supports `laminar-defects-localize-to-a-nonsofic-overfilled-star`. Builds on
`research/artifacts/finite-subgroup-combination-defects-2026-09-12.md` (lane `w4-kap-join`), whose
conventions, Theorem 2.1, Lemma 2.3, Corollary 2.4 and Theorem 2.6 are used below.

## 0. Setting

- `G` is any group, `p` a prime, `S = F_p[G]`.
- `H_0, ..., H_k <= G` are finite subgroups and `F = {x_i}` is a laminar family, `x_i` an idempotent of
  `M_n(F_p[H_(s(i))])`. Pairwise products lie in `{0, x_i, x_j}`.
- `r(x) = dim_(F_p)(x F_p[H]^n) / |H|` for an idempotent over a finite `H`, and `r(1) := n`.
- As in the proof of Theorem 2.1 of the `w4-kap-join` artifact: every member has a unique parent (the
  smallest member strictly above it, or `1`); `C(y)` is the set of children of `y in {1} u F`; the atoms
  `alpha_y = y - sum_(z in C(y)) z` are pairwise orthogonal idempotents summing to `1`; and every nonzero
  idempotent `d` of the span `B` of `1` and `F` is a sum of distinct nonzero atoms.
- `t_p` is the lifted trace on `K_0(S)`. On a laminar combination it takes the rational value
  `m n + sum m_i r(x_i)`.

## 1. A balanced configuration contains one nonsofic overfilled star

**Definition.** For `y in {1} u F`, the *star* of `y` is the laminar family `F_y = C(y) u {y}` (just `C(1)`
when `y = 1`), carried by the finite subgroups `Star(y)`: the subgroups of the members of `C(y)`, together
with the subgroup of `y` when `y != 1`. The star is *overfilled* when `sum_(z in C(y)) r(z) >= r(y)` and
`alpha_y != 0`.

**Theorem 1.1.** Let `d in B` be a nonzero idempotent with `t_p([d S^n]) <= 0` (for instance a balanced
combination, `t_p = 0`). Then some nonzero atom `alpha_y <= d` has an overfilled star, and that star occurs
in no sofic group, in the sense of Theorem 2.6: no sofic group contains finite subgroups `K_s ~= H_s`
(`H_s in Star(y)`) with isomorphisms agreeing on pairwise intersections and `K_s n K_t` equal to the image
of `H_s n H_t`.

*Proof.*
1. **Traces of atoms.** Write `d = sum_(alpha in T) alpha` over a nonempty set `T` of distinct nonzero
   atoms. Classes add over orthogonal idempotents, so `t_p([d S^n]) = sum_(alpha in T) t_p([alpha S^n])`.
   From `y = alpha_y + sum_(z in C(y)) z` and LFT1 of `lifted-trace-detects-finite-subgroup-projectives`,
   `t_p([alpha_y S^n]) = r(y) - sum_(z in C(y)) r(z)`, a rational number.
2. **One atom is overfilled.** If every `alpha in T` had positive trace, the sum would be positive. So some
   `alpha_y in T` has `sum_(z in C(y)) r(z) >= r(y)`, and `alpha_y != 0`.
3. **The star is laminar, and `alpha_y` is one of its atoms.** `F_y` is a subset of `F`, so its pairwise
   products lie in `{0} u F_y`. The members of `F_y` strictly below `y` are exactly `C(y)`: they are below
   `y` by definition, and no member of `C(y)` lies below another, since they are nonzero and pairwise
   orthogonal. So within `F_y` the children of `y` are `C(y)`, and `alpha_y` is an atom of `F_y`: a nonzero
   laminar combination of `F_y`.
4. **No sofic realization.** Suppose a sofic group contains `Star(y)`. Theorem 2.6, applied to the laminar
   family `F_y` over the subgroups of `Star(y)` and to the combination `alpha_y`, gives
   `t_p([alpha_y S^n]) > 0`. This contradicts step 2. QED

**Corollary 1.2 (shape of the star).** In Theorem 1.1, put `Y = y` and `C(y) = {z_1, ..., z_m}`. Then:
- `z_1, ..., z_m` are pairwise orthogonal, each `z_i <= Y`, and `z_1 + ... + z_m != Y`;
- `r(z_1) + ... + r(z_m) >= r(Y)`, although each `r(z_i) < r(Y)` by
  `nested-two-finite-subgroup-idempotents-have-strict-rank`, so `m >= 2`;
- the graph `Phi_y` on the distinct subgroups of `Star(y)`, with an edge for each nontrivial pairwise
  intersection, is not a forest, by Corollary 2.4 of the `w4-kap-join` artifact. So `Star(y)` has at least
  three distinct subgroups, and the children use at least two of them.

*Proof.* The first two items restate the definitions, step 2, and TFR1 applied to each pair `z_i < Y`.
If `Phi_y` were a forest, the intersection amalgam of `Star(y)` would be virtually free (Corollary 2.4),
hence sofic, and it contains `Star(y)` (Lemma 2.2), against Theorem 1.1. A graph with a cycle has at least
three vertices, and the parent's subgroup is at most one of them. QED

**Reading.** An overfilled star is a finite *paradoxical packing*. Finitely many pairwise orthogonal
finite-subgroup packets sit strictly inside one packet, yet their normalized sizes add up to at least its
size. Theorem 1.1 says every balanced configuration contains one, and Lemma 2.3 says no sofic group can host
one. With strict inequality `sum r(z_i) > r(Y)` the star's atom has negative lifted trace, so it would be an
even stronger certificate of nonsoficity than a balanced configuration.

**Corollary 1.3 (hosts).**
1. **Common finite overgroup.** If the subgroups of every star lie in a common finite subgroup of `G`, no
   nonzero laminar combination has `t_p <= 0`. In `R^x` this covers every star built from constants at
   finitely many prefix levels, which all lie in one `Theta(GL_(2^K)(F_2))` (Section 8.2 of the ternary
   normal-forms artifact).
2. **Sofic overgroup.** If the subgroups of a star lie in a sofic subgroup of `G`, that star is not
   overfilled with a nonzero atom. So an overfilled star with all its subgroups inside Thompson's group
   `V <= R^x` certifies that `V` is not sofic, which is open.
3. **The search is local.** A candidate for `leavitt-units-have-laminar-finite-subgroup-defect` is decided
   star by star: one parent packet, its orthogonal children, and a cycle of nontrivial intersections among
   at least three finite subgroups. The rest of the family can be discarded.

*Proof.* Items 1 and 2 are Theorem 2.6 with `Gamma` the finite overgroup or the sofic subgroup, which
contains the star with the actual intersections. Item 3 is Theorem 1.1. QED

**Answer to "does local finiteness kill cycles in `R^x`?"** Only in part. Local finiteness of the
constants kills every star inside finitely many levels (1.3.1). A star with a Thompson conjugate
`u H u^(-1)` escapes, and for stars inside `V` the question is at least as hard as soficity of `V` (1.3.2).

## 2. Redundant intersection edges, and essential cycles

For finite subgroups `H_0, ..., H_k <= G` put `D_ij = H_i n H_j`, and let `A` be the colimit of all the
inclusions `H_i <- D_ij -> H_j` (as in the `w4-kap-join` artifact). Write `iota_i : H_i -> A`.

**Lemma 2.1 (an edge inside a third subgroup is redundant).** Suppose `D_ij <= H_l` for some `l != i, j`.
Then the colimit of the diagram with the edge `{i, j}` removed is canonically isomorphic to `A`.

*Proof.* Let `A'` be the colimit without that edge. The universal properties give `A' -> A`. For the
converse map it is enough that `iota_i(g) = iota_j(g)` holds in `A'` for every `g in D_ij`. Such a `g` lies
in `H_i n H_j n H_l`, so `g in D_il` and `g in D_lj`. The edges `{i, l}` and `{l, j}` are still present, so
`iota_i(g) = iota_l(g) = iota_j(g)` in `A'`. The two maps are mutually inverse on generators. QED

**Corollary 2.2 (essential graph).** Let `Phi` be the graph with an edge `{i, j}` for each nontrivial
`D_ij`. Repeatedly delete an edge `{i, j}` for which some `l` has `D_ij <= H_l` and both `{i, l}` and
`{l, j}` are still edges. Every such deletion keeps `A` unchanged. Call the final graph `Phi^ess`. If
`Phi^ess` is a forest, `A` is the fundamental group of a finite tree of finite groups, hence virtually free
and sofic, and no laminar combination over these subgroups has `t_p <= 0`.

*Proof.* If `D_ij != 1` and `D_ij <= H_l`, then `D_il` and `D_lj` contain `D_ij`, so they are nontrivial.
The condition on the current graph is exactly what Lemma 2.1 uses, so each deletion preserves the colimit.
The forest case is the argument of Corollary 2.4 of the `w4-kap-join` artifact, run on `Phi^ess`, followed
by Theorem 2.1 there. QED

**Corollary 2.3 (three-subgroup stars).** A star of Theorem 1.1 that uses exactly three distinct finite
subgroups `H_0, H_1, H_2` needs `D_ij` not contained in the third subgroup, for all three pairs.
Equivalently, each pairwise intersection is strictly larger than the triple intersection
`H_0 n H_1 n H_2`. If one pairwise intersection equals the triple intersection, the star's amalgam is
virtually free.

*Proof.* `D_ij <= H_l` is the same as `D_ij = H_i n H_j n H_l`. Corollary 2.2 then deletes that edge
and leaves a path, which is a forest. QED

**Example 2.4 (a degenerate cycle).** In Thompson's `V`, write `a, b, c, d` for the cylinders `[00]`,
`[01]`, `[10]`, `[11]`, and `Sigma(P)` for the group permuting the pieces of a cylinder partition `P` by
prefix replacements (Section 3). Take:
- `H_0 = Sigma({a, b, c, d}) ~= S_4`, the level-two constants;
- `H_1 = Sigma({[0], c, d}) ~= S_3`;
- `H_2 = Sigma({[000], [001], b, c, d}) ~= S_5`.

Intersections:
- `D_01 = <(c d)>`. An element of `H_1` moving `[0]` sends `[00]` to a depth-three cylinder.
- `D_12 = <(c d)>`. `[0]` is a union of three pieces of the third partition, so it must be fixed pointwise.
- `D_02 = Sym{b, c, d}`. `a` is subdivided in the third partition, so it must be fixed pointwise.

All three edges are nontrivial, and the join is infinite.
- Let `sigma in H_1` be the 3-cycle `0x -> 10x -> 11x -> 0x`, and `(a c) in H_0` the swap `00x <-> 10x`.
- Then `g = sigma (a c)` maps `10x -> 100x`. So with `y = (10)^inf`, `g(1 0^k y) = 1 0^(k+1) y` for
  `k >= 1`.
- That orbit is infinite, so `g` has infinite order.

But `D_01 = D_12 = H_0 n H_1 n H_2`, so the amalgam is virtually free. No star over these subgroups is
overfilled.

**Remark 2.5 (only the abstract star matters for the trace).** By Lemma 2.2 and Theorem 2.6 of the
`w4-kap-join` artifact, whether a star can be overfilled depends only on the abstract data: the groups
`H_s`, the subgroups `D_st`, and their identifications. If the same abstract data occur among finite
subgroups of a finite group, or of any sofic group, no realization in any host carries an overfilled star.
So replacing a constant configuration by Thompson conjugates helps only when the conjugation changes the
abstract intersection pattern. Conjugating each subgroup separately while keeping the same groups and
intersections cannot help.

**Where the known cases stand (literature, not re-read here).** Colimits of triangles of finite groups
with angle sum at most `pi` are developable (Gersten--Stallings). They include hyperbolic groups and
lattices of `A_2~`-buildings. Residually finite or finitely generated linear colimits die by Theorem 2.6.
Soficity of the rest, such as general hyperbolic colimits and exotic `A_2~`-lattices, is open. A surviving
essential triangle must be one of those, with no finite or sofic quotient injective on the union of its
vertex groups.

## 3. Finite subgroups of Thompson's `V` permute a canonical partition

For a finite partition `P` of `X = {0,1}^N` into cylinders, `Sigma(P) ~= Sym(|P|)` is the group of
homeomorphisms that permute the pieces of `P` by prefix replacements.

**Proposition 3.1.** Let `H <= V` be finite. Let `C_H` be the set of cylinders `c` such that every `h in H`
restricts to a prefix replacement of `c` onto a cylinder. Then:
1. `C_H` is closed under subcylinders and invariant under `H`;
2. its maximal elements form a finite partition `P_H` of `X`;
3. `H` permutes `P_H` by prefix replacements, so `H <= Sigma(P_H)`;
4. every partition `P` with `H <= Sigma(P)` refines `P_H`.

*Proof.*
1. **Closure and invariance.** Subcylinder closure is immediate. For `c in C_H` and `g, h in H`,
   `g` restricted to `h(c)` equals `(g h)` restricted to `c`, composed with the inverse of the prefix
   replacement `c -> h(c)`. Both are prefix replacements, so `h(c) in C_H`.
2. **The partition.**
   - Each `h in V` is a prefix replacement on the pieces of some finite partition `D_h`. So every point
     lies in a cylinder inside a piece of every `D_h` (`h in H`), and that cylinder is in `C_H`.
   - The cylinders containing a given cylinder form a finite chain, so a largest one in `C_H` exists.
   - Two cylinders are nested or disjoint, so distinct maximal elements are disjoint. They cover `X`,
     and compactness makes them finitely many.
3. **The action.** Let `c in P_H` and `h in H`. Then `h(c) in C_H` lies in a maximal `c'`. If
   `h(c) != c'`, then `h^(-1)(c')` is a cylinder in `C_H`, because `h^(-1)` is a prefix replacement on
   `c'`, and it strictly contains `c`. That contradicts maximality.
4. **Minimality.** The pieces of such a `P` lie in `C_H`, hence inside maximal elements. QED

**Corollary 3.2 (intersections).** For finite `H, K <= V`, `H n K <= Sigma(P_H ^ P_K)`, where `P_H ^ P_K`
is the common refinement. An element of `H n K` permutes both partitions by prefix replacements, maps
`p n q` onto `g(p) n g(q)`, and restricts there to the prefix replacement of `p`.

So a star inside `V` is a star of subgroups of symmetric groups on cylinder partitions. Its pairwise
intersections lie in the symmetric groups of the common refinements, as in Example 2.4. This fact is
standard, and the proof above is included only to make the search checkable.

## 4. V-hosted stars without block symmetries occur in a finite symmetric group

**Proposition 4.1 (label realization).** Let `H_0, ..., H_k <= V` be finite, and choose cylinder
partitions `P_s` with `H_s <= Sigma(P_s)`. Suppose that for all `s != t`, every element of `H_s n H_t`
maps each piece of `P_s \ P_t` and each piece of `P_t \ P_s` to itself. Then the configuration occurs in
the finite group `Sym(Y)`, where `Y` is the set of cylinders that are pieces of some `P_s`. So no nonzero
laminar combination over these subgroups has `t_p <= 0`.

*Proof.*
1. **The actions.** Let `psi_s(h)` permute `P_s <= Y` as `h` permutes the pieces, and fix `Y \ P_s`. An
   element of `Sigma(P_s)` fixing every piece is the identity, because it is a prefix replacement of each
   piece onto itself. So `psi_s` is injective.
2. **Agreement on intersections.** Let `g in H_s n H_t`.
   - On `P_s n P_t`, `psi_s(g)` and `psi_t(g)` both apply the geometric action of `g`.
   - On `P_s \ P_t` and `P_t \ P_s`, both fix every point: by hypothesis for the partition `g`'s own
     subgroup uses, and because the other `psi` fixes labels outside its partition.
   - Elsewhere both fix everything.
3. **Exact intersections.** Suppose `psi_s(h) = psi_t(h')` with `h in H_s` and `h' in H_t`.
   - This permutation fixes `P_s \ P_t` and `P_t \ P_s` pointwise, so `h` is the identity on
     `X \ union(P_s n P_t)`. That set equals `union(P_s \ P_t) = union(P_t \ P_s)`. The same holds for `h'`.
   - On the common pieces `h` and `h'` are the same prefix replacements between the same pieces.
   - So `h = h'` as homeomorphisms, and it lies in `H_s n H_t`. Thus `psi_s(H_s) n psi_t(H_t) = psi(D_st)`.
4. **Conclusion.** Theorem 2.6 of the `w4-kap-join` artifact applies with `Gamma = Sym(Y)`. QED

**Example 4.2 (an essential triangle in `V` with an infinite join, which still dies).** Put
`U_1 = [000]`, `U_2 = [001]`, `U_3 = [010]`, `U_4 = [011]`, `U_5 = [10]`, `U_6 = [11]`, and take:
- `P_0 = {U_1, U_2, U_3, [0110], [0111], U_5, U_6}` (`U_4` split);
- `P_1 = {U_1, U_2, U_3, U_4, U_5, [110], [111]}` (`U_6` split);
- `P_2 = {U_1, [0010], [0011], U_3, U_4, U_5, U_6}` (`U_2` split);
- `H_s = Sigma(P_s) ~= S_7`.

Each split region is the unique piece of its shape, so it is fixed pointwise by every intersection. The
intersections are:
- `D_01 = Sym{U_1, U_2, U_3, U_5}`;
- `D_12 = Sym{U_1, U_3, U_4, U_5}`;
- `D_02 = Sym{U_1, U_3, U_5, U_6}`;
- triple intersection `Sym{U_1, U_3, U_5}`.

So:
- **Essential.** Every edge is essential: `(U_1 U_2) in D_01 \ H_2`, `(U_3 U_4) in D_12 \ H_0` and
  `(U_5 U_6) in D_02 \ H_1`.
- **Infinite join.** With `t = (010x <-> 0110x) in H_0` and `(U_3 U_4) in H_1`, the composite
  `g = (U_3 U_4) t` maps `[010]` into `[0100]`, so `g` has infinite order.
- **Still dead.** The hypothesis of Proposition 4.1 holds, so the configuration occurs in `Sym(12)` and
  carries no overfilled star.

**Corollary 4.3 (block symmetries).** An overfilled star with all subgroups in `V` has the following
property for every choice of partitions `P_s` with `H_s <= Sigma(P_s)`: some intersection element moves a
piece of `P_s \ P_t` to a different piece. That element exchanges two regions with the same relative
substructure: two pieces of `P_s` that are subdivided identically in `P_t`, or that sit at the same address
inside two pieces of `P_t`.
