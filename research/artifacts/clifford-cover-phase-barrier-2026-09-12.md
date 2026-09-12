# Complete-graph Clifford covers: the phase barrier and the transplant collapse

Lane `w4-clifford-complete`, 2026-09-12. Host, coordinates and notation as in Section 0 of
`research/artifacts/clifford-cover-orbital-localization-2026-09-12.md`: a group `G`, a `G`-set `X`, a
`G`-invariant graph `S`, the Clifford cover `E_S = Vtilde_S semidirect G` with central `eps`, and elements
written `(u, s, g)`.

Nothing here decides `kun-thom-clifford-cover-nonsurjunctive`. Two results are proved.

- **Theorem 1 (phase barrier).** A finite table carrying the Kun--Thom phase has no coordinate realization in
  any Clifford cover whose edges are all profinitely separable, over any base group and any site set. So no
  variant of the saturation method (Theorem C of the orbital artifact), with a different base group, site set
  or graph, reaches a window that carries the phase.
- **Lemma 2 (transplant collapse).** On the complete graph over an infinite set, and on every graph with an
  infinite induced matching, each subgroup whose lamp part has finite codimension contains `eps`. So the
  marked-site transplants that prove the Kun--Thom wreath surjunctive see only `eps`-invariant
  configurations, and the peeling proof does not transfer to these covers.

## 0. Coordinate realizations

Let `F` be a finite subset of `E_S` and `P` a set of pairs `(a, m)` in `F x F` with `a m` in `F`. For
`a = (u_a, s_a, g_a)` and `m = (u_m, s_m, g_m)`, the pair `(a, m)` has the **moves** `y -> g_a y` for
`y in supp u_m`. The **read sites** are the sites in the lamp supports of elements of `F`, together with
their images under moves.

Let `G'` be a group, `Y` a `G'`-set and `S'` a `G'`-invariant graph on `Y`, with the same square constant `q`.
A **coordinate realization** of `(F, P)` in `E_(S')(Y)` is a map

```text
phi(u, s, g) = (lambda u, s, psi(g)),
```

where `lambda` is injective on the read sites (extended linearly to their span), `psi` is defined on the
`G`-parts of `F`, and

- `psi(g_a g_m) = psi(g_a) psi(g_m)` for `(a, m) in P`;
- `lambda(g_a y) = psi(g_a) lambda(y)` for every move `y -> g_a y`;
- `phi(a m) = phi(a) phi(m)` for `(a, m) in P`, sign coordinate included.

The embeddings used by Theorems B', B'' and C of the orbital artifact are coordinate realizations. Since the
table group `U` of `(F, P)` is presented by the relators `[g_a][g_m] = [g_(am)]`, `psi` extends uniquely to a
homomorphism `U -> G'`.

**Signs of a transposed pair.** For distinct sites `x, y`, `c_x c_y` and `c_y c_x` have lamp part `e_x + e_y`,
group part `1`, and signs `beta(e_x, e_y)` and `beta(e_y, e_x)`. Exactly one of `x < y`, `y < x` contributes,
so the two signs add to `b_S(x, y)`, whatever the order on `X`.

## 1. Theorem 1: the phase barrier

**Phase data.** A coordinate realization `phi` of `(F, P)` *sees phase data* at a read site `x_0` if there are
`G`-parts `b_1, ..., b_k`, `t`, `b`, `h` of `F` with the following properties.

1. **Fixing moves.** Each `b_i` occurs in a move `x_0 -> b_i x_0 = x_0`. So `psi(b_i)` fixes `lambda(x_0)`.
2. **Ascending relations.** `psi(t) psi(b_i) psi(t)^(-1)` lies in `B' = <psi(b_1), ..., psi(b_k)>` for each `i`.
3. **The phase element.** `psi(b)` lies in `B'` and `psi(h) = psi(t)^(-1) psi(b) psi(t)`.
4. **Moving the site.** `h x_0 != x_0`, and some move `x_0 -> h x_0` has group part `h`.
5. **Both orders read.** `P` contains `(c_(x_0), c_(h x_0))` and `(c_(h x_0), c_(x_0))`, and `{x_0, h x_0}` is
   an edge of `S`.

Conditions 2 and 3 hold automatically once `P` contains chains of products computing `t b_i t^(-1) = w_i(b)`,
`t t^(-1) = 1` and `h = t^(-1) b t`, because `psi` is multiplicative on `P`.

**Theorem 1.** If a coordinate realization `phi` of `(F, P)` in `E_(S')(Y)` sees phase data at `x_0`, then
`lambda(x_0)` and `lambda(h x_0)` are distinct sites of `Y`, joined by an edge of `S'`, and no finite quotient
`K\Y` (with `K` normal of finite index in `G'`) separates them. So `S'` is neither a finite pullback nor
profinitely saturated.

*Proof.*
- **Distinct.** `lambda` is injective on read sites.
- **Adjacent.** `phi` keeps the sign coordinate of both products in condition 5. In `E_S` their signs add to
  `b_S(x_0, h x_0) = 1`. In `E_(S')` the same two products have signs adding to
  `b_(S')(lambda x_0, lambda h x_0)`. So that value is `1`.
- **Inseparable.** Let `K` be normal of finite index in `G'` and `f : G' -> G'/K`. By condition 2,
  `f(psi t) f(B') f(psi t)^(-1)` is contained in `f(B')`. Both are finite of equal order, so they are equal.
  By condition 3, `f(psi h) = f(psi t)^(-1) f(psi b) f(psi t)` lies in `f(B')`. So `psi(h) = k beta` with
  `k in K` and `beta in B'`. By conditions 1 and 4,

  ```text
  lambda(h x_0) = psi(h) lambda(x_0) = k beta lambda(x_0) = k lambda(x_0),
  ```

  so `K lambda(h x_0) = K lambda(x_0)`.
- **Consequences.** A finite pullback has no edge inside a `K`-fibre, and saturation condition 1 asks every
  edge to be separated by some `K`. QED

**Corollary 1.1 (the Kun--Thom phase window).** Let `Gamma < G` be the Kun--Thom Theorem E pair,
`X = G/Gamma`, `o = Gamma`. `Gamma = EL_r(F_q[x_1, ..., x_d])` is finitely generated, say by `b_1, ..., b_k`,
and there are `t` with `t Gamma t^(-1) <= Gamma` and `gamma in Gamma` with `h = t^(-1) gamma t` outside `Gamma`
(`kun-thom-clifford-radical-phase`). Let `S` be any `G`-invariant graph on `X` containing `{o, h o}`, the
complete graph included. The finite table of `E_S` made of `c_o`, `c_(h o)`, `eps`, the `b_i`, `t`, `t^(-1)`,
`gamma`, `h` and the products expressing

```text
b_i c_o = c_o b_i,   t b_i t^(-1) = w_i(b),   t t^(-1) = 1,   h = t^(-1) gamma t,
h c_o = c_(h o) h,   c_o c_(h o) = eps c_(h o) c_o
```

has phase data at `o` under every coordinate realization. It has no coordinate realization in any Clifford
cover, over any group, whose edges are all profinitely separable.

**Consequence 1.2 (what the barrier blocks).**
- Theorem C transports finite windows, coordinate for coordinate, into separated covers over the same base.
  Theorem 1 blocks every such transport of a phase window, whatever base group, site set or graph is chosen.
- Finite targets are covered by Theorem B''. Theorem 1 covers infinite Clifford targets as well.
- A surjunctivity proof for any Clifford cover carrying the phase edge therefore needs a target that is not a
  Clifford cover with separable edges, or a realization that does not send lamps to lamps.
- The barrier applies only to windows that carry phase data. Theorem B' shows that a strict pair on the
  complete-graph cover must read a non-closed holonomy configuration. That configuration need not contain
  both products of condition 5.

## 2. Lemma 2: cofinite lamp subgroups contain the center

Let `V = directSum_X F_2` with its adjacency form `b_S`. For `H <= E_S` put
`L_H = proj_V(H cap Vtilde_S)`, the **lamp part** of `H`.

**Lemma 2.** Suppose `b_S` vanishes identically on no subspace of finite codimension in `V`. Then every
`H <= E_S` whose lamp part has finite codimension contains `eps`.

*Proof.* `b_S` does not vanish on `L_H`, so there are `u, u'` in `L_H` with `b_S(u, u') = 1`. Choose lifts
`ut, ut'` in `H cap Vtilde_S`. In `Vtilde_S` the commutator of any lifts of `u, u'` is `eps^(b_S(u,u'))`,
because lifts differ by central elements and the commutator form is bilinear. So `eps = [ut, ut'] lies in H`.
QED

**Instances.**
- **The complete graph on an infinite set.** `V/L_H` is finite, so infinitely many `e_x` lie in one coset.
  Take three distinct sites `a, b, c` among them. Then `u = e_a + e_b` and `u' = e_a + e_c` lie in `L_H`, and
  `b_S(u, u') = b(a,c) + b(b,a) + b(b,c) = 1`.
- **Graphs with an infinite induced matching** `{a_i, b_i}`. Infinitely many indices share the pair of
  cosets `(e_(a_i) + L_H, e_(b_i) + L_H)`. Take distinct `i, j, k` among them. Then `u = e_(a_i) + e_(a_j)` and
  `u' = e_(b_i) + e_(b_k)` lie in `L_H`, and `b_S(u, u') = 1 + 0 + 0 + 0 = 1`, since the matching is induced.
  Every bounded-degree graph with infinitely many edges has an infinite induced matching.

**Consequence 2.1 (marked-site peeling does not transfer).** The proof of
`rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive` transplants an injective automaton to the coset spaces
`H_(S,A_0)\W`. Their lamp part contains every lamp off finitely many marked sites. The proof needs these
subgroups to separate every finite subset (its Lemma 1.2), and its strata lemma uses the finite lamp data
`Abar^S`. On a Clifford cover satisfying Lemma 2:

- **The center collapses.** Every subgroup with cofinite lamp part contains `eps`. So its coset space is a coset
  space of `W = E_S/<eps>`, pulled-back configurations are `eps`-invariant, and the transplanted automaton is a
  transplant of the automaton induced on `A^W = Fix(eps)`. These transplants reprove only bijectivity on
  `Fix(eps)`, which already follows from surjunctivity of `W`.
- **No separation.** No subgroup containing `eps` separates `1` from `eps`, so no family of cofinite-lamp
  subgroups satisfies Lemma 1.2.
- **Infinite data.** A subgroup that does separate `1` from `eps` has lamp part of infinite codimension. Its
  coset space carries infinitely many lamp classes over each group coordinate. The strata argument, as written,
  uses finitely many marked sites, and no infinite-data version is known.

This complements `kun-thom-clifford-cover-has-no-finitary-site-structure`, which rules out normal site
projections. Lemma 2 rules out the non-normal marked-site transplants too.
