# Square-complex table cores: lattices in products of trees as hosts for strict automata

Lane `gk-free-wild`, 2026-09-12. Handwritten proofs, nothing run. Supports
`strict-automaton-on-lattice-in-product-of-trees`,
`mixed-bigon-difference-graphs-present-vh-square-complexes`,
`hyperbolic-cubulated-groups-are-residually-finite` and
`cubulated-hyperbolic-table-cores-carry-no-strict-pair`.

Conventions are those of `canonical-table-groups-for-automaton-designs-2026-09-12.md`
and `table-group-holonomy-normal-form-2026-09-12.md`. A design is `D = (A, S, M, nu, mu)`,
`E` is a marked partition of `S x M`, `U_E` its table group, `Gamma_E` the decoder
difference graph, and `M' = M \ {1_M}`.

## 1. The approach, and why this one

The free lane was asked for the most unconventional justified attack. I took the
geometric group theory of the table group itself.

* By `strict-automata-live-on-canonical-table-groups` and
  `table-groups-are-memory-holonomy-groups`, a Gottschalk counterexample is a finite
  presentation assembled from holonomies of difference labels `x_m' x_m^(-1)`, with
  finitely many reverse hinge words that must stay nontrivial. Curvature of that
  presentation is a rule-independent filter, and also a source of candidate hosts.
* Every lane in the swarm works on Kazhdan hosts (the Leavitt tower, the fixed tester,
  simple Kazhdan containers). Those hosts are forced for a *proof*, by
  `gottschalk-reduces-to-fg-simple-kazhdan-groups`. A *counterexample* can live
  anywhere, because nonsurjunctivity ascends to overgroups.
* Hyperbolic cubulated cores are residually finite, hence carry no strict pair
  (Section 4). The nonpositively curved cores that escape are square complexes with
  flats. Among them, irreducible lattices in products of two trees include the
  Burger–Mozes groups, whose soficity is recorded as unknown (Cornulier, *A sofic group
  away from amenable groups*, p. 4, quoted in
  `research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md`).
* Those lattices are a-T-menable. So no rigid compression defect exists in them
  (`a-t-menable-groups-have-no-rigid-compression-defect`), and every known nonsoficity
  mechanism is silent there. A strict automaton over one would be simultaneously a
  Gottschalk counterexample and the first nonsofic a-T-menable group, by a mechanism
  orthogonal to (T).
* Complete one-vertex square complexes have unique vertical-times-horizontal normal
  forms (Section 3), so every reverse table over them is decidable by hand.

This is a host class for the negative direction. It is not a proof strategy for the
positive direction, which by the reduction must handle simple Kazhdan hosts.

## 2. Mixed bigons present VH square complexes

A *one-vertex VH complex* `X` has one vertex, oriented edges partitioned into vertical
letters `V` and horizontal letters `H`, and square 2-cells whose boundary words
alternate horizontal and vertical letters. Here every square reads
`h v^(-1) h' v'^(-1)` with `h, h'` in `H` and `v, v'` in `V`.

**Theorem B.** Let `E` be a marked partition whose difference graph `Gamma_E` is
connected and loop-free. Suppose:

1. `M' = V ⊔ H`, and every edge label `x_m' x_m^(-1)` has both `m, m'` in `M'`;
2. `Gamma_E` has a spanning tree `T` such that every edge outside `T` is parallel to the
   tree edge joining the same two decoder addresses;
3. if the tree edge `s' -> s` has type HV (label `x_h x_v^(-1)`), then a parallel
   non-tree edge `s' -> s` has type VH (label `x_v' x_h'^(-1)`), and a parallel
   non-tree edge `s -> s'` has type HV.

Then `U_E ≅ pi_1(X_E)`. Here `X_E` is the one-vertex VH complex with edges `V ⊔ H` and
one square per non-tree edge:
* `h v^(-1) h' v'^(-1)` for a same-orientation edge;
* `h v^(-1) h'' v''^(-1)` for a reversed edge labelled `x_h'' x_v''^(-1)`.

Conversely, every finite one-vertex VH complex `X` with squares
`q = h_q v_q^(-1) h'_q v'_q^(-1)` is `U_E` for the *star partition* `E_X` of
`S_X x M_X`, where:
* `S_X = {1} ∪ {s_q}` and `M_X = {1} ∪ V ∪ H`;
* the identified pairs are `(s_q, v_q) ~ (1, h_q)` and `(s_q, h'_q) ~ (1, v'_q)`;
* every other class is a singleton, and the marked class is `{(1,1)}`.

*Proof.* Theorem H of the holonomy artifact, with `c = 1`, gives
`U_E = Hol_M(E) = < M' | w_s = w_s' delta_e for e: s' -> s outside T >`.
* For a non-tree edge `e` parallel to the tree edge `t: s' -> s`, the tree gives
  `w_s = w_s' delta_t`. So the relator becomes `delta_t = delta_e`, that is
  `delta_t delta_e^(-1) = x_h x_v^(-1) x_h' x_v'^(-1)`.
* For a reversed edge `e: s -> s'`, the relator `w_s' = w_s delta_e` becomes
  `delta_t delta_e = 1`, that is `x_h x_v^(-1) x_h'' x_v''^(-1)`.
* Both words alternate `H` and `V^(-1)` letters. All of `M'` survives as generators,
  since the decoder letters are the ones eliminated.

For the converse, `Gamma_(E_X)` is the star with center `1_S` and a double edge to
each `s_q`. The pair `(s_q, v_q) ~ (1, h_q)` is an edge `1 -> s_q` with label
`x_h_q x_v_q^(-1)`. The pair `(s_q, h'_q) ~ (1, v'_q)` is a parallel edge with label
`x_v'_q x_h'_q^(-1)`. Taking the first as tree edge, the relator is
`x_h_q x_v_q^(-1) x_h'_q x_v'_q^(-1)`. QED

**Remark.** Theorem B concerns table groups of partitions. Whether `E_X` is a
*minimal forward-sufficient* partition for some rules `(nu, mu)` is the realizability
step (Section 5). Section 7 settles it: no rule pair with a non-permutation encoder is
forward sufficient on these partitions.

**Scope correction.** Every relator Theorem B produces reads `h v^(-1) h' v'^(-1)` in
positive letters, so opposite sides of each square are antiparallel. A square with one
letter on two opposite sides in parallel, such as the commutator squares of the product
complex of `F_V x F_H`, has no such reading under any orientation of the letters. So the
converse covers the complete complexes admitting an orientation in which every square
reads `h v^(-1) h' v'^(-1)`. It does not cover every lattice in a product of trees acting
simply transitively on vertices, as the first landing of
`mixed-bigon-difference-graphs-present-vh-square-complexes` said.

## 3. Complete VH complexes and products of trees

`X` is *complete* when every corner pair `(v^(±1), h^(±1))` occurs exactly once among
the square corners, meaning the link is complete bipartite.

For complete finite one-vertex VH complexes, these are Wise's complete square
complexes (D. T. Wise, *Complete square complexes*, Comment. Math. Helv. 82 (2007)
683–724, cited in `research/artifacts/hyperbolic-rf-vtf-osin-full-proof-2026-09-11.md`).
Their standard properties:
* the universal cover is `T_(2|V|) x T_(2|H|)`, so `Gamma = pi_1(X)` is a torsion-free
  cocompact lattice in `Aut(T_(2|V|)) x Aut(T_(2|H|))` acting simply transitively on
  vertices;
* every element has a unique normal form `(reduced V-word)(reduced H-word)`, so the
  word problem, and every product table, is decidable by square moves;
* `Gamma` acts properly on a product of trees, so it has the Haagerup property;
* `Gamma` contains `Z^2`, so it is not hyperbolic, and the filter of Section 4 does
  not apply;
* the class contains reducible lattices (`F_V x F_H`, residually finite, sofic, so
  useless as hosts), irreducible lattices that are not residually finite (Wise), and
  virtually simple ones (Burger–Mozes).

A strict design needs a nonsofic table core (`forward-relations-of-a-counterexample-have-a-nonsofic-core`).
So only complete VH complexes whose lattice is not known to be sofic are candidates:
the non-residually-finite irreducible ones.

## 4. Filter: cubulated hyperbolic cores carry no strict pair

**Citation (hyperbolic cubulated groups are residually finite).**
* Agol, *The virtual Haken conjecture*, Doc. Math. 18 (2013), Theorem 1.1: a hyperbolic
  group acting properly and cocompactly on a CAT(0) cube complex is virtually special.
* Haglund–Wise, *Special cube complexes*, GAFA 17 (2008): virtually special groups
  virtually embed in right-angled Artin groups, hence are linear over `Z` and residually
  finite.
* Wise, *Cubulating small cancellation groups*, GAFA 14 (2004): finite classical
  `C'(1/6)` and `C'(1/4)–T(4)` presentations give groups acting properly cocompactly on
  CAT(0) cube complexes. They are hyperbolic in the `C'(1/6)` case.

Trust surface: the quoted statements, as in `cprime-one-sixth-presentations-are-hyperlinear`,
which records the same chain through Martin–Steenbock.

**Proposition C.** Let `T_f` be a forward table and `C(D)` the group presented by the
2-core of its relator hypergraph. If `C(D)` is hyperbolic and cubulated (in particular
if the core presentation is finite classical `C'(1/6)`), then no strict data with
forward table `T_f` is realized in any group.

*Proof.* The chain above makes `C(D)` residually finite, hence sofic. A strict
realization would force `C(D)` to be nonsofic, by
`forward-relations-of-a-counterexample-have-a-nonsofic-core`. QED

So the geometric survivors are cores with flats or with non-cubulated geometry. Section 3
is the flat, CAT(0), a-T-menable end of that spectrum; Kazhdan cores are the other end.

## 5. Open: realizing a complete non-residually-finite VH complex by rules

**Target** (`strict-automaton-on-lattice-in-product-of-trees`): rules `(nu, mu)` for which
some `E_X` of a complete, irreducible, not residually finite VH complex `X` is
minimal forward-sufficient, and the realization over `pi_1(X)` has a nontrivial
reverse hinge.

**Attempt 1: single-track 0/1 linear rules over `F_2`.** Then
`sigma o tau = tau_(beta alpha)`, with `alpha = sum_(m in M) m` and
`beta = sum_(s in S) s`. Forward sufficiency is `beta alpha = 1`, which pairs *all*
`|S||M| - 1` non-marked products. The star partition `E_X` pairs only `2|squares|` of
them. The remaining products `s_q * 1 = s_q` and `s_q m` force extra coincidences,
which are not VH squares in general. So the star partition is never realized
single-track. Strictness would be `alpha beta != 1`, a Kaplansky counterexample for
`F_2[pi_1 X]`.

**Lemma D (small gadgets need torsion).** In any group, if `s != s'`, `m_1 != m_2` and
`(s + s')(m_1 + m_2) = 0` in `F_2[G]`, then `m_2 m_1^(-1)` has order exactly two.

*Proof.* The four products cancel in pairs. Since `s m_1 != s m_2` and `s m_1 != s' m_1`,
we get `s m_1 = s' m_2` and `s m_2 = s' m_1`. So `s'^(-1) s = m_2 m_1^(-1) = m_1 m_2^(-1)`,
whose square is `1`, and it is not `1`. QED

Complete VH lattices are torsion-free, so a multi-track linear realization cannot
cancel products with two-by-two track supports. Tracks need at least three addresses
on one side.

**Update (sibling results since the first landing).**
* `bijective-designs-force-every-finite-presentation` (gk-n-twocycle) forces every
  finite presentation as the principal forward table of a shift–shear design over
  `F_2^T`, with a bijective encoder over every group. Every complete VH complex is
  therefore forced by some design, and realizing forward tables is solved. What remains:
  * forcing the squares through an irreversible component;
  * keeping a reverse hinge nontrivial in `pi_1(X)`.
* `boolean-core-is-uniform-single-demand-network-coding` (gk-n-boolean): strict data are
  uniform codes solving `N(T_f)` and failing the transposed `N^t(T_r)`.
  `smallest-boolean-strict-core-is-a-one-sided-inverse`: group-realized 2x2 reverse
  tables are transposes. Irreversible square gadgets therefore need shapes larger than
  2x2, consistent with Lemma D.

**Next steps.**
1. In the shift–shear design for a complete square complex, let the decoder read a key
   track at two addresses joined by a square, instead of translating it back. The
   forward table keeps the square, the encoder loses its inverse, and the reverse
   table is then computed by the normal form.
2. Take Wise's smallest non-residually-finite complete square complexes as `X`, and
   decide each reverse hinge word by square moves.

Both steps are settled in Section 6: the first cannot give strictness, so the second is
moot for that architecture.

## 6. The square-read shift–shear design is bijective over every group

The lead asked for step 1 of Section 5: the shift–shear design of
`bijective-designs-force-every-finite-presentation` for the square presentation of a
complete complex `X`, with the decoder reading a key track at two addresses joined by a
square instead of translating it back. No design of this architecture is strict,
whatever it forces.

**The architecture.** Write a square `h v^(-1) h' v'^(-1)` in holonomy shape
`u v^(-1) = w z^(-1)`, with `u = h`, `w = v'`, `z = h'`. The shift–shear design has key
tracks `a`, `b` and a data track `d`:

    a'(g) = a(g v),   b'(g) = b(g h'),   d'(g) = d(g) + a(g h) b(g v').

The decoder reads `a'` at `v^(-1)`, `b'` at `h'^(-1)`, and both at `p = h v^(-1) = v' h'^(-1)`.
The square is forced by the data shear. The proposed modification replaces the
translations by a key automaton reading each key track at two addresses, such as
`a'(g) = phi(a(g v), a(g h))`, and lets the decoder recover the keys through a square.

**Theorem E (shear reduction).** Let `A = K x D`, `kappa` a cellular automaton on `K^G`,
`N` finite and `pi : K^N -> Sym(D)`. Put

    tau(x)(g) = ( kappa(x_K)(g),  pi((x_K(g n))_(n in N)) (x_D(g)) ).

Then `tau` is injective iff `kappa` is, and surjective iff `kappa` is.

*Proof.* Write `pi_x(g)` for the permutation used at `g`. It depends only on `x_K`.
* If `kappa` is surjective, take `y`, pick `x_K` with `kappa(x_K) = y_K`, and put
  `x_D(g) = pi_x(g)^(-1)(y_D(g))`. If `tau` is surjective, so is its first coordinate `kappa`.
* If `kappa` is injective and `tau(x) = tau(x')`, then `x_K = x'_K`, so the permutations
  agree and `x_D = x'_D`. If `tau` is injective and `kappa(x_K) = kappa(x'_K)`, take any `x_D`
  and put `x'_D(g) = pi_(x')(g)^(-1)(pi_x(g)(x_D(g)))`. Then `tau(x) = tau(x')`, so
  `x_K = x'_K`. QED

**Corollary 6.1.** Suppose the key automaton acts track by track, and each track
automaton reads at most two addresses. Then the design is injective only if it is
bijective, over every group.

*Proof.* A product automaton is injective, respectively surjective, iff every factor is.
A track automaton `k -> phi(k(. v), k(. h))` is the bijective translation `k -> k(. v)`
followed by an automaton with memory `{1, c}`, `c = v^(-1) h`. That automaton acts on every
left coset `g<c>` as one automaton on `A^(<c>)`, through `x(g c^n)`, so it is injective,
respectively surjective, iff that one is. A cyclic group is residually finite, hence
sofic and surjunctive (`sofic-groups-are-surjunctive`). Theorem E finishes. QED

**What this settles.** The squares of `X` are forced by the data shear, and Theorem E
says coincidences forced only through a data shear never bear on strictness. So the
proposed step is dead over every host. The reverse hinges of step 2 need no computing,
because the encoder is bijective and `tau sigma = id` holds identically. A strict design
of shear shape needs a strict key automaton, whose own left inverse forces a nonsofic
core (`forward-relations-of-a-counterexample-have-a-nonsofic-core`).

## 7. Private origin rows carry no information

Call `(s, 1_M)` the *origin cell* of row `s`. Use the network form of
`boolean-core-is-uniform-single-demand-network-coding`: one source per class, one relay
per row applying `mu`, one sink applying `nu`.

**Lemma F.** Let `E` have marked class `{(1_S, 1_M)}`. Suppose the rows `S \ {1_S}` admit an
order `s_1, ..., s_k` such that the class of `(s_i, 1_M)` contains no cell of row `1_S`, no
other cell of row `s_i`, and otherwise only cells of rows `s_j` with `j > i`. If
`(nu, mu)` is forward sufficient on `E`, then `mu = psi o pi_(1_M)` for a permutation `psi` of `A`.

*Proof.*
1. The origin source `c_0` feeds only relay `1_S`, at position `1_M`. With every other
   source fixed, the side relays do not move, and the sink returns `c_0` from
   `y_(1_S) = mu(c_0, rest)`. So `mu(., rest)` is injective, hence a bijection of `A`, for
   every `rest`.
2. Given any assignment and targets `t_1, ..., t_k`, change the origin source of `s_i` for
   `i = 1, ..., k` in turn. That source sits at position `1_M` of relay `s_i` and nowhere
   else in that row, so by step 1 some value makes `y_(s_i) = t_i`. It occurs elsewhere
   only in rows `s_j` with `j > i`, so `c_0`, `y_(1_S)` and the relays already set keep
   their values.
3. If two assignments give the same `y_(1_S)`, steer both to the same side relays. Their
   origin sources `c_0` are unchanged, the sink sees equal inputs, and it returns both
   `c_0`. So `y_(1_S)` determines `c_0`.
4. So `mu(a, rest) = mu(a', rest')` forces `a = a'`, and with step 1 the bijection
   `mu(., rest)` is the same `psi` for every `rest`. QED

The encoder is then `x -> psi o x`, bijective over every group, so no realization with
forward table dominating `E` is strict.

**At a group realization.** The marked class is the origin iff `S ∩ M^(-1) = {1}`. The
origin cell of `s` is private iff `s` is no product `s' m'` other than `s . 1`.

**Consequence for Theorem B.** Its partitions use only non-identity memory labels, so the
marked class is the origin and every origin cell is a singleton. So every
forward-sufficient rule pair on them has a permutation encoder, and no rule pair that is
forward sufficient on a star partition `E_X` is strict. A square table that can carry a
strict pair needs anchoring cells `(s, 1_M) ~ (s', m')` whose gluing reaches row `1_S` or
closes a cycle, so some decoder addresses must be memory products. The shift–shear
designs do this through the marked cells `(v_r^(-1), v_r)`, which enlarge the marked class.

## 8. Reflected squares decide the transposed hinges

By `transposed-hinges-are-conjugated-commutators`, a forward identification
`s m = s' m'` keeps its transposed reverse identification `m s = m' s'` exactly when
`m'^(-1) m` commutes with the common product.

**Corollary H.** In `Gamma = pi_1 X` for a complete one-vertex VH complex, let
`h v^(-1) h' v'^(-1)` be a square in positive letters, and take the identification
`(s, m) = (h, v^(-1)) ~ (s', m') = (v', h'^(-1))`. Its transpose `v^(-1) h = h'^(-1) v'` holds iff
the reflected word `h v'^(-1) h' v^(-1)` is also a square of `X`.

*Proof.* `v^(-1) h` is in normal form, with vertical part `v^(-1)` and horizontal part `h`. By
completeness the word `h'^(-1) v'` has a unique normal form `w k`, given by the unique
square at the corner `(h'^(-1), v')`. By uniqueness of normal forms the transpose holds iff
`w = v^(-1)` and `k = h`, that is, iff `h'^(-1) v' h^(-1) v` bounds a square. Conjugating by `v`
and inverting gives `h v'^(-1) h' v^(-1)`. QED

Every square with `v = v'` is its own reflection, and its transposed hinge dies. A
square that is not reflection-symmetric leaves the nontrivial hinge
`(h'^(-1) v')^(-1) v^(-1) h`, and square moves decide it. So the lattice target lives or dies on
irreversibility of the encoder, not on its reverse table.

## 9. Host filter: surjunctive quotients must kill both factor subgroups

Let `X` be complete, `Gamma = pi_1 X`, `F_V = <V>` and `F_H = <H>`. `Gamma` acts freely and
vertex-transitively on `T_V x T_H` and preserves the vertical and horizontal edge types.

**Proposition G.** If a homomorphism `f : Gamma -> G` into a surjunctive group is injective on
`F_V` or on `F_H`, then `Gamma` is surjunctive.

*Proof.*
1. `Gamma` acts on the factor `T_H`, transitively on vertices. The base vertex of `T_H` is
   the vertical slice through the base point `o`, whose vertices are `F_V . o`. An element
   fixing it sends `o` to some `u . o` with `u in F_V`, so freeness makes it equal to `u`.
   Hence the stabilizer is `F_V`.
2. `Gamma` is torsion-free: a finite subgroup fixes a point of the CAT(0) complex
   `T_V x T_H`, and the action is free.
3. Bass–Serre theory, after subdividing the edges of `T_H` that `Gamma` inverts, writes `Gamma`
   as the fundamental group of a graph of groups with injective edge maps. Its vertex
   groups are conjugates of `F_V` and, after subdivision, midpoint stabilizers `P`
   containing an edge stabilizer `Q <= F_V^g` with `[P : Q] <= 2`.
4. `f` is injective on each conjugate of `F_V`. On `P`, `ker f ∩ P` meets `Q` trivially, so it
   injects into `P / Q`, has order at most two, and is trivial by step 2.
5. `graph-folds-over-surjunctive-groups-are-surjunctive` makes `Gamma` surjunctive. The case
   of `F_H` uses `T_V`. QED

**Consequences.**
* A strict automaton over `Gamma` forces every homomorphism into a surjunctive group to
  kill a nontrivial element of `F_V` and one of `F_H`.
* The quotient by the finite residual `Gamma_0` is residually finite, hence sofic and
  surjunctive. So a host of a strict automaton has `Gamma_0 ∩ F_V != 1` and
  `Gamma_0 ∩ F_H != 1`.
* If `Gamma` has a finite-index simple subgroup `Gamma_s`, then `F_V ∩ Gamma_s != 1`, so
  injectivity of `f` on `F_V` forces `ker f ∩ Gamma_s = 1`. The hypothesis then embeds
  `Gamma_s` in a surjunctive group, which already makes `Gamma` surjunctive, because
  surjunctivity passes to subgroups and up from finite-index subgroups. The filter
  excludes nothing on virtually simple lattices, and they are the hosts that survive it.

## 10. Where the lattice target stands

* Forcing the squares is solved (Section 5 update). Architectures that force them
  through a key-controlled data shear are never strict (Section 6). Partitions whose
  origin rows are private never carry strict rules (Section 7).
* Reverse hinges are cheap: they survive at every square that is not
  reflection-symmetric (Section 8).
* A host must lose part of both factor subgroups in every surjunctive quotient
  (Section 9). Virtually simple lattices survive.
* The remaining problem is a key automaton that mixes its tracks and is strict on its
  own, over a virtually simple lattice, whose left inverse forces an anchored square
  presentation (Section 7). In the linear case this is a one-sided matrix inverse over
  `F_2[Gamma]`, a failure of stable finiteness, where two-by-two track gadgets need
  2-torsion (Lemma D). No such key automaton is known, and no obstruction specific to
  lattices in products of trees is known.
