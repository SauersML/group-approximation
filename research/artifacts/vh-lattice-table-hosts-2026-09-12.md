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
step (Section 5).

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
