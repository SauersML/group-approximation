# Rectangle clauses and the arithmetical position of surjunctivity

Date: 2026-09-12. Lane `gk-logic`. Handwritten proofs; no computation.

This note settles what kind of statement Gottschalk's conjecture is.

- **Theorem 1 (two-table certificates).** A group is not surjunctive iff some
  pair of local rules satisfies the decoder identity on a forward rectangle
  `S x M` and fails the encoder-after-decoder identity on the reverse rectangle
  `M x S`. The identity survives coarser tables; its failure survives finer ones.
- **Theorem 2 (axiomatization).** The surjunctive groups are exactly the models
  of a decidable set of universal sentences
  `forall x (AND of equations -> OR of equations)`, with forward-rectangle
  premises and reverse-rectangle conclusions. Heredity, closure under
  ultraproducts, local embeddings and arbitrary directed colimits follow from the
  syntax. Existentially closed groups decide the conjecture.
- **Theorem 3 (upper bound).** Surjunctivity is `Pi^0_2` on finite, recursive and
  enumerated presentations. On a finitely generated group with decidable word
  problem, non-surjunctivity is `Sigma^0_1`, uniformly in the decider.
- **Theorem 4 (dichotomy).** Either every group is surjunctive and recognition is
  trivial, or surjunctivity is `Pi^0_2`-complete on enumerated presentations and
  undecidable on finite presentations, with the finite presentations of
  nonsurjunctive groups `Pi^0_1`-hard and not recursively enumerable.

So a counterexample is a finite certificate only modulo inequalities in a finitely
presented group. No uniform `Sigma^0_1` certificate format can list every
nonsurjunctive finite presentation, unless there are none. Relative to a host with
decidable word problem, such as the binary Leavitt unit group, the search is
`Sigma^0_1`.

No counterexample is constructed and the conjecture is not decided here.

## 0. Conventions

A cellular automaton over a group `G` has a finite alphabet `A`, a finite memory
and a local rule. With memory labels `M` and a labelling `lambda: M -> G`,

    tau(x)(g) = mu( (x(g lambda(m)))_(m in M) ),

and `tau` commutes with `(h.x)(g) = x(h^-1 g)`. Distinct labels may name the same
group element; the rule then reads that coordinate twice, and `tau` is still a
cellular automaton. This is the convention of
`strict-pairs-transfer-to-table-realizations` and of the certificate checker.

## 1. Tables and two identities

**Label data.** Fix finite sets `S` and `M`, each containing a distinguished label
`1`. The forward cells are `S x M` and the reverse cells are `M x S`. A *forward
table* is an equivalence relation `T_f` on `S x M`; a *reverse table* is an
equivalence relation `T_r` on `M x S`.

A *labelling* in a group `K` is a map `lambda: S ⊔ M -> K` sending both labels `1`
to `1`. It realizes the tables

    (s,m) T_f(lambda) (s',m')   iff   lambda(s) lambda(m) = lambda(s') lambda(m'),
    (m,s) T_r(lambda) (m',s')   iff   lambda(m) lambda(s) = lambda(m') lambda(s').

For a finite alphabet `A` and rules `mu: A^M -> A`, `nu: A^S -> A` define

    Dec(T_f):  every p: S x M -> A constant on T_f-classes satisfies
               nu( ( mu( (p(s,m))_(m in M) ) )_(s in S) ) = p(1,1);

    Enc(T_r):  every q: M x S -> A constant on T_r-classes satisfies
               mu( ( nu( (q(m,s))_(s in S) ) )_(m in M) ) = q(1,1).

**Lemma 1.1 (monotonicity).** If `T ⊆ T'`, then `Dec(T)` implies `Dec(T')` and
`Enc(T)` implies `Enc(T')`.

*Proof.* A function constant on the classes of the coarser relation `T'` is
constant on the classes of `T`, so the coarser condition quantifies over a subset
of the same functions. QED.

So the decoder identity is inherited by every coarser forward table, and the
failure of the reverse identity by every finer reverse table.

**Lemma 1.2 (evaluation).** Let `lambda` be a labelling in `K`, and let `tau` and
`sigma` be the automata over `K` with memories `lambda(M)`, `lambda(S)` and rules
`mu`, `nu`. Then

    sigma tau = id   iff   Dec(T_f(lambda)),
    tau sigma = id   iff   Enc(T_r(lambda)).

*Proof.* For `x` in `A^K` and `g` in `K`,

    sigma tau (x)(g) = nu( ( mu( (x(g lambda(s) lambda(m)))_m ) )_s ).

Put `p(s,m) = x(g lambda(s) lambda(m))`. It is constant on `T_f(lambda)`-classes,
and `p(1,1) = x(g)`. Conversely, `(s,m) -> g lambda(s) lambda(m)` induces an
injection of the classes into `K`, so every function constant on the classes
arises from some `x`. Hence `sigma tau = id` at every `g` iff `Dec(T_f(lambda))`.
The reverse composite is the same computation with the roles exchanged. QED.

**Lemma 1.3 (left inverses).** Every injective automaton `tau` over `K` has an
automaton `sigma` with `sigma tau = id`.

*Proof.* `tau` is a homeomorphism of the compact space `A^K` onto its closed
invariant image `X`. The inverse `X -> A^K` is continuous and equivariant, so
`y -> tau^-1(y)(1)` is locally constant on `X` and reads a finite window `S_0`
containing `1`. Choose `nu` on `A^(S_0)` with that value on patterns of `X` and
arbitrary values elsewhere. Equivariance gives `sigma(y)(g) = nu((y(g s))_s)` with
`sigma tau = id`. QED.

**Theorem 1.** `K` is not surjunctive iff there are label data `S, M`, a labelling
`lambda` in `K`, an alphabet `A` and rules `mu, nu` with

    Dec(T_f(lambda))   and   not Enc(T_r(lambda)).

*Proof.*
- (=>) Let `tau` be injective and not surjective, with memory `M ⊂ K` containing
  `1`. Lemma 1.3 gives `sigma` with memory `S` containing `1`. Label by inclusion.
  `Dec` holds by Lemma 1.2. If `Enc` held, then `tau sigma = id` and `tau` would be
  surjective.
- (<=) `sigma tau = id` makes `tau` injective. If `tau` were surjective, every
  `y = tau(x)` would satisfy `tau sigma(y) = tau(sigma tau (x)) = y`, so
  `tau sigma = id`, contradicting `not Enc`. QED.

**Strict data.** A tuple `D = (S, M, A, mu, nu, T_f, T_r)` is *strict* if `Dec(T_f)`
and `not Enc(T_r)`. Strictness is decidable: it checks finitely many functions.

**Corollary 1.4 (realizations).** If a labelling `lambda` in `K` has
`T_f(lambda) ⊇ T_f` and `T_r(lambda) ⊆ T_r` for strict `D`, then `K` is not
surjunctive.

*Proof.* Lemma 1.1 gives `Dec(T_f(lambda))` and `not Enc(T_r(lambda))`; apply
Theorem 1. QED.

**Corollary 1.5 (canonical host).** For strict `D` put

    P(D) = < x_a (a in S ⊔ M) | x_1 = 1 for both labels 1,
                                x_s x_m = x_s' x_m' whenever (s,m) T_f (s',m') >.

If `D` is realized in some group `K`, it is realized by the canonical labelling
`a -> x_a` of `P(D)`, which is then not surjunctive.

*Proof.* The relations hold in `K`, so `x_a -> lambda(a)` defines a homomorphism
`P(D) -> K`. Coincidences can only be created along it, so the canonical labelling
has forward table containing `T_f` and reverse table contained in `T_r(lambda)`,
hence in `T_r`. Apply Corollary 1.4. QED.

`P(D)` needs at most `|S||M|` relators, each of length at most four.

**Relation to the neighbouring nodes.**
- `strict-pairs-transfer-to-table-realizations` transports a strict pair together
  with a Garden-of-Eden pattern `p` on a window `Omega`; the cells `p`
  distinguishes must stay apart. Here the pattern is replaced by the reverse
  rectangle. A failure of `Enc` at `y` is a Garden-of-Eden pattern on the window
  `M S`, since every image point `y = tau(x)` has `tau sigma (y) = y`. The gain is
  syntactic: both halves of a certificate are identities of local rules on
  rectangles, so the premises and the conclusions of Section 2 are equations.
- `forward-memory-lifts-exclude-strict-cellular-sections` records `P(D)` for the
  exact forward table and shows it must be nonsurjunctive. Corollary 1.5 adds the
  converse bookkeeping: realizability of strict data is exactly the survival of the
  reverse inequalities in `P(D)`.

## 2. The axiomatization

For strict `D` let `rho_D` be the universal sentence

    forall (x_a)_(a in S ⊔ M):
       [ x_1 = 1 (both labels)  AND  AND_( (s,m) T_f (s',m') )  x_s x_m = x_s' x_m' ]
       ->  OR_( (m,s), (m',s') not T_r-related )  x_m x_s = x_m' x_s'.

An empty disjunction is false.

**Lemma 2.1.** `K` fails `rho_D` iff `D` is realized in `K`.

*Proof.* A failing instance is a labelling whose forward coincidences contain
`T_f` and all of whose reverse coincidences lie in `T_r`. QED.

**Theorem 2.** A group is surjunctive iff it satisfies `rho_D` for every strict `D`.

*Proof.* If `K` is not surjunctive, Theorem 1 gives `lambda`, and
`D = (S, M, A, mu, nu, T_f(lambda), T_r(lambda))` is strict and realized by
`lambda`, so `K` fails `rho_D`. If `K` fails some `rho_D`, Lemma 2.1 and Corollary
1.4 show `K` is not surjunctive. QED.

**Consequences.**
- **(a) Subgroups.** Universal sentences pass to subgroups. This recovers
  `surjunctivity-passes-to-subgroups`.
- **(b) Local embeddings and ultraproducts.** A failing instance of `rho_D` in `G`
  involves finitely many elements and products. An injective partial
  multiplication table of those elements into `K` preserves the premise equations
  and the conclusion inequalities, so `K` fails `rho_D`. Hence a group locally
  embeddable into surjunctive groups is surjunctive, and ultraproducts of
  surjunctive groups are surjunctive (Łoś). This agrees with Corollary A1 of the
  table-realization artifact.
- **(c) Directed colimits with arbitrary structure maps.** Let `G = colim G_i` fail
  `rho_D` through a labelling `lambda`. Lift the finitely many values of `lambda`
  to some stage. The finitely many premise equations hold at a later stage `j`.
  Every conclusion equation fails in `G`, so it fails at every stage, because an
  equation holding at a stage holds in the colimit. So `G_j` fails `rho_D`. This
  is the colimit permanence of `gottschalk-surjunctivity-fixed-tester-proof`, now
  read off the shape of the sentences: premises and conclusions are both
  equations.
- **(d) Direct products are not covered.** `K × L` fails `rho_D` when each
  conclusion equation fails in one factor or the other. That gives no failing
  instance in either factor. A Horn sentence, with a single equation as
  conclusion, would pass to products; these conclusions are genuine
  disjunctions. Whether surjunctivity passes to finite direct products is not
  decided here.
- **(e) Existentially closed groups decide the conjecture.** Gottschalk's
  conjecture holds iff some existentially closed group is surjunctive, iff every
  existentially closed group is surjunctive.
  *Proof.* `not rho_D` is an existential sentence. If it holds in some group `L`,
  it holds in `H * L`, which extends `H`. An existentially closed `H` therefore
  satisfies it and is not surjunctive. Conversely, a nonsurjunctive group refutes
  the conjecture. Every group embeds in an existentially closed group. QED.
- **(f) The conjecture as a statement about presentations.** `rho_D` holds in every
  group iff it holds in `P(D)`: the canonical labelling satisfies the premises,
  and every labelling satisfying them factors through `P(D)`, where equations can
  only be created. So

      Gottschalk's conjecture
        <=>  for every strict D, some conclusion equation of rho_D holds in P(D).

  Strictness is decidable and each equation in `P(D)` is `Sigma^0_1`. The
  conjecture is therefore a `Pi^0_2` sentence of arithmetic in this natural form.

## 3. Upper bounds

Syntaxes: `fp` for finite presentation codes, `rec` for finitely generated
recursive presentations, `enum` for countably generated recursively enumerated
presentations.

**Theorem 3.** Let `q` code a presentation `<X | R>` of `K` with `R` recursively
enumerable. Then `K` is not surjunctive iff there are strict `D` and words
`w_a` in `X^(±1)` (`a` in `S ⊔ M`, both labels `1` given the empty word) with

    (premises)    w_s w_m = w_s' w_m'  in K  for all (s,m) T_f (s',m'),      [Sigma^0_1]
    (conclusions) w_m w_s != w_m' w_s' in K  for all pairs not T_r-related.  [Pi^0_1]

Hence `NONSURJ_fp`, `NONSURJ_rec` and `NONSURJ_enum` are `Sigma^0_2`, and the
positive sets are `Pi^0_2`, uniformly in the code.

*Proof.* Lemma 2.1 and Theorem 2. A labelling in `K` is a choice of words. An
equation in `K` is witnessed by a finite derivation from `R`, which a
recursively enumerable relator set lets us enumerate. QED.

**Decidable hosts.** If `K` is finitely generated and its word problem is
decided by a total program `e`, both brackets become decidable, so
non-surjunctivity of `K` is `Sigma^0_1`, uniformly in `(q, e)`. For the binary
Leavitt unit group this is `leavitt-unit-certificate-predicates-are-decidable`.

## 4. The dichotomy

**Theorem 4.** Exactly one of the following holds.

- **(A)** Every group is surjunctive. Then `SURJ_fp`, `SURJ_rec` and `SURJ_enum` are
  the full sets, and the negative sets are empty; all are decidable.
- **(B)** Some group is not surjunctive. Then
  - **(B1)** some finitely presented group is not surjunctive, namely `P(D)` for
    the data of any counterexample (Corollary 1.5);
  - **(B2)** `SURJ_enum` is `Pi^0_2`-complete and `NONSURJ_enum` is
    `Sigma^0_2`-complete;
  - **(B3)** `SURJ_fp` is `Sigma^0_1`-hard and lies in `Pi^0_2 \ Pi^0_1`;
    `NONSURJ_fp` is `Pi^0_1`-hard and lies in `Sigma^0_2 \ Sigma^0_1`.

*Proof of (B2).* Surjunctivity is hereditary (Consequence (a)), holds for the
trivial group and fails for the finitely presented seed `E = P(D)`. By
`arbitrary-forbidden-seed-hereditary-property-switch` (clause P5) the positive
set on enumerated codes is `Pi^0_2`-hard and the negative set is
`Sigma^0_2`-hard. Theorem 3 supplies membership. For Markov properties the
enumerated hardness is Theorem 3.1 of Bilanovic--Chubb--Roven, Arch. Math. Logic
59 (2019) 293--312, as recorded in
`second-level-rice-theorem-for-local-approximation-properties`. This lane did not
re-check whether that node's two-generator bridge (clause (b)) uses more than
heredity and residual finiteness, so no `rec2` claim is made here.

*Proof of (B3).* Surjunctivity is a Markov property of finite presentations: the
trivial group has it, and `E` embeds in no surjunctive group, by heredity. By the
Adian--Rabin theorem (Lyndon--Schupp, *Combinatorial Group Theory*, Chapter IV,
Theorem 4.1), there is a computable map `w -> P_w` from words of a finitely
presented group `U` with `Sigma^0_1`-complete word problem to finite
presentations, with `P_w` trivial when `w = 1` in `U` and `E <= P_w` when
`w != 1`. So `{w : w = 1}` many-one reduces to `SURJ_fp` and `{w : w != 1}` to
`NONSURJ_fp`. A `Sigma^0_1`-complete set is not `Pi^0_1`, so `SURJ_fp` is not
`Pi^0_1` and `NONSURJ_fp` is not `Sigma^0_1`. Theorem 3 gives the upper bounds.
QED.

**Corollary 4.1.** The following are equivalent.

    (i)   Gottschalk's conjecture fails;
    (ii)  some finitely presented group is not surjunctive;
    (iii) SURJ_fp is undecidable;
    (iv)  NONSURJ_fp is not recursively enumerable;
    (v)   SURJ_enum is Pi^0_2-complete.

*Proof.* (i) gives the rest by (B). Under (A) the sets are full or empty, so
(iii), (iv) and (v) all fail; a computable set is not `Pi^0_2`-complete. QED.

**Answer to "is it `Pi^0_1` or `Sigma^0_1`?"** In its natural form the conjecture
is the `Pi^0_2` sentence of Consequence (f). The counterexample side is not
`Sigma^0_1` on finite presentations unless it is empty: listing every
nonsurjunctive finite presentation with finite certificates is impossible if one
exists. Individual counterexamples do have finite certificates relative to a
decider for their word problem, and a search over one decidable host is
`Sigma^0_1`.

## 5. Scope and what remains

- **What is new here.** The two-table form with the reverse rectangle; the
  universal axiomatization with equational premises and conclusions; the
  existentially closed test; the `Pi^0_2` upper bound; and the surjunctivity row
  of the recognition dichotomy. The hardness engines are the established switch
  theorem and the classical Adian--Rabin theorem, applied once a seed exists.
- **What this does not give.** It decides neither the conjecture nor the
  surjunctivity of any particular group.
- **The finitary core that remains open.** Fix realizable tables `T_f` and `T_r`.
  Does some alphabet with rules `mu, nu` make `(S, M, A, mu, nu, T_f, T_r)` strict?
  The alphabet is unbounded. The question has the shape of a uniform
  network-coding problem on two rectangles: one decoder must recover the corner
  from row encodings on the forward rectangle, and must fail to be undone on the
  reverse rectangle. No bound on the alphabet, and no decision procedure, is known
  here. Associativity links the two tables only through `P(T_f)`, and the whole
  conjecture lives in that link: which reverse coincidences are consequences of
  the forward relations.

## 6. Peeling the forward relations

Let `D` be rectangle data with forward table `T_f`. Choose spanning relators
class by class: for each class of size `c`, `c - 1` relators
`x_s x_m x_m'^-1 x_s'^-1`, with identity letters deleted and the word freely
reduced. Each generator occurs at most once in each relator. The `S`-labels and
`M`-labels are different generators, and a relator with `s = s'` or `m = m'`
reduces to length two.

**Relator hypergraph.** Its vertices are the generators and its hyperedges are
the sets of generators of the relators. The *2-core* is the largest subfamily of
relators in which every generator that occurs, occurs in at least two members.
It is unique, and it is reached by repeatedly deleting any relator that contains
a generator occurring in no other remaining relator, in any order.

**Proposition 6.1.** `P(D) ≅ C(D) * F`, where `C(D)` is presented by the
generators and relators of the 2-core and `F` is free.

*Proof.* If a generator `g` occurs once in a relator `r` and in no other remaining
relator, then `r` expresses `g` as a word in the other generators of `r`. A Tietze
move deletes `g` and `r`, and no other relator changes. After peeling to the
core, the surviving generators that occur in no core relator generate a free
factor. QED.

**Corollary 6.2.** If `D` is strict and realized in some group, then its 2-core
is nonempty and `C(D)` is not sofic. In particular `C(D)` is neither residually
finite nor amenable.

*Proof.* `P(D)` is not surjunctive (Corollary 1.5), hence not sofic, by
`sofic-groups-are-surjunctive`. Free groups are sofic, and free products of
sofic groups are sofic (Elek--Szabó, *On sofic groups*, J. Group Theory 9 (2006);
this lane did not re-read the statement). So `C(D)` is not sofic. If the core
were empty, `P(D)` would be free. QED.

**Corollary 6.3 (a rule-independent filter).** Let `T_f` be the forward table of
memories `M`, `S` in some group. If the 2-core of its relator hypergraph is
empty, or presents a sofic group, then no strict data with forward table `T_f` is
realized in any group. The filter reads only the forward products. No reverse
product and no rule needs to be examined, and the empty-core case needs no
citation.

*Proof.* `P(D) ≅ C(D) * F` is sofic, hence surjunctive. Its canonical labelling
satisfies `Dec`, so by Theorem 1 it satisfies `Enc` at its own reverse table. A
realization of `D` anywhere would give `not Enc` there, by the argument of
Corollary 1.5. QED.

**Examples and relations.**
- Memories `{1, a}` and `{1, b}` admit only the coincidences `a = b` and `ab = 1`.
  Their core presents at most `Z/2`, so no strict pair ever uses such memories.
- `forward-memory-lifts-exclude-strict-cellular-sections` is the case of no
  forward coincidences, where the relator set is empty.
- `strict-automaton-tables-present-an-invisible-window-difference` shows that the
  table group, including the window products, is nonsofic. Here the forward
  rectangle alone already carries a nonsofic core, and a free factor splits off.

