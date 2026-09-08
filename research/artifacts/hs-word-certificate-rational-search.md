# Exact rational falsification of an HS word certificate

2026-09-07. This is an elementary effectiveness refinement of the existing
finite word-certificate criterion. It constructs no nonhyperlinear group.
The Cayley parametrization and semidecision method already occur in the
repository's `hyperlinear-hs-dehn-modulus-solvable-word-problem-proof`;
the contribution here is their specialization to one proposed coefficient
and a dependency-free executable verifier. No global novelty or Lean
verification is claimed.

## Proposition

Fix finitely many generators, a finite list R of words, a word w, and a
positive rational C. Set

\[
 e_v(U)=\frac1d\sum_{i,j}|v(U)_{ij}-\delta_{ij}|^2,
 \qquad F_C(U)=e_w(U)-C\sum_{r\in R}e_r(U).
\]

The following are equivalent:

1. The proposed bound `e_w <= C sum_R e_r` fails on a unitary tuple in
   some finite positive dimension.
2. It fails strictly on a tuple of exactly unitary matrices with entries
   in Q(i).
3. It fails strictly on a tuple of Cayley transforms of skew-Hermitian
   matrices with entries in Q(i).

Consequently failure of a fixed proposed rational coefficient is uniformly
recursively enumerable. Validity of that fixed coefficient is a Pi-zero-one
predicate on the finite word data. Neither statement asserts a hardness
classification or a decidable validity test.

## Proof

For a skew-Hermitian matrix K, `I+K` is invertible: for every vector x,

\[
 \|(I+K)x\|^2=\|x\|^2+\|Kx\|^2.
\]

The Cayley transform `T(K)=(I-K)(I+K)^(-1)` is unitary. Indeed the two
polynomials `I-K` and `I+K` commute, and taking adjoints interchanges them,
which gives `T(K)^*T(K)=I`. Rational real and imaginary entries are
preserved by the inverse and product, so K in Q(i) gives T(K) in Q(i).

Conversely, if V is unitary and has no eigenvalue -1, then
`K=(I-V)(I+V)^(-1)` is skew-Hermitian and `T(K)=V`. Such V are dense in
U(d): multiply any given V by scalar phases tending to one and avoiding
the finitely many phases producing an eigenvalue -1. Rational
skew-Hermitian K are dense in the real vector space of all skew-Hermitian
matrices. Continuity of inversion at the invertible matrix I+K then shows
that their Cayley transforms are dense in U(d). Apply this separately to
each generator, in the same fixed dimension.

Each free-word evaluation is continuous on unitary tuples; inverses there
are adjoints. Thus F_C is continuous. A strict positive value of F_C
persists in a neighbourhood, which contains a rational Cayley tuple by
density. This proves 1 implies 3. The other implications are immediate.

There are d^2 real rational parameters in a d-dimensional skew-Hermitian
matrix. Enumerate dimensions and these parameters, compute the Cayley
transforms by exact rational elimination, and evaluate F_C exactly. Its
value is rational, and positivity is decidable. The procedure stops on
some tuple if and only if the coefficient fails. This proves the
semidecision assertion, including the empty-relator and empty-word cases.

An explicit fair schedule, implemented by `rational_tuples`, uses stages
h=1,2,... . At stage h enumerate d<=h, a common positive denominator q<=h,
and all integer parameter vectors with total absolute numerator sum <=h.
Each stage is finite. Every tuple of rational skew-Hermitian matrices has
some common denominator q and a finite numerator sum, so it appears at
every sufficiently large stage. Repetition is harmless. Optional bounds
in the command line restrict this enumeration and are reported as bounds;
they do not preserve its unbounded completeness assertion.

## What the executable certifies

`experiments/hs_word_certificate.py` uses exact pairs of rational numbers
for complex entries. The `verify` command checks dimensions and exact
unitarity before evaluating words, and sums squared entry differences
directly, divided by dimension. It never trusts energies stored in its
input. In particular inverse letters are evaluated as adjoints only
after the input matrices have passed the unitarity check.

A witness contains `format: hs-word-counterexample-v1`, a `candidate`, and
`matrices`. The candidate has distinct `generators` names, signed integer
word lists `relators` and `word`, and a positive rational `coefficient`.
Indices start at one; a negative index denotes the inverse. Each matrix
entry is `[real, imaginary]`, with integers or rational strings, for
example `["3/5", "4/5"]`. Floating-point JSON entries are rejected.

```
python3 experiments/hs_word_certificate.py verify witness.json
python3 experiments/hs_word_certificate.py search candidate.json --max-tests 1000
python3 -m unittest discover -s experiments -p test_hs_word_certificate.py -v
```

Exit 0 means a strict counterexample was verified. Exit 2 means either
the supplied tuple does not violate the inequality or the bounded search
is inconclusive. Exit 64 means invalid input. Search success includes the
actual rational matrices so it can be replayed without rerunning a search.

The tests include a Pauli commutator with exact involution relators,
scalar phases, empty relator lists, equality at the proposed coefficient,
identity padding and its dimension normalization, complex Cayley matrices,
malformed/nonunitary input, and the bounded-search outcome. These verify
the finite computation, while the proof above establishes the density
and semidecision assertions.

## Boundary of the existence argument

The previously established `hyperlinear-radical-has-linear-word-certificate`
asserts that a radical word has some finite relator list and integer N
valid in every matrix dimension. This proposition permits exact refutation
of any proposed N. It does not select a valid N, and no finite period of
unsuccessful counterexample search proves validity. Changing N after each
refutation does not construct an all-dimensions inequality.

Nontriviality of the word in the presented group is a separate obligation.
Even a sound inequality for a trivial word proves no nonhyperlinearity.
Conversely, rejecting one coefficient does not prove the group hyperlinear:
another coefficient may work, or the selected word may lie outside its
hyperlinear radical. The main existence claim remains open.

The current primary-source check, on 2026-09-07, included
[Taller--Vidick, version 2](https://arxiv.org/html/2507.22444v2).
Its abstract and introduction explicitly retain perfect completeness as
an additional condition needed for their route to nonhyperlinear existence.
This supports that route's stated boundary; it is not an exhaustive
classification of every possible existence proof.
