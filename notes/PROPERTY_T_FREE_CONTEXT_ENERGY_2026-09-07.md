# Exactly what finite relation-energy certificates prove

Date: 2026-09-07.

## Outcome and scope

The requested existence theorem remains unproved in this work. In particular,
neither the property-(T)-free explicit-group target nor the binary-Leavitt
target is closed by this note. The result below is a complete elementary
characterization of one proposed proof mechanism. It strengthens the
[finite-ball observation](PROPERTY_T_FREE_FINITE_BALL_LIMIT_2026-09-07.md):
arbitrarily many **fixed, finite word contexts** do not turn a vector
relation-energy argument into a non-MF obstruction. Polynomial contexts are
also excluded for a nontrivial marked word.

The concurrently integrated
[finite-context relator-energy note](../research/artifacts/finite-context-relator-energy.md)
already proves the ordinary-word-kernel and polynomial-context conclusions.
Those are reused below for context, not registered as duplicate Cairn claims.
The additional statement here is the fixed-list free-subgroup criterion,
with a linear witness-size bound in place of a full word ball.

The proof uses free groups, coset actions, extension of partial permutations,
and Cauchy--Schwarz. It uses no rigidity theorem. No literature novelty or
Lean verification is claimed. Cairn records the written mathematical proof;
its graph validation is not a proof-assistant check.

Throughout, a word is a finite string in letters
`s_1,...,s_m,s_1^{-1},...,s_m^{-1}`. Its length is the length of the chosen
string, so freely reducing it can only improve the bounds below. Matrix
products act on column vectors from right to left.

## 1. A finite permutation witness with a linear size bound

**Lemma.** Let `F=F(s_1,...,s_m)`, let `H` be any subgroup of `F`, and let
`Q` be a finite set of word strings. There are a finite set `X`, a point
`o in X`, and permutations `sigma_1,...,sigma_m` of `X` such that, for
every `q in Q`, the endpoint of the word permutation at `o` is the coset
`qH`. Here `X` is identified with a finite subset of the left coset space
`F/H`, and `o=H`. Moreover,

\[
 |X|\leq 1+\sum_{q\in Q}|q|.                                      \tag{1}
\]

**Proof.** Include in `X` the cosets of all suffixes of every word in `Q`,
including the empty suffix. There are at most the number in (1). For each
generator, restrict left multiplication by `s_i` to the pairs of endpoints
that both lie in `X`. This is a bijection between a subset `D_i` of `X`
and a subset `E_i` of `X`. Since `|D_i|=|E_i|`, choose any bijection
`X\D_i -> X\E_i` and use it to complete the partial map to `sigma_i`.

The inverse permutation agrees with multiplication by `s_i^{-1}` whenever
both endpoints lie in `X`: that edge is the inverse of an edge already in
the partial map. Applying a word to `H` follows its suffixes from right to
left. Every such step was retained, so its endpoint is exactly `qH`.
This proves the lemma. The construction is an existence argument for an
arbitrary `H`; it does not assume an algorithm for its membership problem.
`square`

## 2. Universal energy domination is subgroup membership

For a unitary tuple `U=(U_1,...,U_m)` write

\[
 E_v(U)=(v(U)-I)^*(v(U)-I).
\]

**Theorem.** Given word strings `v_1,...,v_k,w`, the following are equivalent:

1. `w` belongs to the subgroup `H=<v_1,...,v_k>` of the **free group** `F`.
2. Some finite `C>=0` satisfies

   \[
   E_w(U)\leq C\sum_{j=1}^k E_{v_j}(U)                           \tag{2}
   \]

   for every matrix dimension `d>=1` and every `U in U(d)^m`.
3. In every finite permutation tuple, every vector fixed by all the
   `v_j(U)` is fixed by `w(U)`.

If `w` is a product of `L` factors from `{v_j,v_j^{-1}}`, then (2) holds
with `C=L^2`. If `w notin H`, a counterexample to (2), for **every** `C`,
exists in a dimension satisfying

\[
 d\leq 1+|w|+\sum_{j=1}^k|v_j|,                                \tag{3}
\]

and has a unit vector `xi` with

\[
 (v_j(U)-I)\xi=0\quad\text{for all }j,\qquad
 \|(w(U)-I)\xi\|^2=2.                                          \tag{4}
\]

**Proof of 1 implies 2.** Suppose
`w=v_(i_1)^{epsilon_1}...v_(i_L)^{epsilon_L}` in `F`, where each
`epsilon_t` is `1` or `-1`. Evaluation in arbitrary unitaries respects
free-group equality. Set `A_t=v_(i_t)(U)^{epsilon_t}`. The telescoping
identity is

\[
 A_1\cdots A_L-I=\sum_{t=1}^L A_1\cdots A_{t-1}(A_t-I).
\]

For each vector `xi`, unitarity and Cauchy--Schwarz give

\[
 \|(w(U)-I)\xi\|^2
 \leq L\sum_{t=1}^L\|(A_t-I)\xi\|^2
 \leq L^2\sum_{j=1}^k\|(v_j(U)-I)\xi\|^2.                       \tag{5}
\]

The inverse-letter step is exact:
`(V^{-1}-I)xi=-V^{-1}(V-I)xi`, so it has the same norm as `(V-I)xi`.
Repeated occurrences contribute at most `L` times the sum over the
original list. Since (5) holds for every vector, it is the operator-order
inequality (2). For `L=0`, `w=1` and `C=0` works.

**Proof of 2 implies 3.** Evaluate (2) on a common fixed vector. Its
right-hand quadratic form is zero, hence so is the left-hand form.

**Proof of 3 implies 1, with the bound.** Suppose `w notin H`. Apply the
lemma to `Q={v_1,...,v_k,w}` and this subgroup `H`. Let
`U_i delta_x=delta_(sigma_i(x))` and `xi=delta_H` in `ell^2(X)`.
Each `v_j` fixes `H`, while `wH!=H`. Thus all relation displacements
vanish and the target displacement is a difference of two orthogonal
unit basis vectors. This is (4), contradicts 3, and gives (3). It also
contradicts (2) directly by the inequality `2<=0`. `square`

The distinction between subgroup and normal closure matters. For example,
in `F(a,b)`, the word `b^{-1}ab` belongs to the normal closure of `a`
but not to `<a>`. Consequently no constant controls
`E_(b^{-1}ab)(U)` by `E_a(U)` on the same vector. Adding the context `b`
does supply that particular word equality, as the next corollary explains.

## 3. Finite transported tests give exactly ordinary word equalities

Let `G=<S | R>=F/N`, where `N=<<R>>` is the normal closure in `F`.
The relation set may be infinite. Choose finitely many pairs
`(r_j,q_j)` with `r_j in R` and `q_j in F`, and define

\[
 D_j(U)=(r_j(U)-I)q_j(U).
\]

**Corollary.** For these fixed pairs, the existence of a finite constant
`C>=0` such that

\[
 E_w(U)\leq C\sum_j D_j(U)^*D_j(U)                             \tag{6}
\]

in all finite matrix dimensions is equivalent to

\[
 w\in\langle q_j^{-1}r_jq_j:j\rangle\leq F.                    \tag{7}
\]

Allowing the finite list of pairs and `C` to vary, a certificate (6)
exists **if and only if `w=1` in `G`**.

**Proof.** Put `v_j=q_j^{-1}r_jq_j`. Then

\[
 v_j(U)-I=q_j(U)^*D_j(U),\qquad E_{v_j}(U)=D_j(U)^*D_j(U).
\]

The theorem proves the fixed-list equivalence. Every such `v_j` lies in
`N`, proving necessity of `w in N`. Conversely, membership in a normal
closure means that `w` is a finite product of conjugates of relators and
their inverses. Use those finitely many conjugates in (7), and use (5)
for the bound. This proves sufficiency, including inverse relators.
`square`

This is a positive completeness statement for this certificate language,
as well as a limitation: it certifies exactly ordinary word triviality.
An MF-invisible word that is nontrivial in the group cannot have such a
certificate. For the fixed list, its counterexample dimension is at most

\[
 1+|w|+\sum_j(2|q_j|+|r_j|).                                  \tag{8}
\]

## 4. Polynomial contexts do not repair the obstruction

**Corollary.** Suppose `w!=1` in `G`. For any finite relator list
`r_1,...,r_k` and any finitely supported complex free-group polynomials
`p_1,...,p_k`, there are a finite permutation tuple `U` and a unit vector
`xi` such that

\[
 (r_j(U)-I)p_j(U)\xi=0\quad(j=1,\ldots,k),\qquad
 \|(w(U)-I)\xi\|^2=2.                                         \tag{9}
\]

Thus no inequality (6) holds universally with
`D_j(U)=(r_j(U)-I)p_j(U)`. The same conclusion holds with an added slack
`alpha I` on the right for any `alpha<2`.

**Proof.** Use the lemma with the normal subgroup `N`, and include `w`
and all words `q` and `r_jq` for `q` in the support of `p_j` in `Q`.
Because `r_j in N` and `N` is normal, `(r_jq)N=qN`. Both paths are
preserved by the finite permutations. Therefore
`(r_j(U)-I)q(U)xi=0` for each support word, and linearity gives the first
part of (9). The cosets `wN` and `N` are distinct, which gives the second
part. Evaluating the purported inequality yields `2<=0`, or `2<=alpha`.
No assertion about approximate satisfaction in full operator norm is used.
`square`

There is also an effective construction avoiding membership computations
in `G`. Generate the free subgroup `H` by the finitely many words
`q^{-1}r_jq` over the polynomial supports. The promise `w!=1` in `G`
implies `w notin H`, since `H` lies in the relator normal closure.
The fixed-list theorem and its folding implementation then give a witness
of dimension at most

\[
 1+|w|+\sum_j\sum_{q\in\operatorname{supp}p_j}(2|q|+|r_j|).
\]

The identity `E_(q^{-1}r_jq)=((r_j-I)q)^*((r_j-I)q)` shows that the
witness kills each individual support-word residual, hence their linear
combination. This alternative proof is wired into the existing Cairn
polynomial-context claim through
`polynomial-context-witness-via-free-subgroup`. Without the nontriviality
promise, the counterexample still refutes the fixed inequality but does not
decide the quotient word problem. A member report for this enlarged word
list need not imply domination by the original polynomial contexts, whose
coefficients may cancel.

## 5. What remains to prove for non-MF existence

The MF convention here is group embedding in the unitary group of
`prod_n M_(d_n)(C) / directSum_(operator norm) M_(d_n)(C)`.
An adequate new construction would specify a countable `G`, a nontrivial
word `w`, and prove that every such corona homomorphism kills `w`, without
using the repo's Kazhdan-dependent existence theorem as an input.

None of (2), (6), or (9) gives global control of the matrices' relator
defects. In the permutation witnesses a relator can fix `xi` while moving
another basis vector. A scalar estimate involving
`max_r ||r(U)-I||` may still be possible, as may a matrix-dependent
selection argument with additional established hypotheses. Those mechanisms
are outside the theorem, and no successful instance is supplied here.

In particular, this result does not disprove the requested existence
theorem, does not claim that property (T) is necessary, and does not remove
any dependency from the current non-MF manuscript.

## 6. Exact certificate generation and replay

The stdlib-only
[certificate builder](../experiments/word_energy_certificate.py) constructs
finite permutation witnesses for the fixed-list theorem. Its JSON input
contains `generator_count`, `subgroup_words`, and `target_word`; each word
is a list of signed generator indices. For example, `[ -2, 1, 2 ]` means
`b^{-1}ab`. The output uses the convention
`U_i delta_x=delta_(permutations[i-1][x])`.

The construction is the usual finite inverse-graph folding method. Begin
with a based loop for each inverse subgroup word and a based path for the
inverse target word. Include the inverse of every labelled edge. Fold two
edges with the same label and initial vertex by identifying their terminal
vertices. Each nontrivial identification decreases the vertex count, so
the process terminates.

Folding does not change the subgroup of reduced loop labels: the two
identified endpoints were connected by a path labelled `s^{-1}s`, whose
free-group value is the identity. A path across an identified vertex can
be lifted by inserting such paths; the inserted labels contribute no
group element. Conversely every original based loop maps to a based loop.
After folding, paths with a given starting point and word label are unique.
Since inverse edges are present, deleting an adjacent inverse-letter pair
does not change a path's endpoint. Thus the target endpoint equals the
basepoint exactly when the target belongs to the original subgroup.
This is standard Stallings folding; see
[Kapovich--Myasnikov, *Stallings foldings and the subgroup structure of free
groups*](https://arxiv.org/abs/math/0202285).

If the endpoint is different, complete each partial labelled permutation
by matching its unused source and target vertices. Take the inverses of
these completed permutations as the matrices' tables: right-to-left matrix
evaluation of `w` then follows the constructed path labelled `w^{-1}`.
Folding and completion add no vertices, so (3) holds. The implementation
also preserves the original input words for replay, including free
cancellations.

The separate verification function checks bijectivity, all word endpoints,
the dimension bound, and target displacement using only integer arithmetic.
It does not trust the graph construction. A `member` report is explicitly
an algorithmic result; the replay verifier accepts only explicit permutation
counterexamples, not those reports.

Replay the committed four-dimensional example with:

```sh
python3 experiments/word_energy_certificate.py verify \
  research/artifacts/word-energy-fixed-list-certificate.json
python3 -m unittest discover -s experiments -p test_word_energy_certificate.py -v
```

In that example `v_1=a` and `w=b^{-1}ab`. The basepoint is `0`,
`a` swaps `1,2`, and `b` swaps `0,1` and `2,3`. Thus `a` fixes
`delta_0`, while `b^{-1}ab` sends it to `delta_3`. In particular, the
global operator norm `||a(U)-I||` is `2`, even though its displacement
on the chosen vector is zero. This is a witness against the fixed-list
inequality, not a proof that `w` is nontrivial in a presented quotient:
indeed `w=1` in `<a,b | a>`.

The tests include cyclic membership, inverse factors and cancellation,
150 explicitly generated subgroup products, and independent finite-action
oracles for nonmembership. Malformed and tampered certificates are rejected.
These are exact computational checks of the implementation; the general
mathematical theorem is proved above.
