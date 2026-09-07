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
