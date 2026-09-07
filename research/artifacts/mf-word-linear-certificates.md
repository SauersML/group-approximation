# Linear certificates for individual MF-radical words

This gives a strengthening of the finite-certificate section of
`non_mf_groups_exist.tex`. The contribution is a written proof for individual
words, including words in groups whose MF radical is proper. It uses ordinary
tensor powers in operator norm. No Lean verification or priority over the
literature is asserted.

## Statement

Let `G = F_m / N`, where `m` is finite, let `w` be a word in `F_m`, and put

\[
 d_w(U)=\|w(U)-I\|,\qquad
 \delta_R(U)=\max_{r\in R}\|r(U)-I\|
\]

for a finite subset `R` of `N` and a tuple `U` of `m` unitary matrices of any
common positive dimension. The maximum over the empty set is zero. Then
the following are equivalent:

1. Every homomorphism from `G` to an MF group kills the image of `w`.
2. There are finite `R subset N` and `eta > 0` such that
   `delta_R(U) < eta` implies `d_w(U) < 1` in every dimension.
3. There are finite `R subset N` and `C > 0` such that
   `d_w(U) <= C delta_R(U)` in every dimension.

In fact, the same `R` in (2) works in (3), with `C = 6/eta`.
No perfectness, torsion, normal-generation, property-(T), or finite
presentation hypothesis is needed. The constants and finite window are
existential; this is not an algorithm for finding them.

## 1. A scalar cannot hide from all its first powers

Let `z` have modulus one and let `t = |z-1| > 0`. If an integer `N >= 1`
satisfies `N t > 4`, then some `1 <= k <= N` satisfies `|z^k-1| > 1`.

Otherwise `|z^j-1|^2 = 2 - 2 Re(z^j) <= 1` for every `1 <= j <= N`,
so `Re(z^j) >= 1/2`. For `S = z + ... + z^N` this gives

\[
 N/2\le\operatorname{Re}S\le |S|,
 \qquad (1-z)S=z-z^{N+1},\qquad t|S|\le2.
\]

Together these imply `Nt <= 4`, a contradiction. In particular, with
`N = floor(4/t) + 1` there is such a `k` with

\[
 kt\le Nt\le4+t\le6. \tag{1}
\]

The selection of the exponent matters: a predetermined tensor power can
send a nontrivial scalar root of unity back to the identity.

## 2. Operator-norm amplification with linear cost

Let `A` be a finite-dimensional unitary and `t = ||A-I|| > 0`. By unitary
diagonalization there is an eigenvalue `z` of `A` with `|z-1| = t`. If `v`
is a corresponding unit vector, then `v^(tensor k)` is a unit eigenvector
of `A^(tensor k)` with eigenvalue `z^k`. Section 1 therefore gives

\[
 1\le k\le 6/t,\qquad \|A^{\otimes k}-I\|>1. \tag{2}
\]

For any two unitaries `A,B`, telescoping one tensor factor at a time gives

\[
 A^{\otimes k}-B^{\otimes k}
 =\sum_{j=0}^{k-1}
 A^{\otimes j}\otimes(A-B)\otimes B^{\otimes(k-1-j)},
 \qquad
 \|A^{\otimes k}-B^{\otimes k}\|\le k\|A-B\|. \tag{3}
\]

Here the operator norm of a tensor product is the product of its factor
norms, and the unitary factors have norm one. The map
`A -> A^(tensor k)` is a group homomorphism, so for every group word `r`,

\[
 r(U_1^{\otimes k},\ldots,U_m^{\otimes k})=r(U)^{\otimes k}.
 \tag{4}
\]

Equations (3)--(4) imply `delta_R(U^(tensor k)) <= k delta_R(U)`.
All statements hold for scalar matrices as well; there is no removal of
scalar phases or conversion to normalized Hilbert--Schmidt norm.

## 3. Proof of the equivalences

**(1) implies (2).** Exhaust the countable set `N` by finite increasing
sets `R_n`. If (2) fails, for every `n >= 1` choose a dimension `d_n` and a
tuple `U^(n)` with `delta_(R_n)(U^(n)) < 1/n` and `d_w(U^(n)) >= 1`.
Evaluation defines a homomorphism from `F_m` into the unitary group of

\[
 \mathcal Q=\prod_n M_{d_n}(\mathbb C)/\bigoplus_n M_{d_n}(\mathbb C).
\]

Every fixed relation eventually belongs to `R_n`, so its evaluations tend
to the identity. Thus the homomorphism descends to `G`. Its countable image
is MF by the corona characterization, while the image of `w` has distance
at least one from the identity. This contradicts (1).

**(2) implies (3), with the same finite window.** Fix a tuple `U` and write
`t=d_w(U)` and `delta=delta_R(U)`. If `t=0`, the bound is immediate. If
`t>0`, choose `k` using (2) of Section 2 for `A=w(U)`. The amplified tuple
has marked displacement greater than one, so the contrapositive of the
threshold assumption gives

\[
 \eta\le\delta_R(U^{\otimes k})\le k\delta\le\frac6t\delta.
\]

Multiplication by `t/eta` proves `d_w(U) <= (6/eta) delta_R(U)`.
The argument also covers `delta=0`: in that case a positive `t` would
contradict the displayed inequality.

**(3) implies (1).** Compose any homomorphism from `G` to an MF group with
a corona embedding of its countable image. Lift the images of the finitely
many generators to sequences of unitaries. Such lifts exist: for a lift
`a_n` of a corona unitary, both `a_n^*a_n-I` and `a_na_n^*-I` tend to zero,
and the polar unitaries of `a_n` differ from `a_n` by a norm-null sequence
after finitely many coordinates are replaced. Each word of `R` is a
relation, so its lifted defect tends to zero. The inequality in (3) makes
the lifted displacement of `w` tend to zero, hence the homomorphism kills
`w`. This proves the theorem.

## 4. Consequences for the manuscript

**Finite sets of words.** For a finite set `W` of MF-radical words, apply
the theorem to each word, take the union of the finite relation windows,
and take the maximum of the positive constants. Then

\[
 \max_{w\in W}d_w(U)\le C\delta_R(U).
\]

Alternatively a single threshold for the maximum gives `C=6/eta` directly
by amplifying a word attaining that maximum. Taking `W` to be the generator
words recovers the manuscript's full-radical linear-collapse proposition
without its perfectness and quadratic-bootstrap argument.

**Finite presentation witnesses.** If `w` is MF-invisible in `F_m/N`, the
same word is MF-invisible in the finitely presented group
`P_R = <x_1,...,x_m | R>` supplied by the theorem: apply the converse to
the same inequality. The natural surjection `P_R -> G` preserves the
mark. If the mark is nontrivial in `G`, it is nontrivial in `P_R`, so
`P_R` is non-MF. More generally the marked-word radical condition holds
on the entire clopen relation cylinder defined by `R` in the space of
`m`-marked groups. Nontriviality of the mark is a separate clopen condition.

**A specified finite presentation.** If
`G=<x_1,...,x_m | S>` with `S` finite, the theorem can use `S` itself.
Each `r in R` is a finite product of conjugates of elements of `S` and
their inverses. Let `a_r` be the number of factors in one such expression.
Unitary conjugation preserves the norm and products telescope, giving
`d_r(U) <= a_r delta_S(U)`. With `A=max(1,max_(r in R) a_r)`, one has
`d_w(U) <= C A delta_S(U)`. This explicitly accounts for the change of
presentation; it does not assume the compactness window was contained in
the originally listed relators.

## Relation to existing work and verification boundary

The existing Cairn claims `full-mf-radical-linear-relator-inequality` and
`full-mf-radical-forces-perfect-commutator-bound` treat simultaneous
collapse of all generators through perfectness. The present theorem
includes a word in a proper radical. `sofic-radical-linear-action-criterion`
uses Cartesian powers and Hamming distance, while
`adaptive-tensor-amplification` changes operator-norm separation to an HS
separation and pays a dimension-dependent cost. Neither is the assertion
proved here.

The underlying tensor-amplification method is standard in matrix
approximation. The repository's `TensorPowerAmplification.lean` proves
tensor telescoping, and `OperatorMFPairAmplification.lean` supplies a
different bound using a real-part gap; those files do not by themselves
formally verify the linear spectral bound or the new wordwise theorem.
This artifact supplies the complete mathematical argument. Cairn checks
the claim graph and references, not the correctness of this prose proof.

The concurrently developed `hyperlinear-radical-has-linear-word-certificate`
is the squared normalized-HS counterpart. Its trace-amplification argument
and norm are different. The present proof keeps scalar phases and uses an
eigenvalue attaining the operator norm, so it gives a linear bound in the
unsquared operator-norm defects.
