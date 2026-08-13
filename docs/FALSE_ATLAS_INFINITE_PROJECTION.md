# Infinite projections inside the hard Leavitt-atlas prefix pairs

Date: 2026-08-11

## 1. Result

Let

\[
 D=(000,001,010,011,10,11)
\]

be the six-leaf binary prefix code used in the all-depth survivor audit.
For each of the six distinct hard pairs \((q,l)\) isolated in
`atlas_survivor_prefix_obstruction.py`, let

\[
 A(q,l)=\mathbb F _2\langle q,l,q^*,l^*\rangle
 \subset L_{\mathbb F _2}(1,2).
\]

The projection identities in that script prove that all six cylinder
projections \(p_\alpha=\alpha\alpha^*\), \(\alpha\in D\), belong to
\(A(q,l)\).

**Theorem.** Every one of the six algebras \(A(q,l)\) contains an infinite
projection. More precisely, there are a cylinder \(e=p_\alpha\), one proper
binary child \(f=p_{\alpha0}<e\), and an element \(v\in A(q,l)\) such that

\[
 v^*v=e,\qquad vv^*=f,\qquad
 e=f+p_{\alpha1}.                                    \tag{1}
\]

In particular, \(A(q,l)\) is infinite-dimensional and is not stably finite.
It cannot be contained in any finite scalar prefix-chart algebra.

The identities are extracted and verified exactly by
`experiments/atlas_survivor_infinite_projection.py`.

## 2. Structural proof

Fix one hard pair. Since all \(p_\alpha\), \(\alpha\in D\), lie in
\(A(q,l)\), every nonzero corner

\[
 p_\beta q p_\alpha=\beta\alpha^*
 \quad\hbox{or}\quad
 p_\beta q^*p_\alpha=\beta\alpha^*                 \tag{2}
\]

lies in the algebra. Products of these corners give matrix units along the
connected components of the support graph of the \(D\)-chart matrix of
\(q\). In all six cases those components are

\[
 \{000,010,10\},\qquad \{001,011,11\}.              \tag{3}
\]

Thus any two cylinder projections in the same triple are
Murray--von Neumann equivalent inside \(A(q,l)\).

The next unit \(l\) has a corner which splits a cylinder in the first
component. Depending on the orientation, it is one of

\[
 \beta(\alpha0)^*=p_\beta l p_\alpha,
 \qquad
 (\alpha0)\beta^*=p_\alpha l p_\beta,               \tag{4}
\]

where \(\alpha,\beta\in\{000,010,10\}\). Equation `(4)` identifies the
proper child \(p_{\alpha0}\) with \(p_\beta\), while `(2)--(3)` identify
\(p_\beta\) with \(p_\alpha\). Composing the two partial isometries gives
the element \(v\) in `(1)`. The complementary projection
\(p_{\alpha1}\) is a nonzero Leavitt monomial, so the inclusion
\(f<e\) is strict.

The six exact certificates are:

| class/orientation | \(e\) | \(f\) | support path for `(2)` | splitting corner `(4)` |
|---|---:|---:|---|---|
| 11, forward rotation 0 | \(p_{010}\) | \(p_{0100}\) | \(010\to10\) | \(p_{10}lp_{010}=10(0100)^*\) |
| 11, forward rotation 3 | \(p_{010}\) | \(p_{0100}\) | \(010\to000\to10\) | \(p_{10}lp_{010}=10(0100)^*\) |
| 11, inverse rotation 6 | \(p_{000}\) | \(p_{0000}\) | \(000\to010\) | \(p_{010}lp_{000}=010(0000)^*\) |
| 30, forward rotation 3 | \(p_{000}\) | \(p_{0000}\) | \(000\to10\) | \(p_{000}lp_{10}=0000(10)^*\) |
| 30, forward rotation 6 | \(p_{000}\) | \(p_{0000}\) | \(000\to010\to10\) | \(p_{000}lp_{10}=0000(10)^*\) |
| 30, inverse rotation 3 | \(p_{010}\) | \(p_{0100}\) | \(010\to10\) | \(p_{010}lp_{10}=0100(10)^*\) |

For example, in the first row put

\[
 m=p_{10}q^*p_{010}=10(010)^*,\qquad
 n=p_{10}lp_{010}=10(0100)^*.
\]

Then \(v=n^*m=0100(010)^*\), so

\[
 v^*v=p_{010},\qquad vv^*=p_{0100}.
\]

The remaining rows are the same calculation, with a product of two matrix
units when the support path has length two.

## 3. Why this is stronger than the cardinality contradiction

The earlier proof assigned positive integers to descendant suffix sets and
obtained an impossible equation \(x=x+y\). Equation `(1)` is the algebraic
source of that equation: any faithful finite-dimensional representation
would give

\[
 \operatorname{rank}(e)=\operatorname{rank}(f),
 \qquad
 \operatorname{rank}(e)=\operatorname{rank}(f)
   +\operatorname{rank}(p_{\alpha1}),
\]

forcing the nonzero complementary projection to have rank zero. Thus the
obstruction is not peculiar to scalar leaf counts. It rules out containment
in **every** finite-dimensional star algebra.

This does not prove that either surviving central class is nonzero in
\(R/[P,R]\). A general multi-chart filling need not place a running prefix
and its next syllable in one finite-dimensional star algebra. The theorem
instead identifies the exact local phenomenon any such filling must bypass:
crossing the hard edge creates a properly infinite corner immediately.

## 4. Exact scope of the characteristic-two certificates

The archived artifact `experiments/atlas-prefix-obstruction.json` contains
all 32 cyclic orientations of classes `11` and `30`.  Twelve orientations
reach the hard generated-projection case, representing six distinct prefix
pairs.  Eleven have projection certificates of monomial depth at most six;
one has depth seven.  Every hard pair uses a genuinely mixed monomial in
`q` and `l`, and each cylinder identity contains between four and 28
monomials.

These are identities in the **additive** \(\mathbb F _2\)-span of Leavitt
monomials.  Thus their displayed sums are XOR sums.  They are not complex
linear identities and cannot be evaluated by replacing `q,l` with arbitrary
unitary matrices and adding the resulting matrices over \(\mathbb C\).
Doing so would silently replace characteristic two by characteristic zero.

At group level the additive identities can be retained only through the
elementary-abelian root law

\[
 x_{13}(a+b)=x_{13}(a)x_{13}(b),
\]

followed by Fourier decomposition of the root subgroup.  The resulting
spectral projections are ambient projections, and ambient finite-trace
calculus alone cannot turn `(1)` into a proper isometry: the same group
relations hold in the exact regular representation.  Consequently the JSON
certificate confirms, but does not cross, the matrix-specific seam.  A
hyperlinear obstruction still has to recover the characteristic-two
coefficient operations in one finite coordinate multiplicity algebra.  This
is precisely the fiber-identification / reduced-Fourier gate `(RPC128)` in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.

## 5. Reproduction

```text
python3 experiments/atlas_survivor_prefix_obstruction.py \
  > experiments/atlas-prefix-obstruction.json

python3 experiments/atlas_survivor_infinite_projection.py \
  > experiments/atlas-infinite-projection.json
```

The second command reconstructs the six pairs independently, finds the
support paths and splitting corners, and checks all three identities in
`(1)` by exact Leavitt multiplication and all-depth prefix expansion.
