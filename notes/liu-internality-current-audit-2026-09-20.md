# Current Liu/Thom internality interface: bounded source and proof audit

Date: 2026-09-20. Read-only inspection of existing claims; this note is
the only edited file. No mathematical computation, build, or external
contact was performed. Network reads, PDF text extraction, and byte
checksums were used for source verification.

## Verdict and its limits

The present primary PDFs state the universal homomorphism quantifiers
used by Cairn. I found no mismatch in the internality definition, no
contradiction from the examined counterexamples, and no defect in the
small analytic passages reconstructed below. This is **not** a fresh
independent verification of the whole internality theorem. In particular,
the long block construction and matching arguments remain dependencies
of the maintained acceptance, not consequences of merely reading the
theorem statement.

## 1. Source versions and exact logical interfaces

Both primary URLs returned HTTP 200 directly. The web reading service
could not open them, but ordinary HTTPS access and PDF text extraction
succeeded. The hashes agree exactly with the existing acceptance records:

* Jihao Liu, [Nonhyperlinear groups exist](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf):
  `6da1adbd94c82914457f6435426824087dd865a6af3d61d2bcd87a8bec89e71e`.
  HTTP Last-Modified: 20 September 2026, 15:21:29 GMT.
* Andreas Thom, [A conditional construction of a nonhyperlinear group and the centralizer problem](https://andreasthom.github.io/pdf/nonhyperlinear.pdf):
  `0776bde0857be69c8768f5bf1a816db68a48a36fb5c30f1e48ac474773dd39aa`.
  HTTP Last-Modified: 16 September 2026, 19:38:23 GMT.

The Liu definition immediately preceding Theorem 1.2, on printed page 3,
uses coordinate unital star-subalgebras A_n of the specified M_(d_n).
Their internal algebra consists of the classes of all uniformly
operator-norm-bounded sequences a_n in A_n. Equality is as subalgebras
of the specified tracial matrix ultraproduct, not just abstract
isomorphism, dense containment, or existence of separately chosen lifts
for finitely many test elements.

His Theorem 1.2 / 6.7 covers every finitely generated discrete Kazhdan
group, every indicated free ultrafilter and dimension sequence, and
every homomorphism into that ultraproduct. Neither injectivity nor the
canonical group character is assumed. The chosen A_n need not be the
exact centralizers of the supplied generator lifts. Exact coordinate
group representations are not asserted.

Thom's Theorem 1.2, on printed page 2, is conditional on a positive
answer to this universal centralizer problem. Both subgroup H and
ambient group G must be Kazhdan, with H infranormal in G. It then gives
normalization of the subgroup commutant for every homomorphism of G.
His proof uses internality of **both** subgroup and ambient commutants.
Theorem 1.3 gives nonhyperlinearity of the nonnormal infranormal double
under the same universal premise. Liu's page 4 explicitly credits Thom
with priority for this conditional normalization/construction mechanism.

This matches the scope of `non-hyperlinear-from-internality-and-thom-double`.
It does not turn Thom's theorem alone into an unconditional internality
theorem. Liu's stronger subgroup-only, per-model normalization interface
is a separate statement, unnecessary for that particular Cairn route.

## 2. Small decisive check: internal algebra lifting is not representation stability

Suppose A=[A_n]_omega is internal and a unitary u=[u_n] commutes with A.
Then

    epsilon_n = sup_(v in U(A_n)) ||[u_n,v]||_2 ->_omega 0.       (1)

Indeed, a contrary subsequence supplies maximizing unitary witnesses
v_n; their bounded class lies in A but does not commute with u.
This use of *all* bounded sequences is essential.

Haar averaging gives b_n=E_(A_n')(u_n), with b_n in A_n',
||b_n||<=1, and ||u_n-b_n||_2<=epsilon_n. Complete the polar part
of b_n inside the finite-dimensional algebra A_n' to a unitary w_n.
Its singular-value formula is the minimum distance from b_n to a
unitary, so

    ||w_n-b_n||_2 <= ||u_n-b_n||_2,
    ||w_n-u_n||_2 <= 2 epsilon_n.                             (2)

Thus u has representatives in the exact coordinate commutants of A_n.
The same operation applies to a fixed finite generator list. Their
group relators still only tend to zero; nothing in (1)--(2) makes them
exact. This verifies the key lifting distinction used in Thom's
Proposition 5.1 and the existing Cairn reviews.

There is an elementary two-dimensional test showing why the original
coordinate centralizers cannot replace the unknown A_n. Let H=C_2 x C_2,
with generators a,b, let X,Z be real Pauli matrices, and set

    u_n=Z,       v_n=cos(1/n) Z + sin(1/n) X.

Both are exact involutions and their commutator tends to zero. They
therefore define an ultraproduct homomorphism with pi(a)=pi(b)=Z.
For each n their exact common centralizer is C I, whereas the limiting
commutant is span{I,Z}. It is internal, represented by the constant
diagonal algebra. Moreover

    ||[u_n,Z]||_2=0,       ||[v_n,Z]||_2=2 sin(1/n),
    dist_2(Z,C I)=1.

So property (T), even for a finite group and exact involutory lifts,
does not give a uniform coordinate gap off the **uncorrected** exact
centralizers. It gives a gap off the actual ultraproduct commutant.
This counterexample is compatible with, rather than contrary to, Liu's
statement.

## 3. Check of the quotient-gap passage and its low-rank safeguard

I compared the current PDF's Proposition 3.1 and Theorem 3.2 with
`quotient-gap-expectation-lift-proof` and Section A of the maintained
analytic-leaves acceptance artifact.

For the true conjugation representation on L2(M), property (T) gives
a gap off the invariant vectors. Bounded mean-ergodic averaging and
L2 density identify these vectors with L2(C), C=pi(H)' intersect M.
For the lazy positive conjugation average T and r=1-a, this gives

    ||T^k-T^j||_(2->2) <= r^j,       k>=j.                   (3)

For uniformly bounded coordinate maps in both relevant norms, the
operator-unit-ball-to-L2 norm of their quotient equals the ultralimit
of their coordinate norms. Coordinate maximizing contractions prove
the potentially delicate inequality. Applying this to fixed powers
in (3), then diagonalizing finitely many inequalities at each stage,
really does produce one sequence T_n^(ell_n) inducing E_C on **every**
bounded sequence. It does not diagonalize individual elements of a
nonseparable commutant. This passage checks out.

It supplies an additive uniform error on coordinate projections, not
a relative estimate valid after dividing by an arbitrarily small rank.
Theorem 3.2's exception-removal step addresses precisely that issue.
For fixed accuracy and depth k, choose a maximum-rank bad projection q.
Its rank fraction tends to zero by the additive estimate. Remove the
span of its translates by words of length at most 2k+2. If a nonzero
bad projection p remained in the complement, the length-(k+1) word
spans of p and q would be orthogonal. Both D(p) and T^k D(p), and their
adjoints, are supported there. Their squared norms consequently add
for p+q, making p+q bad and contradicting maximal rank.

The finite set of possible ranks ensures a maximum; no compactness of
an open feasible set is invoked. For each fixed target, the number of
words is fixed before the coordinate limit. Finally diagonalizing the
targets preserves the fact that the retained corner was chosen before
all its test projections. I found no gap in this step or its stated
quantifier order. It does not yet construct the internal algebras.

## 4. Counterexample and dependency audit

The directly checked instability theorem of
[Becker--Lubotzky](https://math.huji.ac.il/~alexlub/PAPERS/Group%20stability%20and%20Property%20%28T%29.pdf)
rules out strict normalized-HS representation stability for infinite
hyperlinear Kazhdan groups. Its conclusion concerns perturbation to
genuine representations, unlike internality. It therefore does not
contradict the current Liu statement or (1)--(2).

The following apparent conflicts in Cairn also fail to be contradictions:

* `hrf-audit-projective-internality-does-not-round` gives projective lifts
  whose adjoint actions are genuine representations. Their original
  commutants already are internal, despite nonroundability. This makes
  the stability/internality distinction explicit.
* `factorial-leavitt-models-have-external-corner-commutants` is conditional
  on existence of a canonical model with factorial global commutant.
  It does not construct that model. Combining its conclusion with Liu
  excludes the hypothesized model rather than contradicting internality.
* The canonical Kun--Thom wreath-factor countermodels are in their own
  tracial von Neumann algebras; matrix-ultraproduct embeddability is not
  supplied. Rank-metric block counterexamples use a different norm and
  do not satisfy the unitary Hilbert-space spectral-gap hypotheses.

There is a genuine warning already in Thom's Remark 4.3: an internal
algebra may have a proper, ambient-unitarily implemented, trace-preserving
endomorphism. Internality plus one-sided conjugation inclusion alone is
not enough for normalization. His theorem additionally uses an internal
common fixed algebra. The existing bypass route retains this input by
applying universal internality to the ambient Kazhdan group as well.

The maintained universal-internality route is
`kazhdan-internality-from-blocks-and-exhaustion`. Beyond the locally
checked expectation lift, it consumes:

1. the physical scalar-block construction, assembled from projection
   repair, equivariant POVM rounding, resolvent covariance/leakage, and
   defective-block pruning;
2. fixed-gap Kazhdan matching of rectangular blocks and their full
   multiplicity algebras;
3. internal-corner exhaustion using the same uniform expectation lift.

Existing artifacts record written acceptance and independent conditional
assembly reviews, with finite-von-Neumann-algebra imports attributed to
Houdayer--Vaes and Ioana. This audit checks the stated interfaces and
the small passages above; it does not replace those larger proof reviews.
Nor does the graph's derived ESTABLISHED status constitute an external
referee verdict or formal verification.

## 5. Precise stopping point

The source statements really have the broad representation scope used
in Cairn. The fetched source versions have not changed relative to the
recorded hashes. The inspected local estimates and lift quantifiers are
sound. No counterexample to universal internality was found among the
examined primary or repository examples. A targeted fresh search found
no primary erratum, but that absence is not certification.

No existing acceptance, route, or claim was changed. The mathematical
status added by this note is a bounded scope/proof check, not a new
unconditional proof of Liu's entire theorem or its downstream roots.
