# LXI attack: universal compression, corner transport, and the free envelope

Date: 2026-09-05. **Research note: LXI remains unresolved.**
This is not a Cairn route and does not claim a counterexample.

## 1. Concrete universal target

Blanchard–Rohde–Rørdam, *Properly infinite C(X)-algebras and K1-injectivity*,
J. Noncommut. Geom. 2 (2008), Theorem 5.5, reduce LXI to
\(O_\infty*_{\mathbb C}O_\infty\).
Theorem 5.5(iv) asks for a homotopy between suitable nontrivial
projections coming from the two factors.
[Primary paper](https://ems.press/content/serial-article-files/30436?nt=1).

Blanchard, *K1-injectivity for properly infinite C*-algebras*,
Proposition 4.2 and Remark 4.7, gives a smaller finitely generated
target \(T_2*_{\mathbb C}T_2\). If \(s_1,s_2\) are the Toeplitz
isometries and \(j_0,j_1\) the inclusions, it suffices to connect
\(j_0(s_1s_1^*)\) to \(j_1(s_1s_1^*)\).
These projections are Murray–von Neumann equivalent and have
properly infinite full complements, but unitary equivalence does
not yet supply a unitary in the identity component.
[Primary manuscript](https://arxiv.org/pdf/0804.4624).

The target is genuinely non-simple. Tensoring a finite obstruction
with \(O_\infty\), or embedding it in a stable multiplier algebra,
does not by itself retain that obstruction.

## 2. Exact corner-transport lemma

**Lemma.** Let \(B\) be unital, let \(p\in B\) be a projection, and
let \(a\in U(pBp)\). Suppose
\[
\operatorname{diag}(a,p)\sim_h\operatorname{diag}(p,p)
\quad\text{in }U(M_2(pBp)).
\]
If \(p\precsim1-p\), then
\[
a+(1-p)\sim_h1_B\quad\text{in }U(B).
\]

**Proof.** Choose \(t\in B\) with \(t^*t=p\) and
\(tt^*=q\le1-p\). The formula
\[
\Theta\begin{pmatrix}x&y\\z&w\end{pmatrix}
=x+yt^*+tz+twt^*
\]
is a *-homomorphism from \(M_2(pBp)\) onto
\((p+q)B(p+q)\), taking the matrix unit to \(p+q\).
Transport the asserted unitary path by \(\Theta\), and add the
constant projection \(1-p-q\). Its endpoints are \(a+1-p\) and
\(1_B\). \(\square\)

More generally, if an \(n\)-fold stabilization of \(a\) is null and
\(1-p\) contains \(n-1\) orthogonal copies of \(p\), the same
matrix-unit construction contracts \(a+1-p\).

If \(1-p\) is properly infinite and full, these copies exist:
a properly infinite full projection dominates every projection in
the algebra and every finite sum of projections. This is the
projection comparison fact recalled just before Proposition 2.3
of the BRR paper.

**Consequence for the LIX witness.** Its first matrix stabilization
is already null. Any attempt to place that witness in a corner of
a properly infinite algebra must therefore prove
\(p\nprecsim1-p\) for the corner support. If the complementary
projection is properly infinite and full, the construction fails
by the explicit path above. This is a proved restriction, not
evidence that an arbitrary embedding preserves the class.

## 3. Every ordinary properly infinite tensor factor kills the witness

This exclusion is broader than tensoring with \(O_\infty\).

**Proposition.** If \(D\) is any unital properly infinite
\(C^*\)-algebra, \(A\) is unital, and \(a\in U(A)\) has zero
stable \(K_1\)-class, then
\[
a\otimes1_D\sim_h1
\quad\text{in }U(A\otimes_{\min}D).
\]
The same assertion holds for the maximal tensor product.

**Proof.** Choose isometries \(s,t\in D\) with orthogonal ranges.
For \(p=ss^*\), both \(p\) and \(1-p\) are properly infinite
and full: \(p\sim1_D\), and \(1-p\) contains \(tt^*\sim1_D\).
Thus \(q=1_A\otimes p\) and \(1-q\) are properly infinite full
projections in the tensor product. They commute with
\(a\otimes1_D\), whose stable class vanishes by functoriality.
BRR Lemma 2.4(ii), with commutator norm zero, supplies the
null-homotopy. \(\square\)

In particular, replacing \(O_\infty\) by \(T_2\), another
properly infinite algebra, or an ordinary coefficientwise
properly infinite tensor factor cannot repair the LIX-to-LXI
transfer. A successful twisting must prevent the existence
of a global properly infinite full splitting commuting with
the witness.

## 4. A surviving candidate mechanism: the full free envelope

Let \(A\) and \(v\) be the simple AH algebra and order-two unitary
of the LIX manuscript. Form
\[
B=A*_{\mathbb C}T_2
\]
with its canonical unital inclusions, and let \(\bar v\in U(B)\)
be the image of \(v\). The canonical maps into a full unital free
product are injective; \(B\) is properly infinite because it
contains the Toeplitz isometries unitally. Functoriality gives
\[
\bar v^2\sim_h1,\qquad
\operatorname{diag}(\bar v,1)\sim_h1.
\]
Thus the only unresolved assertion needed for this particular
counterexample is
\[
\bar v\not\sim_h1.
\tag{3.1}
\]
It must not be inferred from injectivity of \(A\to B\).

The finite vector-bundle proof does not extend automatically:
a path in \(B\) need not take values in the endomorphism bundle
used to detect \(v\). A quotient of \(B\) cannot restore a unital
finite-rank bundle model, since every nonzero unital quotient of
a properly infinite algebra is properly infinite. The obvious
finite-dimensional evaluation method is therefore unavailable.

There is a precise compression formulation. If \(s,t\in B\) are
isometries with orthogonal ranges and
\[
C_s(b)=sbs^*+(1-ss^*)\quad(b\in U(B)),
\]
the matrix homomorphism
\[
[b_{ij}]\longmapsto
s b_{11}s^*+s b_{12}t^*+t b_{21}s^*+t b_{22}t^*
\]
transports a null-homotopy of \(\operatorname{diag}(\bar v,1)\)
to one of \(C_s(\bar v)\). Therefore
\[
C_s(\bar v)\sim_h1.
\]
The missing step is to compare \(\bar v\) with
\(C_s(\bar v)\). The compression is a nonunital corner map at
the algebra level, and there is no established homotopy from
that map to the identity in this free envelope.

For this specific witness BRR Lemma 2.4(ii) provides a sufficient
criterion: if a projection \(q\in B\) has both \(q\) and \(1-q\)
properly infinite and full and satisfies
\[
\|[\bar v,q]\|<1,
\]
then \(\bar v\sim_h1\). No such \(q\), and no obstruction excluding
all possible \(q\), is constructed here.

There is, however, an exact calculation excluding every projection
chosen solely from the new Toeplitz factor. Choose the original
generator \(u:S^4\to SU(2)\subset U(2)\). This is possible because
the inclusion induces an isomorphism on \(\pi_4\). The map is
surjective onto \(SU(2)\cong S^3\): omitting a point would factor
it through a contractible space and make its class zero. Hence
\(\sigma(v)=S^1\), and injectivity of the maps preserves this
spectrum.

**Proposition.** For every projection \(0\ne q\ne1\) in the
Toeplitz free factor,
\[
\|[\bar v,q]\|=1.
\tag{4.1}
\]

**Proof.** For a unitary and a projection the commutator norm
is at most \(1\): in the two-by-two decomposition given by the
projection, the commutator is off-diagonal and each off-diagonal
block is a contraction.

Choose an infinite-multiplicity faithful representation \(\rho\)
of \(A\). Since \(1,-1\in\sigma(v)\), the spectral theorem gives
orthogonal unit vectors \(\xi,\eta\) with
\(\rho(v)\xi\) arbitrarily close to \(\xi\) and
\(\rho(v)\eta\) arbitrarily close to \(-\eta\). Choose a projection
\(P\) whose restriction to their span has range
\(\mathbb C(\xi+\eta)\), and whose range and kernel are both
infinite-dimensional. On this two-dimensional subspace,
the commutator with the limiting diagonal unitary
\(\operatorname{diag}(1,-1)\) has norm \(1\).
Thus \(\|[\rho(v),P]\|\) is arbitrarily close to \(1\).

An infinite amplification of a faithful representation of \(T_2\)
has infinite-dimensional range and kernel for its image of \(q\).
Conjugating that representation by a Hilbert-space unitary makes
the image of \(q\) equal to \(P\). The universal property of the
full free product combines it with \(\rho\), with no commutation
relations required. Therefore the full free-product norm of
\([\bar v,q]\) is at least \(1-\varepsilon\) for every
\(\varepsilon>0\). The upper bound proves (4.1). \(\square\)

Consequently any projection satisfying the strict BRR commutator
criterion for this candidate must involve both free factors.
The equality (4.1) does not rule out such mixed projections and
does not prove survival of \(\bar v\).

## 5. An exact issue with the 2016 counterexample preprint

Blanchard's arXiv:1606.04773v1 is not imported as a solution.
[Primary preprint](https://arxiv.org/pdf/1606.04773).

There is a direct covariance obstruction in Proposition 2(5),
Step 2, independent of questions about its finite-stage argument.
The step invokes evaluation of the crossed-product implementing
unitary at \(1\), while retaining the coefficient algebra
\(\ddot A\). Such a retraction does not exist for the nontrivial
shift automorphism used there.

Indeed if \(U a U^*=\alpha(a)\) is the crossed-product covariance
relation and a *-homomorphism \(r\) fixed every \(a\in\ddot A\)
while sending \(U\) to \(1\), applying \(r\) would give
\[
a=\alpha(a)\quad\text{for every }a\in\ddot A.
\]
The dilation automorphism is not the identity. For
\(p=\mu_0(1_A)\), the construction gives
\[
\ddot\alpha(p)=\mu_0(s_1s_1^*)<p.
\]
The strict inequality survives because \(\mu_0\) is injective
and \(1_A-s_1s_1^*\ne0\). Hence the asserted retraction contradicts
covariance. Evaluation on a free factor \(C^*(\mathbb Z)\) is
valid for a free product, but cannot erase a nontrivial
crossed-product action in this way.

The earlier repository firewall criticized the finite-stage
passage in Step 1 too generally. If the *same compatible
unitary* had actually been proved non-null at every stage,
passage to an injective inductive limit would be valid, by
finite-stage detection of null-homotopies. Injectivity of algebra
maps alone is insufficient, but it is not necessary to prove
injectivity on every unitary component. Thus the exact
compatibility and finite-stage claim would need checking before
that step alone could be declared invalid. The covariance
obstruction above is a separate concrete defect.

## 6. Present boundary

The corner lemma is proved, and the full free envelope is an
explicit properly infinite candidate with an explicit stably
null unitary of component order at most two. Its non-nullness
is unproved. No LXI graph status change is justified.
