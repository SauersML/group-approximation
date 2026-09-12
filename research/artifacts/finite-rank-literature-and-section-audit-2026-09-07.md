# Finite-rank arguments, literature scope, and local sections

Research audit, 2026-09-07. These are handwritten mathematical arguments
and source comparisons, not proof-assistant certificates. The two
headline conjectures remain unresolved in this work.

## Primary literature checked

* Xuan Kien Phung, *Stable finiteness of twisted group rings and noisy
  linear cellular automata*, Canadian Journal of Mathematics 76 (2024),
  1089-1108; [publisher version](https://doi.org/10.4153/S0008414X23000329),
  [arXiv text](https://arxiv.org/html/2209.06002).
  Definition 1.2 uses asymptotically constant configurations of local
  rules. Theorem A represents their operator algebra using D^1(k[G]);
  Theorem B and Theorem 7.2 relate that ring's finiteness to nonuniform
  automaton properties. Those stated equivalences concern D^1(k[G]),
  rather than the full-certificate crossed product used here. The
  inspected statements do not explicitly give our one-invertible-fiber
  theorem. This comparison does not establish novelty.

* Xuan Kien Phung, *On linear non-uniform cellular automata: duality and
  dynamics*, [arXiv:2208.13069](https://arxiv.org/pdf/2208.13069).
  Theorem B / Theorem 10.1(ii) characterizes stable post-surjectivity by
  a finite-memory linear right inverse for countable groups and finite
  vector alphabets. Lemma 8.2 and Theorem 8.3 give uniform bounded-support
  corrections over orbit closures; Theorem 9.1(ii) gives the relevant
  transpose duality. These are the closest inspected precedents for the
  finite-support section criterion below. Its core correction and
  compactness mechanism should not be advertised as new.

* Henry Bradford and Francesco Fournier-Facio, *Hopfian wreath products
  and the stable finiteness conjecture*,
  [accepted article](https://www.repository.cam.ac.uk/items/0f95f613-8809-44a4-ac92-ec54a577b3a9),
  [arXiv:2211.01510](https://arxiv.org/abs/2211.01510).
  This connects Hopficity of abelian wreath products with Kaplansky's
  conjecture and reduces coefficient-field questions to finite prime
  fields. It is relevant context, but is not being used as the proof
  of our induced finite-rank lamp-representation theorem.

Searches for finiteness, finite-rank perturbations, wreath products,
and nonuniform linear automata were used to locate primary sources.
Failure to find an identical statement is not evidence that the
statement is new. No exhaustive literature review is claimed.

## A precise finite-support criterion for the remaining local section

Here is the full-certificate formulation obtained during this audit.
Let k be any field, B a finite nonempty alphabet, C=B^G, and Q_c a
certificate-local finite-memory linear map from (k^n)^G to (k^m)^G.
Then Q admits a certificate-local finite-memory linear right inverse
if and only if, for every c,

    Q_c:k^(G x {1,...,n})->k^(G x {1,...,m})

is onto, where parentheses denote finitely supported functions. No
uniform support bound or continuous choice of these preimages is
assumed. The conclusion supplies both.

Necessity holds because a finite-memory linear right inverse sends
finite-support inputs to finite-support outputs.

For sufficiency, choose for each c finitely supported v_j with
Q_c v_j=delta_1 e_j, j=1,...,m. A fixed tuple of such v_j remains a
witness on a clopen certificate neighborhood: if their supports lie
in K and Q has data memory F, their output supports lie in KF^(-1),
so only finitely many coefficient values and certificate sites enter
these finitely many equations. These neighborhoods cover C. Compactness
gives a finite subcover, and a disjoint clopen refinement gives locally
constant choices v_j(c), all with support in a common finite K and
depending on a common finite certificate window D.

Define

    (P_c z)(g)=sum_(h in G,j) z_j(h) v_j(h^(-1).c)(h^(-1)g).

Only h=gk^(-1), k in K, contribute to this sum. Thus P has data memory
K^(-1) and certificate memory contained in the finite union of k^(-1)D.
Equivariance of the Q family gives

    Q_c(h.v_j(h^(-1).c))=delta_h e_j.

Consequently Q_c P_c agrees with I on every unit input. Since the
operators are linear and have finite memory, this identifies every
output-row coefficient and proves QP=I on all configurations.

Full-shift surjectivity of each Q_c is a weaker premise and does not
suffice. For example, 1-shift on k^Z is onto on all configurations by
recursion, but sends every finitely supported input to an output whose
coordinate sum is zero. It cannot produce delta_0 from finite support.

This criterion offers a way to prove a local section without guessing
its radius. It does not evade the finite-rank fiber theorem: if a
secant family satisfying this criterion has one injective fiber, it
is invertible on every fiber. In particular a family retaining a
nonlinear decoder collision must already contain a strict one-sided
linear operator at each constant diagonal certificate.

## What was checked independently

The root agent derived finite-rank propagation from one certificate
fiber; the secant agent independently checked the invariant finite-
dimensional range argument and its application to dense finite changes.
The algebra agent constructed the induced lamp representations; the
root checked the semidirect-product law, the finite-transporter bound,
the fixed-matrix-size hypothesis, and separation of nonzero coefficients.
These checks support the written proofs, but do not replace formalization
or an external mathematical review.
