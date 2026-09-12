# Import: Toms, "A simple C*-algebra which is not K1-injective"

Source: A. S. Toms, arXiv:2609.09535v1, submitted 2026-09-08 23:30 UTC,
24 pages, math.OA (MSC 46L35). The PDF footer reads "Draft of September
10, 2026". It was fetched from `https://arxiv.org/pdf/2609.09535v1` on
2026-09-12. The literature scout read pages 1--3 (introduction, outline,
AI statement, start of the preliminaries). Pages 4--24 were not read, so
nothing below reports their contents. The paper has not been refereed.

## Verbatim statements

Theorem 1.1 (p. 1): "There exists a simple, separable, unital,
infinite-dimensional, nuclear AH algebra A such that K1(A) = 0 and
U(A)/U0(A) contains a nonzero element of order two. In particular, A is
not K1-injective."

Framing (p. 1): "Whether simplicity alone forces K1-injectivity has
nevertheless remained open and appears as Problem LIX in [23]. The
purpose of this paper is to give a negative answer to that question."
Here [23] is the Schafhauser--Tikuisis--White problem list.

AI statement (p. 3): "All mathematical arguments and proofs are due to
the author, and the author takes full responsibility for them. ChatGPT
5.6 was used to search for references. Several of these, which the
author might not have found on his own, clarified that our original real
K-theory invariant (which still works, incidentally) could be understood
in terms of spin bordism. We then realized that the spin bordism
viewpoint was enough to prove our main result from existing
technology---the real K-theory approach just represented an inessential
layer of complexity."

## Mechanism (pp. 1--3, as outlined by the author)

- The seed is the generator u of π4(U(2)) ≅ π4(SU(2)) ≅ Z/2, represented
  by a smooth map S^4 → SU(2). It is not null-homotopic in U(2), but
  u ⊕ 1_2 is null-homotopic in U(4).
- "Higher-rank matrix trapping" generalizes Villadsen's rank-one corner
  trapping. At one stage the base is B = S^4 × X, with X a closed simply
  connected spin manifold of dimension 4r and Q → X a Hermitian bundle
  of rank r. The bundles are E = C² ⊕ Q and W = Hom(Q, C²) ≅ Q* ⊕ Q*.
- A nonzero Euler class of W_R forces the block-diagonal locus Z(v) of a
  unitary section v to meet every X-slice. After transverse perturbation,
  Z(v) is a closed spin four-manifold.
- The invariant is
  ν_{X,Q}(v) = [Z(v), f_v] − [Z(v), c_v] ∈ Ω̃^Spin_4(SU(2)) ≅ Z/2.
  It is nonzero on w = (u ∘ pr_{S^4}) ⊕ 1_Q and zero on 1_E.
  Proposition 4.2 multiplies the seed class by ⟨c_r(Q)², [X]⟩, which the
  construction arranges to equal one.
- Products of Grassmannians preserve the spin and dimension conditions
  along the inductive system. Choosing dense evaluation points gives
  simplicity. The spectra have only even-dimensional cells, so
  K1(A_i) = 0.
- If the witness became null-homotopic in the limit, it would already
  be null-homotopic at a finite stage.

## Relation to this graph

- It answers STW Problem LIX negatively in the public literature, as an
  arXiv preprint dated 2026-09-08. This graph's own negative answer,
  `stw59-simple-ah-non-k1-injective`, was internally reviewed on
  2026-09-05 and is not a public preprint. This import makes no priority
  adjudication.
- As stated, Theorem 1.1 is weaker than `stw59-simple-ah-non-k1-injective`.
  It does not assert stable finiteness or that diag(v, 1) is
  null-homotopic in U(M2(A)); only the seed statement u ⊕ 1_2 ~ 1 in
  U(4) appears on p. 1. The mechanisms also differ: spin bordism over
  S^4 × X with higher-rank trapping, against parity over S^4 × ∏ CP^r.
- On pages 1--3 Toms asserts no factorial or larger component groups, no
  unique trace, no stable rank, and no noncommutativity of U(A)/U0(A).
  The graph's stronger results (`stw59-exact-factorial-unitary-component-groups`,
  `stw59-exact-finite-abelian-unitary-component-groups`) are not
  subsumed by Theorem 1.1.
