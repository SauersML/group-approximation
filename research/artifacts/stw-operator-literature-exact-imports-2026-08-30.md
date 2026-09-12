# STW/operator-algebra exact literature imports (2026-08-30)

## Scope and novelty gate

This audit compares current 2026 primary sources with the Cairn claims and
routes attached to the open STW/operator-algebra roots.  Searches covered the
arXiv identifiers, exact paper titles, authors, theorem keywords, and the
conclusions below.  Before this change, Cairn had no claim or route importing
any of the four statements.

Two superficially new papers were deliberately excluded.  Pask,
arXiv:2607.27691, was already analyzed in the LXXVII and LXXXIII audits, and
Ohshima, arXiv:2608.26987, was already analyzed in the XCI finitary-wreath
audit.  Repackaging those mentions would not be a genuinely missing
literature result.  The withdrawn and explicitly incorrect preprints flagged
elsewhere in the corpus were likewise not used.

The four imports below establish exact bounded claims.  None is presented as
a solution of a broader universal STW root.

## 1. The shape-system obstruction to KK Hausdorffness

Primary source: Jose R. Carrion, *A Milnor exact sequence for E-theory*,
[arXiv:2608.06496v1](https://arxiv.org/abs/2608.06496), submitted
2026-08-06.

* Theorem 1.1 gives, for separable `A,B` and every shape system `(C_n)` for
  `SA tensor K`, the natural Milnor exact sequence and identifies its
  `lim^1` term with the closure of zero in `E(A,B)`.
* Corollary 4.3 says that `E(A,B)` is Hausdorff exactly when this `lim^1`
  vanishes, and gives the stated Mittag--Leffler sufficient condition.
* Proposition 4.5 says that for nuclear `A`, the topological isomorphism
  `E(A,B)=KK(A,B)` carries this closure onto the closure of zero in `KK`.

| Imported hypothesis | Source hypothesis |
| --- | --- |
| `A,B` separable | Theorem 1.1 and Corollary 4.3 |
| `(C_n)` a shape system for `SA tensor K` | Theorem 1.1 and Corollary 4.3 |
| `A` nuclear for the `KK` formulation | Proposition 4.5 |
| conclusion: Hausdorff iff the displayed `lim^1` is zero | Theorem 1.1, Corollary 4.3, Proposition 4.5 |

This sharpens Problem V to an exact obstruction but does not show that a
separably `Q`-stable target makes the obstruction vanish.

## 2. A trace-problem class from locally finite nuclear dimension

Primary source: Xuanlong Fu, *Divisibility and Real Rank Zero*,
[arXiv:2605.21655v1](https://arxiv.org/abs/2605.21655), submitted
2026-05-20, Theorem 10.12.

| Imported hypothesis | Theorem 10.12 wording |
| --- | --- |
| algebraically simple | algebraically simple |
| separable and non-elementary | separable and non-elementary |
| stable rank one | stable rank one |
| `T(A)` nonempty and compact | `T(A)` non-empty and compact |
| locally finite nuclear dimension | locally finite nuclear dimension |

Theorem 10.12 concludes, among its listed structure results, the literal
equality `T(completion_(2,T(A))(A))=T(A)`.  This is exactly the assertion that
all traces on this uniform tracial completion are designated uniform
`2`-norm-continuous traces.  No simplicity, rank, compactness, or local
nuclear-dimension assumption is discarded.

## 3. Rational twisted virtually-abelian nuclear dimension

Primary source: Forrest Glebe, Pradyut Karmakar, and Iason Moutzouris,
*Nuclear Dimension of Twisted C-star Algebras of Virtually Abelian Groups*,
[arXiv:2605.27936v1](https://arxiv.org/abs/2605.27936), submitted
2026-05-27.

Theorem 4.12 (Theorem A) states word-for-word that for a finitely generated
virtually abelian group `G` and rational `[sigma] in H^2(G,T)`,

```text
dim_nuc C*(G,sigma)=h(G).
```

Theorem 3.9 supplies the equivalent root-of-unity-representative formulation
for this group class.  The import does not extend Theorem 4.12 to irrational
classes.  In particular, it does not turn Theorem 5.11's upper bound for
irrational noncommutative tori into an exact computation.

## 4. Completion of the selfless dichotomy

Primary source: Miles Gould, *The Selfless Dichotomy*,
[arXiv:2606.09654v2](https://arxiv.org/abs/2606.09654), revised
2026-07-22.

* Theorem 1 (Theorem 2.5) proves that a selfless C-star probability space
  with nonfaithful state has purely infinite simple underlying algebra.
* Theorem 2 states that every selfless C-star probability space is simple;
  in the tracial case it has stable rank one, strict comparison, and a unique
  normalized `2`-quasitrace, while in the nontracial case it is purely
  infinite.
* Corollary 3 states that every selfless C-star algebra is pure.

This resolves the nonfaithful-state gap in Robert's selfless dichotomy.  It
does not prove selflessness for an additional group and therefore does not
close STW Problem XCI.

## Trust boundary

All four sources are current arXiv preprints as of 2026-08-30, not
journal-final versions.  Cairn imports only their numbered theorem
statements and the explicit hypothesis matching above.  Their long proofs
are not reconstructed, and no universal STW root is relabelled on the basis
of a stronger paraphrase.
