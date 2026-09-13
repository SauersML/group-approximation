# EX review, second wave, quantum and L²: part 2. L², determinant and Strong Atiyah imports read at source; two derived claims

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Method.**
- **Texts.** The PDFs were fetched from arXiv on MSI on 2026-09-13 into
  `/scratch.global/sauer354/ex/ex-verify2-quantum-l2/pdf/` and extracted with ghostscript `txtwrite`.
- **Comparison.** Each statement quoted in a node was compared with the extracted lines. Line numbers
  refer to the `.txt` files.
- **What PASS means here.** "PASS at source" certifies that the theorem number, the statement and the
  hypotheses match. It does not re-derive the paper's proof.

## 2.0 Verdicts

| claim | lane | source | verdict |
|---|---|---|---|
| `binary-leavitt-frame-complexes-are-highly-acyclic` | lueck | Khanh arXiv:2609.08428v1: Def. 2.1 (l. 99), proof of Thm 2.2 (l. 275), Cor. 4.3 | PASS at source |
| `integral-eigenvalues-galois-balanced-for-sofic-groups` | determinant-monster | Thom arXiv:math/0701294v3, Thm 1.1 | PASS at source |
| `agp-purely-infinite-simple-rings-have-cancellative-projectives` | lueck | Ara–Goodearl–Pardo arXiv:math/0111066v1, definition (l. 123), Prop. 2.2 | PASS at source |
| `purely-infinite-leavitt-path-v-monoid-cancellation` (+ `-agp-proof`) | lueck | derived | PASS |
| `leavitt-path-algebras-purely-infinite-simple-criterion` | lueck | Abrams–Aranda Pino arXiv:math/0509496v1, Thm 11 (l. 452) | PASS at source; the cofinality derivation PASS |
| `lamplighter-groups-have-irrational-l2-betti-numbers` | lueck | Grabowski arXiv:1004.2030v4 Thm 1.1; arXiv:1009.0229v4 Thm 2 and abstract | PASS at source |
| `lamplighter-powers-have-undecidable-l2-kernel-and-zero-divisors` | lueck | Grabowski arXiv:1202.1162v2, problem definition (l. 65–68), Thms 1–2, Cor. 5 | PASS at source |
| `cyclotomic-integer-matrices-classified` | determinant-monster | McKee–Smyth arXiv:0705.3599v1, Thms 1–3 (l. 112, 140, 183) | PASS at source |
| `smith-serre-measures-are-conjugate-limits` | determinant-monster | Smith arXiv:2111.12660v2, Thm 1.5 (p. 4) | PASS at source |
| `one-relator-groups-satisfy-strong-atiyah` | atiyah-torsion-free | Jaikin-Zapirain–López-Álvarez arXiv:1810.12135v4, Cor. 1.3, Thm 1.1 | PASS at source |
| `strong-atiyah-passes-to-locally-indicable-extensions` | atiyah-torsion-free | same paper, Prop. 6.5 (l. 1849) | PASS at source |
| `determinant-conjecture-excludes-liouville-atiyah-exceptions` | atiyah-torsion-free | derived | PASS as a statement: item 1 re-derived, items 2–3 as corollaries of a PASSED theorem (2.4) |

## 2.1 Lück-approximation imports

- **Khanh.**
  - Cor. 4.3 reads "For r ≥ 3, one has H̃_d(X_r(R), Z) = 0 for 0 ≤ d ≤ r −3", with `R = L_(F_2)(1,2)`.
    That is the node's statement.
  - Line 99 is the end of Def. 2.1 ("there are no simplices in dimensions p ≥ r").
  - Line 275 opens the proof of Thm 2.2 ("The group Γ_r acts transitively on the ordered (k−1)-simplices
    of X_r(A)").
  - The proof of 4.3 on the same page cones a finite cycle, with a common frame extension from
    Prop. 4.2. That matches the route's summary.
- **AGP.**
  - Prop. 2.2 is verbatim.
  - The definition at line 123 reads "A simple ring R is said to be purely infinite if every nonzero right
    ideal of R contains an infinite idempotent". No regularity is assumed. The node's "no regularity" is
    correct.
- **`purely-infinite-leavitt-path-cancellation-agp-proof`.** Re-derived.
  - `[P] = [Q]` in `K_0(L)` iff `P (+) L^n ≅ Q (+) L^n` for some `n`.
  - In the group `V(L)*`, cancel `[L^n]`, which is nonzero.
  - The claim needs `L_K(E)` purely infinite simple, which is its hypothesis.
- **Abrams–Aranda Pino.**
  - Thm 11 (i)–(iii) is verbatim, and its proof invokes Prop. 10, a "not a division ring, plus `a alpha b =
    beta`" test. That is equivalent to AGP's definition for unital rings, so both papers use the same
    notion.
  - The claim's derivation for finite, sinkless, cofinal graphs with (L) is correct:
    - (ii) is (L).
    - (iii): an infinite path repeats a vertex.
    - (i): a nonempty proper hereditary saturated `H` meets every cycle, since vertices of `H` reach it.
      A vertex outside `H` emits an edge landing outside `H`, since otherwise saturation would put it in
      `H`. So there is a cycle outside `H`, a contradiction.
- **Grabowski.**
  - arXiv:1004.2030v4 Thm 1.1 (l. 117): the superscripts are pushed to line 116 in the extraction.
    Line 209 confirms "In Theorem 1.1 we prove C((Z/2Z ≀ Z)3) * Q", so the group is `(Z/2 ≀ Z)^3`, as the
    node says.
  - arXiv:1009.0229v4 Thm 2 (l. 56) gives a matrix over `Z[Z_p ≀ Z]` with an explicit series kernel
    dimension. The abstract (l. 8–14): "can be irrational".
  - arXiv:1202.1162v2:
    - Trivial-l2-Betti-numbers takes "a number n and the description of the gluing maps used to build a
      CW-complex X", and asks "if the n-th l2-Betti number of X is 0".
    - Thm 1 (l. 69), Thm 2 (l. 97) and Cor. 5 are verbatim.
    - The node's three bullets match.

## 2.2 Determinant-monster imports

- **Thom.** Thm 1.1 (i)–(ii) is verbatim, and "These theorems will be proved as Theorem 4.2 and 4.3".
  - The node's total-reality step is correct: self-adjoint operators have real eigenvalues, and every
    conjugate is an eigenvalue.
  - The right-multiplication remark is correct: `g -> g^-1`, with transpose, conjugates the right action
    to the left action of a matrix over `Z[Γ]`.
- **McKee–Smyth.**
  - Thms 1–3 are verbatim at lines 112, 140 and 183, including the containment clauses.
  - The node's derived remark on balls of radius `r` (at most `2(2r+1)` vertices) follows from the rung
    structure of `T_2k` and `C_2k`.
  - The remark "every maximal graph satisfies `A^2 = 4I`" is at l. 153 ("their adjacency matrices A all
    satisfy A = 4I, so all their eigenvalues are ±2"; the extraction drops the exponent).
- **Smith.** Thm 1.5 is verbatim on p. 4 (l. 132–143), with capacity strictly larger than 1 and at most
  countably many components. The node's contrast with the Serre class (atoms) is an interpretation, not
  an import claim.

## 2.3 Strong Atiyah imports

- **Cor. 1.3** is verbatim: "The strong Atiyah conjecture, the strong algebraic eigenvalue conjecture, the
  center conjecture and the independence conjecture hold for one-relator groups."
- **Thm 1.1** is verbatim: "Let G be a locally indicable group. Then G satisfies the strong Atiyah
  conjecture over C."
- **The claim's formulation.** Bounded orders of finite subgroups, and ranks in `(1/lcm) Z`, is the
  standard Strong Atiyah statement. The bound holds for one-relator groups, since finite subgroups are
  conjugate into the cyclic group generated by the root of the relator. So the formulation is faithful.
- **Prop. 6.5** is verbatim (l. 1849): `G_1` is a torsion-free normal subgroup of `G_2` satisfying Strong
  Atiyah over `K`, and `G_2/G_1` is locally indicable.

## 2.4 `determinant-conjecture-excludes-liouville-atiyah-exceptions`: PASS as a statement

**Setting.** `G` is torsion-free and satisfies Strong Atiyah over `Qbar` and the determinant conjecture.
`A(x)` is a matrix over `O_F[x][G]`, `r(A)` its rank over `D(x)`, and
`kappa(z) = dim ker A(z) - (n - r(A))`.

- **Item 1, re-derived.**
  - Over the noncommutative PID `D[x]` (`x` central), write `P A Q = diag(f_1, ..., f_r) (+) 0`, with `P`
    and `Q` invertible and `f_i` monic up to units.
  - Evaluation at a central algebraic `xi` is a ring map `D[x] -> D`. So `P(xi)` and `Q(xi)` stay
    invertible, and `rank_D A(xi) = #{ i : f_i(xi) != 0 }`.
  - Strong Atiyah over `Qbar` makes the von Neumann rank of `A(xi)`, a matrix over `Qbar[G]`, equal to its
    `D`-rank.
  - A monic `f` over a skew field has at most `deg f` central roots: `f(xi) = 0` gives
    `f = (x - xi) g`, and a second central root `xi'` gives `(xi' - xi) g(xi') = 0`.
  - So at most `sum deg f_i` algebraic points have `kappa != 0`. The artifact's eigenspace-independence
    argument is equivalent.
- **Items 2–3.** `determinant-conjecture-gives-one-variable-atiyah-base-change` (PASS, groups part 10
  §10.1) proves, under the same hypotheses, that `x -> z` embeds `D(x)` into `U(G)` as the division closure
  of `Qbar(z)[G]`, for every transcendental `z`.
  - Then `A(z)` has von Neumann rank `r(A)`, so `kappa(z) = 0` at every transcendental `z`.
  - Item 2 (a lower bound for `|z_0 - xi|` when `kappa(z_0) > 0`) is vacuous.
  - Item 3 (no algebraically Liouville exceptions) holds, because the exceptional set is empty.
- **The route's own item-2 argument** (artifact §4). It was read at step level: Cauchy's root bound,
  Lemma 6 conditioning polynomial in `H`, the small spectrum from Lemmas 5 and 1, and Lemma 3
  perturbation. It is consistent. The constants were not re-derived. The node already records that it is
  superseded.
