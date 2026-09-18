# gq-referee-b: `decidable-group-with-coarsely-embedded-expanders-exists` and `coarse-embeddability-separates-boone-higman` (citation and scope lens)

Nodes as landed at 8093ecc84, with the Greendlinger step as rewritten at 54fdf3550 (lane bh-refute). Both were
passed by referee a (3ef678ef5).

Sources:
- Osajda, arXiv:1406.5015, read from the TeX at `gq/src/bh-graphical-sc/osajda-1406-sclsiga.tex`. Numbers are from
  its counters, with a shared theorem counter per section.
- Gruber–Sisto, arXiv:1408.4488v3, pp. 5–9, read in the arXiv PDF.

**Verdict: PASS for both.**
- Every Osajda and Gruber–Sisto statement the nodes quote checks out at source, with the numbers given.
- The two hypotheses of Lemma 2.14 hold, and so does the `i ≥ e` step.
- The Lyndon–Schupp appeal is correctly gone.
- No mismatch was found. There are two wording points.

## 1. Osajda, arXiv:1406.5015

- **Standing hypotheses**, §2, TeX l.256–263. "Throughout this paper we work with the sequence `Θ = (Θ_n)` of
  disjoint finite connected graphs of degree bounded by `D > 0`", with `girth Θ_n → ∞`,
  `diam Θ_n ≤ A girth Θ_n`, `λ ∈ (0, 1/6]` and `1 < ⌊λ girth Θ_n⌋ < ⌊λ girth Θ_(n+1)⌋`. Also: "this can be fulfilled
  by passing to a subsequence". ✓
- **Theorem 2.7** (`l:c2LLL`, l.688; §2 contains Lemmas 2.1–2.6 before it): "The labelling `(Θ,m)` is reduced and no
  `m_n`-labelling of a path of length at least `λ girth Θ_n` in `Θ_n` appears as the `m`-labelling of some other path
  in `Θ`." ✓
- **Remark 2.8** (`r:recurs`, l.694). It includes "brute force algorithm" and "if the sequence `Θ` of finite graphs is
  recursive, the small cancellation labelling `(Θ,m)`, as well as the resulting small cancellation presentation ...
  are recursive". It continues: "Recursive sequences of finite graphs `Θ` (satisfying our assumptions from the
  beginning of Section 2) exist. Examples are expander graphs given by Cayley graphs of some finite linear groups." ✓
- **§2.4** (`s:discus`, l.711). `Θ_n = X^(p,q_n)`, Cayley graphs of `PGL_2(q_n)` for "primes `p ≠ q` congruent to `1`
  modulo `4` and with the Legendre symbol `(p/q) = −1`". "Then the family `Θ` is an expander with the constant degree
  `D := p+1`, with `girth Θ_n → ∞` ..., and for which there exists a constant `A` such that (1) holds." ✓
- **§3.2** (l.832): "we use the labelling `(Θ,m)` as in Theorem 2.7, obtained for `λ ≤ 1/24`". ✓
  - Theorem 3.2 (`t:mainex`): "each `Θ_n` embeds isometrically into the Cayley graph". ✓
  - Corollary 3.3 (`c:Hilbert`): "If `Θ` is an expanding sequence of graphs then the group `⟨Γ | Θ⟩` is not coarsely
    embeddable into a Hilbert space". ✓
  - Numbering: §3 contains Lemma 3.1 (`l:remb`), then 3.2, then 3.3. ✓
- **The group is the same.** Osajda defines `G = π_1(Γ)/⟨⟨φ_*(π_1(Θ_n))⟩⟩` over a bouquet `Γ` (l.763). The node's
  `M = G(Γ)`, with `Γ = ⊔ Θ_n` in the Gruber–Sisto convention, has the same normal closure, as the node argues. ✓

## 2. Gruber–Sisto, arXiv:1408.4488v3

- **§2.2, p. 5.**
  - `G(Γ) := ⟨S | labels of simple closed paths in Γ⟩`.
  - Essentially distinct lifts: "`p_2 ≠ φ(p_1)` for every label-preserving automorphism `φ`".
  - Definition 2.3, `Gr'(λ)`: "the labelling is reduced and every piece `p` that is a subpath of a simple closed path
    `γ` satisfies `|p| < λ|γ|`".
  - "Note that the `Gr'(1/n)`-condition is stronger than the `Gr(n+1)`-condition." Verbatim, p. 5. ✓
- **The node's derivation of `Gr'(1/24)`.** By Theorem 2.7, a lift `p_2` of `p_1` with `|p| ≥ λ girth Θ_n` is `p_1`
  itself, hence essentially equal. So pieces have length `< λ min(girth) ≤ λ|γ|`. Osajda's "reduced" (locally
  injective, l.277) is Gruber–Sisto's "reduced". ✓
- **Lemma 2.4, p. 6:** "Let `Γ` be a `Gr(6)`-labelled graph, and let `w` be a word in `M(S)`. Then `w` represents the
  identity in `G(Γ)` if and only if there exists a `Γ`-reduced diagram for `w`."
  - The paragraph after it: "Whenever an arc `a` lies in the intersection of two faces `Π` and `Π′` of `D`, it is a
    piece. Therefore, `D` is a `(3,k)`-diagram. If `Γ` moreover satisfies the graphical `Gr′(λ)`-condition, then we
    have `|a| < λ|∂Π|`." ✓
- **§2.5, p. 8.** "If `Π` is a face, then `i(Π)` denotes the number of interior maximal arcs in `∂Π`, and `e(Π)`
  denotes the number exterior maximal arcs in `∂Π`."
- **Lemma 2.14**, p. 8, "([Str90, p. 241])": "Let `D` be a diagram without vertices of degree 2 such that every edge
  is contained in a face. Then `6 = 2 Σ_v (3 − d(v)) + Σ_(e(Π)=k) (6 − 2k − i(Π))`." The node transcribes it
  correctly. ✓

**The hypotheses, as applied to `D_0`.**
- `D_0` is a disk component with at least two faces, and its degree-2 vertices are smoothed away.
- **Every edge lies in a face.** This holds because `D_0` is homeomorphic to a 2-disk. ✓
- **No vertices of degree 2.** Smoothing removes them. Every vertex of a disk has degree at least 2. With at least two
  faces there is an interior arc, and its endpoints have degree at least 3, so the smoothed graph is nonempty. ✓
- Gruber–Sisto define a diagram as a finite contractible planar 2-complex (p. 6), so a disk component qualifies.

**The `i ≥ e` step** (the lane asked for this).
- Let `v` be a vertex of the smoothed `D_0` shared by two consecutive maximal arcs of `∂Π`.
- If both arcs were exterior, the corner of `Π` at `v` would fill the whole interior angle at `v`. A disk has no cut
  vertices, so `v` would then have degree 2, which smoothing excludes.
- So exterior arcs of `∂Π` are separated by interior ones. With `e ≥ 1` for a boundary face, this gives `i ≥ e`. ✓
- This is the standard reading of §2.5. Faces with `e = 1` and `i ≤ 3` are the only positive terms, each at most 3.
  So there are at least two such faces. ✓

**The remaining arithmetic.**
- `|e| > (1 − 3/24)|∂Π| = (7/8)|∂Π|`.
- An extremal disk component meets the rest of `D` in one vertex. The two distinguished faces have distinct exterior
  edges, so at most one of them contains that vertex in its interior.
- The girth bound `girth Θ_i ≤ |γ| = |∂Π| < (8/7)|e| ≤ (8/7)|w|` then gives the search bound `N`.
- Girths increase strictly, since `⌊λ girth⌋` is strictly increasing. So `N` is computable. ✓

## 3. `coarse-embeddability-separates-boone-higman`

- **Yu, A ⇒ CE.** Osajda §1.2 (l.169): "Property A implies coarse embeddability into a Hilbert space \cite{Yu}."
  Secondary pin; Yu's paper itself was not read. The node's other source, Willett's notes via the exactness artifact,
  agrees. ✓
- **Walls and Haagerup.** Osajda §1.2 (l.190): "Acting properly on a CAT(0) cubical complex is equivalent to acting
  properly on a space with walls \cites{HP,Nica,ChaNib} ... This implies in particular the Haagerup property, and hence
  equivariant coarse embeddability into a Hilbert space." This matches the node's "[HP98, Nic04, CN05]". ✓
- **Theorem 2** (l.188): "There exist finitely generated groups acting properly on CAT(0) cubical complexes and not
  having property A." This is the node's item-3 example of `CE` but not exact. ✓
- **Expanders are not in `CE`.** Osajda l.849: "Expanders do not admit coarse embeddings into Hilbert spaces
  \cite{Mat}". Corollary 3.3 rests on this. ✓
- **Scope.**
  - Items 1–2 are correct as stated: a subgroup inclusion is a coarse embedding, and separation is as defined in
    `hereditary-approximation-disproofs-of-boone-higman`.
  - The "What survives" paragraph correctly marks as open whether any finitely presented simple group fails `CE`. ✓

## Warnings (wording only)

- **W1.** The decidable node's Greendlinger paragraph says "which referees should check". It can now cite this
  report: the `i ≥ e` step holds because a disk has no cut vertices and smoothing removes degree-2 vertices.
- **W2.** Osajda's existence statement for recursive `Θ` is in Remark 2.8 itself, TeX l.694–706. The node attributes
  it to "p. 15". Page numbers of the published or arXiv PDF may differ from the TeX, so cite "Remark 2.8 and §2.4".
