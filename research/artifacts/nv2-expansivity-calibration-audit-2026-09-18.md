# Adversarial audit of the expansivity calibration wave (nV Haagerup lane)

Agent `e2-w2-audit-nv2`, wave `swarm-0917`, 2026-09-18. No new research; verification only.

Five claims landed ESTABLISHED on main on 2026-09-17 with no referee stage:

| id | kind | verdict |
|---|---|---|
| `nekrashevych-expansive-groupoid-criteria` | import | **survives** |
| `ad-nuclear-crossed-product-gives-amenable-action` | import | **survives** |
| `robertson-steger-word-products-and-boundary-topology` | import | **survives** (one implicit step, filled below) |
| `ample-groupoid-products-expansive-iff-factors-are` | proof | **survives** |
| `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host` | proof | **survives as stated**; its stated consequence is incomplete (D1) |

The three TeX sources were re-downloaded independently of the original lane, from
`https://arxiv.org/e-print/1511.08241`, `https://arxiv.org/e-print/1302.5593` and
`https://arxiv.org/e-print/math/0005014`, and every imported sentence was matched
character by character against the source. Line numbers below are this audit's own.

## 1. Citation lens

### 1.1 Nekrashevych, `fullgr.tex` (arXiv:1511.08241)

All seven imported items and the three standing conventions are **verbatim**:

- standing assumptions, line 228: "All groupoids in this paper are étale (see below) and
  the unit space `\G^{(0)}` is homeomorphic to the Cantor set."
- bisection / étale, lines 236-241; minimal, line 185; `examp:action`, lines 201-211
  (multiplication `(g_1,x_1)(g_2,x_2)=(g_1g_2,x_2)` defined iff `g_2(x_2)=x_1`,
  `\be(g,x)=x`, `\en(g,x)=g(x)`).
- `def:compactgenset` and the two remarks after it, lines 788-805.
- expansive cover, lines 823-830 — the source does say **"open compact generating set"**,
  which the node reproduces; this matters, because the product proof needs openness.
- independence of the cover, lines 831-838; `pr:bebasis`, lines 860-878; transversals,
  lines 921-924; `pr:expansivegroups`, lines 965-983; `th:finitelygenerated`, lines
  1075-1079.

**The node's "reading" of *expansive groupoid* is confirmed by the source, not merely
consistent with it.** The paper indeed has no definition environment for it, but
Theorem `th:universalcov` (line 1318) reads "A compactly generated groupoid `\G` is
expansive if and only if there exists a finite generating set `\mathcal{S}` of bisections
such that …", which presupposes exactly the node's reading (compactly generated, plus an
expansive cover of some compact open generating set). The proof of `pr:expansivegroups`
(lines 985-1041) was read in full; (3)⇒(4)⇒(1),(2) is the direction the two downstream
proofs use, and it is proved there.

*Item not imported but available for free, used in D2 below.* Proposition
`pr:essprincipalHaus`, line 1099: "If `\G` is essentially principal and Hausdorff, then it
is a groupoid of germs. **Every second countable groupoid of germs is essentially
principal.**" Its proof (lines 1103-1118) needs only that
`\{\gamma : \be(\gamma)=\en(\gamma)\}` is closed — which holds for any étale groupoid with
Hausdorff unit space, since it is the preimage of the diagonal under the continuous map
`\gamma \mapsto (\be(\gamma),\en(\gamma))` — plus Baire on `\G^{(0)}`. Hausdorffness of
`\G` itself is **not** used.

### 1.2 Anantharaman-Delaroche, `Edinburgh.tex` (arXiv:math/0005014v2)

Definition 2.1 (lines 148-160), the transformation-group setting (lines 127-134), the
notation paragraph (lines 509-514) and Theorem 3.4 (lines 587-603) are **verbatim**,
including the final sentence "Morever (4) `\Rightarrow` (1) if `G` is discrete."

Standing hypotheses match what the host proof uses: `X` locally compact (here `\Omega`
compact Hausdorff), `G` locally compact (here `\Gamma` discrete), continuous left action.
The downstream specialization (4)⇒(1)⇒(2) with `A = C(\Omega)` is legitimate: `C_0(X)` is
trivially a `G`-`C_0(X)`-algebra, so (2) applies to it and gives full = reduced.

### 1.3 Robertson–Steger, `CK1.tex` (arXiv:1302.5593)

Items 1-6 (lines 200, 205-222, 225-235, 244-248 for (H1), 461-471 for Corollary 4 with its
one-line proof `\ou v=(d,uv)`) and items 7-11 (lines 1527, 1541-1545, 1549, 1597-1600,
1749-1754) are **verbatim**. The relations `rel1` (lines 666-676), Lemma `f2` (684-693),
Lemma `5` (699), Lemma `oalpha` (1758), Lemmas `c1` (1809) and `c2` (1817), the formula for
`\phi` (lines 1794-1800, "Let `\g \in \G` be the unique element such that
`\g t(p_1)=t(p_2)`"), Theorem `main2` (1905) and the Remark after it (1925-1934) were all
checked as well, because the host proof's algebra rests on them.

**D3 (implicit step, filled, not a defect in substance).** The node derives "`D` is
finite" from "`\delta : D \to A` is injective" plus "`A` is a finite set". The second half
is the *general* Section 1 convention (line 200, "We fix a finite set `A`"); in Section 7
the alphabet is redefined as `A = \G\backslash\fT` (line 1598) and Robertson–Steger never
prove that this quotient is finite. It is: `\cB` is locally finite (line 1527), so only
finitely many type rotating isometries `\ft \to \cB` are based at each vertex, and `\G` has
finitely many vertex orbits (line 1549). This one line should be stated, because `D` finite
is what makes `\cA` unital (Remark `finitedecorate`, line 715) and hence what lets Remark
`previous` (line 1514) — and therefore the Remark after `main2`, which is the source of
simplicity, nuclearity and pure infiniteness — apply at all.

Two smaller bookkeeping notes: the citation route's line window "1546-1547" for the
sentence introducing `\G` is 1549 in the copy fetched here, and "207-248" for the standing
conventions is 201-241; the content is identical.

## 2. Proof-gap lens

### 2.1 `ample-groupoid-products-expansive-iff-factors-are`

Every step was re-derived. No gap found. The checks that could have failed and did not:

- **(P1)** `(P_1\times Q_1)(P_2\times Q_2) = P_1P_2 \times Q_1Q_2` really is an equality and
  not just `\subseteq`: composability in a product groupoid is coordinatewise, so the two
  coordinates may be chosen independently.
- **Item 1, forward.** `(g,h) = (g_1,\en(h))\cdots(g_n,\en(h))\cdot(\be(g),h_1)\cdots(\be(g),h_m)`
  is composable, because a unit composes with itself and the source of the first block,
  `(\be(g),\en(h))`, is the range of the second. Each factor lies in `S\cup S^{-1}`.
- **Item 1, converse.** `\pi_1` is a groupoid homomorphism (composability is
  coordinatewise), `X_2 \ne \emptyset`, so a word for `(g,y)` projects to a word for `g`.
- **Item 2, only if, Step 1.** The refinement `\mathcal{R}` satisfies `\bigcup\mathcal{R} =
  \bigcup\mathcal{S} \supseteq S`, compact and open, so it is a finite cover by bisections
  of a compact **open** generating set — the openness that the definition of an expansive
  cover requires is supplied by bisections being compact open. Lifting a word for `u`
  through `\gamma = \gamma_1\cdots\gamma_n` into `\mathcal{R}\cup\mathcal{R}^{-1}` keeps the
  source inside the original source, so disjointness is inherited.
- **Item 2, only if, Step 2.** `S'_1 = \bigcup\mathcal{R}_1 \supseteq \pi_1(S)` generates by
  the converse of item 1 plus "supersets of generating sets generate". The projection step
  uses a **fixed** `z \in X_2` on both sides, which is what forces `\be(P)\cap\be(P') =
  \emptyset` out of the disjointness of the two rectangles.
- **Item 3.** The identification of `U_{\mu,\nu}\cap U_{\mu',\nu'}`, compactness of
  `U_{\mu,\nu}`, `U_{\emptyset,\emptyset} = U_{0,\emptyset}^{-1}U_{0,\emptyset} = X`
  (all of `X`, not only `[0]`), and the expansive cover
  `\{U_{0,\emptyset},U_{1,\emptyset}\}` via `\be(U_{\nu,\emptyset}^{-1}) = [\nu]`: all
  correct.
- **Item 4.** `E\times M` generates `\Gamma\times M` with the paper's multiplication
  convention, and `pr:expansivegroups` (1)⇔(4) is applied with its two hypotheses (`\Gamma`
  finitely generated, `M` a Cantor set) actually in force.

### 2.2 `rs-boundary-groupoid-is-expansive-amenable-kazhdan-host`

The four load-bearing assertions of the wave's conclusion were each re-derived.

- **Expansive (Step 2): confirmed.** The finite obstruction set `C` is genuinely finite and
  independent of the pair `(x,y)`: `\bar W_0 \cong D` is finite, `A_0 \subseteq A` is
  finite, and `W_{e_j} \subseteq A^{[0,e_j]}` is finite. Every rectangle misses the
  diagonal, using Lemma A(b) for level-0 and, for the second family, that
  `r_a w \ne r_a w'` when `w \ne w'` (Corollary 4 plus uniqueness in (H1)). The minimal-`|m|`
  argument is sound: the set of shapes at which the cells of `x` and `y` differ is upward
  closed because cells refine (A(c)), `m-e_j \ge 0` whenever `m_j \ge 1`, so minimality
  gives `\bar u' = \bar v'` and hence `w \ne w'`. The last-row decomposition A(e) uses the
  **undecorated** restriction `u|_{[m-e_j,m]}`, which is correct even when `m = e_j`, where
  the decorated convention `\bar w|_{[0,l]}` would have produced a decorated word.
  The generator algebra A(d1)-(d3) was re-derived from `rel1a`, `rel1b`, `f2` and Lemma `5`;
  in particular `s_{\bar v w',\bar u w'} s_{\bar u w,\bar u w} =
  s_{\bar v w',\bar u w'}s_{\bar u w',\bar u w'}s_{\bar u w,\bar u w} = 0` for `w' \ne w`
  needs the insertion of `s_{\bar u w',\bar u w'}` first, which the proof does.
- **Minimal (Step 3): confirmed.** The quotient `\pi : C(\Omega)\rtimes\Gamma \to
  C(Y)\rtimes\Gamma` is nonzero and has nonzero kernel `1_U`, contradicting simplicity.
  No circularity with Step 4: Step 3 uses simplicity, Step 4 uses nuclearity, both from the
  same RS Remark.
- **Amenable (Step 4): confirmed**, given D3 above (which is what licenses the Remark).
- **Infinite Kazhdan subgroup (Steps 1, 5): confirmed.** `\Gamma \to \full{R}`,
  `g \mapsto \{g\}\times\Omega`, is a homomorphism for the paper's multiplication
  convention and is injective; the corresponding map into the full group of the germ
  groupoid is injective because the action is faithful. Property (T) and finite generation
  come from established nodes whose own imports (BdHV 1.3.4, 1.4.15, 1.7.1; BdHV 1.3.1)
  were not re-fetched in this audit.
- Perfectness, infinite orbits and the absence of invariant measures: confirmed.

**Conclusion of the proof-gap lens: no step of either proof is wrong.** Both claims keep
ESTABLISHED.

## 3. D1 — the one material defect: the class kill is silent about Hausdorffness

The host node's "What survives" says, of the groupoid level, "**only** proofs using
effectiveness and amenability *together with* expansivity". That word "only" is wrong, and
the gap it hides is the one that matters for `2V`.

The two hosts sit on opposite sides of a property neither list mentions:

| | `R = \Gamma\ltimes\Omega` | germ groupoid `\G_{germ}` |
|---|---|---|
| Hausdorff | **yes** (`\Gamma` discrete, `\Omega` Hausdorff) | **not established** |
| effective | **not established** (needs `\Gamma\curvearrowright\Omega` topologically free) | **yes** |
| amenable | yes (Step 4) | not established |
| expansive, minimal, compactly generated, no invariant probability measure | yes | yes |

`(L_{germ})` as written — étale, Cantor unit space, compactly generated, expansive,
minimal, effective, no invariant probability measure — omits Hausdorffness, so the kill is
literally correct. But **no Haagerup theorem for topological full groups is stated outside
the Hausdorff setting.** Matui's theorem, which this very route cites as the model
(`sft-topological-full-groups-have-the-haagerup-property`), and every statement about
`G_2^n` in `brin-thompson-groups-nv-are-a-t-menable` ("ample, topologically amenable,
minimal, essentially principal and purely infinite"), live in Hausdorff étale groupoids.
Against the hypothesis list that anyone would actually write down —

> Hausdorff, étale, Cantor unit space, compactly generated, **expansive**, minimal,
> **effective**, no invariant probability measure

— **neither host is a counterexample**, and the wave's headline "expansivity with
effectiveness is also killed" does not reach it. The same silent omission is repeated in
`brin-thompson-groups-nv-are-a-t-menable` ("Also killed: expansivity with effectiveness")
and in its calibration table ("Expansivity-based …: RS. Only effectiveness is left out").

This is recorded as a caveat, not a refutation: the claims' own statements are true.

### 3.1 The single statement that closes D1

> **(TF)** For a lattice `\Gamma \le PGL_3(K)` acting type rotatingly and freely on the
> vertices of its `\tilde A_2` building with finitely many orbits, the boundary action
> `\Gamma \curvearrowright \Omega` is topologically free: `\operatorname{int}\{ \omega :
> \gamma\omega = \omega\} = \emptyset` for every `\gamma \ne 1`.

(TF) makes `R` effective, hence `R = \G_{germ}`, and then a **single** groupoid is
Hausdorff, étale, ample, compactly generated, expansive, minimal, effective, essentially
principal, amenable, with no invariant probability measure and a simple nuclear purely
infinite C\*-algebra — every property `G_2^n` is known to have, except the product
factorization — while hosting an infinite Kazhdan group in its full group. That would
close the whole groupoid level of the nV Haagerup problem, leaving only the product
factorization, which is exactly where
`rank-two-prefix-replacement-groups-contain-infinite-kazhdan` already says the argument
must go.

Two routes to (TF), neither attempted here (this is an audit lane):

1. **Word-system route, internal to Robertson–Steger.** Suppose `\gamma \ne 1` fixes a
   nonempty open set pointwise. Cells form a basis (`c2`), and they refine (A(c)), so
   `\gamma` fixes some cell `\Omega(p)` pointwise with `p \in \bar{\mathfrak W}_m` and
   `m_1, m_2 \ge d(O,\gamma^{-1}O)`. By `main2` and Lemma A(d), `\gamma|_{\Omega(p)}` is a
   prefix replacement `\bar u \Rightarrow \bar v` with `\bar u = \bar\alpha(p)`,
   `\bar v = \bar\alpha(p')`, so `\Omega[\bar u w] = \gamma\Omega[\bar u w] =
   \Omega[\bar v w]` for every admissible `w`. If one can show `\sigma(\bar u) =
   \sigma(\bar v)`, then Lemma A(b) forces `\bar u = \bar v`, hence `p' = p`, hence
   `\gamma t(p) = t(p)`, hence `\gamma = 1` by freeness on vertices. The missing step is
   the shape equality. It should follow from counting level-`k` subcells of the one set
   `\Omega[\bar u] = \Omega[\bar v]` in two ways: the counts are
   `\#\{w \in W_{k-\sigma(\bar u)} : o(w) = a\}` and
   `\#\{w \in W_{k-\sigma(\bar v)} : o(w) = a\}` with `a = t(\bar u) = t(\bar v)`, and
   thickness of `\cB` should make `m \mapsto \#\{w \in W_m : o(w)=a\}` strictly increasing.
   **Falsifiable first step:** prove that every row sum of `M_1` and of `M_2` is at least 2
   for a thick `\tilde A_2` building, or exhibit a tile with a unique extension.
2. **Algebraic-group route.** `\Omega` is the space of chambers at infinity of the
   Bruhat–Tits building of `PGL_3(K)`, i.e. `G/B(K)`, and `\Gamma \le G`. For `\gamma \ne
   1`, the fixed subvariety `(G/B)^\gamma` is proper (the intersection of all Borels is the
   centre, trivial in the adjoint group), and a proper Zariski-closed subset of a smooth
   irreducible `K`-variety has empty interior in the `K`-topology. This needs one import —
   the `\Gamma`-equivariant identification of the Robertson–Steger boundary with `G/B(K)` —
   which the graph does not yet have.

## 4. D2 — a free strengthening the wave left on the table

By Nekrashevych `pr:essprincipalHaus`, second sentence (quoted in §1.1), **every second
countable groupoid of germs is essentially principal**, and its proof does not use
Hausdorffness of the groupoid. `\G_{germ}` here is second countable (`\Gamma` countable,
`\Omega` second countable by Step 1 of the host proof), so:

> `\G_{germ}` is **essentially principal**, at no cost.

"Essentially principal" may therefore be added to `(L_{germ})` for free. This matters
because it is one of the five properties `brin-thompson-groups-nv-are-a-t-menable` lists
for `G_2^n`, so the kill covers it too — and it isolates Hausdorffness (D1) as the *only*
remaining structural escape at the effective end, alongside amenability of `\G_{germ}` and
pure infiniteness in Matui's groupoid sense.

## 5. Verdicts posted to the bus

`survives` for all five ids, with D1 recorded as an incompleteness of the stated
consequence and D3 as an implicit step now filled.
