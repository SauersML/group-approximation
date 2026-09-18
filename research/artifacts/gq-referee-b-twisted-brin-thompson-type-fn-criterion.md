# gq-referee-b: twisted Brin–Thompson type `F_n` criterion and its inputs (citation, scope and priority lens)

Nodes on origin/main at review time (lane bh-typeA-universal; 4292385f3 and later), all with their routes:
- `twisted-brin-thompson-type-fn-criterion` (+ `twisted-bt-type-fn-interval-filtration-proof`);
- `twisted-brin-thompson-type-fn-implies-type-an` (+ `twisted-bt-type-fn-necessity-citation`);
- `stein-complex-elementary-intervals-are-grid-spheres` (+ `stein-interval-grid-sphere-proof`);
- `abstract-twisted-bt-type-fn-criterion` and `interval-spherical-brown-criterion`, citations only, per the addendum.

Referees a and c passed the proofs.

**Sources.**
- BZ: Belk–Zaremsky, arXiv:2001.04579. The TeX is local at `gq/src/bh-typeA-universal/bz-2001.04579.tex`, which is
  byte-identical to `gq/src/bh-free-17/bz22/twisted_Brin_Thompson.tex`.
- FFWZ: arXiv:2603.24687v2. The text extraction is local at `gq/src/bh-typeA-universal/ffwz-2603.24687.txt`, and
  its line numbers agree with the lane's.

**Verdict: PASS.**
- All BZ and FFWZ quotations are verbatim.
- All eight BZ labels point to the statements used, with one citation slip (W2).
- FFWZ Proposition 4.8(ii) needs only faithfulness, as the route says.

**Priority.** A bounded arXiv search finds no proof of BZ Conjecture H, and none of FFWZ's non-faithful conjecture.
The latest relevant papers record both as open (§4). One newer question is answered conditionally by the node (§4,
FFKLZ).

**Imports.**
- Cameron's theorem is not needed. An elementary argument replaces it (W1).
- Quillen's fiber lemma is pinned secondarily.
- Brown VIII.7 and Brown 1984 remain unpinned. Brown 1984 can be replaced by an argument written out in a paper on
  arXiv (W3).

## 1. BZ, read at source

**The conjecture**, TeX l.220–227. The quotation in the node is verbatim:

> "The group `SV_G` is of type `F_n` if and only if the following conditions hold: (1) The action of `G` on `S` has
> finitely many orbits of `n`-element subsets. (2) `G` is of type `F_n`. (3) For each `1 ≤ k < n`, the stabilizer in
> `G` of any `k`-element subset of `S` is of type `F_(n−k)`."

**The letter H.** The introduction uses a single lettered counter, `\renewcommand*{\thetheorem}{\Alph{theorem}}`
(l.148). Its environments are:

| Letter | Line | Environment |
|---|---|---|
| A | l.157 | `thm:FinitelyGeneratedTheorem` |
| B | l.164 | quasi-retracts |
| C | l.169 | quasi-isometric embedding |
| D | l.178 | `finitenesstheorem` |
| E | l.192 | Corollary |
| F | l.201 | `thm:FinitenessLength` |
| G | l.211 | Houghton corollary |
| H | l.220 | the conjecture |

So it is **Conjecture H**, matching FFWZ's "[BZ22, Conjecture H]". ✓

**Labels.** After l.237, `\numberwithin{theorem}{section}` applies.

| Label | Line | Number | As used |
|---|---|---|---|
| `prop:JoinForests` | 601 | Prop 5.3 | dyadic partitions, refinement, least common refinement ✓ |
| `prop:cible` | 647 | Prop 5.6 | contractibility by interval length; "`\|[v,w)\| ∪ \|(v,w]\|` ... is isomorphic to the suspension of `\|(v,w)\|`" ✓ |
| `lem:vtx_stab` | 686 | Lemma 6.3 | "stabilizer ... of a vertex of `X` with rank `m` is isomorphic to `G ≀ Σ_m`" ✓ |
| `lem:stab_spectrum` | 693 | Lemma 6.4 | see W2 |
| `prop:stabs` | 703 | Prop 6.5 | simplex stabilizer "commensurate with `∏ Stab_G(Spec(f_i))`" ✓ |
| `prop:cocpt` | 722 | Prop 6.7 | proof: "`SV_G` acts transitively on the set of vertices `v` with `φ(v) = m`" ✓ |
| `lem:all_big` | 832 | Lemma 7.6 | nerve: "a (contractible) simplex" if some `SSpec(f_i) ⊊ Spec(f_i)`, else "the boundary of a simplex whose vertices are indexed by pairs `(i,s)`", `s ∈ Spec(f_i)` ✓ |
| `prop:E_hi_conn` | 856 | Prop 7.9 | "at least the minimum of `ν(m/2)−2` and `log_2(m/2)−2`" ✓ |

**Further checks against BZ.**
- **Elementary chains.** The route's Step 2, "every chain in `[v,w]` is elementary", is BZ's parenthesis at the
  definition of the Stein complex: "`v_0 ⪯ v_k` (and hence `v_i ⪯ v_j` for all `i ≤ j`)". Apply it to the chain
  `v ≤ u_0 ≤ u_k ≤ w`. ✓
- **The grid-sphere node.** Its statement is exactly Lemma 7.6's nerve dichotomy, for an arbitrary elementary
  interval. Lemma 7.6 is stated only for vertices of `E_m ∖ VE_m` with `μ_2 = 0`, but the nerve computation in its
  proof uses only the lattice of dyadic partitions (Prop 5.3). So the generalization is legitimate. ✓

## 2. FFWZ, read at source

**Definition 1.3**, l.83–91: `[A_n]`, and `(A_n)` when faithful. Verbatim ✓. Condition (ii) uses `Stab_G(T)`. Setwise
and pointwise stabilizers of a finite `T` are commensurable, so BZ's (3) and FFWZ's (ii) agree.

**§4.2, l.919–927.** Verbatim ✓. It includes: "for `3 ≤ n < ∞`, even in the faithful case, `G ↷ S` being of type
`[A_n]` is not sufficient for the action of `SV_G` on `SX^m_G(k)` to reveal that `SV_G` is of type `F_n` (as
conjectured), since not all simplex stabilizers have the 'right' finiteness properties."

**l.1167–1193.** Verbatim ✓. This covers `[HA_n]`, Corollary 4.18, its proof ("[Alo94] ... [dC06, BdCK15]"), and the
paragraph "this is even unknown in the faithful case, see Conjecture H of [BZ22], where this direction is still
open".

**Proposition 4.8**, l.906–918: "Assume `G ↷ S` is faithful." Item (ii): "For all `n ∈ N` there exists `M ∈ N` such
that for all `m ≥ M` the complex `SX^m_G` is `(n−1)`-connected." Its proof is "[BZ22, Proposition 7.9] ... with
standard discrete Morse theory, e.g., [BB97, Corollary 2.6]", together with (i), "[BZ22, Proposition 5.6]".

**Hypothesis match.** Faithfulness is the only hypothesis. BZ §7 is combinatorial in the forests and uses no property
of `G`.

**Same complex.** FFWZ's `SX_G` (Def. 4.7) is the flag complex on cosets `W(m)h` with elementary edges. BZ's `X`
consists of the elementary chains of `P_1`. These are the same complex:
- a set of vertices that are pairwise elementary-adjacent is a chain with `min ⪯ max`;
- conversely, a chain with `min ⪯ max` has all pairs elementary, by BZ's parenthesis;
- `W(m) = 𝒢(m)`.

The sublevel sets agree as well. So the route's Step 1 is covered. ✓

**Necessity node.** FFWZ l.96–98: "for an infinite group `B` of type `F_n`, the permutational wreath product
`B ≀_S G` is of type `F_n` if and only if the action `G ↷ S` is of type `[A_n]` [dC06, BdCK15, FFKLZ25]".
- With `B = Z`, this gives the wreath-product equivalence used. Proposition 4.17 (l.1107) requires type `[A_1]`, as
  the node notes. ✓
- de Cornulier and BdCK15 themselves are pinned only through FFWZ.

**Addendum: the FFWZ gap node** (`ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel`).
- FFWZ Lemma 4.9(i), l.940–944, reads "the stabilizer in `SV_G` of `x` is conjugate in `SV_G` to
  `W(n) ≅ Σ_n ⋉ G^n`".
- Its proof ends: "the action of `SV_G` on `SX_(G/K)` is induced by `SV_G → SV_(G/K)`, so all the results are
  immediate from the faithful case" (l.986–987).
- The stabilizer in the non-faithful case contains the kernel of `SV_G → SV_(G/K)`, and the proof does not address
  it. So the text supports the gap node's reading at source. That node says the gap is in the proof and not in the
  theorem, which is the right claim.

## 3. The imports

- **Cameron, Math. Z. 148 (1976): not needed (W1).** Claim item 3 needs only this: finitely many orbits on
  `n`-subsets gives finitely many orbits on `k`-subsets for each `k ≤ n`, for infinite `S`.
  - Every `k`-subset lies in some `n`-subset.
  - So the orbits of pairs `(T ⊆ U)` with `|T| = k` and `|U| = n` map onto the orbits of `k`-subsets.
  - There are at most `C(n,k)` orbits of pairs per orbit of `U`.
  - Cameron's theorem is the stronger inequality `n_k ≤ n_(k+1)`, which is not needed.
  - Orbits on `S^n` then follow, as in the route's Step 5.
- **Quillen's fiber lemma.** Pinned secondarily. Guzeev, arXiv:2307.00177, Theorem 4 (Quillen–McCord): "If
  `∀y ∈ Y` `B(f^(−1)(Y_(≤y)))` is contractible, then `Bf` is a homotopy equivalence", following Quillen's Theorem A.
  - The route uses fibers `α^(−1)(B°_(≥U))`. That is the same statement for the opposite posets, since
    `|P^op| = |P|`. ✓
  - Alternatively, BZ's own proof of Lemma 7.6 uses the Nerve Lemma, BZ Lemma 7.1, citing Björner's Lemma 1.2. That
    gives the same dichotomy, so the node can cite BZ for the argument.
- **Brown, *Cohomology of Groups*, VIII.7** (finitely presented and `FP_n` implies `F_n`, Wall). Not re-read. It is a
  standard textbook fact and is cited the same way elsewhere in the repository. Unpinned.
- **Brown, JPAA 32 (1984)**, used in the finite-presentation parts of the abstract and interval-spherical nodes. Not
  on arXiv and not read.
  - Khanh, arXiv:2609.08428, l.458–460, writes out a self-contained verification of the 2-dimensional Borel
    construction presentation. It uses path pairs `(g, [p])` and edge-path homotopies. I read it for report 740389fd9.
  - Its general form is exactly what "finitely presented vertex stabilizers, finitely generated edge stabilizers,
    finitely many cell orbits in dimension `≤ 2`" needs. It could be cited in addition to Brown, or instead of Brown
    (W3).

## 4. Priority, bounded, 2026-09-18

**arXiv search.** An arXiv API query for "twisted Brin" (all fields, newest first) returns eleven papers. Six concern
finiteness:
- BZ 2001.04579;
- Zaremsky, 2201.00711 and 2405.18354;
- Wu–Wu–Zhao–Zhou 2407.07703;
- Fournier-Facio–Kropholler–Lyman–Zaremsky (FFKLZ) 2506.02319v2, 2026-02-27;
- FFWZ 2603.24687v2, revised 2026-04-02.

Palmer–Wu 2510.16879 is also on the list. A second query, on abstracts containing "twisted Brin-Thompson" or "Stein
complex", adds nothing after 2026-04-02 in this area.

**What the recent papers say.**
- FFWZ v2 states Conjecture H open, in the faithful case, at l.117 and l.1188–1193.
- FFKLZ proves an obstruction: "`SV_G` ... is not of type `FP_∞`" for groups in `HF` acting on infinite sets
  (Theorem 1.2). It does not treat the conjecture.
- Palmer–Wu and Wu–Wu–Zhao–Zhou concern acyclicity.

So, to the extent searched, Conjecture H (faithful, `3 ≤ n < ∞`) and FFWZ's non-faithful conjecture are unresolved in
the literature. I did not search MathSciNet or zbMATH. This is weaker than a priority clearance, and the node should
say "bounded search".

**A consequence worth recording (optional).** FFKLZ Corollary 1.6 takes `G = Aut_Γ(Γ ∗ F_n)` acting on
`S = Hom_Γ(Γ ∗ F_n, Γ)`, with `Γ` a simple Burger–Mozes group. They show "`SV_G` is finitely presented, but not of
type `FP_∞`", and ask: "For example, is it of type `FP_3`?"
- By the node, that question is equivalent to whether this action is of type `(HA_3)`.

## Warnings

- **W1.** Claim item 3: drop Cameron. Use the elementary pairs argument of §3, or cite Cameron only for the
  inequality.
- **W2.** The route's Step 5 cites `lem:stab_spectrum` for "a twist `γ` at root `i` sends `C_i` to `γC_i`". That
  statement is BZ Lemma `lem:Relations`(7): `x_(γs) τ_γ = (τ_γ ⊕ τ_γ) x_s`. Lemma 6.4 only gives the stabilizer of
  `[f]`.
- **W3.** Brown 1984: also cite Khanh l.458–460 as a written-out proof of the Borel-construction presentation, or
  keep Brown marked "not read".
- **W4.** Priority wording: "bounded arXiv search (API, 'twisted Brin', through 2026-09-18) found no resolution;
  FFWZ v2 (2026-04) and FFKLZ v2 (2026-02) record it open." Add the FFKLZ `FP_3` reduction if you wish.
