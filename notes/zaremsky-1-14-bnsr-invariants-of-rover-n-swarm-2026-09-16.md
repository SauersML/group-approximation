# Zaremsky 1.14 (BNSR invariants of Röver–Nekrashevych groups): swarm notes, 2026-09-16

- Agent: `swarm-zaremsky-1-14-bnsr-invariants-`.
- Target root: `zaremsky-1-14-bnsr-invariants-of-rover-nekrashevych-groups`.
- Hole locked and worked: `characters-living-on-m-plus-one-factors-lie-in-sigma-m`.
- New node: `research/characters-living-on-m-plus-one-factors-meinert-citation.md` (route, `requires: []`, citation
  import plus a short induction). `check.sh` exit 0.
- Nothing committed.

## 1. Setup

- `d >= 2` and `G <= Aut(T_d)` is self-similar. `Γ = V_d(G)`.
- The root's candidate answer is `rover-nekrashevych-higher-sigma-invariants-are-full`: `Σ^m(V_d(G)) = S(V_d(G))`
  whenever `G` has type `F_m`.
- Its only route is `rover-nekrashevych-higher-sigma-full-via-kernel-brown`. That route requires three claims:
  1. `rover-nekrashevych-characters-are-sum-invariant` (already established);
  2. `characters-living-on-m-plus-one-factors-lie-in-sigma-m` (the hole worked here);
  3. `rover-nekrashevych-stein-farley-complex-properties` (open).
- The kernel-Brown route uses the hole in Step 4. There, the kernel `K_k` of `Φ_G ⊕ ... ⊕ Φ_G` on `G^k` (with
  `k >= m+1`) must have type `F_m`. By Bieri–Renz this means: every character `(λ∘Φ_G, ..., λ∘Φ_G)` of `G^k` lies in
  `Σ^m(G^k)`, and each such character is nonzero on every factor.

## 2. What was established

**Result.** The claim `characters-living-on-m-plus-one-factors-lie-in-sigma-m` is now computed ESTABLISHED. Its route
is `characters-living-on-m-plus-one-factors-meinert-citation`. `check.sh` reported "unlocked by this change:
established: characters-living-on-m-plus-one-factors-lie-in-sigma-m" and "route
rover-nekrashevych-higher-sigma-full-via-kernel-brown -> rover-nekrashevych-higher-sigma-invariants-are-full: missing
only rover-nekrashevych-stein-farley-complex-properties (was 2 open)".

**Content of the route.**

- **Import.** Meinert's inequality, homotopical half, as stated in Bieri–Geoghegan arXiv:0808.0013v2, Theorem 1.2:
  `Σ^n(G×H)^c ⊆ ∪_{p=0}^n Σ^p(G)^c ∗ Σ^{n−p}(H)^c`. The paper's join, complement and `Σ^0 = S` conventions are quoted
  in the node.
- **Derivation.** Statement P(j): for `G_1, ..., G_j` of type `F_m` and a character nonzero on every factor, `[χ] ∈ Σ^n`
  for all `n <= min(m, j−1)`. The proof is by induction on `j`:
  - split off one factor, `χ = χ_1 + χ′`;
  - Theorem 1.2 puts a non-member `[χ]` in some `Σ^p(A)^c ∗ Σ^{n−p}(B)^c`;
  - both components are nonzero, so the join forces `[χ_1] ∉ Σ^p(A)` and `[χ′] ∉ Σ^{n−p}(B)`;
  - `Σ^0 = S` forces `p >= 1`, and P(j−1) gives the contradiction.
  - P(k) with `k >= m+1` and `n = m` is the claim.
- **Unwinding the import.** Only the both-components-nonzero case of Theorem 1.2 is used. That case is equivalent to the
  join inequality: if `[χ_1] ∈ Σ^p(A)` and `[χ′] ∈ Σ^q(B)`, both nonzero, then `[χ_1+χ′] ∈ Σ^{p+q+1}(A×B)` in the
  range where it is defined. To see this, let `p_0` be maximal with `[χ_1] ∈ Σ^{p_0}(A)`. The condition at
  `p = p_0 + 1` forces `[χ′] ∈ Σ^{n−p_0−1}(B)`.
- **Consistency checks** in the node, which are not part of the proof:
  - the `F_2 × F_2` sharpness example from the claim node;
  - the Meier–Meinert–VanWyk living-link count for `F_{r_1} × ... × F_{r_k}`, which needs exactly `k >= m+1`. That
    criterion was not re-read, and its theorem number was not checked.

**Certificate boundary.**

- Bieri–Geoghegan state Theorem 1.2 as Meinert's (unpublished) theorem and refer to Gehrke 1998 §9 and Bieri 1999 for
  proofs. Neither was read.
- The BG footnote says matching their formulation to Gehrke's "requires a little work". The one-character-zero case is
  their Proposition 5.1 (label `extreme`; the number was computed from the LaTeX counters). The other case, the one
  used here, is "a straightforward exercise".
- So the route rests on a published statement whose homotopical proof was not inspected. It is the weakest point.

## 3. Literature gate, 2026-09-16

- **Zaremsky, *Some open problems*.** https://zaremsky.github.io/open_problems.pdf, "Date: July 12, 2026",
  SHA-256 `d14c2ce7c26b60363693d1c549f5a25d51ab271e15e5ff4fa8215477d30cde50`. §1 Problem 14 reads "Compute the
  BNSR-invariants of Rover–Nekrashevych groups", with no update note. The problem is still listed as open.
- **Search.** I found no BNSR/Σ^m computation for Röver–Nekrashevych groups in the literature I could reach. This is not
  a certificate of absence.
- **Novelty of the imported statement.** None. It is a standard consequence of Meinert's inequality. The route
  only records a checked derivation.
- **Bieri–Geoghegan, *Sigma invariants of direct products of groups*.** arXiv:0808.0013v2: v1 published 2008-07-31, v2
  updated 2009-08-05, per the arXiv API. `product21.tex` SHA-256
  `7eb4155df547c21c935a3ebd7254532e96b228944fdb853cf0aa14288af98e90`. The journal reference (Groups Geom. Dyn. 4, 2010)
  appears in the claim node and was not re-checked.
- **Skipper–Zaremsky, *Almost-automorphisms of trees, cloning systems and finiteness properties*.** arXiv:1709.06524v2.
  `nekr_fin_props.tex` SHA-256 `b5f2a1f1ed9d8efc2cbb70b91a9cba59fc97b6992a36577d701fa643558c5812`. Numbering was
  computed from `\newtheorem` counters (one shared counter within sections):
  - Lemma 3.1 (Morse lemma, `F_∞` form); Def 3.5 (A-coarsely self-similar); Lemma 3.7 (stabilizers);
    Cor 3.8; Lemma 3.9 (cocompact); Def 3.10 (nuclear); Lemma 3.11 (`P_H^m` directed);
  - Def 4.3 (orderly); Prop 4.7 (lubs); Prop 4.12 (`|P_H^1| ≃ Stein_H`); Cor 4.13 (contractible); Obs 4.17
    (polysimplicial subdivision); Obs 4.18 (feet affine); Lemma 4.21 (disjoint merges span); Obs 4.22 (nested or
    disjoint); flag-complex Lemma 4.23 (unlabelled); Citation 4.24 (Belk–Matucci Thm 6.2 / Belk–Forrest Thm 4.9);
    Lemma 4.25; Prop 4.26 (descending links); Thm 4.27; Cor 4.28;
  - Lemma 5.4 (Šunić groups); Question 5.7.

## 4. Stein–Farley properties (a)–(d) for H = G: analysis only, no node written

The hole `rover-nekrashevych-stein-farley-complex-properties` is the last missing input of the kernel-Brown route. I
did not lock it (one hole per agent), so these checks stay here. A future agent can write them as a `-citation`
route. All references are to SZ arXiv:1709.06524v2, with `H = G` and `A = {id}`. `G` is nuclear in itself and
`{id}`-coarsely self-similar, and `(G, {id})` is orderly (SZ, proof of Cor 4.28). None of the geometric facts below uses
any finiteness property of `G`.

**Shape of the complex when H = G.**

- For `g ∈ G`, `g∨ = ∨ψ(g)` with `ψ(g) ∈ S_d ≀ G` the wreath recursion. So `[x g ∨]_G = [x ∨]_G`.
- Each foot of a vertex has exactly one length-1 splitting class. The elementary sets are `{1_1}` and `{1_1, ∨}`, and
  elementary intervals are cubes. `Stein^poly_G` is the cube complex of the claim node, with `Stein_G` as its
  simplicial subdivision (Obs 4.17).
- Simple elementary mergings have length 1: one merge of `d` feet.

**(a) Contractibility and cocompactness.**

- Contractibility is Cor 4.13 together with Obs 4.17.
- There is one vertex orbit per feet value: Lemma 3.9, or directly, since Γ acts transitively on table maps with `n`
  feet.
- Cubes with bottom vertex `[x]` correspond to subsets `J` of the feet. So sublevel sets are cocompact.

**(b) Stabilizers.**

- `Stab([x]_G) = x(S_n ≀ G)x^{-1}` (Lemma 3.7).
- For the cube with bottom `[x]` and split set `J`, an element `x g⃗ x^{-1}` with `g⃗ ∈ G^n` maps each vertex
  `[x Υ_K]` (`K ⊆ J`) to `[x g⃗ Υ_K] = [x Υ_K w]` for some `w ∈ S ≀ G`, which is `[x Υ_K]`. So `G^n` fixes the cube
  pointwise.
- The stabilizer is `x(G^n ⋊ (S_J × S_{J^c}))x^{-1}`, of index `C(n, |J|)` in the vertex stabilizer. This confirms
  the claim node's "contains all of `G^n`".

**(c) The tall part is contractible.**

- `P_{>= n_1}` (vertices with `>= n_1` feet) is directed. By Lemma 3.11 two elements have an upper bound in `P`, and
  it has at least as many feet, so it is tall. Hence `|P_{>= n_1}|` is contractible.
- Prop 4.12's proof attaches the non-elementary intervals `[x, y]` in order of length along the suspension of the open
  interval `(x, y)`. It shows `(x, y)` is contractible with cone point `core_x(y)`.
- If `x` is tall, every element of `[x, y]` is tall. So the same intervals, attached in the same order, build
  `|P_{>= n_1}|` from `Stein_{>= n_1}`, the elementary chains with minimum `>= n_1`. That subcomplex is the subdivision
  of the full subcomplex `X_{>= n_1}` of the cube complex.
- Hence `X_{>= n_1}` is contractible.

**(d) Truncated descending links.** Let `[x]` have `f` feet.

- `dlk[x]` in `Stein^poly_G` is a flag complex (Lemma 4.23). Its simplices are sets of single merges with pairwise
  disjoint supports (Obs 4.22 plus Lemma 4.21; nesting is impossible at length 1).
- A simplex with `q` vertices comes from a `q`-cube whose bottom vertex has `f − q(d−1)` feet.
- So the descending link inside the full subcomplex `X_{>= n_1}` is exactly the `(Q−1)`-skeleton of `dlk[x]`, where
  `Q = ⌊(f − n_1)/(d−1)⌋`.
- Prop 4.26 (ground simplex, Citation 4.24, Lemma 4.25) gives that `dlk[x]` is `c(f)`-connected, with
  `c(f) = ⌊(⌊f/d⌋ − 1)/(2d−1)⌋ − 1`.
- A `k`-skeleton of a `c`-connected CW complex is `min(c, k−1)`-connected (cellular approximation). So the truncated
  descending link is `min(c(f), Q−2)`-connected.
- For `(m−1)`-connectivity it suffices that `f >= d((2d−1)m + 1)` and `f >= n_1 + (d−1)(m+1)`. The bound does not
  depend on `G`, which confirms the conclusion of (d).
- **Correction to (d)'s explanation.** The claim node says "only the permutation image π(G) <= S_d affects merges".
  That is inaccurate:
  - Fix a support of `d` feet of `x`. The dlk vertices with that support are `[x w^{-1} ∨^{-1}]_G`, and they are in
    bijection with the coset space `(S_d ≀ G)/ψ(G)`, because `∨^{-1} g = ψ(g) ∨^{-1}`.
  - This set can be infinite. For the binary odometer, `ψ(Z) ≅ Z` has infinite index in `S_2 ≀ Z ⊇ Z^2`.
  - The connectivity bound is unaffected, because Belk–Forrest's criterion only looks at supports.
  - The node's "Direct route for (d)" via Hatcher–Wahl complete join complexes is not needed.

**Shape of a future citation route into the properties claim.**

- Import SZ Lemma 3.7, Lemma 3.9, Lemma 3.11, Prop 4.12, Cor 4.13, Obs 4.17, Lemma 4.21, Obs 4.22, Lemma 4.23,
  Lemma 4.25 and Prop 4.26. Add the three derivations above: `G^n` in cube stabilizers, the tall restriction of
  Prop 4.12, and the skeleton truncation.
- Certificate boundary: Belk–Forrest Theorem 4.9 is imported only through SZ Citation 4.24 (not read). SZ remark that
  finiteness of `Δ` can be dropped.
- Also: SZ define `Stein^poly` via polysimplices and `dlk` in that complex. Before writing the route, recheck that the
  claim node's height (number of copies) equals `feet`, and that its cells are SZ's polysimplices.

## 5. Status of the root after this session

- `rover-nekrashevych-higher-sigma-full-via-kernel-brown` now misses only
  `rover-nekrashevych-stein-farley-complex-properties`.
- Once that claim lands, the candidate answer (`Σ^m(V_d(G)) = S` for `G` of type `F_m`) is computed established only
  for the subclass "G of type F_m". The route also imports Bieri–Renz, Brown's criterion and the Morse lemma at
  statement level, and that is a referee target in the route itself.
- The root requires an answer for every finitely generated self-similar `G` and every `m` where `V_d(G)` has type
  `F_m`. That remains open for `G` not of type `F_m`; see §6.

## 6. Beyond G of type F_m: sketch only, unverified

**Setting.** SZ Theorem 4.27: `H <= G` nuclear, `A`-coarsely self-similar for finite `A`, `(H, A)` orderly, `H` of
type `F_m`.

**Plausible kernel-Brown variant.**

- Nuclearity plus iterated sum-invariance, `Φ_G(g) = Σ_{leaves u of T} Φ_G(g|_u)`, give `Φ_G(H) = Φ_G(G)`.
- Cell stabilizers have finite index in `x(S_n ≀ H)x^{-1}` (Lemma 3.7). So they contain some `∏_i H_i` with each
  `H_i` of finite index in `H`: intersect with the coordinate copies.
- Hence `Φ(Stab σ)` has finite index in `Φ(Γ)`: each Γ-orbit of cells splits into finitely many N-orbits.
- `N ∩ Stab σ` contains `ker(Φ on ∏ H_i)` with finite index. Meinert (now established) applies to `∏ H_i` once
  there are `>= m+1` factors.
- The truncated dlk should contain the `(Q′−1)`-skeleton of `dlk`, with `Q′ = ⌊(f − n_1)/(2(d−1))⌋`, since simple
  elementary mergings have length `<= 2`. Not checked: that every vertex of the minimal polysimplex containing `q`
  dlk vertices has feet `>= f − 2q(d−1)` when nested mergings occur.

**Where it dies as a contribution.**

- SZ's non-`F_m` examples in this setting are the Šunić groups `G_{ω,ρ} = ⟨A, B⟩`, with `A` cyclic of order `d` and
  `B^d = 1` (SZ §5.2). They are generated by torsion elements, so `Hom(G, R) = 0` and the character sphere of
  `V_d(G)` is empty. For them the extension says nothing about Σ.
- (This corrects an earlier working guess of mine that Šunić groups would give free-abelian kernels.)
- I know of no group in the nuclear-H setting with a nonzero sum-invariant character that is not already of type `F_m`.

**Contracting groups with nonempty sphere outside all known frameworks.**

- The Basilica group, with the standard recursion `a = (1, b)`, `b = (1, a)σ` (not re-checked against a source), has
  sum-invariant characters `χ(a) = χ(b)`: a one-dimensional space. So `S(V_2(Basilica)) = S^0`.
- `Σ^1` is full there by the established direct proof.
- `Σ^m` for `m >= 2` is out of reach of this route. Even `F_∞` for such `V_d(G)` is SZ Question 5.6 (Bartholdi–Geoghegan
  unpublished, per SZ).
- Whether the Basilica group itself is finitely presented was not checked this session.

## 7. Approaches and where each dies

1. **Meinert via Bieri–Geoghegan Theorem 1.2 plus induction.** Works; written as the route.
   - Dies only at the certificate boundary: the homotopical proof of Theorem 1.2 (Gehrke / Bieri 1999) is unread.
2. **Self-contained proof of the join inequality** `[χ_1] ∈ Σ^p(A)`, `[χ′] ∈ Σ^q(B)` ⇒ `[χ_1+χ′] ∈ Σ^{p+q+1}(A×B)`,
   via controlled connectivity of `{χ_1(a) + χ′(b) >= t}` in `X_A × X_B`.
   - Not written. The join estimate for superlevel sets needs the "essentially `(n−1)`-connected with lag" formulation
     and a careful product filtration. That is more than a short node, so I kept the citation boundary instead.
3. **Living-link criterion directly** (RAAG-style).
   - Dies: it applies only to RAAGs. It was used only as a sanity check of the threshold `m+1`.
4. **Writing the Stein–Farley properties route this session.**
   - Not done: one-hole rule. The mathematics is in §4, and the remaining risk is matching the claim node's complex
     to SZ's polysimplicial complex.
5. **Nuclear-H extension to non-`F_m` G.**
   - Dies for Šunić groups (empty sphere). No example with nonempty sphere is known to fit; see §6.

## 8. Weakest steps (for the referee)

- Theorem 1.2 of arXiv:0808.0013v2 is a stated-without-proof import. The case used is the one BG call "a straightforward
  exercise" relative to Gehrke's formulation.
- The route's Step 4 uses only linear algebra of `Hom(A×B, R) = Hom(A, R) ⊕ Hom(B, R)` and the join definition as quoted.
  Referees should check that BG's `P∗Q` includes `P ∪ Q`, since Step 2 excludes those points. The quoted definition does
  include them.

## 9. Literature consulted, with access dates

- R. Bieri, R. Geoghegan, *Sigma invariants of direct products of groups*, arXiv:0808.0013v2 (v2 2009-08-05). LaTeX
  source read 2026-09-16.
- R. Skipper, M. C. B. Zaremsky, *Almost-automorphisms of trees, cloning systems and finiteness properties*,
  arXiv:1709.06524v2. LaTeX source read 2026-09-16, §§3–5.
- M. C. B. Zaremsky, *Some open problems*, version of July 12, 2026. PDF fetched 2026-09-16.
- Not read, only cited through the above:
  - R. Gehrke, Comm. Algebra 26 (1998), §9;
  - R. Bieri, *Finiteness length and connectivity length for groups* (1999);
  - J. Belk, B. Forrest, Theorem 4.9, and J. Belk, F. Matucci, Theorem 6.2 (via SZ Citation 4.24);
  - L. Bartholdi 2003 on regular branch groups not being `F_2` (via SZ §5.2);
  - Meier–Meinert–VanWyk living-link criterion (consistency check only);
  - S. Witzel, M. C. B. Zaremsky, arXiv:1405.5491 (cited in the properties claim node; not re-read this session).

## Referee (2026-09-16)

**What I checked.**

- **Bieri–Geoghegan source.** Re-downloaded the arXiv e-print of 0808.0013v2. `product21.tex` has SHA-256
  `7eb4155d...e98e90`, matching the node.
  - Recomputed the numbering from the counters (`\newtheorem{theorem}{Theorem}[section]`, shared counter). The
    unnamed MMVW2 theorem is 1.1, Meinert's Inequality (label `Meinert`) is 1.2, and Prop `extreme` is 5.1.
  - Every quote in the route matches the source: the join `P*Q := {[χ+χ′]} ∪ P ∪ Q`, `A^c`, the `Σ^0(G)=S(G)`
    footnote, "only defined when G has ... type F_n", the Gehrke2 §9 / Bieri remark and the footnote ("requires a little
    work", "straightforward exercise").
  - The homotopical half is stated for the Bieri–Renz `^*Σ^n`, the standard homotopical invariants.
  - The arXiv API has no journal-ref for 0808.0013. The GGD 2010 reference stays unchecked, as the node already says.
- **Induction, re-derived line by line.**
  - Base case: `n <= min(m, 0) = 0` and `Σ^0 = S`.
  - Steps 2–4: points with both components nonzero are not in `P ∪ Q`, and the decomposition is direct. The
    positive-scalar bookkeeping is correct.
  - Step 5: `p = 0` would give `[χ_1] ∈ Σ^0(A)^c = ∅`.
  - Step 6: `n − p <= min(m−1, j−2)`.
  - All invariants used are defined, since finite products of `F_m` groups are `F_m`.
  - No hidden hypotheses. The sign convention for `Σ` (`χ >= 0` versus `χ <= 0`) does not matter, because the
    hypothesis and the inequality are both symmetric under `χ -> −χ`.
- **Sanity checks of Theorem 1.2 as quoted.**
  - `Z × Z`, all `n`: gives `Σ^n = S`, which is true.
  - `F_2 × Z`, `n = 1`: complement contained in `S(F_2)`, which is true.
  - `F_2 × F_2`, `n = 1`: complement contained in `S(G) ∪ S(H)`, which is true.
  - It is equivalent to the familiar join form `Σ^p(G) * Σ^q(H) ⊆ Σ^{p+q+1}(G×H)` (Meier–Meinert–VanWyk / Bux–Gonzalez
    usage).
- **Consistency checks.**
  - Re-derived the MMVW living-link count for complete multipartite graphs, which needs `k >= m+1`.
  - Verified the claim node's `k = m = 2` sharpness example with its vertex labelling. The 4-cycle
    `a_1-a_2-b_1-b_2-a_1` has factors `<a_1,b_1>` and `<a_2,b_2>`, so `χ` is living on both. The dead edge
    `{b_1,b_2}` has no common neighbour, so `[χ] ∉ Σ^2`.
- **Duplicates.** `cairn search --similar` and a grep for Meinert / 0808.0013 found no duplicate claim or route.
- **Other sources in the notes.**
  - Zaremsky open-problems PDF: SHA-256 `d14c2ce7...cde50` matches.
  - SZ arXiv:1709.06524v2 `nekr_fin_props.tex`: SHA-256 `b5f2a1f1...8c5812` matches. Recomputed its §3–§5
    numbering, and every label listed in §3 of these notes is right.
  - The Prop 4.26 connectivity formula `⌊(⌊f/d⌋−1)/(2d−1)⌋−1` is as quoted.
  - Citation 4.24 is Belk–Matucci Thm 6.2, attributed to Belk–Forrest Thm 4.9.

**What I changed.**

- In `research/characters-living-on-m-plus-one-factors-lie-in-sigma-m.md`, replaced the stale bold label
  "**OPEN (... the source is still to be read)**" with an ESTABLISHED label naming the citation route. Nothing else
  changed.
- The route is unchanged.

**Verdict.** Sound, landed as a literature-import route (`requires: []`). Its trust surface is exactly the published
statement of Bieri–Geoghegan Theorem 1.2, whose proof (Gehrke 1998 §9; Bieri 1999) was not read; the node says so.

- §§4 and 6 of these notes are analysis only and were not refereed as proofs.
- `rover-nekrashevych-stein-farley-complex-properties` stays OPEN, as does the root question outside "`G` of type
  `F_m`".
