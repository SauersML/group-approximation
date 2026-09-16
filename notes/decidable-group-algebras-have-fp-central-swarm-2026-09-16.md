# Attack on `decidable-group-algebras-have-fp-central-simple-hosts`

Lane `swarm-decidable-group-algebras-have-`, 2026-09-16. The hole was locked for
this attack. Long proofs are in
`research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md`.

## Setup

**Target.** Let `G` be finitely generated with solvable word problem. Find a
finitely presented central simple unital `F_2`-algebra `B` with a unital
`F_2[G] -> B` and `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`, where `L = L_(F_2)(1,2)`.

**The certificate chain.**
- By `leavitt-tensor-hosts-acyclic-steinberg-and-fp` (conditional on Khanh),
  `(B ⊗ L)^x` is finitely presented.
- By `central-simple-leavitt-tensor-unit-groups-are-simple`, `(B ⊗ L)^x` is
  simple.
- So the target implies `boone-higman-conjecture`
  (`boone-higman-via-central-simple-leavitt-tensor-host`).

**State before this lane.** Attempt 5 on the target showed that left coherent
hosts containing `F_2[G]` flatly are impossible once `G ⊇ Z wr Z`
(`coherent-flat-group-algebra-hosts-force-fp-infinity`). The only available
source of the `K`-theory condition was regular (super)coherence of `B`:
- `ara-cortinas-leavitt-tensor-k-theory-vanishes`;
- `regular-coherent-coefficients-kill-leavitt-tensor-k-theory`.

So the target split into two problems: a `K`-theory source that works without
coherence, and existence.

## What was proven

1. **Theorem A**, node `fjc-crossed-products-of-k-trivial-regular-rings-vanish`.
   - **Statement.** Let `P` be torsion-free and satisfy the `K`-theoretic
     Farrell–Jones conjecture with additive coefficients. If `K(R) ≃ 0` and
     every `R[Z^m]` is regular coherent, then every crossed product `R_(α,τ)P`
     has `K ≃ 0`.
   - **Proof.** Bartels–Reich assembly. The orbit values are `R` (Lemma 2.1:
     the unit is `τ_(e,e)^−1 e`) and skew Laurent rings over `R` (Lemma 2.2).
     These are `K`-trivial by Bartels–Lück Nil vanishing. Then a skeletal
     induction.
   - **Novelty.** None claimed: it abstracts the route for tensor powers of `L`.
2. **Theorem B**, node `cantor-crossed-product-leavitt-tensors-are-k-trivial`.
   - **Statement.** Let `B = LC(X, k) ⋊ P`, with `X` compact Hausdorff and `P`
     torsion-free Farrell–Jones. Then `K_n(B ⊗ L) = 0` in every degree.
     Moreover `B` is not left coherent once `P` has a finitely generated
     subgroup that is not `FP_infinity`.
   - **Proof.**
     - `B ⊗ L ≅ LC(X, L) ⋊ P`.
     - `LC(X, L)` is a directed union of finite products of `L`, so it is
       `K`-trivial.
     - Its Laurent extensions are regular coherent: flat unions of finite
       products of central localizations of `L[t_1..t_m]`, which is regular
       coherent by Ara–Cortiñas Lemma 6.1.
     - Theorem A then applies.
   - **What it does.** It obtains the `K`-theory without coherence, which is
     what Attempt 5 asked for. For instance `P = Z wr Z`, which satisfies
     Farrell–Jones by Wegner, at abstract level only.
3. **Reduction**, route `fp-central-simple-hosts-via-cantor-crossed-products`.
   The target follows from the open claim
   `decidable-group-algebras-have-fp-cantor-crossed-hosts` together with
   Theorem B. On this route the `K`-theory half is automatic, and only
   existence remains.
4. **Smaller facts**, in the artifact and not given nodes.
   - **The corner swindle in every degree** (Proposition 8.1). For every unital
     `B`, `K_n(B) -> K_n(B ⊗ L)` is zero for all `n ∈ Z`.
     - `φ(r) = x_1 r y_1 + x_2 r y_2` induces `2·id`: the bimodule `R_φ` splits
       as `R p_1 ⊕ R p_2`, and each summand is isomorphic to `R` through
       `a |-> a y_i`.
     - `φ` fixes `B ⊗ 1`.
     - This is classical; the `K_1` case is already a node.
   - **Necessary shape of a crossed-product host** (Lemmas 6.1–6.3).
     - Finite generation forces `P` finitely generated and `X` a subshift.
     - Simplicity with `P` infinite forces an infinite minimal system.
     - Minimal and topologically free gives centre `k`.
   - **Order-two units.** For clopen `U` with `gU ∩ U = ∅`,
     `(1 − 1_U − 1_(gU)) + 1_(gU) g + 1_U g^−1` squares to `1` in
     `LC(X, k) ⋊ P`. So a torsion-free `P` does not force `B^x` to be
     torsion-free.

## Approaches tried, and exactly where each dies

1. **Hosts of the form `LC(X, F_2) ⋊ P` (open claim C).** The `K`-theory is
   settled by Theorem B, so only existence is left. The attacks are recorded as
   Attempts on `decidable-group-algebras-have-fp-cantor-crossed-hosts`.
   - **`P = Z`. Dies.** Simplicity forces an infinite minimal subshift, which is
     never finitely presented
     (`minimal-subshift-crossed-product-is-not-finitely-presented`, via LEF).
   - **`P = Z^2`. Gated.**
     - Centre `F_2` forces a free action (abelian `P`, minimality). Finite
       presentation forces an SFT and quantum rigidity over `F_2` (both nodes
       unreviewed).
     - Even one such SFT is the `F_2` form of the open
       `free-minimal-z2-sft-is-quantum-rigid`.
     - Each host has a Følner rank model, so this case would make every
       decidable `G` `F_2`-linear sofic.
   - **Amenable `P`. Heuristic only**, with the same linear-soficity
     consequence.
   - **`P = F_d` on `∂F_d`. One host.** It is a Leavitt path algebra: finitely
     presented, simple, with centre `F_2` by Lemma 6.3. One host has one
     complexity bound. Free groups are not an imported Farrell–Jones instance,
     and no finite-presentation criterion for `F_d`-subshifts exists in the
     graph.
   - **Groupoid hosts from Belk–Bleak–Matucci–Zaremsky.** Out of scope:
     Theorem A has nothing to say about Steinberg algebras of non-transformation
     groupoids.
   - **Universality.** No single `(P, X)` works, by
     `complexity-bounded-host-classes-are-not-universal` applied to
     `(B ⊗ L)^x`.
2. **Retract principle. Dies: it produces no hosts.**
   - Let `B` be finitely presented and `B = colim_i B_i`, a directed colimit.
     Then `id_B` factors through some `B_i`, so `B` is a retract of `B_i`, and
     `K(B ⊗ L)` is a retract of `K(B_i ⊗ L)`.
   - So the `K`-theory condition passes from approximants to finitely presented
     retracts.
   - It dies because nothing here produces finitely presented simple retracts of
     `K`-trivial approximants. The approximants of interest (finite products
     over `L`, crossed products) are already covered by Theorem B.
   - It is recorded only as a principle; no node.
3. **Torsion in the acting group. Not attempted.**
   - Theorem A needs `P` torsion-free. For finite `H <= P` the orbit value is a
     crossed product by a finite group; in characteristic `2`, `k[Z/2]` is not
     regular.
   - No vanishing is claimed for such `P`, and `K(L[Z/2])` was not computed.
   - This is why claim C asks for `P` torsion-free. As noted above, `B` can
     still contain torsion units.
4. **Other host shapes over `F_2[G]`. Not attempted.** Free products and HNN
   extensions of algebras over `F_2[G]` fall under the coherence obstruction
   of Attempt 5. A Waldhausen-type vanishing theorem for their Leavitt tensors
   would be the analogue of Theorem A. It was not looked for.
5. **Coherent or regular supercoherent hosts. Dead before this lane** (Attempt 5
   on the target). Not re-attacked.

## Weakest points for a referee

- **Theorem A, Step 4.** The Davis–Lück properties of `H_*^P(−; K_𝒜)` are used
  without being re-read. This is the same trust surface as the existing
  tensor-power route.
- **Lemma 4.2.** Non-connective `K`-theory commutes with directed colimits of
  rings (standard; also used in `leavitt-crossed-product-coefficient-ring-proof`).
- **Lemma 4.3.** Regular coherence of `LC(X, L)[Z^m]` uses Ara–Cortiñas Lemma 6.1
  through the graph import, with their convention for "regular coherent",
  transferred to the Bartels–Lück convention in Section 1 of the artifact.
- **Theorem B.2.** It rests on the unreviewed
  `coherent-flat-group-algebra-hosts-force-fp-infinity`. The `Z wr Z` example
  rests on Wegner at abstract level.

## Literature consulted (2026-09-16)

- **arXiv listing "Boone-Higman" via WebFetch.** 2609.01868, 2603.24687,
  2506.02319, 2503.21882, 2408.05673, 2407.03149, 2405.18354, 2405.10234,
  2405.09722, 2309.06224 (Belk–Bleak–Matucci–Zaremsky) and 2306.16356 (survey).
  None of them is about algebra hosts, and none proves the general conjecture,
  as far as the abstracts show.
- **Steinberg and Leavitt path algebra `K`-theory.** 2506.20321, 2412.15112,
  2309.14325, 1704.01214 (listings and abstracts).
- **Farrell–Jones for crossed products and coefficients.** 2401.14806,
  2006.08454, 1311.6285, 0710.2282, math/0510602 (listings and abstracts).
- **Wegner, arXiv:1308.2432** (Farrell–Jones for virtually solvable groups).
  Abstract fetched. The e-print download failed ("CONNECT tunnel failed,
  response 502"), so the theorem statement is **unverified** beyond the abstract.
- **Bartels–Lück–Reich, arXiv:math/0701434.** Abstract only; not used.
- **The arXiv API returned HTTP 429** for one query. The listing pages were
  used instead.
- **Graph imports**, read from their nodes, whose sources were read in earlier
  lanes:
  - Bartels–Reich math/0510602;
  - Bartels–Lück 2002.03412;
  - Lück–Steimle 1309.1353;
  - Ara–Cortiñas 1108.0352v3;
  - Bartels–Farrell–Lück 1101.0469.
- **Result of the search.** No prior statement of Theorem A or B was found. The
  search was bounded, so no novelty is claimed.

## Referee (2026-09-16)

**Checked.**
- Read all eight files in full, plus the imported nodes
  `crossed-product-rings-inherit-fjc-with-additive-coefficients`,
  `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`,
  `ara-cortinas-leavitt-tensor-k-theory-vanishes`,
  `coherent-flat-group-algebra-hosts-force-fp-infinity`, the existing route
  `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` (which Theorem A
  abstracts), and the nodes cited in the Attempts on claim C. Every cited id exists.
- **Lemma 2.1** re-derived: (C2) with `g = h = e` gives `c` central; (C1) with
  `g = h = e` and with `h = k = e` gives `τ_(e,k) = c`, `τ_(g,e) = α_g(c)`;
  `c^−1 e` is a two-sided unit and `r |-> r c^−1 e` is multiplicative.
- **Lemma 2.2** re-derived: `t (1 g^−1) = ι(τ_(g,g^−1) c)`, `ι(r) t^n = r u_n g^n`,
  grading gives injectivity of `Ψ`, and `t a = φ(a) t`.
- **Theorem A Steps 2–4**: torsion-free virtually cyclic groups are `1` or `Z`;
  skeletal induction is the same Davis–Lück trust surface as the existing route.
- **Lemma 4.3**: central localization (clear denominators with central units),
  finite products (`e_j M` pieces), flatness of the directed union (each `D^𝒬` is
  a finite sum of summands `D^𝒫 e_U` on each side), descent of finite
  presentations, and the side swap by `x_i <-> y_i` extended pointwise. No gap found.
- **Theorem B.1**: `(f g)(f' h) = f α_g(f') gh` matches the Bartels–Reich product
  with `τ ≡ 1`, and `α'_g α'_h = α'_(gh)`.
- **Theorem B.2**: `B` is a free right `k[S]`-module on `{f_j c}` containing `1`;
  the hypotheses of the imported coherence obstruction are met.
- **Lemmas 6.1–6.3**, the order-two unit of attack 6 (all nine products
  recomputed), and Proposition 8.1 (the bimodule splitting and `β_i`) re-derived.
- **Duplicates**: `bin/cairn search --similar` on the three new claims finds no
  duplicate; the nearest nodes are already in `distinct_from`.
- **Citations spot-checked (WebFetch, 2026-09-16)**: arXiv:1308.2432 is Wegner,
  "The Farrell-Jones Conjecture for virtually solvable groups", abstract as quoted,
  J. Topol. DOI 10.1112/jtopol/jtv026. arXiv:2309.06224 is
  Belk–Bleak–Matucci–Zaremsky, "Hyperbolic groups satisfy the Boone-Higman
  conjecture" (hyperbolic case only; the general conjecture remains open as far as
  Zaremsky's arXiv listing shows).

**Changed.**
- "At least as hard as Boone–Higman" in claim C, the reduction route and the
  artifact now says the implication is granted the graph's chain, which is
  conditional on Khanh arXiv:2609.08428v1 through
  `leavitt-tensor-hosts-acyclic-steinberg-and-fp`.

**Verdict.** Theorems A and B are sound derivations from graph imports (no
novelty claimed, honestly labelled unreviewed); claim C is an honest open hole
with Attempts; the reduction route is correct. Landed with the small fix above.
Remaining trust: Davis–Lück properties, the Ara–Cortiñas convention for regular
coherence, and the unreviewed coherence obstruction used only in B.2.
