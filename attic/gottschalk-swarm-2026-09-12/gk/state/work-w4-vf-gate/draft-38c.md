
### 38.5 Claim display, entry, subsumption and advisories. PASS

- **Claim display.**
  - Point 1 is Proposition 1.1(1)–(3). Point 2 is Theorem 2.3 and Corollary 2.4. Point 3 is Proposition 3.1 and
    Corollary 3.2. Point 4 is Section 4. All are as recomputed in 38.1–38.4.
  - Point 2 cites Theorem 1.1 through `graphs-of-locally-finite-groups-carry-regular-rank-models`, which is
    ESTABLISHED (Section 29).
  - The "Payoff" and "Not claimed" paragraphs match Section 7.
- **Inputs on main.**
  - `leavitt-unit-group-finitely-presented` is ESTABLISHED (literature import).
  - `monomial-rank-models-are-hamming-models`, `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` and
    `graphs-of-locally-finite-groups-carry-regular-rank-models` are ESTABLISHED.
  - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` is ESTABLISHED conditional on its import.
  - `binary-leavitt-unit-group-is-simple`, `openai-leavitt-unit-nonsofic`,
    `d-ary-leavitt-groups-nonsofic-over-finite-fields` and `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`
    each have a proof route. I did not re-check those routes.
- **Entry** on `binary-complement-corner-has-no-weakly-finite-image` (its lines 74–90). It summarizes Sections 1–4 and
  7 accurately, except for the rank bullet (advisory 4).
- **Subsumption scan at `4e7e23aa0d`.** Six phrases hit 133 research files: "closing letter", "close the hexagon",
  "closes the hexagon", "hexagon closing", "no nontrivial finite quotient" and "kills the closing". I read the claim
  and route nodes among them by title and hit line.
  - **Same tool, different complex.** `leavitt-regular-atlas-asymptotic-permutation-cover` (its lines 93–100)
    excludes exact finite covers of the A8 atlas by the same no-finite-quotient argument, applied to `U_Q`. It is
    about atlas covers, not the hexagon letter. It may be listed in `distinct_from`.
  - **Same tool, other statements.** These nodes use the absence of finite quotients for other conclusions:
    - `binary-leavitt-unit-group-is-weakly-sofic` (weak soficity);
    - `simple-group-relator-width-in-finite-simple-targets` (relator width);
    - `large-window-table-groups-present-the-ambient-group` (window screens);
    - `atlas-rankwise-gap-is-ultraproduct-obstruction` (atlas gaps);
    - `finite-orbit-indices-miss-twists-without-finite-quotients` (orbit indices);
    - `thompson-v-not-lef` (LEF).
  - **Recorded.**
    - `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` mentions the letter in an entry.
    - `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` is already in `distinct_from`.
  - **Everything else.** The remaining hits are hyperbolic, Kazhdan, Rips, Higman, random-complex and Titz–Witzel
    nodes, plus artifacts. None concerns stage models of the hexagon.

  No duplicate.
- **Advisories.**
  1. `C_n` names two groups.
     - The centralizer `K_n wr Sym(r_n)`: Summary, Proposition 1.1(4), and the coset in Corollary 2.4's last sentence.
     - The six-piece colimit: Corollary 2.4, Remark 2.5, and claim point 2.

     Rename one, for example `Z_n` for the centralizer.
  2. The Summary and Remark 2.5 speak of "the finite six-piece colimit `C_n`". `C_n` is a colimit of finite pieces
     and is itself infinite. Suggested wording: "the six-piece colimit of finite pieces".
  3. **Route requirements (Section 8).** The claim covers `p = 3`, but the list names only binary inputs.
     - A route should also require `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` and
       `d-ary-leavitt-groups-nonsofic-over-finite-fields`.
     - It should also require `projective-leavitt-unit-groups-mod-scalars-are-nonsofic`, as long as Proposition 3.1
       cites it. The claim's point 3 Inputs omit that node too.
     - Alternatively, the display keeps the ternary half conditional.
  4. **The entry's rank bullet.** It says "`rk(σ(t) - 1) >= ε > 0` in every monomial rank model", which fails for
     the trivial model. What is proved:
     - `rk(σ(t) − 1) > 0` in every monomial rank model with `rk(σ(x_12(1)) − 1) > 0` (Proposition 3.1);
     - the uniform `ε_p` in Theorem 1.1 models (Corollary 3.2).

     A diagonal ultraproduct gives a gap that is uniform over monomial rank models with
     `rk(σ(x_12(1)) − 1) >= δ`, for each `δ > 0`. Suppose `σ_k` violate `1/k`. Their ultraproduct over `k` is a
     monomial rank model with `rk(σ(t) − 1) = 0` and `rk(σ(x_12(1)) − 1) >= δ`, and the proof of Proposition 3.1
     works over any ultrafilter. The claim display (point 3) is already correct.
  5. Section 7 attributes to Arzhantseva–Păunescu the question whether linear sofic groups are sofic, from memory.
     That matches my recollection, but I did not check the source.
- **Scope.** Sections 2–3 obstruct stage models from closing the letter. They make no rank model trivial, and Section
  4 exhibits closing models wherever a hypothesis fails. Still OPEN: `binary-complement-corner-has-no-weakly-finite-image`,
  `binary-leavitt-unit-group-is-f2-linear-sofic`, the gate and Plan 1. The lane may create the route, with advisory 3.
