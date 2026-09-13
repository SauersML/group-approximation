
### 36.5 Section 5, claim displays, entries, routes, subsumption and scope. PASS

- **Section 5, item 1: the route `summand-obstruction-from-four-transvection-defect`, recomputed.**
  - A unital `ψ : S_- -> W` gives `ρ(g) = ψ(ε_- g)`, a homomorphism `G -> W^x` with `ρ(z) = ψ(−ε_-) = −1`.
  - `D_ρ` involves only `x_12(1)` and `x_23(1)`, both in `Γ_5`, so the OPEN claim gives `D_ρ = 0`.
  - `weakly-finite-leavitt-representations-killing-defect-are-trivial` (ESTABLISHED, characteristic `p > 0`,
    `Γ = R^x`) makes `ρ` trivial. Then `−1 = 1`, so `W = 0` in characteristic three.
  - The target says that no nonzero quotient of `S_-` is weakly finite. Such a quotient is a `W` as above, so the
    implication is valid, and the route is correctly OPEN.
- **Refuters, recomputed.**
  - Soficity: Theorem 4.1 applies to a sofic `Γ_5`, since `z` and `x_12(1)` lie in `<S4>`.
  - Finite quotients: let a finite quotient `Q` separate the eight elements.
    - The image of `z` is central of order two, so `ε_-` is a central idempotent of the finite-dimensional algebra
      `F_3[Q]`.
    - The same eight-term `D` is nonzero there.
- **Item 2.**
  - `jacobson-elementary-subgroups-are-locally-finite-by-linear` is ESTABLISHED (Section 31.1 here).
  - The Tits alternative holds for finitely generated linear groups in every characteristic.
    `SL_2(F_p[ζ, ζ^(-1)])` is not virtually solvable, so `<S4>` is not amenable and lies in no `U_< ⋊ P`.
  - A graph of groups with sofic vertex groups and amenable edge groups is sofic.
- **Items 3–4** restate Propositions 3.3(d) and 3.2(c).
- **Claim displays.**
  - Escape claim: items 1–4 are Theorem 1.1, Remark 1.2, Proposition 1.3 and Corollary 1.4, as recomputed in 36.1.
  - Symbol claim: items 1–5 are Theorem 2.1(a)–(c), Lemma 2.2, and Propositions 3.2 and 3.3(c)–(d). The
    non-amenability consequence is item 2 above.
  - Defect claim: items 1–4 are Theorem 4.1, Corollary 4.2, Theorem 4.3 and Lemma 3.1. The Scope is Remark 4.4.
  - OPEN claim: the statement, the refuters and the algebra-level Attempt are as recomputed. The Attempt is
    Corollary 3.4(b): a weakly finite image kills `s_1 t_1` and `s_0 t_1`.
- **Entries.** The two entries on the ternary nodes summarize Sections 1–5 accurately, subject to advisory 1.
- **Routes.**
  - `four-transvection-escape-proof` requires `depth-monotone-leavitt-subalgebras-are-stably-finite`, which is
    ESTABLISHED. Its steps are 36.1.
  - `four-transvection-symbol-firewall-proof` requires only the Alahmedi–Alsulami–Jain–Zelmanov normal form
    (literature). Its steps are 36.2–36.3.
  - `depth-monotone-tensor-cube-defect-proof` requires the depth-monotone node and
    `linear-sofic-group-algebra-is-stably-finite`, both ESTABLISHED. Its steps are 36.3–36.4.
- **Advisories (wording only).**
  1. "Every five-transvection set" means `S4 ∪ {T}`. The phrase appears in the Scope of the escape claim and in the
     first ternary entry. Section 5, item 4 says that other five-transvection sets are not covered.
  2. The symbol claim's consequence "An anti-central model that is not an algebra homomorphism needs at least six
     transvections" is about obstructions, not models. Suggested wording: "for a set containing `S4`, an obstruction
     that no algebra-level model defeats needs at least six transvections, or a relation outside the span of the
     group".
  3. Remark 4.4 says that `z -> −1` and `D != 0` "fail together only for algebra-level models", which is not proved.
     What is proved is Lemma 3.1, plus the non-additive models of Theorems 4.1 and 4.3. No claim display uses the
     stronger wording.
- **Subsumption scan at `39971c4c98`.** Seven phrases hit 145 research files: "tensor cube", "weakly finite corner",
  "one-sided inverse pair", "transvection set", `EL_2(J`, `SL_2(F_3[` and "nonzero defect". I read the claim and
  route nodes among them by title and hit line.
  - **Unitriangular groups, no `z`.** `unitriangular-data-cannot-assemble-corner-leavitt-families` and
    `unipotent-frame-relations-cannot-assemble-corner-cuntz-family` give rank models with nonzero two-root defect on
    unitriangular groups. Those groups do not contain `z`, so neither is the anti-central form. The defect claim may
    list the first in `distinct_from`.
  - **Inputs to the route.** `ternary-weakly-finite-representations-give-anti-central-images` and
    `no-weakly-finite-representation-from-summand-obstruction` relate representations and summand images, which the
    route uses.
  - **Different targets.** `ternary-defect-is-full-in-largest-weakly-finite-image` is a different OPEN target, and
    `rank-two-jacobson-groups-have-no-infinite-kazhdan-subgroup` is about Kazhdan subgroups of `EL_2(J_k)`.
  - **Other senses.** The remaining hits use the phrases in other senses: A8 certificates, one-hot encodings, Hamming
    defects, and orbits of one-sided pairs.
  - **Recorded.** `distinct_from` already records `depth-monotone-configurations-cannot-force-ternary-minus-one`,
    whose models kill `D`. It also records `anti-central-sofic-data-cannot-force-defect-submultiplicativity` (rank
    `5/9` on cylinder defects) and `ternary-weakly-finite-representations-kill-two-root-defect`.

  No duplicate.
- **Scope.** Each firewall exhibits a nontrivial weakly finite model. None forces a rank model, or `theta`, to be
  trivial. Still OPEN: soficity of `<S4>` and of `Γ_5`, whether `<S6> = G`, and conjugate frames inside `<S4>`.
