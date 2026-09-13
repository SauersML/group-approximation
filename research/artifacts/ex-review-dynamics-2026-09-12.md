# EX review: dynamics and entropy lanes (2026-09-12)

Lane `ex-verify-dynamics`, adversarial verifier of the EX swarm. One section per lane under review.
Long sections move to part files `research/artifacts/ex-review-dynamics-2026-09-12-part<N>.md`,
indexed at the end.

## 0. Scope and method

Lanes under review:
- ex-bernoulli-negative;
- ex-bernoulli-positive;
- ex-rokhlin-lower;
- ex-nonsofic-action-relative;
- ex-nonsofic-action-entropy;
- ex-bernoulli-rokhlin-complete;
- ex-lattice-space-action;
- ex-tree-lattice-mixing.

Verdicts are as in `research/artifacts/ex-review-groups-2026-09-12.md` §0:
- **PASS**: the argument was re-derived, and the statement, hypotheses and citations match.
- **FAIL**: the statement is false as written, or the argument has an error with no local fix.
- **GAP**: the statement may be true, but the written argument does not prove it.

Already passed by `ex-verify-groups`: nothing from these lanes. Its only review section is the Pestov 9.1
candidate. So nothing here is skipped.

Sources read for this review:
- Seward arXiv:1805.08279v1 from the PDF text on MSI (`review-lit/entropy/1805.08279.txt`): Definition 2.1,
  Proposition 2.2, Lemma 3.1, Theorem 3.2 and its proof, references [6], [17], [18].
- Păunescu arXiv:1002.0605v5 and Ciobotaru arXiv:1403.0223 from the PDFs (Section 2).

## 1. ex-bernoulli-negative (44fec21fb7, d2a8ad5ce4, 2c4a31bcd4, a005a66833, c52c701fd7)

| node | verdict |
|---|---|
| `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli` (+ `-proof`) | Corollary D: PASS for countably infinite `G`. Theorem C: GAP in one edge case (§1.1). Statement: FAIL for finite `G`; corrected to "countably infinite" |
| `stable-finiteness-failure-is-algebraic-bernoulli-absorption` (+ `-proof`) | PASS |
| `bernoulli-factor-algebraic-actions-have-finite-stabilizers` (+ `-proof`) | PASS |
| `leavitt-module-dual-actions-are-self-squares-off-bernoulli` (+ `-proof`) | PASS |
| `finite-subgroup-induced-absorption-conserves-entropy` (+ `-proof`), with its input `lifted-trace-finite-subgroup-proof` | PASS |
| `induced-projective-absorption-breaks-bernoulli-classification` (+ `-proof`) | PASS as an implication. Its hypothesis never holds |
| `leavitt-unit-algebra-absorbs-an-induced-projective` [REFUTED], dead route `leavitt-induced-absorption-gives-bernoulli-collapse` | PASS. The invalidator is established through a `requires: []` chain, so the dead route does not fire into the famous root |
| `bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square` (+ `-proof`) | PASS |
| `bernoulli-collapse-ascends-to-universal-hosts` (+ `-proof`) | PASS, one note (§1.6) |
| `bernoulli-isomorphism-collapse-set-is-a-subgroup` items 1–7 (landed by ex-bernoulli-positive, consumed here) | PASS. Item 8 rests on `rokhlin-supremum-dichotomy-with-centralized-self-copies`, which is not re-derived here |

### 1.1 Theorem C (co-induced Ornstein)

**Source.** Seward's Definition 2.1 of `R_Γ` matches the hypothesis of Theorem C for `Y_i = L_i^Γ`:
- equal entropy;
- a Borel `Γ`-invariant `P ⊆ (L ∩ K)^Γ` with `λ^Γ|P = κ^Γ|P`, `λ^Γ(P) > 0`, and trivial stabilizers on `P`.

Seward's Theorem 3.2 is his main theorem restated. After Lemma 3.1 (either `Z <= G`, or a finite
`Γ <= G` with `|Γ| >= 5`) and Proposition 2.2, its proof treats the `R_Γ` case. The citations `[6, Lem. 3.25]`
(Jackson–Kechris–Louveau) and `[17, 18]` (Ornstein) match the artifact. Wording note: "Seward's Theorem 3.2
in that case" should read "the `R_Γ` case of the proof of Seward's Theorem 3.2".

**Re-derivation.** Steps 1–6 of the artifact were re-derived.
- The freeness count in Step 2 is right.
- `Z_*` is `F`-invariant because `z(f^-1) = f.z(1)`.
- The rows `f_i(w^j_0 . x)` are i.i.d. with law `alpha_i^Z` conditionally on `z = theta_i(x)`. The
  distinguished root of a `*`-coset is a `z`-measurable choice. `alpha_i` is `F`-invariant because `A_i` and
  `nu_i` are. So re-rooting a label does not change its conditional law, and labels at distinct cosets stay
  conditionally independent.
- The display `(w^j_n . pi(x))(1_G) = zeta(f_1(w^j_0 . x))(-n)` checks: `f = 1` at a distinguished root,
  and `zeta` commutes with the shift.
- The co-induced relation `pi(x)(g f'') = f''^-1 . pi(x)(g)` checks.

**GAP (edge case).** Step 4 cancels `H_(nu_i)({P, A_i}) + rho H(P, nu_i|P / rho)` from both sides. When
that term is infinite, the cancellation is invalid and the proof fails.

Counterexample to the step: `F = C_2`, `P` a nonatomic free `C_2`-space. `A_1` is one fixed point, and `A_2`
is two fixed points of equal total mass. Then:
- `H(Y_1) = H(Y_2) = ∞`;
- `H(A_1) = 0 != log 2 = H(A_2)`;
- so no `zeta` exists.

Whether `Coind(Y_1) ≅ Coind(Y_2)` in such cases is not decided here. Local fix: add the hypothesis
`H(nu_i|P) < ∞`. It holds automatically when `H(Y_i) < ∞`, and in every use in the graph, since Corollary D
uses a finite free orbit `P`. No downstream node is affected. Seward's display on p. 9 has the same
subtraction. This review did not audit his infinite-entropy case, and nothing here consumes it beyond the
refereed Theorem 1.1.

**FAIL (wording, finite groups).** The claim says "every countable group". For finite `G`, Theorem C and
Corollary D are false: take `G = F`, so `Coind(Y) = Y`, and two non-isomorphic F-spaces of equal entropy
sharing a free orbit. Step 2 uses that `G/F` is infinite. Correction: "countably infinite".

### 1.2 Corollary D

Re-derived.
- **Lemma T.** The interpolation `(q, r u, r(1-u)/(N-1), ...)` has entropy running continuously from
  `H(q, r) + r log N` down to `H(q, r)`.
- **Tuning `K`.** `H(1 - δ, ε, δ - ε) = H_2(δ) + δ H_2(ε/δ) <= H_2(δ) + δ log 2`.
- **The free orbit.** `(f.k*)(f) = k*(1_F) = k_1 != k_0`, so the orbit of `(y_0, k*)` is free. Each point
  has mass `c = nu(y_0) ε (1 - δ)^(|F|-1)`, since `nu` is `F`-invariant.
- **Tuning `M`.** `mu_a = c/β^(|F|-1) <= 2c <= 2ε`, so `r = 3ε - mu_a >= ε`, and
  `H(β, mu_a, r) <= H_2(3ε) + 3ε log 2`.
- **Entropy equation.** `H(Y) + |F| h_K = |F| h*`.
- **Identifications.** `Coind(Y × K'^F) = Coind(Y) × K'^G` and `Coind(L^F) = L^G` check.

The sanity check over amenable groups is consistent. There `Coind(Y)` is a Bernoulli factor, hence Bernoulli
by Ornstein–Weiss, with entropy `H(Y)/|F|`, so Corollary D is known in that case. Novelty over nonamenable
groups was not checked beyond the lane's bounded check.

### 1.3 Algebraic absorption, finite stabilizers, Leavitt duals

- **`stable-finiteness-failure-is-algebraic-bernoulli-absorption`: PASS.**
  - (1)⇒(2): `rho_B` is injective with image `R^n e`, and `P = R^n(I - e) != 0`.
  - (2)⇒(1): `pi = rho_A` is a split surjection with nonzero kernel. `AB = I` would make it injective.
  - (a), (b) and (c) follow as written. Dual isomorphisms preserve Haar measure.
  - The `F_q` reduction is a unital ring embedding.
- **`bernoulli-factor-algebraic-actions-have-finite-stabilizers`: PASS.**
  - The character `f_a` is `Stab(a)`-invariant, because `(g^-1.x)(a) = x(ga)`.
  - Bernoulli shifts are mixing along any infinite subgroup.
  - A nonzero element of `F_p[G]^n` has stabilizer inside `S s^-1` for its finite support `S`.
- **`leavitt-module-dual-actions-are-self-squares-off-bernoulli`: PASS.**
  - The maps `phi`, `psi` are mutually inverse, using `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`.
  - Every nonzero right ideal has dimension `>= 2^n` for all `n`, so `Fix(u) = Ann((u^-1 - 1)L)` has
    infinite index, and Haar measure `0`.
  - The `2^n - 1` translates `a + s_u y` are distinct, so the orbits on characters are infinite and the
    action is ergodic.
  - `iota_1(b) = s_0 t_0 + s_1 b t_1` is an injective homomorphism fixing `s_0 m`.
  - The consumer node (the finite-stabilizer test) is stated for `Hom(M, T)`, and `Hom(M, F_2)` is the same
    group.

### 1.4 Lifted trace and conservation of entropy

- **`lifted-trace-finite-subgroup-proof`: PASS.** It lies outside the EX lanes but is consumed by the
  invalidator, so it was checked.
  - `C = c_0(G, Z_p)` is complete, with `C/pC = F_p[G]`.
  - The iteration `a ↦ 3a² - 2a³` lifts idempotents.
  - `W = E'E + (1 - E')(1 - E) ≡ 1 mod p` conjugates lifts.
  - Lifted equivalences give `T(E) = T(F)`.
  - For finite `H`, the linear trace of `E` on `Z_p[H]^n` is `d = rank`, and also `|H| T(E)`.
- **`finite-subgroup-induced-absorption-conserves-entropy`: PASS.**
  - Additivity gives equality in `Z_p`, hence in `Q`.
  - Nonnegativity forces `Q_i = 0`.
  - Projectivity of `Q_i` is automatic: `Q_i` is the `F_i · 1 · F_i` summand of `Res_(F_i) Ind(Q_i)`, and
    restriction of a projective `F_p[G]`-module to `F_p[F_i]` is projective.
  - Left versus right modules: the involution `g ↦ g^-1` exchanges them and fixes the identity coefficient.
- **Firing check.** The DEAD route `leavitt-induced-absorption-gives-bernoulli-collapse` has `requires: []`
  and targets `some-group-has-isomorphic-bernoulli-shifts-of-different-entropy`, the negation of the famous
  root. Its invalidator is established by `finite-subgroup-induced-absorption-conserves-entropy-proof`,
  which requires only `lifted-trace-detects-finite-subgroup-projectives`, itself established by the
  `requires: []` route above. So the dead route does not fire.
- **Theorem E (`induced-projective-absorption-breaks-bernoulli-classification`): PASS as an implication.**
  The iteration of Corollary D over `i` is valid, since the Bernoulli part keeps positive finite entropy.

### 1.5 Self-square equivalence

**`bernoulli-collapse-iff-a-bernoulli-shift-is-its-own-square`: PASS.**
- (2)⇒(1): `X_h × X_h ≅ X_(2h)`.
- (1)⇒(2): item 6 of the collapse-subgroup node gives the threshold `θ = max_i (w_i + |d_i|)`, and `h = nd >= θ`
  works for every large `n`.
- A failure of the form `X_h ≅ X_∞` is covered: item 5 gives `D(G) = R`. Directly,
  `X_h × X_h ≅ X_∞ × X_h ≅ X_∞ ≅ X_h`.

Items 1–7 of `bernoulli-isomorphism-collapse-set-is-a-subgroup` were re-derived, in particular:
- item 3: the witness `p = max(h, k - d)` satisfies `p + d >= k` and `p + d + e >= 0`;
- item 6: all increasing steps are taken before the decreasing ones, so every intermediate point is at
  least `min(h, h') >= θ`.

### 1.6 Universal hosts

**`bernoulli-collapse-ascends-to-universal-hosts`: PASS.**
- Permanence under co-induction is part (d) of the constraints node.
- Item 1 uses the Hall–Schupp embedding. The node `countable-group-embeds-in-two-generator-simple-group`
  records that its source was not re-read, and that caveat carries over.
- Item 2: `whitehead-universal-finitely-presented-container` covers countably generated recursively
  presented groups.
- **Note on item 3.** The route derives a recursive presentation from decidability on a generating set.
  Finite generation is not needed. The set of units of `L` is recursively enumerable (search for an
  inverse), and products are decidable by the normal form, so enumerating the units gives a recursive
  presentation.
- The reading "a collapse over `U_*` forces `h^Rok_sup(U_*) = 0`" is correct given item 8 and the dichotomy
  corollary, whose hypotheses `U_*` meets. `U_* × U_*` is finitely presented, hence embeds in `U_*`, and
  `U_*` contains every finite group. The dichotomy node itself is not re-derived here.

## Part files

None yet.
