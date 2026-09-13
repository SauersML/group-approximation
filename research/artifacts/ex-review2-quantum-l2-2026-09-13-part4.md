# EX review, second wave, quantum and L²: part 4. Quantum PCP and unique-games imports read at source; port-generated square completions at artifact level

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Method.** arXiv PDFs were extracted with ghostscript on MSI (`/scratch.global/sauer354/ex/ex-verify2-quantum-l2/pdf/`).
Line numbers refer to the `.txt` files.

## 4.0 Verdicts

| claim | lane | source | verdict |
|---|---|---|---|
| `commuting-hamiltonians-on-small-set-expanders-in-np` | quantum-pcp | Aharonov–Eldar arXiv:1301.3407v1, Thms 1–2 (l. 200–216) | PASS at source |
| `natarajan-vidick-games-pcp-amplification-error` | quantum-pcp | Natarajan–Nirkhe arXiv:2403.13084v1: (2e) (l. 441), (5), Lemma 6 with (6)–(7) (l. 473–486), the error paragraph (l. 469–473) | PASS at source |
| `nlts-hamiltonians-from-good-qldpc-codes` | quantum-pcp | Anshu–Breuckmann–Nirkhe arXiv:2206.13228v4, Thm 1 (l. 46–51) | PASS at source |
| `product-states-approximate-high-degree-2-local` | quantum-pcp | Brandão–Harrow arXiv:1310.0017v2, Cors. 4–5 (l. 245–262) | PASS at source |
| `two-local-degree-amplification-gives-np-witnesses` | quantum-pcp | same paper, Cor. 11 (l. 403–422) | PASS at source; the node's NP form comes from the proof, as the node says |
| `small-set-expansion-hypothesis-implies-ugc` | ugc | Raghavendra–Steurer–Tulsiani arXiv:1011.2586v1, Hypothesis 3.1 (l. 294) and Cor. 3.3 (l. 316) | PASS (the implication holds through Cor. 3.3; RS10 Thm 1.4 not re-read) |
| `affine-ug-easy-on-globally-hypercontractive-graphs` | ugc | Bafna–Minzer arXiv:2304.07284v1, Thm 1.5 | PASS at source for Thm 1.5; Thms 1.6–1.8 not re-read |
| `affine-ug-easy-on-certifiably-hypercontractive-graphs` | ugc | Bafna–Barak–Kothari–Schramm–Steurer arXiv:2006.09969v3, Thm 1.1 (l. 155–162), Cor. 1.3 | PASS at source |
| `port-generated-square-completions-force-coset-support` (+ `-proof`) | kac-quantum-compiler | artifact `ex-kac-quantum-compiler-latin-completions-2026-09-13.md` §1–3 | PASS, artifact level |
| `galois-games-round-linearly-for-bounded-fibre-size` (+ `-proof`) | ugc-rounding-pgroups | route body, which is the derivation, with (16.2) of part 2 | PASS |
| `abelian-normal-closure-fibres-round-linearly` (+ `-proof`) | ugc-rounding-pgroups | route body, with (16.2) and (11.2) | PASS |

## 4.1 Quantum PCP imports

- **Aharonov–Eldar.**
  - Thm 1 as printed: "Let γ(ε) = 2kdε. Let H be an instance of CLH(k,d) for constant k,d whose bi-partite
    interaction graph has a right degree D_R, and is ε-small-set expanding, for ε < 1/2." For every
    eigenvalue there is a constant-depth state with `| ||H ψ_i|| - λ_i | <= γ(ε)||H||`, and "the
    γ(ε)-approximation problem ... is in NP".
  - Thm 2: for `ε < 1/2` the approximation is NP-hard.
  - The node's (AE1)–(AE2) match. Its bearing on the root is the contrapositive of Thm 1.
- **Natarajan–Nirkhe.**
  - Lemma 6 is verbatim: `−1 ≼ H ≼ 1`; the promise `λ_max ≥ 1 − 1/p` or `≤ 1 − 1/q`; an `ℓk`-local `H''`
    with (6) `λ_max ≥ 1 − k/p` or `≤ 2e^(−k/(2q)) − 1`; and (7) `‖H''‖_(P,1) ≤ 1 + 2((1+‖H‖_(P,1))/2)^k`.
  - (5) gives `‖H^(⊗n)‖_(P,1) = sqrt2^n` for `H = (X+Z)/sqrt2`.
  - The printed error statement: Natarajan–Vidick "incorrectly calculated the amplification of the Pauli
    1-norm".
  - The node's (NN1)–(NN4) match. Equation (9) was not re-located.
- **Anshu–Breuckmann–Nirkhe.**
  - Thm 1: a fixed `ε > 0` and explicit `O(1)`-local frustration-free commuting `H^(n)` with `m = Θ(n)`
    terms, such that states with energy below `εn` have circuit complexity `Ω(log n)`.
  - The extraction garbles the energy inequality symbol. The node's strict `< εn` is implied by either
    reading.
  - The good-qLDPC existence imports (Panteleev–Kalachev, Leverrier–Zémor) were not re-read here.
- **Brandão–Harrow.**
  - Cor. 4 (7): `tr(Hϕ) ≤ e_0(H) + 12 (d² ln(d)/D)^(1/3)` for a product state, with
    `H = E_((i,j)∈E) H_ij = (2/(nD)) Σ H_ij` and `‖H_ij‖ ≤ 1`.
  - Cor. 5: if `β − α ≥ 12(d² ln(d)/D)^(1/3) + δ`, there are witnesses of length `O(nd log(n/δ))`, and the
    verifier takes time `nDd^4 polylog(1/δ)`.
  - Cor. 11 (i)–(vii) match the node's items 1–5, with (iii) `deg(P_t(H)) ≥ deg(H)^t`. The node's
    "regular of degree at least" is a stronger hypothesis, which it records and justifies from the proof.
  - The printed conclusion is "Then the quantum PCP conjecture is false"; the node's NP-membership form is
    what the proof of §6 gives.

## 4.2 Unique-games imports

- **SSEH ⇒ UGC.**
  - Hypothesis 3.1 of RST is UG hardness, alphabet `q = q(ε,η,M)`: Yes `opt > 1 − ε`; No `opt < η`, with
    small-set expansion of the constraint graph.
  - It is a restriction of UG hardness to a subclass of instances, so it implies Conjecture 1.2 (UGC).
  - Cor. 3.3 (verbatim) makes SSEH equivalent to it. So the implication holds from the re-read source.
  - The node's primary quote (RS10, STOC, Thm 1.4) was not re-read; the authors' PDF was not fetched.
- **Bafna–Minzer, Thm 1.5.** Verbatim: there is `ε_0`; for `α ∈ (0,1)` and `0 < ε ≤ ε_0`, on
  `(1 − ε)`-satisfiable affine UG over `J(n, ℓ, αℓ)`, in time `n^poly(ℓ,|Σ|,1/ε)`, it satisfies a
  `2^(−O(√ε/α))` fraction.
- **BBKSS.**
  - Thm 1.1 is verbatim: `val(I) = 1 − ε` with `ε ≤ λ²/100` gives value at least `ελ⁴/(64C)`.
  - The printed bound shrinks as `ε → 0`. The node transcribes it faithfully; the constant guarantees
    `τ(α, ε)` are Cors. 1.3–1.5.
  - Cor. 1.3 is verbatim (`0.001 > ε > 0`, `1/4 > α > 0`).

## 4.3 `port-generated-square-completions-force-coset-support`: PASS

- **The definition matches.** Closure-safe (artifact §1) means every connected component of the support
  graph between question pairs and answer pairs is accepted throughout.
- **Latin form.** Every completion with entries in the port span is Latin: for fixed `a`, `x -> y` is a
  bijection.
- **(L1).**
  - The pair `(x, x')` of block `q` has neighbourhood `graph(L_x' L_x^-1)`, because the PVM is orthogonal
    and the support is full.
  - Latin columns give `z` with `L_z(y_0) = L_x' L_x^-1(y_0)`, so `graph(L_z)` shares a component with
    `graph(L_x' L_x^-1)`.
  - Acceptance of that whole graph at `(p_q, z)` forces `L_x' L_x^-1 = L_z`.
  - So the rows are closed under `(x, x') -> L_x' L_x^-1` and contain `id`. They form a group, regular by
    the Latin property.
  - Conversely, the graphs of distinct elements of a regular group are disjoint components, each decoding
    to equal answers.
- **(L2).**
  - Answer pair `h` is adjacent to question pair `g` iff `h ∈ gΣ`, with `e ∈ Σ`.
  - The question side of `e`'s component is `<Σ>`: `g' ∈ hΣ^-1`, positive words suffice, and a finite
    monoid generated by `Σ ∋ e` is a group. The answer side is `<Σ>Σ = <Σ>`.
  - At `g ∈ M = <Σ>`, decoding gives `(g^-1 h) s_0 ∈ M s_0`. Components of `g ∉ M` are translates with the
    same decoded sets. Both directions hold.
- **Oracularized consequence.** Take `S = graph(π_i)` and `W = graph(π_i)`.
  - `M s_0 = graph(π_i)`, and `M` acts freely, being inside a regular action, so `|M| = |O_c|`.
  - `(e,k) ∈ M` fixes a point, so `k = e`. Projection to `K_c` is a bijection, and
    `M = {(k, φ_i(k))}` for a homomorphism `φ_i`.
  - Context supports are then orbits of `{(φ_i(k))_i}`. Correct.
- **Sharpness.**
  - The incidence relation of `S_3` on points and 2-subsets contains `(0,{0,1})`, `(1,{0,1})` and
    `(0,{0,2})` but not `(1,{0,2})`.
  - Cosets are rectangular (`c_1 c_2^-1 c_3` stays in a left coset), and rectangularity does not depend
    on the chosen bijections. So the incidence relation is not a coset.
- **Boolean consequence.** For `|O_q| = 2`, `K_q = Z/2`, and cosets in `(Z/2)^2` are affine. The block
  rests on `jnvwy-active-output-has-no-affine-safe-perfect-model`, which is not re-derived here.

## 4.4 Galois games with bounded or abelian-closure fibres: PASS

Logic-quantum part 4 reviewed both claims at node level only (its §8.2). Their route bodies are the full
derivations.

- **`galois-games-round-linearly-for-bounded-fibre-size`.**
  - Step (i) of Theorem 12 uses only `phi = 0` on `K \ {e}`. So `K` meets the normal intersection of the
    good `ker rho` trivially, for every `K`.
  - For good `rho = Ind_H sigma` with `sigma` primitive, (16.2) gives mass `>= 1 - 3 eps/c` for every
    conjugate of `ker sigma`.
  - The `K`-core `L_i' = intersection over b in K of b L_i b^-1`:
    - it is normalized by `K`, which permutes the conjugates;
    - it omits `a`, since `b = e` is one of the terms;
    - it costs at most `k` conjugates, so `mu(G \ L_i') <= 3 eps k/c`.
  - Each chain step gives a proper subgroup, so there are at most `log_q k` steps.
  - `L` is normalized by `K`, so `KL` is a subgroup, and permutable rounding (part 5 of
    `galois-games-round-through-free-subgroups`) gives `val >= mu(L)`.
  - The minimum with Corollary 17 gives the stated `min(k, [G : N_G(K)])`.
- **`abelian-normal-closure-fibres-round-linearly`.**
  - **Step 1.**
    - Clifford gives `rho = Ind_I^G psi` with `psi|_A = e theta`, and a minimal `H <= I` gives a primitive
      `sigma`.
    - Mackey decomposes `psi|_A` into `Ind_(A cap xHx^-1)^A`. With `A` abelian, a proper
      `A' = A cap xHx^-1` would contribute all `[A : A'] >= 2` extensions of a character, which are
      distinct. That contradicts homogeneity. So `A <= H`.
  - **Step 2.** For any `x in G`, `x A x^-1 = A <= x H x^-1`, and `x (ker sigma) x^-1` is normal there. So
    `K <= A` normalizes it.
  - **Steps 3–4.** (16.2), or (11.2) for M-groups, and the chain give `L` normalized by `K`, with
    `L cap K = {e}` and `mu(G \ L) <= 3 eps log_q k/c`.
  - **Test case.** In `F_2 wr F_2^n`, the normal closure of `<(0,t)>` is `Im(1+t) x <t>`:
    - it is abelian, since `t (1+t) b = (1+t) b`;
    - it is normal, since `(b,0)` conjugates `(0,t)` to `((1+t)b, t)` and `P` preserves `Im(1+t)`.
    The claim's example is correct.
