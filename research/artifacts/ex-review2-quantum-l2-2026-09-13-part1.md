# EX review, second wave, quantum and L²: part 1. Galois-game rounding read line by line, and the Kun–Thom rational-character obstruction

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

## 1.0 Verdicts

| item | lane | verdict |
|---|---|---|
| `primitive-projective-representations-have-a-trace-gap` (artifact part 2, Theorem 15) | ugc-rounding-pgroups | PASS, artifact level |
| `normal-fibre-galois-games-round-linearly-over-m-groups` (artifact part 1, Lemma 11, Lemma 12a, Theorem 12) | ugc-rounding-pgroups | PASS, artifact level |
| `normal-fibre-galois-games-round-linearly-over-all-groups` (part 2, Theorem 16, Remark 18) | ugc-rounding-pgroups | PASS, artifact level. Uniformity in `m` uses CFSG, as stated |
| `free-subgroup-rounding-fails-for-non-normal-fibres` (part 1, Proposition 13) | ugc-rounding-pgroups | PASS, independently of logic-quantum part 2 |
| `free-rounding-pays-the-number-of-fibre-conjugates` (part 1, Theorem 14; part 2, Corollary 17) | ugc-rounding-pgroups | PASS |
| `kun-thom-wreath-is-not-rational-character-approximable` (+ `-proof`) | determinant-monster | PASS at the checked steps, conditional on the established pre-EX `hilbert-embeddable-witness-impossible`. One justification (step 3) was wrong about the length convention and is corrected forward (1.6) |

**Artifacts.**
- Part 1: `research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md`.
- Part 2: `research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md`.

**Inputs not re-read here.** Theorems 3, 7, 8 and 10 of `ugc-galois-games-part2-2026-09-12.md`. They are
PASSED at node level in logic-quantum part 2 (`galois-games-round-through-free-subgroups`). The part-4
claims `galois-games-round-linearly-for-bounded-fibre-size` and `abelian-normal-closure-fibres-round-linearly`
are not in these two artifacts and are not re-read here.

## 1.1 Theorem 15, the trace gap: PASS

- **Reduction.**
  - `Z` is the scalar kernel, and `N/Z` is minimal normal in `X/Z`.
  - Isotypic components under `N` are permuted, so primitivity leaves one, and `V = V_tau (x) W`.
  - Burnside gives `span sigma(N) = End(V_tau) (x) 1`.
  - By Skolem–Noether, conjugation by `sigma(x)` is `Ad taut(x)`. Then `(taut(x)^-1 (x) 1) sigma(x)` lies
    in the commutant `1 (x) End(W)`.
  - `pit` is scalar on `N`, and it is irreducible, since `V_tau (x) W'` would be invariant. It is
    primitive, since blocks `W_i` give blocks `V_tau (x) W_i`.
  - `tr sigma(h) = tr taut(h) tr pit(h)`.
  - In the scalar case, induction on `|X/N| < |X|` applies, and sections of `X/N` are sections of `X`.
- **Case A, `N/Z` elementary abelian.**
  - The commutator form has an `X`-invariant radical. By minimality the radical is `0` or everything, and
    everything forces `dim V_tau = 1`, `N <= Z`. So the form is nondegenerate.
  - `tr U_v = 0` for `v != 0`, and the `p^(2a) = (dim V_tau)^2` lifts are an orthonormal basis.
  - With `A = taut(h) = sum c_v U_v`, comparing the `U_u`-coefficient of `A U_w = lambda_w U_(gw) A`
    (unimodular structure constants) gives `|c_(u-w)| = |c_(u-gw)|`. So `|c|` is constant on cosets of
    `Im(g-1)`.
  - If `g != 1`, then `p|c_0|^2 <= 1`.
  - If `g = 1`, then `lambda` is a character, equal to `omega(v_0, .)`. So `U_(v_0)^-1 A` is central, `A` is
    a scalar times `U_(v_0)` with `v_0 != 0`, and `tr A = 0`.
- **Case B, `N/Z = T^s`.**
  - Künneth with `H_1(T) = 0` gives `H_2(T^s) = H_2(T)^s`, so `tau = tensor of tau_i`, each of dimension
    at least `2`, since a scalar factor would lie in `Z`.
  - `Ad A` permutes the factors `End(V_i)` by `pi`. So `P_pi^-1 A` preserves every factor, hence lies in
    `C^x (A_1 (x) ... (x) A_s)`, with each `A_i` unitary up to a scalar.
  - If `pi != 1`, the trace factors over the cycles, and the ratio is at most `d_0^(-1) <= 1/2`.
  - If `pi = 1`, some non-scalar `A_j` normalizes `tau_j(T)`, and the ratio is at most `gamma(T)`.
- **`gamma(T) < 1` is a finite maximum.**
  - Two unitaries inducing the same automorphism differ by a character of the perfect `T`, so by a
    scalar.
  - `tau` ranges over a finite Schur cover, and `Aut(T)` is finite.
- **Sharpness.**
  - The faithful 2-dimensional irreducible of `GL(2,3)` restricts irreducibly to `SL(2,3)`, so it is
    primitive. An element of order 8 has eigenvalues `zeta_8, zeta_8^3` and trace `i sqrt 2`: Case A with
    `N/Z = V_4` and `rank(g-1) = 1`.
  - The standard representation of `S_n`, `n >= 5`: blocks give a subgroup of index at most `n-1`, hence
    `A_n`, on which the representation stays irreducible. So it is primitive.

## 1.2 Lemma 11 and Theorem 12: PASS

- **(11.1).** `chi_(Ind sigma)(g)/d_rho = |G|^-1 sum_x chidot_sigma(x^-1 g x)/d_sigma`, and conjugation
  invariance of `mu` collapses the `x`-sum.
- **(11.2).** The summand `1 - Re thetadot` is `1` off `H`, `0` on `ker theta`, and at least
  `1 - cos(2 pi/m)` elsewhere.
- **Lemma 12a.** This is the textbook `p`-group M-group argument: a maximal abelian normal `A` is
  self-centralizing, and the Clifford correspondence induces from a proper inertia group. The
  direct-product step is also standard.
- **Step (i).**
  - `mu` is central, so `sum mu phi = sum_rho w_rho lambda_rho` over the isotypic weights of the GNS
    vector.
  - Markov gives `sum over rho notin calG of w_rho < 1/3`.
  - On the intersection of the `ker rho`, `rho in calG`, the fixed components contribute
    `sum over calG of w_rho > 2/3`, and the rest contribute at least `-1/3`. So `Re phi > 1/3`.
  - `phi` vanishes on `K \ {e}`, so `K` meets that intersection trivially.
- **Steps (ii)–(v).**
  - `ker Ind theta` is the intersection of the conjugates of `ker theta`.
  - Each chain step removes an element, and a proper subgroup of `N_(i-1)` has index at least `q`, so
    `t <= log_q k`.
  - Conjugation invariance and the union bound give (12.1).
  - Since `K` is normal, `L cap xKx^-1 = {e}`, which is freeness.
- **Model test.** In the artifact's `Q_8` check, `lambda = 1 - delta` with `delta = 2 eps`, the cost is
  `2 eps <= 3 eps`, and `L = {e}` is forced, because every nontrivial subgroup contains `-1`.

## 1.3 Theorem 16, Corollary 17 and Remark 18: PASS

- **Primitive inducing data.** A subgroup `H` minimal among those inducing `rho` carries a primitive
  irreducible `sigma`: a block system of `sigma` would induce `rho` from a smaller subgroup.
- **(16.2).**
  - The summand is at least `1 - cos(2 pi/m)` when `sigma(h) = zeta I`, `zeta^m = 1`, `zeta != 1`.
  - Otherwise Theorem 15 for `H`, a linear representation read projectively, gives
    `Re chi_sigma(h)/d_sigma <= gamma(H) <= gamma(G)`, since sections of `H` are sections of `G`.
- **The steps of Theorem 12.** They use only `ker rho` equal to the intersection of the conjugates of
  `ker sigma`, and (16.2) in place of (11.2). Step (i) does not use monomiality.
- **Remark 18.** It is correct given CFSG: `A_n` has an element of order at least `n-1`, groups of Lie type
  have element orders growing with `q` and the rank, and there are 26 sporadics. So finitely many simple
  groups have exponent dividing `m`, and `gamma_m < 1`. Without CFSG the constant is uniform over solvable
  groups, as the artifact says.

## 1.4 Proposition 13, the counterexample over `F_2 wr F_2^n`: PASS

- **Exponent.** `(b,t)^2 = (b + t.b, 0) in B`, so `exp G = 4`.
- **`mu_delta`.** It is conjugation invariant: `B` is abelian and `P` permutes the coordinates.
- **(a).** `L = {b_0 = 0}` meets `K = <e_0>` trivially, `KL = B`, and `mu(L) = 1 - delta`.
- **(b).** The conjugates of `K` are the `<e_j>`. A free `H` contains no `e_j`, so
  `mu(G \ H) >= N delta (1-delta)^(N-1)`.
- **(c).** With `delta = N^-2 = eps`, Bernoulli gives `N(1 - N^-2)^(N-1) >= N - (N-1)/N > N - 1`. So
  `mu(G \ H) > (N-1) eps log_2 k`, and no `C(4)` exists.

The value bound in (a) rests on Theorem 10, which was not re-read (1.0).

## 1.5 Theorem 14: PASS

- Each `ker rho` is normal, so step (i) gives `K_j cap (intersection of ker rho) = {e}` for every conjugate
  `K_j`.
- The chain runs through `K_1, ..., K_r`. It removes an element of some `K_j cap L` each time, so each step
  divides one order by at least `q`, and there are at most `r log_q k` steps. The cost bound follows.
- Proposition 13 has `r = N` and `k = 2`, so (14.1) is tight up to the constant.

## 1.6 `kun-thom-wreath-not-rational-character-approximable-proof`: PASS at the checked steps; step 3 justification corrected

- **Step 1.**
  - `rho(F) <= GL_d(Q)` preserves a positive definite `q`. A `q`-orthonormal real basis puts `rho(F)` in
    `O(d) <= U(d)`, with the same normalized Hilbert–Schmidt norm.
  - Multiplicativity is unitarily invariant: `||k k' k''^-1 - 1||_2 = ||k k' - k''||_2`.
- **Step 2.** `||rho phi(s) - 1||_2^2 = 2 - 2 Re Tr/d >= 2 - 2 eps`.
- **Step 3, the wrong justification.** The route says the length `ell(k) = ||k - 1||_2` "is Hilbert
  embeddable, being the square root of the conditionally negative definite `1 - Re (1/d) Tr`". In the
  repository's convention (`hilbert-embeddable-length-hyperlinearity`), a length is Hilbert embeddable
  when `(a,b) -> ell(a^-1 b)` is itself conditionally negative definite. The square of `ell` has that
  property; `ell` itself need not.
- **What makes the step true.** The witness notion refuted by `hilbert-embeddable-witness-impossible`,
  as stated in `hilbert-embeddable-witness-for-kun-thom-wreath`, allows one increasing `f` with
  `f(0) = 0`, continuous at `0` and independent of `n`, such that `f o d_n` is Hilbert embeddable and
  bounded by `1`.
  - Take `d_n(k) = ||k - 1||_2` and `f(t) = t^2/4`. Then `f(d_n(a^-1 b)) = ||a - b||_2^2/4`, a squared
    Hilbert distance, so it is conditionally negative definite and at most `1`.
  - The defect is at most `eps^2/4`, and the separation is at least `(1 - eps)/2`.
  - So the models are witnesses in the refuted sense, and step 4 applies. The conclusion stands.
- **Step 4.** It is conditional on `hilbert-embeddable-witness-impossible`, which is pre-EX and
  established through `witness-yields-two-point-approximation` and `two-point-approximation-fails`. Its
  trust surface is Kun–Thom arXiv:2608.06222 Theorem 4.1. That chain is not re-derived here.
- **Graph role.** The claim invalidates `determinant-conjecture-via-rational-character-models`, a
  `requires: []` route into a famous root. The invalidator is established, so the dead route does not fire.
