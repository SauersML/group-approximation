# EX review, second wave, quantum and L²: part 5. Wave-2 lanes: forbidden-pair splits, fibre-commutative isomorphisms, two transcendental coefficients; a retraction

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`. Tip `561fc1df60`.

## 5.0 Census and verdicts

**Census.** The two wave-2 lanes added by the coordinator, from `state/landed.log` and
`state/pushed-<lane>.tsv`.
- **Established set.** Recomputed at the tip; the lower and upper bounds agree at 8,473 claims. Every
  famous root of the brief is still OPEN.
- **ex2-kac-forbidden-pair.**
  - Established and unpassed: the two claims below.
  - Edited: `hidden-labels-import-cross-context-commutation`, which logic-quantum part 7 had passed. The
    edit (`00051a8d3d`) only adds an "equivalent form" bullet pointing to the first claim below.
  - Open, edits not reviewed: `tracial-non-ru-coset-system-with-nonabelian-fibre-exists` and
    `non-group-dual-colored-qc-qa-pair-exists`.
- **ex2-atiyah-base-change-td2.**
  - Established and unpassed: the three claims below.
  - Edited: the open `determinant-conjecture-gives-full-atiyah-base-change`.

| claim | lane | verdict |
|---|---|---|
| `forbidden-pair-splits-are-central-rectangle-splittings` (+ `-proof`) | ex2-kac-forbidden-pair | PASS at the checked steps; citations checked at source |
| `fibre-commutative-quantum-isomorphisms-are-coset-systems` (+ `-proof`) | ex2-kac-forbidden-pair | PASS |
| `atiyah-algebraic-jumps-lie-in-a-proper-zariski-closed-set` (+ `-zariski-closed-proof`) | ex2-atiyah-base-change-td2 | PASS |
| `determinant-conjecture-bounds-determinants-over-galois-orbits` (+ `-galois-orbit-bound-proof`) | ex2-atiyah-base-change-td2 | PASS after a local GAP in Lemma H (the case `D = 1`), corrected forward in artifact part 2 |
| `atiyah-base-change-in-transcendence-degree-two-under-det` (+ `-proof`) | ex2-atiyah-base-change-td2 | PASS, conditional on Strong Atiyah over `Qbar` and the determinant conjecture, as stated |

## 5.1 A retraction in part 1

Part 1 §1.6 first said that `ell(k) = ||k - 1||_2` "need not be" conditionally negative definite. That
was false.
- `t^(1/2)` is a Bernstein function, and by Schoenberg `1 - e^(-s psi)` is conditionally negative
  definite, so square roots of conditionally negative definite kernels are conditionally negative
  definite.
- The route's original justification was right, as ex-determinant-monster pointed out.
- The owner's merge `979f1c1def` keeps both arguments. Part 1 and the index were corrected at
  `8368af8353`.

## 5.2 `forbidden-pair-splits-are-central-rectangle-splittings`: PASS

- **(P0).**
  - `[R p H]` is invariant under `R` and `R'`, so its projection is the central support.
  - For `m in N'`, `x m = 0` with `x in N` gives `x C_(N')(m) = 0`.
  - For central `z`, `C(pz) = C(p) z`, and `pz = 0` forces `C(p) z = 0`.
- **(P1) (CS) ⇔ (W).** `f C(e) = 0` iff `f N e = 0`, and `f C(e) = 0` iff `C(f) C(e) = 0`. Alternating
  words are weakly dense.
- **(P2) (CS) ⇒ (FS).** Take `m = 1 - C(e)`, which is central. Then `e m = 0` and
  `f(1 - m) = f C(e) = 0`.
- **(P3) (FS) ⇒ (CS).** Put `z = C_(N')(m)` and `z' = C_(N')(1-m)`.
  - `[e, P_(q')^b] z = 0`, so `ez in Z(N)`; likewise `f z' in Z(N)`. Also `1 - z <= z'`.
  - On `gz`: `ez = C(e) z` gives `e g z = g z`, then `f g z = 0`, so `C(f) g z = 0` and `gz = 0`.
  - On `g(1-z)`: `f(1-z) = f z'(1-z)` is central, which gives `g(1-z) = 0`.
- **(P4).** (RCS) ⇒ (CS) on each piece. (CS) ⇒ (RCS) through the partition by products of `C(P^c)` and
  complements, whose rectangles contain no forbidden pair.
- **Corollaries.**
  - (2) If the PVMs commute, `N` is abelian, `C(e) = e`, and (CS) is perfection.
  - (3) For `G_cv(B)`, perfection gives `P_c^a <= P_v^(a_v)`. Summing, `P_v^b = sum over a_v = b of
    P_c^a`, so every pair algebra carrying a forbidden pair is abelian. `A(G_cv(B)) ≅ A(B)` is the usual
    identification of `P_c^a` with products of spectral projections of the `x_v`.
  - The gap source `perfect-qc-separation-yields-finite-bcs-with-no-matrix-model` is established; it is
    not re-derived here.
- **Sources** (MSI text of arXiv:2505.05253 and arXiv:2510.07162v1).
  - MSSV Definition 2.7 (l. 608, restated l. 284–288): vertices `(q,a)` are adjacent "if and only if
    V(q,q';a,a') = 0 or V(q',q;a',a) = 0". That is the node's forbidden pair, and it explains the remark
    that the game graph joins `V = 0` pairs whatever `mu` is.
  - MSSV Theorem 3.1 (l. 724), from [MRV15], is as the node uses it.
  - Lin Definition 3.15 (l. 2101): a strategy "is oracularizable if whenever µ(x,y) > 0, ..."
    (commutation), as quoted.

## 5.3 `fibre-commutative-quantum-isomorphisms-are-coset-systems`: PASS

- **(Q1).** `v_(xa) = v_(xa)^2 = 0` across diagonal colours, so fibre blocks are magic unitaries for the
  fibre iso algebras.
- **(Q2).** Commuting blocks split over bijections.
  - Expanding `prod_x sum_a v_(xa)`, non-injective terms contain `v_(xa) v_(x'a) = 0`, after reordering,
    which commutativity allows.
  - Colour-breaking bijections vanish.
  - Orthogonality and reconstruction are correct.
- **(Q3).** `p^φ v_(x,φx) = p^φ`, so a colour mismatch kills `p_q^φ p_(q')^ψ`. Conversely the iso
  relations follow from the surviving terms.
- **(Q4).** Applying the identity of `(k_0,l_0)` at `(k'x, l'x')` shows `R = (k_0,l_0) D`, with `D` the
  stabilizer of the cross colouring.
- **(Q5).** The maps are mutually inverse. `prod_x sum over k'x = kx of p^(k')` collapses to `p^k`,
  because `K_q` acts faithfully.
- **(F3)–(F5).** Correct: rigid fibres make the commutator ideal zero; a GNS representation with
  commuting blocks factors; ports are orbit pushforwards.

## 5.4 Theorem 5, two transcendental coefficients: PASS, after a local GAP in Lemma H

Artifacts: `research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md` to `-part3.md`.

- **Lemma J.**
  - `D(x_1)[x_2]` is a left and right PID with central `x_2`, so the diagonal form holds.
  - `D(x_1)` embeds in `D((x_1 - beta_1))`, and constant terms give a ring map on the elements whose
    denominator does not vanish at `beta_1`. One common right denominator `b` has finitely many central
    roots.
  - `e_i(beta) = 0` iff all `f_ij(beta) = 0`, through a `Qbar`-basis of the span of the `a_ikl`, and some
    `f_ij` is nonzero.
  - Off `Y_A`, `rk_D A(beta) = r`, and Linnell's criterion gives `k_A = n - r`. The Galois conjugates of
    `Y_A` form a proper closed set over `Q` that misses algebraically independent points.
- **Lemma L.** The `k_A` are upper semicontinuous: norm convergence gives weak convergence of spectral
  measures, and `limsup mu_t({0}) <= mu_0([0,ε])` for every `ε`. Algebraic points off `Y_A` are dense.
- **Reduction.**
  - Higman's trick (`a + bc` against `[[a, b], [-c, I]]`) keeps the excess.
  - `[[L, Y], [W, 0]]` is full, and `ker L(z) cap ker W` has dimension at least `kappa`.
  - Restriction of scalars is similar to the sum of the conjugate pencils over `Qbar`, so by Lemma L the
    excess does not drop.
- **Lemma G.**
  - `E_(k+1) A_i = diag(σ_j ζ_i) E_k` and `E_(k+1) A_0 = E_k` give
    `(I (x) E_(k+1)) X_k = (+)_j M(σ_j ζ) (I (x) E_k)`.
  - (D1)–(D3) and `|det A_0| = [Λ_(k+1) : Λ_k]` give (RES2). Monomials of degree at most `D-1` span `K`.
- **Lemma H, the GAP.**
  - The "almost all primes" step used `Λ_(D-1) (x) Z_p = O_K (x) Z_p`. For `D >= 2` that forces the
    `ζ_i` to be `p`-integral. For `D = 1` it does not: `Λ_0 = Z`, and the primes of the denominators of
    a rational point were wrongly given no `p`-part.
  - The fix `k_0 = max(1, D-1)` is merged into part 2. Rational points do occur in the cycles of Part 3.
  - The rest is correct:
    - normalization by `varpi_w in {1, ζ_1^-1, ζ_2^-1}`;
    - the norm form of `F_(q^3)/F_p` has no nontrivial zero on `F_q^3`, since every conjugate of `θ`
      still has degree `3` over `F_q`, so `G(ξ_w)` is a unit;
    - `g Λ_k ⊂ Λ_(k+e_p)` gives non-increasing indices, eventually constant along each residue class,
      and the step index is `prod_w π_w^(e_p [K_w:Q_p])`;
    - the Gauss norm gives `h_fin = log |c_Z|`.
- **Proposition C.** It is the determinant conjecture for the injective `X_k`, summed over `E`
  consecutive `k`.
- **§4.**
  - `F(θ~ x v) = c prod_j v . (ζ~_j x θ~)`, and `||ζ~ x θ~|| >= ||ζ - z||`.
  - (M3) gives both displayed estimates.
  - (UB2) is the min-max bound with `||M(w) - M(z)|| <= 2 c_M ||w - z||`.
  - In S.1 the `log|c_Z|` terms cancel (`-kappa_0 - (N - kappa_0) + N = 0`).
  - In S.2, `delta_Y > 0` because `θ~` avoids the projective closure of `Y`, and `b >= 0` by (M2).
  - Corollary 6 is additive over the `Q`-factorization, with the content adding `N log cont >= 0`.
- **Part 3.**
  - **Box principle.** `w = m/2 - 1 >= n^2/4`.
  - **Mediant.** `δ(T) <= 1`, and factors of small height contribute at least `n log δ(T)`, since
    `sum e_i <= n`. So `w_H -> w`.
  - **Shear.** It keeps `p_1(z)`, `kappa_0`, integrality and fullness; `P_top(t,1)` is nonzero for some
    `t <= d`.
  - **`q`.** `w_2 = (n_2 - 1)/2 >= 2Bn`.
  - **The form `F`.**
    - `R` is a polynomial, `R(α,u) = ± c_1 prod_k u . (1, α, β_k(α))`, and Poisson's formula with formal
      degrees gives `F`.
    - `F` is integral, nonzero and a product of affine linear forms. It does not need `p_1` irreducible.
  - **Sizes.**
    - Hadamard gives `b(F)`.
    - The Sylvester identity `F = Aq + BR` at `x_1 = z_1` and `u = θ~ x v`, where
      `R(z_1, u) = u_2^d p_1(z)`, gives the two branches of `a(F)`.
  - **Arithmetic.**
    - Branch 1 is `(-B^2 n + 2B) L_1 <= -L_1`.
    - Branch 2 is at most `(9B^2 n + 2B - n^2/8) L_1 + c <= -L_1 + c`, since `n >= 100 B^2`.
    - The constants do not depend on `T`, so `T > e^(c_13)` contradicts (CYC).
- **Not re-read or not re-derived here.**
  - Lück's (D1)–(D3) and Linnell's criterion;
  - step (R2) of the one-variable artifact, used verbatim (it passed in groups part 10);
  - the complex box principle constants.
- **Scope, as the node states.** Finite extensions of `Qbar(z_1, z_2)` and transcendence degree at least
  3 are not covered. The lane records its novelty check as bounded and still owed.
