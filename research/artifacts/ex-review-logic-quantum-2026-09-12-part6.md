# EX review, logic and quantum: part 6. Coset systems and quantum bijections (ex-kac-quantum-*), the Mikhailova amplifier (complexity-sofic), and the liftable-masa crux (ex-hs-masa-lift-*)

Lane `ex-verify-logic-quantum`, 2026-09-13 02:20 CDT, tip `d559bc2fa`.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 6.0 Verdicts

| item | lane | verdict |
|---|---|---|
| `independent-set-injection-splits-as-question-bijection` (+ `-proof`) | kac-quantum-bijection | PASS |
| `coset-systems-are-torsor-isomorphism-games` (+ `-proof`) | kac-quantum-bijection | PASS on (T1).  (T2)--(T4) at node level |
| `coset-refinement-forces-rectangular-central-splitting` (+ `-proof`) | kac-quantum-bijection | PASS |
| `exact-label-coset-refinements-are-affine` (+ `-proof`) | kac-quantum-bijection | PASS on (S1)--(S3), i.e. (EL1).  (EL2)--(EL3) at node level |
| `relabelable-coset-systems-are-solution-group-corners` (+ `-proof`) | kac-quantum-compiler | PASS |
| `port-generated-square-completions-force-coset-support` (+ `-proof`) | kac-quantum-compiler | PASS at node level; artifact not read |
| `mikhailova-coset-action-is-two-sided-q-action`, `amenable-base-makes-mikhailova-edge-co-amenable`, `machine-center-amplifier-does-not-bypass-the-sofic-compiler` | complexity-sofic amplifier | PASS |
| `one-compressor-liftable-masa-iff-type-orbits-tight` (+ `-proof`) | hs-masa-lift-counter | PASS on the tight direction; the escaping-mass direction mirrors part 5 §5.4 |
| `liftable-abelian-subalgebras-are-amplification-invariant` (+ `-proof`) | hs-masa-lift-counter | PASS on Lemma 1 (every constant checked); Lemma 2 at node level |
| `theorem-e-liftable-masa-crux-contains-sl-d-z-dec` (+ `-proof`) | hs-masa-lift-counter | PASS |
| `theorem-e-vertex-types-equidistribute-on-finite-sl-d-orbits` (+ `-proof`) | hs-masa-lift-positive | PASS at node level; artifact part 3 not read |
| Open roots `non-group-dual-colored-qc-qa-pair-exists`, `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`, `perfect-completeness-isomorphism-compiler` | kac-quantum-* | OPEN.  The only route into the first requires the second, which has no route, so nothing fires |

## 6.1 Quantum bijections and coset systems: PASS

- **Independent-set split.**
  - (P1): distinct questions may not get equal or adjacent answers, and synchronicity makes
    `(q,a) ~ (q,a')`.
  - Columns of `W` are orthogonal.  `sum_q C_q = |Q|` with `tau(C_q) <= 1` forces `C_q = 1` under a
    faithful trace.
  - `P_q^a W_(iq) = P_i^(q,a) = W_(iq) P_q^a`.
  - (IS2) checks every forbidden pair.
- **(T1) dictionary.**
  - Vertex colours kill cross blocks.
  - `v_((q,x),(q,a)) v_((q,e),(q,b)) != 0` forces `b = a x^-1`, so `A = AB`, `B = BA`, hence `A = B`.
  - Edge colours are right cosets, and `D(x,x') = D c^-1 (a,a')` iff `(s,s') in cD`.
- **Rectangular central splitting.**
  - Cosets are rectangular: `u v^-1 w in cD`.
  - The block projections satisfy `z_i = z_i z'_i = z'_i`.
  - For `z in N'`, the central support `C(z) = [N' z L^2]` is invariant under `N` and `N'`, so it lies
    in `Z(N)`, and used sets are unchanged.
  - The atoms `f_T` partition unity, with `f_emptyset = 0`.
- **Exact labels.**
  - Goursat: blocks are `xN x theta(xN)`.
  - Label exactness allows at most two blocks, so `[K_1 : N] <= 2` and the shared bit is an affine
    character.
  - The support is an intersection of cosets, hence a coset, and the image is affine.
- **Relabelable corners.**
  - Fourier unitaries `X_(q,chi)`.  For `(chi, chi') ⊥ D`, `chi (x) chi'` is constant on `cD` and the
    products sum to one, so the relation becomes a central phase.
  - Converse by averaging over `D^⊥`.
  - The corner `p_omega` has trace `1/n`.  So a hyperlinear `Γ` would put an `R^U` model on `A(S)`.

## 6.2 The Mikhailova amplifier: PASS

- **Two-sided action.**  `Psi(a,b) = phi(a) phi(b)^-1` descends to `(F x F)/M ≅ Q` equivariantly, with
  stabilizer `M`.
- **Co-amenable.**  A bi-invariant mean on `Q` pulls back along `phi x phi`.
- **Non-amenable.**  `M` contains the diagonal.
- **Non-separable** when the word problem of `Q` is unsolvable: `M` is finitely generated in `F x F`,
  so membership is r.e., and separability would make non-membership r.e.
- **Domination.**
  - An amplifier solution contains `E' = (Z/2) wr_(G/Γ) G`, which is nonsofic (Theorem A) and not
    finitely presented (part 5 §5.3).
  - Retracts of finitely presented groups are finitely presented, so `K_e` does not retract onto `E'`.
  - The finitely presented seed runs the same positive branch.

## 6.3 Liftable masas: PASS

**One compressor, tight periods.**
- `Ad V^l` on the factor `A_x` is inner (`w_x`).  The transported eigenprojections `q_p` commute with
  `V`.
- Maximality uses the Poincaré inequality on the `l`-cycle, with gap `4 sin^2(π/l) >= 16/l^2`:
  `||y - E_C y||_2^2 <= (K^2/16) ||[V,y]||_2^2 + 4 tau(P_(>K))`.

**POVM orthogonalization (Lemma 1).**
- **Dilation.**  `V^* E_A V = a_A` and `sum_A ||(1-Π) E_A Π||'^2 = γ`.
- **Diagonal part.**  `||Π - Π_D||'^2 <= 2γ`.
- **Rounding.**  `|t - 1_(t>1/2)|^2 <= t(1-t)`, which gives `8γ`.
- **Rank repair.**  `u <= (2+u)^(1/2) (8γ)^(1/2)`, so `η = 32γ + 8γ^(1/2)`.
- **Polar compression.**  `||1 - |W_0| ||_2 <= ||1 - |W_0|^2||_2`, so `||U - V||' <= 2 η^(1/2)`.
- **Constant.**  `a_A - p_A = (V-U)^* E_A V + U^* E_A (V-U)` gives `16η = 512γ + 128γ^(1/2)`.

**The crux contains `DEC_κ(SL_d(Z))`.**
- **Finite rings.**  `B_l = F_q[(Z/l)^d]` is semisimple, `Γ` maps onto `prod_P SL_r(F_P)`, and 2-transitivity
  makes each `l^2_0` irreducible.
- **Character bound.**  Fixed lines of a non-scalar `k` number at most `[r-1]_Q + 1`, and
  `dim l^2_0 = Q [r-1]_Q`, so `|chi|/dim <= 1/Q`.
- **Traces vanish, case `M != I`.**
  - `M` is non-scalar because `d` is odd, so it is non-scalar mod `l` for almost all `l`.
  - Eigenspaces cover at most `2 l^(d-1)` vectors, so the moved points number at least `l^(d-1)/2`,
    and each cycle costs a factor `>= 2^(l_c/2)`.
- **Traces vanish, case `M = I`, `k != 1`.**
  - `gcd(r, q-1) = 1` excludes scalars, so some entry `f != 0`.
  - `f` has at most `d D l^(d-1)` zeros on `mu_l^d`.
- **Transfer.**
  - `σ_n = τ_(l_n) (x) (h_n o quo)` is trace-preserving, and its vertex restriction is genuine.
  - `at-op62-holds-for-representation-lifts` gives `σ(G)' cap M = 1 (x) (h(SL_d(Z))' cap prod_U M_k)`.
  - Amplification invariance finishes.

## 6.4 Graph checks at `d559bc2fa`

- `non-group-dual-colored-qc-qa-pair-exists` is OPEN.  Its route
  `non-group-dual-colored-qc-qa-pair-from-coset-system` requires
  `tracial-non-ru-coset-system-with-nonabelian-fibre-exists`, which is OPEN, has Attempts, and has no
  route.
- `perfect-completeness-isomorphism-compiler` is OPEN.
- Every famous root of these lanes still reads OPEN (part 3 §3.4).
