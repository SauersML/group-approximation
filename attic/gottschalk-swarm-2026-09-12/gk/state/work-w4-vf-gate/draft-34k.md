
## 34. w7-k2-unstable (8afa07966)

Sources:
- Artifact `leavitt-unstable-k2-steinberg-reduction-2026-09-12.md` (blob `c47819ab`), Sections 0–5. Sections 6–8 were
  checked as listings.
- The OPEN claim `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` (blob `5a8142c3`).
- The lane's Attempts entries on `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (entry as landed at
  `ac79e865`) and `binary-complement-corner-has-no-weakly-finite-image` (blob `97bd6534`).

**Verdict: PASS on Sections 1–5, the claim display and both entries.** No corrections. The imports are exactly those
the artifact's Section 7 names:
- Khanh's (KH1), Lemma 5.2, Theorem 5.1 and Proposition 4.2;
- the statement of Voronetsky's Proposition 1;
- for the ternary host, `khanh-acyclicity-and-steinberg-criteria` through the host theorem.

It is decision-level for the gate plans. Option 2 of Remark 3.2 in the mismatched-factor firewall is empty for both
hosts. Nothing here says that rank models or weakly finite images are trivial. The binary corner claim, both
submultiplicativity claims and Plan 1 stay OPEN. The lane may create the route.

### 34.1 Stable K-theory and the identification (Sections 0–1). PASS

- **Stable groups.** For one vertex with two loops, `N_E = (2)` and `1 − N_E^t = −1`, which is invertible on every
  `K_n(k)`. In the long exact sequence every map `K_n(k) → K_n(k)` is then an isomorphism, so each `K_n(L_k(1,2))`
  is squeezed between a zero cokernel and a zero kernel. This agrees with `ara-cortinas-leavitt-tensor-k-theory-vanishes`.
- **The identification.** The code `{0, 10, 11}` gives `R ≅ R^3` as right modules, so `M_3(R) ≅ R` and `R^x ≅ GL_3(R)`.
- **`GL_3 = E_3`.** Binary: `leavitt-gl-equals-el-and-perfect-unit-group`. Ternary: part 2 of the host theorem, whose
  proof takes GE from Menal–Moncasi and not from the Steinberg comparison, so the use is not circular.

### 34.2 Binary: `K_2(3, R_2) = 0` (Section 2). PASS

- **Step 1, recomputed.**
  - `x_ij(a) = [x_ik(a), x_kj(1)]`, so `S_3` is perfect.
  - The five-term sequence gives `H_2(G_3) → N_3/[S_3, N_3] → H_1(S_3) = 0`. `(KH1)` covers `n = 2`, `r = 3`: it holds
    "for every n > 0 and r >= 1" (`leavitt-steinberg-map-iso-from-rank-three`, line 17). So `N_3 = [S_3, N_3]`.
  - Lemma 5.2 makes `j_3(N_3)` central in `S_4`. Hence `j_3(N_3) = [j_3(S_3), j_3(N_3)] = 1`.
- **Step 2.** The hypotheses (1)–(3) listed match Theorem 5.1 as quoted in item 2 of
  `khanh-acyclicity-and-steinberg-criteria`: `GL_(n−1) = E_(n−1)` and `GL_(n−2) = E_(n−2)`, `j_(n−1)(N_(n−1)) = 1`, and
  `|X_n|` simply connected, at `n = 4`. Imported.
- **Step 3, recomputed.**
  - `U_3 T_3 (x) = (x_1, x_2, (ee* + ff*) x_3) = x`, and `T_3 U_3 (x_1, x_2, y, z) = (x_1, x_2, e*(ey + fz), f*(ey + fz)) =
    (x_1, x_2, y, z)`.
  - `T_3 E_33 U_3` sends `(x_1, x_2, y, z)` to `(0, 0, y, z)`, which is `E_33 + E_44`.
  - For `i < 3`, `E_i3 U_3 = e E_i3 + f E_i4`. So `α_3(1 + a E_i3) = 1 + ae E_i3 + af E_i4 = (1 + ae E_i3)(1 + af E_i4)`,
    since `E_i3 E_i4 = 0`.
  - **Voronetsky's family.** `E_11, ..., E_44` is a complete orthogonal family, and it is Morita equivalent because
    `E_ii = E_ij E_jj E_ji`. With `n = 4` and `S = {1}`, `b = α_3(a E_i3) = ae E_i3 + af E_i4` has `b E_33 = ae E_i3` and
    `b E_44 = af E_i4`. So `F_α ∘ St(α_3)` agrees with `D_3` on generators, and `φ_4 D_3 = α_3 φ_3` holds on generators,
    hence everywhere.
- **Step 4.** `ker φ_3 = ker(α_3 φ_3) = ker(φ_4 D_3) = D_3^(−1)(N_4) = 1`. Only the injectivity of `D_3` is used.

### 34.3 Ternary: `K_2(3, R_3) = 0` (Section 3). PASS, conditional as stated

- Theorem 3.1 of `boone-higman-prime-field-leavitt-hosts-2026-09-12.md`, read at `bd53fc92c`:
  - part (1) with `N = 2` gives `H_n(GL_r(R); Z) = 0` for `1 <= n <= 2` and all `r`;
  - part (2) needs `N >= 2` and gives `St_r(R) ≅ GL_r(R)` for `r >= 3`.
- `B = F_3` is simple and unital, and 34.1 gives every `K_i(R_3) = 0`.
- The step descriptions match the proof list of Theorem 3.1: Theorem 2.1 (`n >= 4`, any nonzero unital ring) replaces
  Theorem 5.1, and Voronetsky's refinement needs no characteristic hypothesis.
- The prime-field host node is ESTABLISHED conditional on `khanh-acyclicity-and-steinberg-criteria`, as Section 7
  says.

### 34.4 The Steinberg residue (Section 4). PASS

- **(St3) index check.** `[x_ij(a), x_kl(b)] = 1` needs `j ≠ k` and `i ≠ l`. Both hold for `x_ik` against `x_ij` and
  against `x_jk`. So `x_ik(c)` commutes with both.
- **Closure, recomputed.** From (St2), `x_jk(b) x_ij(a) = x_ik(−ab) x_ij(a) x_jk(b)`. Then
  `(λ, μ, ν)(λ', μ', ν') = (λ + λ', μ + μ', ν + ν' − λ'μ)` on `x_ij(λa) x_jk(μb) x_ik(νab)`. This is a quotient of the
  Heisenberg group over `F_p`, of order at most `p^3`: 8 over `F_2`, which is Remark 3.2's bound (line 204), and 27
  over `F_3`.
- **Option 2.** `N_3 = 1` means (St1)–(St3) present `S_3 ≅ R^x`, so there is no `K_2(3,R)` element to use.

### 34.5 Hexagon presentation, calibration and limits (Section 5). PASS

- **Arcs, recomputed.** In the cyclic order `123, 213, 231, 321, 312, 132`, each root's arc of three consecutive
  vertices is:

  | root | vertices |
  |---|---|
  | `(1,2)` | 5, 6, 1 |
  | `(2,1)` | 2, 3, 4 |
  | `(1,3)` | 6, 1, 2 |
  | `(3,1)` | 3, 4, 5 |
  | `(2,3)` | 1, 2, 3 |
  | `(3,2)` | 4, 5, 6 |

  Adjacent vertices share 2 roots, vertices at distance two share 1, and opposite vertices share 0. The shared root at
  distance two lies in both edge groups at the middle vertex.
- **(SPG2) at `n = 3`, independently.**
  - Every Steinberg relation lies in one `U_π`:
    - (St1) lies in any `U_π` containing its root;
    - (St2) for `(i,j)` and `(j,k)` lies in `U_(ijk)`;
    - (St3) for a common source `i` lies in `U_(i··)`, and for a common target `k` in `U_(··k)`.

    No other pair of distinct roots satisfies the (St3) conditions.
  - So `S_3 → colim` is defined. It is inverse to `colim → S_3`, because the copies of each `x_ij(a)` are identified
    along the arc.
  - Killing the off-forest letter of `π_1(Y_hex)` gives the free product of the vertex groups amalgamated along
    every edge, which is the colimit.
- **Calibration.** The main case of Theorem 1.1 of the mismatched-factor firewall applies:
  - The graph is countable and may have cycles.
  - `U_π(R_2)` is countable and locally finite. Finitely many `(a_i, b_i, c_i)` stay inside the finite set
    `span{a_i} × span{b_i} × span{c_i, a_i b_j}`, which is closed under `(a, b, c)(a', b', c') = (a + a', b + b', c + c' + ab')`.
  - Every edge unit is `1`, which is allowed off the forest.
  - `σ` takes values in a weakly finite characteristic-two algebra (Theorem 1.1(3)), is nontrivial, and has
    `σ(t) = [π_(n,e)]`.
  - The representation form of `binary-complement-corner-has-no-weakly-finite-image` ("every homomorphism of
    `L_(F_2)(1,2)^x` into the units of a weakly finite ring of characteristic two is trivial") is refuted by any
    nontrivial such `σ` that kills `t`. The Corollary 1.3-type conclusion, that a relation-only proof must use
    `t = 1`, follows.
- **No `D_A` statement.** Corollary 1.2 needs both unit root pairs in one vertex group (line 95). The frame-vertex
  remark is correct: the amalgam `R^x *_K L_0` needs further relations. Both are non-claims.

### 34.6 Claim display, entries, consumers and scope. PASS

- **Display.** Points 1–4, "Not claimed" and "Payoff" match Sections 1–5. Point 2's "order at most `p^3`" is 34.4.
- **Entries.** The `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` entry and the
  `binary-complement-corner-has-no-weakly-finite-image` entry each state option 2 empty, order at most 8 over `F_2`,
  the two remaining options, and the hexagon as a presentation, not a firewall. That is accurate.
- **Consumers (Section 6).** The plan line numbers 45, 319 and 325 were read at `1754aa79d2`. The plan has since
  moved: it now says this at lines 46–47 and 372–386. The listing is time-stamped, so nothing needs changing. The
  three marked-graph nodes concern Laurent hosts, and are correctly listed as non-consumers.
- **Subsumption scan at `25d2ad26e8`.** `K_2(3` occurs in 11 research files:
  - the claim and its artifact;
  - both entries;
  - `graphs-of-locally-finite-groups-carry-regular-rank-models`;
  - the firewall artifact, the plans artifact and this artifact;
  - the three marked-graph nodes.

  The binary part of point 1 is `(KH2)` at `r = 3`, which the claim's `distinct_from` records. No landed node states the
  ternary rank-three case or the hexagon presentation.
- **Route.** Section 8's five required nodes exist on main and are ESTABLISHED; two of them are literature imports,
  and the host node is conditional. Advisory: Step 2 quotes Theorem 5.1 through
  `khanh-acyclicity-and-steinberg-criteria` directly, so the route may list it too.
- **Scope.** Everything here is a presentation or a vanishing statement about `K_2`. None of it forces a rank model,
  a weakly finite representation or `θ` to be trivial.
