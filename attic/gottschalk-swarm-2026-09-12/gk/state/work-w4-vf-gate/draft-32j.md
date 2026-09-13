
## 32. w7-el3j-sofic (07d43b6a3)

Sources: artifact `jacobson-el3-soficity-firewalls-2026-09-12.md`, Section 3 (blob `02494d50`); claim
`jacobson-one-sided-symbol-preimages-are-lef` (blob `65991c8a`) and its route (blob `4e7a07c7`). The claim landed
ESTABLISHED before verification. **Verdict: PASS.** No corrections. Not decision-level: it proves LEF for the halves,
proves no triviality, and leaves the soficity of `EL_3(J)` open.

### 32.1 `jacobson-one-sided-symbol-preimages-are-lef`: PASS

- **Item 1, structure.**
  - Over a Euclidean ring the Euclidean algorithm reduces a column to `(u, 0, 0)` by elementary moves, and
    `diag(u, u^(-1), 1)` is elementary. So `SL_3 = E_3` over `F`, `F[z]`, `F[z^(-1)]`, and over `F[z, z^(-1)]` (its
    Euclidean function is the width of the exponent range).
  - `π` is entrywise injective on `M_3(F[S])`, so `π : EL_3(F[S]) -> SL_3(F[z])` is an isomorphism. For `h in H_+`
    with `π(h) = π(d)`, `h d^(-1) in L_3`. So `H_+ = L_3 x| EL_3(F[S])`, and likewise for `H_-`. Since
    `F[z] ∩ F[z^(-1)] = F`, `H_0 = L_3 x| SL_3(F)`.
  - **Generation.** `x_ik(S^a T^b) = [x_ij(S^a), x_jk(T^b)]`, the first factor in `H_+` and the second in `H_-`.
- **Item 1, the twist.**
  - `σ(TS - 1) = σ(S)σ(T) - 1 = TS - 1`, and `σ(ST) = ST`, so `σ` descends to `J_F` and fixes `Q`.
  - Entrywise, `σ(gh)^t = σ(h)^t σ(g)^t`, so `θ(g) = (σ(g)^t)^(-1)` is a homomorphism. On generators
    `θ(x_ij(a)) = x_ji(-σ(a))`, so `θ^2 = 1` and `θ(E_F) = E_F`.
  - `π(σ(S^a T^b)) = π(S^b T^a) = z^(b-a)`, which is `π(S^a T^b)` with `z -> z^(-1)`. So `πθ = θ̄π`, and `θ̄` exchanges
    `SL_3(F[z])` and `SL_3(F[z^(-1)])`. Since `θ` and `θ̄` are involutions, `θ(H_+) = H_-`.
- **Item 2, truncation.**
  - **Faithfulness, checked.** If `x = Σ λ_ab S^a T^b` acts as zero on `V`, then on `e_k` with `k` large it gives
    `Σ_d (Σ_(a-b=d) λ_ab) e_(k+d) = 0`. So `π(x) = 0`, and `x` lies in the span of the matrix units `E_kl`, which act
    as independent operators. Hence `x = 0`.
  - `L_3 <= 1 + M_fin(N x 3, F)`. If `g - 1` has row and column support below level `N`, then `g` fixes `U_N`
    pointwise and preserves `W_N`, and so does `g^(-1) = 1 - g^(-1)(g - 1)`. These `L_(3,N)` form an increasing union.
  - Entries in `F[S]` raise the level, so `d in EL_3(F[S])` preserves `U_N`. On `U_N = F[S]^3` it acts by
    left multiplication by `d` itself. Its `W_N`-block `A` is invertible, because `d^(-1)` has the same shape.
  - **The product rule, recomputed.** With `g(w, u) = (Aw, Bw + Du)`,
    `g g'(w, u) = (AA'w, (BA' + DB')w + DD'u)`. This is block multiplication in `M_(3N+3)(F[S])`, and
    `[[A, 0], [B, D]]^(-1) = [[A^(-1), 0], [-D^(-1)BA^(-1), D^(-1)]]`. The operator determines `A`, `B` and `D`
    (`D` from `D ε_j`). So `⟨L_(3,N), EL_3(F[S])⟩` embeds in `GL_(3N+3)(F[S])`.
  - `GL_m(F[S]) -> GL_m(F[S]/(S^k))` has finite target and separates `g != 1` once `k` exceeds every degree in
    `g - 1`. A finitely generated `K <= H_+` lies in some `⟨L_(3,N), EL_3(F[S])⟩`, so it is residually finite and
    LEF. LEF is a local property, and LEF groups are sofic. `H_-` follows by `θ`.
  - **The head.** `π(Q) = 1 - z z^(-1) = 0`, so `x_13(Q) in L_3 <= H_0`. A finite quotient of `⟨Φ⟩` that is injective
    on `Φ` keeps it.
- **Item 3, proper cover.**
  - `[x_ij(a), x_jk(b)] = x_ik(ab)` with `[x, y] = x y x^(-1) y^(-1)`. Recomputed with noncommuting entries:
    `E_jk E_ij = 0`, `E_ik E_ij = 0` and `E_ik E_jk = 0` kill every other term. So `[x_12(S), x_23(T)] = x_13(ST)`,
    and `ST = 1 - Q`, with symbol `x_13(1) in SL_3(F)`.
  - `π(x_12(±S)) = x_12(±z)` is not constant, and likewise for `x_23(±T)`. So the word alternates between
    `H_+ \ H_0` and `H_- \ H_0`, and by the normal form theorem it is not in `H_0 <= P`. Its image equals that of an
    element of `H_0`, and `φ` is injective on `H_0`. So `φ` is not injective.
  - **The Toeplitz remark.** `[x_12(T), x_23(S)] = x_13(TS) = x_13(1)`, and the word alternates `H_-`, `H_+`, `H_-`,
    `H_+`. So the relation fails in `P` as stated.
- **Firewall line, checked.**
  - Over `F_2` every permutation matrix is elementary. So the constants and `x_12(z^(-1))` give all `x_ij(z^(-1))`,
    and through commutators all `x_ij(z^(-m))`. That is `SL_3(F_2[z^(-1)])`, which is infinite and Kazhdan, hence
    nonamenable. The subgroup of `H_-` is LEF by item 2.
  - Corollary 3.4's contrast, that amenable quotients of `E` kill `L`, is the monolith line of 31.1 together with
    (T) from 31.2.
  - Commit `0d600e4ef` exists.
- **Subsumption scan.** Landed nodes matching `SL_3(F[z])` or "symbol preimage" at `0a5550bed`:
  - `binary-jacobson-monomial-symbol-preimage-is-marked-mf` and `binary-jacobson-two-target-parabolic-is-marked-mf`
    concern MF characters of monomial and parabolic preimages. Neither proves LEF for a full half.
  - The OPEN `binary-jacobson-el3-is-sofic` and the Toeplitz bullet describe this claim accurately.
- **Scope.** Item 2 is a positive approximation result for subgroups. Item 3 is a structural statement. Neither says
  that rank models or finite models of `E` are trivial.
