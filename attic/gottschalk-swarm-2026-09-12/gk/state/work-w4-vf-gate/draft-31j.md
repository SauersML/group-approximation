
## 31. w7-el3j-sofic (58760b6ad)

Sources: artifact `jacobson-el3-soficity-firewalls-2026-09-12.md`, Sections 0–2 (blob `ecc44bd3`); claims
`jacobson-elementary-subgroups-are-locally-finite-by-linear` and `jacobson-elementary-groups-are-lea-only-if-lef`, each
with its route. Both claims landed ESTABLISHED before verification. **Verdict: PASS on both.** No corrections. Neither
verdict is decision-level: the soficity of `EL_3(J)` stays open.

### 31.1 `jacobson-elementary-subgroups-are-locally-finite-by-linear`: PASS

- **Kernel.**
  - `S^a T^b` is a basis. So `ker(J_F -> F[z,z^(-1)])` is the set of sums `Σ λ_ab S^a T^b` with
    `Σ_(a−b=d) λ_ab = 0` for every `d`. It is spanned by `S^a T^b − S^(a+1) T^(b+1) = S^a Q T^b`.
  - `QS = 0`, `TQ = 0` and `Q^2 = Q` give `E_kl E_mp = δ_lm E_kp`. For `l > m` the product contains
    `Q T^(l−m−1) (TQ) = 0`, and for `m > l` it contains `(QS) S^(m−l−1) Q = 0`.
  - An element of `L_n` and its inverse both lie in `1 + M_fin(N x n, F)`. So `L_n <= GL_fin`, which is locally finite.
- **Residual finiteness.** `z^(−m) p(z)` is a unit times `p`, and `p` is nonzero modulo `z^N − 1` once `N > deg p`.
- **Proposition 1.3.**
  - **Kernel.** `(H ∩ L_n) M / M` is a locally finite normal subgroup of a finitely generated infinite simple group, so
    it is trivial. Hence `H/M = π(H)/π(M)`.
  - **Bounded exponent.** For torsion `g` in `GL_n(F(z))`, the characteristic polynomial has coefficients in `F`,
    because `F` is algebraically closed in `F(z)`. So the semisimple part has order dividing
    `lcm_(k<=n) (q^k − 1)`, and `p^r >= n` kills the unipotent part.
  - **Zariski closure.** `x^e = 1` holds on the closure `𝐌`, so `𝐌°` contains no torus and is unipotent. `π(H)`
    normalizes `𝐌`.
  - **Two cases.**
    - If `π(H) ∩ 𝐌 = π(M)`, then `H/M` embeds in the `K`-points of the affine group `N(𝐌)/𝐌`. That group is linear,
      so `H/M` is residually finite by Mal'cev.
    - Otherwise `π(H) <= 𝐌`, and `H/M` is virtually nilpotent.
    - Both contradict simplicity.
- **Examples.**
  - **Cohn algebra.** `P = 1 − s_0 t_0 − s_1 t_1` is idempotent, with `t_i P = 0 = P s_i`. So `(P)` is spanned by the
    matrix units `s_v P t_w`, and it is the simple ring `M_fin`.
  - The kernel of `EL_3(C_2) -> EL_3(L_(F_2)(1,2))` therefore lies in `1 + M_fin` and is locally finite, while the
    quotient `R^x` is simple. Proposition 1.3 applies.
  - A torsion-free group has no nontrivial locally finite normal subgroup, so `F`, `BS(2,3)` and Higman's group are
    excluded through item 3.
- **Monolith, checked independently (consequence line only).**
  - The `x_ij(E_kl)`, `i != j`, are the finitary transvections between distinct colours. Their commutators
    `[1 + e_xy, 1 + e_yw] = 1 + e_xw`, with `y` of a third colour, give every transvection. So
    `L = GL_fin(N x {1,2,3}, F_2)`, which is simple because `GL_fin = SL_fin` over `F_2`.
  - If `g` centralizes `L`, then `1 + gv ⊗ φg^(−1) = 1 + v ⊗ φ` for all `φ(v) = 0`. So `gv ∈ F_2 v` for every `v`,
    hence `g = 1`.
  - For a nontrivial `N ⊴ E`, `[N, L]` is a nontrivial normal subgroup of `L`, so `L <= N`. `x_13(Q) ∈ L`, and `E` is
    infinite and Kazhdan (31.2). So `E` is not residually amenable.
- **Dependency note.** The route's `requires` omits `binary-jacobson-mark-dichotomy-holds-from-rank-two` and
  `binary-jacobson-self-centralizing-kernel-proof`, which the monolith line cites. Both facts are re-derived above, and
  the monolith is not a Statement item. No change needed.

### 31.2 `jacobson-elementary-groups-are-lea-only-if-lef`: PASS

- **Property (T), rank three.** `J_F` is a quotient of `F<x,y>`, and `EL_3` of a quotient ring is a quotient group. So
  (T) comes from `elementary-group-property-t-over-free-algebras` (ESTABLISHED).
- **Rank at least four.** (T) for `EL_n(J)` follows from the Kazhdan Steinberg cover, or directly from
  Ershov–Jaikin-Zapirain for `EL_n(F_2<x,y>)`, `n >= 3`. Item 3 needs only `EL_4(J)`.
- **LEA implies LEF.**
  - A finitely generated Kazhdan group is a quotient of a finitely presented Kazhdan group `Γ` (Shalom).
  - The marked groups satisfying the finitely many relators of `Γ` form a neighbourhood, and all of them are quotients
    of `Γ`, hence Kazhdan.
  - A group that is both amenable and Kazhdan is finite.
  - Marked limits agree with local embeddability: a partial embedding of `B_r` makes words of length `<= r` trivial in
    the image exactly when they are trivial in the group.
- **Not LEA for `n >= 4`.** `cohn-elementary-group-is-not-lef` (ESTABLISHED) shows that `EL_4(J)` is not LEF, through
  the finitely presented `St_4(J)`. Block inclusion carries this to every `n >= 4`, since LEF and LEA pass to
  subgroups. So `EL_n(J)` is not LEA.
- **Scope.** The claim is about approximation classes only, and it records that sofic approximations other than
  amenable local embeddings are not excluded. It proves no triviality.
