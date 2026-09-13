# Verification of the weakly finite counterexample chain

Lane `w6-vf-chain`, 2026-09-12, read at main `83204067f`.

**Scope.** Theorem C, binary Theorem B with Proposition C, Theorem W, the weakly finite reflection ideal, defect
triviality, the ternary anti-central images, the flattening results, and the triangular certificate criterion. These
are the premises behind the single-statement forms of the binary and ternary counterexample routes.

**Coverage.** At the read tip all thirteen routes of these claims already carry `w4-vf-linear-b` PASS lines (commits
`1dc81f2a2` and `820fa3ebf`; Sections 28.1, 29.4–29.5, 32, 35–37 of
`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`). This lane does two things:
- Section 1 spot-checks the hardest step of each independently, with the quantifiers checked.
- Sections 2–4 assemble the end-to-end chains from each counterexample statement to its single-statement form,
  including the external inputs. No verifier had assembled them.

## 1. Spot-checks: PASS throughout

### 1.1 Theorem C and Corollary C.2: PASS

Claims `rank-condition-rings-have-weakly-finite-images` and `anti-central-rank-condition-gives-weakly-finite-image`.
- **Retract lemma.**
  - Put `K = UẼV` with `Ẽ² = Ẽ`, `X' = [[X],[ẼV]]` and `Y' = [Y, −UẼ]`.
  - Then `Y'X' = YX − UẼ·ẼV = I_(n+1)`, so `A^(n+1)` is a retract of `A^n ⊕ ẼA^R`.
  - State form: `n + 1 <= n + s([Ẽ]) = n`.
  - Class-zero form, the one the route uses: `ẼA^R ⊕ A^r ≅ A^r`, which gives an epimorphism `A^(n+r) -> A^(n+1+r)`.
- **Maximality is applied in the quotient.** The lemma is used for idempotent matrices over `W = A/J` whose class in
  `K_0(W)` is zero. The preimage in `A` of the ideal they generate has a quotient satisfying the rank condition, so it
  equals `J`.
- **Properness.** The zero ring fails the rank condition at `n = 0`. So the maximal `J` is proper and `W != 0`.
- **Weak finiteness.** `AB = I_n` makes `BA` Murray–von Neumann equivalent to `I_n`. So `I_n − BA` has class zero in
  `K_0(W)`, and it vanishes.
- **Quantifiers.**
  - The rank condition, weak finiteness and the retract are all matrix statements, for every `n`.
  - The class-zero form needs no state and no order unit.
  - The state form needs states normalized at `[W]`. They exist by the census criterion, because `W` satisfies the
    rank condition.
- **Corollary C.2.** Over `F_3`, `1 − z -> 2·1_W != 0`, so the kernel of `G_3 -> W^x` misses `z`.

### 1.2 Binary Theorem B and Proposition C: PASS

Claims `binary-cyclic-corner-full-iff-complement-corner-has-no-state` and
`binary-complement-corner-rank-functions-pull-back-to-units`.
- **Lemma 1.1.** `D(h)[g] = Σ_j s_σ(j) h t_j = [g]D(h)`, where `σ` is the 3-cycle of `g`. So `D` commutes with `e` and
  `f`, and `ψ'` is a unital homomorphism into `T`.
- **Lemma 1.2(d).** `D(e) = e_(K_2) = e_(A_9) + f_(K_2)`. So `ψ'(f) = f − f_(K_2) = f_(K_3) + f_(K_4)`.
- **Lemma 1.2(b), (c).**
  - The `π_M` act transitively on the four lines, so `v = 3[f_(K_1)A] = 3d_1`.
  - `F^k(d_0) = d_k` gives `v = 3^k d_k`.
  - `e = E_(k+1) + Σ_(l=1..k)(E_l − E_(l+1))` gives the count `(3^k − 1)/2`.
- **Lemma 1.3.** A retraction `φ : eA -> A` satisfies `φ(y) = φ(e)y`. So `c = φ(e)` and `b = m`.
- **6 ⇒ 2.**
  - `Nv + v + q = Nv` iterates to `Nv + jv + jq = Nv`.
  - Applying `F^k` with `j = 3^k` gives `Nd_k + v + x = Nd_k`.
  - Once `(3^k − 1)/2 >= N`, we have `p = Nd_k + c`, and hence `u + x = p`.
- **Quantifiers.**
  - Statement 6 is the stable form `[T] <= 0`. It is equivalent to failure of the matrix rank condition, because an
    epimorphism of free modules splits.
  - `ψ'` is unital, so the pulled-back state is normalized at `[A]`, and it gives `[f]` the value `2/3`.
  - Proposition C(b) uses simplicity of `G` (Section 2).

### 1.3 Theorem W: PASS

Claim `binary-corner-weakly-finite-images-are-unit-representations`.
- **Lemma W.2.**
  - The stabilizer of `K_1` in `GL_2(F_3)` acts on the other three lines as `AGL_1(F_3)`. So some `M` fixes `K_1` and
    sends `K_3` to `K_2`.
  - Then `π_M e π_M^(-1) = e`. So `x = π_M f_(K_3) = f x f` lies in `T`, and `xy = f_(K_2)`.
  - Hence `q(f_(K_2)) = q(x) q(f_(K_3)) = 0`.
- **(a) ⇒ (c)** uses only size-one direct finiteness of `W`. `φ(e)` has the one-sided inverses `φ(ebc)` and `φ(bce)`, so
  `φ(e) = 1`. Then `φ(f) = u(1 + u) = 0` gives `u = 1`.
- **(b) ⇒ (a)** uses weak finiteness at every size, through Theorem C.
- **(d)** quantifies over all weakly finite rings of characteristic two. Characteristic two is exactly what extends `ρ`
  to `F_2[G]`.
- **Simplicity.** (d) ⇒ (c) needs no simplicity. (c) ⇒ (d) needs simplicity of `G`.

### 1.4 Reflection ideal, defect triviality, ternary anti-central images: PASS

Claims `weakly-finite-reflection-ideal-detects-weakly-finite-images`,
`weakly-finite-leavitt-representations-killing-defect-are-trivial` and
`ternary-weakly-finite-representations-give-anti-central-images`.
- **`J_omega`.**
  - A pair modulo `J_omega` uses finitely many entries, all in one `J_k`, so its defect lies in `J_(k+1)`.
  - Universality follows by induction on `k`.
  - Part (d): `J_1 = 0` gives `Phi(0) = 0`.
- **Defect triviality, step 4.**
  - In the weakly finite corner, `C(t_0)C(s_0) = p_1` gives `C(s_0)C(t_0) = p_1`, so `C(s_1 t_1) = 0`.
  - Then `p_1 = C(t_1) C(s_1 t_1) C(s_1) = 0`.
  - Steps 1–3 are cited from `w3-vf-linear` Section 23 and were not re-derived here. They carry only (i) ⟺ (iv) of
    Theorem 3, which is not on the equivalence chain.
- **Theorem 3, the cut.**
  - Put `f = 2(1 − u)` with `u² = 1`. Over `F_3`, `f² = 4(2 − 2u) = 8(1 − u) = f`, and `fu = −f`.
  - So `eps_+ = 2(1 + [z]) -> 2(f − f) = 0`, and the map factors through `S_-`.
  - The image is a subring of `fWf` with unit `f != 0`. It is weakly finite by padding with `1 − f`.
- **Quantifiers.** A weakly finite representation is a homomorphism into the units of an arbitrary weakly finite
  `F_3`-algebra. The notion is not restricted to matrices or rank models.

### 1.5 Flattening and the triangular criterion: PASS

Claims `separated-triangular-steps-flatten-to-minors`, `nilpotent-jordan-certificates-flatten-to-minors`,
`k0-state-extends-to-rank-function-iff-triangular-monotone` and `sylvester-rank-functions-iff-no-triangular-certificate`.
- **Lemma S.**
  - `𝓛W𝓡 = [[L_A A R_A + L_1 Z_1 R_1, L_A C R_B], [0, L_B B R_B + L_2 Z_2 R_2]]`.
  - `f` and `g` are idempotent. So compressing by `diag(f, g)` and then multiplying on the right by
    `[[f, −fDg], [0, g]]` gives `f ⊕ g`.
- **Corollary J.** `[[I,0],[−U,I]] · [[V,I],[0,U]] · [[I,0],[−V,I]] = [[0,I],[−UV,0]]`. With `V = u^j` and `U = u`, the
  corner is `u^(j+1)`.
- **Theorem R, extension step.** `h <= nx` and `n'x <= h'` give `n'h <= nn'x <= nh'`. So `phi(h)/n <= phi(h')/n'`.
- **Criterion** (spot-check of `w4-vf-linear-b` Section 28.1). Absorption gives
  `I_(q+1) <=_T I_(q+1) ⊕ X <=_T X <~ I_q`. With minors only, the same argument gives the rank condition.
- **Where they sit.** These four are premises of the Sylvester form of the gate, not of the weakly finite chain in
  Sections 2–4.
