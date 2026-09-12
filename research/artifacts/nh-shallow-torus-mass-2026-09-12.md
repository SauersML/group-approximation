# Shallow non-unit root mass vanishes: compressor constants and the Laurent torus

Lane `nh-shallow-torus-mass`, 2026-09-12. Target: case (ii) of
`theorem-e-vertex-rounds-to-unit-type-representations`, i.e. shallow pure non-unit root mass.
Outcome: case (ii) is closed. The shallow mass is at most `q·η_n + η_n^t`, which tends to 0 along `U`.

## Setting

As in `research/artifacts/nh-unit-type-rounding-2026-09-12.md`:
- `R_+ = F_q[x_1..x_d]`, `L = F_q[x^(±1)]`, `r, d >= 3`, `Γ = EL_r(R_+) < G = EL_r(L) ⋊ SL_d(Z)`;
- `A ∈ SL_d(Z)` a compressor with all entries `>= 1`, `φ_A` the monomial substitution `x^a -> x^(Aa)`;
- `σ : G -> U(prod_U M_n)` trace-preserving, with (H1) rounding `π_n : Γ -> U(n')`, `n'/n -> 1`;
- `μ_n` the normalized spectral measure of `f -> π_n(e_12(f))` on the dual `R_+^` of `(R_+, +)`;
- `η_n = 4δ_n^2/κ^2` from Lemma A (`compressor-transport-exactifies-under-vertex-rounding`), so
  `|μ_n(E) - μ_n(D_A^(-1)E)| <= η_n` for every Borel `E`, with `D_A χ = χ ∘ φ_A`;
- `z = x_1 ⋯ x_d` and `depth(χ) = min{k : χ trivial on z^k R_+}`.

New notation:
- `m = (x_1, ..., x_d)`, and `ev_0 : R_+ -> F_q`, `f -> f(0)`.
- For `ψ ∈ F_q^` put `ψ_0 = ψ ∘ ev_0 ∈ R_+^`. `E_0 = {ψ_0 : ψ ∈ F_q^}` has `q` elements; `E_0^* = E_0 \ {1}`.
- For `χ ∈ R_+^` let `χ|_1 ∈ F_q^` be `c -> χ(c·1)`.
- `Sh = {χ : χ trivial on z R_+} = {depth <= 1}`. Case (ii) is `μ_n(Sh \ {1}) = μ_n(depth = 1)`.
- `E_0 ⊆ Sh`, since `m ⊇ z R_+`.

## §1 Lemma D: compressors send shallow characters to constant terms

1. **Contraction of the maximal ideal.** `φ_A(m) ⊆ z R_+`. For a monomial `x^a` with `a ≠ 0`, every
   coordinate of `Aa` is `Σ_j A_ij a_j >= |a|_1 >= 1`, so `x^(Aa)` is divisible by `z`.
2. **Collapse.** For `χ ∈ Sh` and `f ∈ R_+`, write `f = f(0)·1 + g` with `g ∈ m`. Then
   `χ(φ_A f) = χ(f(0)·1)·χ(φ_A g) = χ|_1(f(0))`, because `φ_A(1) = 1` and `φ_A g ∈ z R_+`.
   So `D_A χ = (χ|_1)_0 ∈ E_0`.
3. **Fibres.** Put `Sh_ψ = {χ ∈ Sh : χ|_1 = ψ}`. By item 2, `Sh_ψ ⊆ D_A^(-1){ψ_0}`, and `ψ_0 ∈ Sh_ψ`.
4. **Per-fibre bound.** Lemma A with `E = {ψ_0}` gives `μ_n(Sh_ψ) <= μ_n(D_A^(-1){ψ_0}) <= μ_n({ψ_0}) + η_n`.
   Since `Sh_ψ = {ψ_0} ⊔ (Sh_ψ \ {ψ_0})`, this is `μ_n(Sh_ψ \ {ψ_0}) <= η_n`.
5. **Sum.** Over the `q` characters `ψ`: `μ_n(Sh \ E_0) <= q·η_n`.

**What the compressor cannot do.** `φ_A(f)(0) = f(0)`, so `D_A` fixes `E_0` pointwise. The same holds
for every nonnegative compressor and every permutation of the variables. Constant-term constituents,
for example `π ∘ (EL_r(R_+) -> SL_r(F_q), x -> 0)`, are exactly invariant under all of them. Lemma A
says nothing about `E_0^*`.

## §2 Lemma E: the Laurent torus kills constant-term characters

**Setup.**
- `t = diag(x_1, x_1, x_1^(-2), 1, ..., 1)`. It lies in `EL_r(L)` by Whitehead's lemma:
  `t = diag(x_1, x_1^(-1), 1, ...)·diag(1, x_1^2, x_1^(-2), 1, ...)`, and `diag(u, u^(-1)) ∈ E_2(L)`
  for every unit `u`.
- `S` is the group of block matrices `[[g, v], [0, 1]]` in rows and columns 1–3, with `g ∈ EL_2(R_+)`
  and `v ∈ R_+^2`, padded by the identity. So `S = <e_12(R_+), e_21(R_+)> ⋉ V` with
  `V = e_13(R_+) × e_23(R_+)`, and `S <= EL_3(R_+) <= Γ`.
- `Ad t` is the identity on the `EL_2` block, since `t_1 = t_2`, and multiplies `V` by `x_1^3`:
  `t e_13(f) t^(-1) = e_13(x_1^3 f)`, `t e_23(f) t^(-1) = e_23(x_1^3 f)`. So `Ad t(S) ⊆ S ⊆ Γ`, and
  `ρ_n^t := π_n ∘ Ad t` restricted to `S` is a genuine unitary representation of `S`.
- `t` does not map `Γ` into `Γ` (`t e_31(f) t^(-1) = e_31(x_1^(-3) f)`), so Lemma A does not apply to it.
- `(F_S, κ_S)` is a finite relative Kazhdan pair for `(S, V)`. It exists by
  `elementary-linear-semidir-pair-relative-t`, since `R_+` is a finitely generated unital ring.
- `V_n` is a unitary representative of `σ_n(t)`, padded by the identity as in Lemma A.
  `δ_n^t = max_(s ∈ F_S) ||ρ_n^t(s) V_n - V_n π_n(s)||_2`, and `η_n^t = 4(δ_n^t)^2/κ_S^2`.

**Steps.**
1. **Defect.** `δ_n^t -> 0` along `U`. For `s ∈ F_S`, both `s` and `t s t^(-1)` are fixed elements of `Γ`, hence
   fixed words in `F_Γ`. `σ` is a homomorphism into the ultraproduct, so
   `||σ_n(tst^(-1))σ_n(t) - σ_n(t)σ_n(s)||_2 -> 0`, and (H1) bounds `π_n - σ_n` on fixed words by
   word length times the generator error.
2. **Linear relative Kazhdan inequality.** `V` is normal in `S`. In any unitary representation of `S`,
   the `V`-invariant subspace is therefore `S`-invariant, and its orthocomplement has no nonzero
   `V`-invariant vector. Apply the relative Kazhdan constant to the complementary component and use
   orthogonality of the decomposition:
   `||ξ - P^V ξ|| <= κ_S^(-1) max_(s ∈ F_S) ||π(s)ξ - ξ||`.
3. **Intertwiner.** Apply item 2 to `Φ(s)X = ρ_n^t(s) X π_n(s)^*` on `(M_(n'), ||·||_2)` with `X = V_n`.
   Then `T = P^V(V_n)` satisfies `||V_n - T||_2 <= δ_n^t/κ_S` and `ρ_n^t(v) T = T π_n(v)` for `v ∈ V`.
   `π_n` and `ρ_n^t` factor through finite quotients (root torsion), so `P^V` is the average of `Φ` over
   a finite group of operator-norm contractions, and `||T|| <= 1`.
4. **Support.**
   - `1 - T^*T = V_n^*(V_n - T) + (V_n - T)^* T`, so `||1 - T^*T||_2 <= 2δ_n^t/κ_S`.
   - `T^*T` commutes with `π_n(V)`, and so does its support `Q`.
   - `τ(1 - Q) = ||(1 - T^*T)(1 - Q)||_2^2 <= η_n^t`.
   - The polar part `W` intertwines `π_n|_V` on `Q` with `ρ_n^t|_V` on `Q'`, and `τ(1 - Q') = τ(1 - Q)`.
5. **Spectral measures.** Let `μ_n^(13)` be the spectral measure of `f -> π_n(e_13(f))`. Since
   `ρ_n^t(e_13(f)) = π_n(e_13(x_1^3 f))`, the spectral measure of `ρ_n^t|_(e_13)` is `μ_n^(13) ∘ D_t^(-1)`,
   with `D_t χ(f) = χ(x_1^3 f)`. The restrictions to `Q` and `Q'` are unitarily equivalent, so
   `|μ_n^(13)(E) - μ_n^(13)(D_t^(-1) E)| <= η_n^t` for every Borel `E`.
6. **Weyl symmetry.** `w_23(1) = e_23(1) e_32(-1) e_23(1) ∈ Γ` conjugates `e_12(f)` to `e_13(±f)`. So
   `μ_n^(13)` is the image of `μ_n` under `χ -> χ ∘ (±1)`, which preserves `E_0^*` and `Sh`.
7. **Kill.** For `ψ_0 ∈ E_0^*`: `D_t ψ_0(f) = ψ((x_1^3 f)(0)) = ψ(0) = 1`. So `D_t^(-1){1} ⊇ {1} ⊔ E_0^*`,
   and item 5 with `E = {1}` gives `μ_n^(13)({1}) + μ_n^(13)(E_0^*) <= μ_n^(13)({1}) + η_n^t`. Hence
   `μ_n(E_0^*) = μ_n^(13)(E_0^*) <= η_n^t`.

## §3 Conclusion

```text
μ_n(depth = 1)  =  μ_n(Sh \ {1})  <=  μ_n(Sh \ E_0) + μ_n(E_0^*)  <=  q·η_n + η_n^t   ->  0  along U.
```

With Lemma C (`pure-nonunit-root-mass-is-log-scale-folner`), all pure non-unit root mass satisfies

```text
μ_n(1 <= depth < ∞)  <=  (q + 1 + log_d(r(r-1) n'))·η_n + η_n^t.
```

So case (ii) of `theorem-e-vertex-rounds-to-unit-type-representations` is closed. What survives:
- (i) pure non-unit mass spread over at least `1/η_n` d-adic depth scales, possible only when
  `δ_n^2 log n` does not tend to 0;
- (iii) mixed constituents, nontrivial on both `A_u` and `A_nu`.

## §4 Components: mixed shallow characters and the only surviving regime

`nonunit-component-root-mass-is-log-scale-folner` (landed while this lane ran) splits a character
`χ` killing a finite-index ideal as `χ = χ_u · χ_nu`, with `χ_u(f) = χ(e_u f)` and `χ_nu(f) = χ(e_nu f)`,
and defines `depth_nu(χ) = min{k : χ_nu trivial on z^k R_+}`. It proves
`μ_n(depth_nu > 1) <= η_n(1 + log_d(r(r-1)n'))`, leaving `μ_n(depth_nu = 1)`. That set contains mixed
characters: the evaluation-at-origin factors tensored with unit-type factors that
`vertex-rounding-non-unit-mass-at-origin` leaves open.

**Test sets.** For `ψ ∈ F_q^` put `M_ψ = {χ : χ_nu = ψ_0}`. `M_1` is the unit-type set, and every `M_ψ` lies in
`{depth_nu <= 1}`. At each finite stage `μ_n` is finitely supported, so every set is measurable.

1. **Lemma D′.**
   - **Transport.** By item 1 of that claim, `(D_A χ)_nu = χ_nu ∘ φ_A`.
   - **Collapse.** If `depth_nu(χ) <= 1` and `χ_nu|_1 = ψ`, then §1 item 2 applied to `χ_nu` gives
     `(D_A χ)_nu = ψ_0`. So `Sh′_ψ := {depth_nu <= 1, χ_nu|_1 = ψ} ⊆ D_A^(-1)(M_ψ)`, and `M_ψ ⊆ Sh′_ψ`.
   - **Bound.** Lemma A gives `μ_n(Sh′_ψ \ M_ψ) <= η_n`. Summing over `ψ`:
     `μ_n({depth_nu <= 1} \ ∪_ψ M_ψ) <= q·η_n`.
2. **Lemma E′.**
   - **Componentwise.** Multiplication by `x_1^3` commutes with the local idempotents of `R_+/I`, so
     `(D_t χ)_u = χ_u(x_1^3 ·)` and `(D_t χ)_nu = χ_nu(x_1^3 ·)`.
   - **Unit part survives.** `x_1^3` is invertible on `A_u`, so `(D_t χ)_u ≠ 1` iff `χ_u ≠ 1`.
   - **Non-unit part dies.** For `χ ∈ M_ψ` with `ψ ≠ 1`, `(D_t χ)_nu = ψ_0(x_1^3 ·) = 1`, so `D_t χ ∈ M_1`.
   - **Inclusion.** `D_t(M_1) ⊆ M_1`, hence `D_t^(-1)(M_1) ⊇ M_1 ⊔ ∪_(ψ≠1) M_ψ`.
   - **Bound.** §2 item 5 with `E = M_1`, plus the Weyl transfer (the component split is invariant
     under `f -> -f`), gives `μ_n(∪_(ψ≠1) M_ψ) <= η_n^t`.
3. **Shallow component mass.**
   `μ_n(depth_nu = 1) = μ_n({depth_nu <= 1} \ M_1) <= q·η_n + η_n^t`.
4. **Corollary.** Item 5 of `nonunit-component-root-mass-is-log-scale-folner` gives

   ```text
   τ(1 - P_n)  <=  r(r-1) · [ (q + 1 + log_d(r(r-1)n'))·η_n + η_n^t ].
   ```

   So under (H1), unit-type rounding (`τ(1 - P_n) -> 0`) holds whenever `δ_n^2 log n -> 0` along `U`.
   The only surviving regime of `theorem-e-vertex-rounds-to-unit-type-representations` is (i):
   non-unit mass spread over at least `1/η_n` d-adic depth scales, when the compressor defect
   decays more slowly than `(log n)^(-1/2)`.

## Remarks

- **Where (T) enters.** Lemma A uses property (T) of `Γ` for the compressor. Lemma E uses relative
  property (T) of `(EL_2(R_+) ⋉ R_+^2, R_+^2)` for the torus element, which maps the block `S` into
  itself but not `Γ` into `Γ`.
- **Why the torus is needed.** Constant-term constituents are exactly invariant under every nonnegative
  compressor and every permutation of the variables. The Laurent torus is the part of `G` that moves
  the origin. This matches the recorded Attempts bullet that any proof must use the Laurent torus of `G`.
- **Scale.** Iterating `t` controls characters trivial on `x_1^(3k) R_+` with `η_n^t` per step, a linear
  count in `k`. So the torus does not replace the logarithmic depth count of Lemma C for deep characters.
- **Mixed constituents.** Multiplication by `x_1^3` is invertible on `A_u`, so `D_t` cannot trivialize
  the unit part of a mixed character. Case (iii) needs a different mechanism.
- Nothing here is reviewed.
