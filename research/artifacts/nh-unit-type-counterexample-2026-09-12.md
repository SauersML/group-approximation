# Where a counterexample to unit-type vertex rounding must live (2026-09-12)

Lane `nh-unit-type-counterexample`. Target: refute
`theorem-e-vertex-rounds-to-unit-type-representations`, or record why that is hard.

**Result.** No counterexample. Under (H1), three rigidity statements hold for every
trace-preserving `σ : G -> U(prod_U M_n)`. They confine non-unit mass to one place, the
origin `m_0 = (x_1, ..., x_d)`, and force deep origin mass to spread over many dyadic depth
scales.

## 1. Setup and notation

- **Rings and groups:** `R_+ = F_q[x_1..x_d]`, `L = F_q[x^(±1)]`, `Γ = EL_r(R_+) < G = EL_r(L) ⋊ SL_d(Z)`, with `r, d >= 3`.
- **(H1):** there are genuine `π_n : Γ -> U(n')`, after `o(n)` padding, with `||σ_n(s) - π_n(s)||_2 -> 0` along `U` for `s ∈ F_Γ`.
- **Kernel ideal of an irreducible `ρ` of `Γ`:** `J_ρ = {a : ρ(e_ij(a)) = 1 for all i ≠ j}`.
  - It is an ideal: `e_ij(fa) = [e_ik(f), e_kj(a)]`.
  - It has finite index (`unit-type-vertex-rounding-forces-compressor-commutant-rigidity` item 1).
  - `ρ` is nontrivial on every local factor of `R_+/J_ρ`.
- **Type of a maximal ideal:** `S(m) = {i : x_i ∈ m}`.
  - `m` is *unit* if `S(m) = ∅`.
  - `m` is *origin* if `S(m) = {1..d}`, which forces `m = m_0`.
  - `m` is *intermediate* otherwise.
- **Mass:** `mass_n(Θ)` is the trace of the isotypic projection of `π_n` over the set `Θ` of irreducible classes.

## 2. The compressor matching lemma

Let `A ∈ SL_d(Z)` have all entries `>= 1`. Examples: `[[2,1],[1,1]]` for `d = 2`, and
`[[1,1,1],[1,2,1],[1,1,2]]` for `d = 3`, which has determinant `1`.
- **Subgroup:** put `y_j = x^(A e_j)`, `S = F_q[y_1..y_d] ⊆ R_+` and `Λ = AΓA^(-1) = EL_r(S) ⊆ Γ`.
- **Isomorphism:** `ψ : S -> R_+`, `y_j -> x_j`, is a ring isomorphism.
- **Two genuine representations of `Λ`:**
  - `ρ_1 = π_n|Λ`;
  - `ρ_2(λ) = U_n π_n(A^(-1) λ A) U_n^*`, where `U_n = σ_n(A)` is taken unitary.

**Lemma 2.1.** Put `η_n = max_(s ∈ F_Λ) ||ρ_1(s) - ρ_2(s)||_2 / κ`, where `(F_Λ, κ)` is a Kazhdan
pair for `Λ ≅ Γ` (Ershov–Jaikin-Zapirain). Then `η_n -> 0` along `U`, and for every set `Θ` of
irreducible classes of `Λ`,

```text
|mass(ρ_1; Θ) - mass(ρ_2; Θ)|  <=  12 η_n.
```

*Proof.*
1. **Both are close to `σ_n`.**
   - `ρ_1(s) = π_n(s)` with `s` a fixed word in `F_Γ`, so it is `o(1)`-close to `σ_n(s)`.
   - `ρ_2(s) = U_n π_n(A^(-1)sA) U_n^*`, and `A^(-1)sA ∈ Γ` is a fixed word. So `ρ_2(s)` is close to `U_n σ_n(A^(-1)sA) U_n^*`, which is close to `σ_n(s)`, because `σ` is multiplicative in the ultralimit.
   - Hence `η_n -> 0`.
2. **An intertwiner near 1.** In the representation `T -> ρ_1(λ) T ρ_2(λ)^*` on `(M_n', ||·||_2)` the identity is `κη_n`-almost invariant. So there is an intertwiner `T ∈ Hom_Λ(ρ_2, ρ_1)` with `||T - 1||_2 <= η_n`.
3. **Trace estimate.** `|a^2 - 1| >= (a - 1)^2` for `a >= 0`, so `|| |T| - 1 ||_2^2 <= ||T*T - 1||_1 <= 3η_n`.
   - The spectral projection `e = 1_[1/2, ∞)(|T|)` commutes with `ρ_2(Λ)`.
   - `τ(1 - e) <= 12 η_n`.
4. **Conclusion.** The polar part of `Te` is a partial isometry intertwining `ρ_2` on `e` with `ρ_1` on a projection of the same trace. Isotypic masses agree up to `12η_n`. ∎

## 3. Types under restriction and transport

**Lemma 3.1 (transport).** The irreducibles of `ρ_2` are `ρ∘ψ` for the irreducibles `ρ` of `π_n`, with
`J = ψ^(-1)(J_ρ)`. Local factors, their types and the nilpotency order of `y_j` equal those of `ρ`
and `x_j`.

**Lemma 3.2 (restriction).** Let `ρ` be an irreducible of `π_n` and `η` a constituent of `ρ|Λ`.
- **Kernel ideal:** `J_η ⊇ J_ρ ∩ S`.
- **Maximal ideals lying under:** every maximal ideal `n` of `S/J_η` lies under some `m ∈ Max(R_+/J_ρ)`.
- **Types:** `y_j ∈ n` iff `x^(A e_j) ∈ m` iff `S(m) ≠ ∅`, since every `A_ij >= 1` and `m` is prime. So every local factor of `η` has type `∅` or full, and full factors sit at the origin `n_0 = (y_1..y_d)` of `S`.
- **Depth:** if `ρ` has no intermediate factor, the `n_0`-factor of `η` comes from the `m_0`-factor of `ρ` alone, with component `J_0`. Write `o_j(x)` for the nilpotency order of `x_j` modulo `J_0`. Then `y_j^k ∈ J_0` as soon as `k A_jj >= o_j(x)`, so `o_j(y) <= ⌈o_j(x) / A_jj⌉`.

## 4. Theorem

**Theorem 4.1.** Assume (H1) for a trace-preserving `σ : G -> U(prod_U M_n)`, and let `η_n` be as in
Lemma 2.1 for a strictly positive `A`.

**(a) Intermediate places carry no mass.**

```text
mass_n(constituents with an intermediate local factor)  <=  12 η_n  ->  0.
```

**(b) Depth scales.** Suppose `A_jj >= 2`, and let `P_n(t)` be the mass of constituents having an origin factor with `o_j(x) >= t`. Then for all `t >= 1`,

```text
P_n(t)  <=  P_n(2t - 1) + 24 η_n,
```

and so `P_n(t) <= 24 η_n (log_(3/2)(D_n / t) + 2)` for `t >= 2`, where `D_n` is the largest origin
order occurring in `π_n`.

**(c) Fixed finite quotients carry no mass.** For each fixed finite-index ideal `I`, the mass of the constituents that factor through `St_r(R_+/I)` tends to `0`.

*Proof.*
- **(a).** Take `Θ` = classes with some intermediate factor. `mass(ρ_2; Θ)` is the mass in `π_n` by Lemma 3.1, and `mass(ρ_1; Θ) = 0` by Lemma 3.2. Apply Lemma 2.1.
- **(b).** Let `Θ_t` = classes of `Λ` with an origin factor in which `y_j` has order `>= t`.
  - `mass(ρ_2; Θ_t) = P_n(t)` by Lemma 3.1.
  - By Lemma 3.2, `mass(ρ_1; Θ_t) <= P_n(2t - 1) + mass_n(intermediate) <= P_n(2t - 1) + 12η_n`.
  - Lemma 2.1 gives the first inequality. For `t >= 2`, `2t - 1 >= (3/2)t`; iterate until the threshold passes `D_n`.
- **(c).** The kernel `Γ_I` (normal closure of `e_ij(I)`) has finite index, so it is Kazhdan.
  - By `kazhdan-projection-is-norm-limit-of-finite-averages`, `e_(Γ_I)` is a norm limit of finite probability averages `a_k` of group elements.
  - `π_n(e_(Γ_I))` projects onto exactly those constituents.
  - `τ(π_n(a_k))` and `τ(σ_n(a_k))` differ by `o(1)` along `U`.
  - `τ(σ(a_k)) = a_k(e)`, the return probability of a random walk on the infinite group `Γ_I`, which tends to `0` in `k`. ∎

## 5. Consequences for the counterexample side

1. **No hyperplane-place models.** A family whose rounding puts order-one mass on local factors where some but not all `x_i` are nilpotent is impossible. That is exactly the one-variable truncation `F_q[x_1]/(x_1^m)` with the other variables units.
2. **Deep origin mass needs many scales.** Order-one origin mass with some `o_j >= 2` requires `η_n log D_n` bounded below. The depth profile must occupy at least order `1/η_n` dyadic scales in every direction `j` (use `A` with `A_jj >= 2`, after permuting coordinates). This matches the aspect-scale bound of `ccr-under-vertex-rounding-from-few-aspect-scales`.
3. **The remaining shape.** Up to `o(1)`, non-unit mass under few depth scales sits on constituents whose origin factor is the evaluation `x -> 0`, tensored with unit-type factors at growing levels. Such tensors are not excluded by any of the three statements. They are the smallest open counterexample shape.
4. **Candidates that are dead.**
   - Truncated rings `F_q[x]/(x^n)` in one direction.
   - `R_+/m_0^n` with a single depth `n`: under a strictly positive `A` its orders shrink by `A_jj`, while transport keeps them.
   - Any fixed finite quotient.

## 6. Not done

- No model realizing item 5.3 was built. A model must be far from genuine on the actor; genuine actor models are unit-type.
- The Laurent torus `diag(x_1, x_1^(-1), 1, ...)` might kill the evaluation shape, but the group `Γ ∩ t^(-1)Γt` is a net-type congruence subgroup of infinite index. Its property (T) was not checked.
- No numerics were run.
