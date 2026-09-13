---
rg: 2
id: kazhdan-properly-nonamenable-reduction-proof
kind: route
title: A hypertrace and Kazhdan rigidity make amenable limits atomic; lift the atoms exactly and correct only the rest
target: kazhdan-hs-instability-lives-on-properly-nonamenable-limits
requires:
  - amenable-rep-of-kazhdan-has-fd-subrep
artifacts:
  - research/artifacts/solve-nh-word-stability-2026-09-13.md
---

## Conventions

- `||x||_2 = tr(x*x)^{1/2}`, with `tr` the normalized trace.
- `M^ω = ∏^ω (M_{d_n}, tr)` is the tracial ultraproduct, with faithful normal trace `τ`.
- For `σ` an asymptotic representation along `ω`, `σ^ω : Γ → U(M^ω)` is a homomorphism.

## (A1)

1. **Hypertrace.** `M = M_φ` acts on `L²(M, φ)` and is injective, so there is a
   conditional expectation `E : B(L²M) → M`. The state `m = φ∘E` is `M`-bimodular, so
   `m(uTu*) = φ(u E(T) u*) = m(T)` for `u ∈ U(M)`. In particular `m` is invariant
   under `Ad π_φ(g)`, so `π_φ` is amenable in Bekka's sense.
2. **Kazhdan.** By `amenable-rep-of-kazhdan-has-fd-subrep`, `π_φ` has a nonzero
   finite-dimensional invariant subspace `V ⊂ L²(M)`.
3. **A finite-dimensional summand.**
   - `V` is invariant under `π_φ(g)` and under `π_φ(g)* = π_φ(g⁻¹)`, so
     `P_V ∈ π_φ(Γ)' = M'`. Hence `V` is `M`-invariant.
   - So `x ↦ x|_V` is a nonzero normal representation of `M` on a finite-dimensional
     space. Its kernel is a weakly closed ideal `M(1−z)` with `z` central and nonzero.
   - `Mz` embeds in `B(V)`, so it is a nonzero finite-dimensional direct summand.
4. **Exhaustion.** Let `z₀` be the sum of all minimal central projections `z_i` for which
   `Mz_i` is finite dimensional, so `Mz₀ = ⊕ M_{k_i}`. Suppose `q = 1 − z₀ ≠ 0`.
   - `Mq` is injective, and `φ_q = φ(·q)/φ(q)` is a faithful normal trace on it.
   - `g ↦ π_φ(g)q` generates `Mq`, and `L²(Mq, φ_q) = qL²(M)`.
   - Steps 1–3 applied to `Mq` give a finite-dimensional summand orthogonal to `z₀`,
     contradicting maximality.
   So `M = ⊕_{i∈I} M_{k_i}`, and `I` is countable because `L²(M)` is separable.
5. **Traces.** `ρ_i(g) := π_φ(g) z_i` is a homomorphism into `U(Mz_i) = U(k_i)`, since
   `z_i` is central. It is irreducible, because `ρ_i(Γ)'' = M_{k_i}`. Then `φ` restricted
   to `Mz_i` is `t_i · tr_{k_i}` with `t_i = φ(z_i)`, so `φ = Σ t_i tr_{k_i}∘ρ_i`.
   Renormalized finite truncations converge pointwise.

## (A2)

Dogon--Vigdorovich, arXiv:2506.20843v2, `Sigma_submission.tex`, Theorem
`thm:HS_for_non_amenable_grps` (MSI copy, l.1557–1562), verbatim:

> Let $\Gamma$ be a finitely generated group, then the following are equivalent:
> (1) $\Gamma$ is hyperfinitely Hilbert--Schmidt stable. (2) Every von Neumann amenable
> character of $\Gamma$ is a limit of finite dimensional traces.

By (A1), condition (2) holds.

## Lemma L: exact lifting of finite-dimensional subalgebras

**Statement.** Let `A = ⊕_{i≤k} M_{k_i}` and let `θ : A → M^ω` be a *-homomorphism. Then
for `ω`-almost every `n` there are *-homomorphisms `θ_n : A → M_{d_n}` such that
`(θ_n(x))_n` represents `θ(x)` for every `x`.

**Proof.**
1. **Orthogonal projections.**
   - Pick distinct `λ_{i,a} ∈ [1,2]`, set `h = Σ λ_{i,a} θ(e^i_{aa})`, and lift `h` to
     self-adjoint `h_n` with `||h_n|| ≤ 2`.
   - With `δ` a third of the minimal gap of `{0} ∪ {λ_{i,a}}` and
     `J = (λ_{i,a} − δ, λ_{i,a} + δ)`, put `q^{i,a}_n = χ_J(h_n)`.
   - Take `f` continuous, equal to 1 on `[λ − δ/2, λ + δ/2]` and 0 off `J`. Take
     `0 ≤ g ≤ 1` continuous, equal to 1 on `J̄ ∖ (λ − δ/2, λ + δ/2)` and 0 near
     `spec(h) ⊂ {0} ∪ {λ's}`.
   - Then `f(h_n)` represents `f(h) = θ(e^i_{aa})`, and
     `||χ_J(h_n) − f(h_n)||_2² ≤ tr g(h_n) → τ(g(h)) = 0` along `ω`.
   - So the `q^{i,a}_n` are pairwise orthogonal projections representing `θ(e^i_{aa})`.
2. **Equal ranks.** `lim_ω (rank q^{i,a}_n − rank q^{i,b}_n)/d_n = 0`. Shrinking each
   `q^{i,a}_n` to rank `m^i_n = min_a rank q^{i,a}_n` changes nothing in `M^ω`.
3. **Partial isometries.**
   - Lift `θ(e^i_{a1})` to `x_n` and set `y_n = q^{i,a}_n x_n q^{i,1}_n`.
   - Along `ω`, `||y_n*y_n − q^{i,1}_n||_2 → 0`. Hence `|| |y_n| − q^{i,1}_n ||_2 → 0`,
     since `|√μ − 1| ≤ |μ − 1|`.
   - Write `y_n = v_n|y_n|`, with `s_n` the support of `|y_n|`. Zero eigenvalues are
     counted in the last norm, so `||q^{i,1}_n − s_n||_2 → 0`, and `v_n` represents
     `θ(e^i_{a1})`.
   - Extend `v_n` by an isometry from `q^{i,1}_n − s_n` onto `q^{i,a}_n − v_nv_n*`, which
     has equal rank. This gives `w^{i,a}_n` with `w*w = q^{i,1}_n` and `ww* = q^{i,a}_n`,
     still representing `θ(e^i_{a1})`. Put `w^{i,1}_n = q^{i,1}_n`.
4. **Matrix units.** `θ_n(e^i_{ab}) := w^{i,a}_n (w^{i,b}_n)*` is an exact system of
   matrix units representing `θ(e^i_{ab})`. ∎

## (A3)

Enumerate `Γ = {g_1, g_2, …}`. For maps `σ_n : Γ → U(d_n)` let `e_n` be the infimum, over
genuine `ρ` on `D ≥ d_n` (`D = d_n` in the strict case), of
`(D/d_n − 1) + Σ_j 2^{-j} min(1, ||σ_n(g_j) − Pρ(g_j)P||_2)`. A sequence is correctable iff
`e_n → 0`, and correctable along `ω` iff `lim_ω e_n = 0`.

**Forward direction.** Suppose `σ` is an asymptotic representation along `ω` with
`lim_ω e_n = ε > 0`.
- For each `K`, the set of `n` with `e_n > ε/2` and all defects
  `||σ_n(g_ig_j) − σ_n(g_i)σ_n(g_j)||_2 < 1/K` for `i, j ≤ K` lies in `ω`, so it is infinite.
- Pick increasing `n_K` in these sets. Then `(σ_{n_K})_K` is an asymptotic representation
  with `e ≥ ε/2`, which contradicts stability.

**Converse.**

0. **Ultrafilters suffice.** If an asymptotic representation is not correctable, `e_n ≥ ε`
   on an infinite set, and a free ultrafilter containing that set sees no correction.
   So it suffices to correct each `σ` along each `ω`, and every asymptotic representation
   is one along each `ω`.
1. **Split.** Let `N = N_ω` and let `z` be the largest central projection of `N` with `Nz`
   injective. It exists by Zorn, since products of injective algebras are injective.
   Then `N(1−z)` has no injective summand.
2. **Amenable part.**
   - If `τ(z) > 0`, then `φ_z = τ(σ^ω(·)z)/τ(z)` is a normalized trace whose GNS algebra
     is `Nz`. By (A1), `Nz = ⊕_{i∈I} M_{k_i}`, with blocks `z_i` and genuine
     representations `ρ_i = σ^ω(·)z_i`.
   - Choose finite `I_m ⊂ I` with `τ(z − z^{(m)}) ≤ 1/m`, where
     `z^{(m)} = Σ_{I_m} z_i`, and apply Lemma L to `A_m = ⊕_{I_m} M_{k_i}`.
   - This gives projections `P^{(m)}_n` representing `z^{(m)}`, and genuine
     representations `ρ^{(m)}_n = θ^{(m)}_n(⊕ρ_i(·))` on `P^{(m)}_n C^{d_n}` representing
     `σ^ω(·) z^{(m)}`.
3. **Diagonal.** Let `p_n` represent `z`, and put
   `E^{(m)}_n = ||P^{(m)}_n − p_n||_2 + Σ_{j≤m} 2^{-j}(||P^{(m)}_n σ_n(g_j) P^{(m)}_n − ρ^{(m)}_n(g_j)||_2 + ||[P^{(m)}_n, σ_n(g_j)]||_2)`.
   - Then `lim_ω E^{(m)}_n ≤ m^{-1/2}`, so `U_m = U_{m−1} ∩ {n : E^{(m)}_n < 2m^{-1/2}}` lies in `ω`.
   - With `m(n) = max{m ≤ n : n ∈ U_m}`, `lim_ω m(n) = ∞`.
   - `P_n = P^{(m(n))}_n` represents `z`. `ρ'_n = ρ^{(m(n))}_n` is `ω`-close to `P_nσ_nP_n`,
     and `[P_n, σ_n(g)] → 0` along `ω`.
4. **The properly non-amenable part.** `Q_n = 1 − P_n` represents `1 − z`.
   - If `τ(1−z) = 0`, let `ρ''_n` be trivial on `Q_nC^{d_n}`.
   - Otherwise let `σ''_n(g)` be a unitary on `Q_nC^{d_n}` extending the polar part of
     `Q_nσ_n(g)Q_n`, as in Lemma L step 3. Then `||σ''_n(g) − Q_nσ_n(g)Q_n||_2 → 0` along
     `ω`, so `σ''` is an asymptotic representation along `ω` of dimension `q_n = rank Q_n`.
   - Its limit algebra is generated by `σ^ω(Γ)(1−z)` inside
     `(1−z)M^ω(1−z) = ∏^ω (Q_nM_{d_n}Q_n)`. That algebra is `N(1−z)`, which has no
     injective summand.
   - The hypothesis gives genuine `ρ''_n` on `D''_n ≥ q_n` (resp. `= q_n`) with
     `lim_ω D''_n/q_n = 1` and `lim_ω ||σ''_n(g) − P''ρ''_n(g)P''||_{2,q_n} = 0`.
5. **Assemble.** Take `ρ_n = ρ'_n ⊕ ρ''_n`. Since `||σ − (PσP + QσQ)||_2 ≤ 2||[P,σ]||_2`,
   the estimates give `lim_ω ||σ_n(g) − P_nρ_n(g)P_n||_2 = 0`, with `lim_ω D_n/d_n = 1`
   (resp. `D_n = d_n`). ∎
