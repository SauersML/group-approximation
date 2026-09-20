---
rg: 2
id: fpbs-mal-seed-density-towers-over-orbit-gapped-bases-proof
kind: route
title: Run the random-lift tower of the uniform witness from the base B instead of a point; the invariant functions of a good lift are pulled back from the level below, so the orbit-wise top eigenvalue is the maximum of the old one and the new-part norm, and the percolation bound is applied orbit by orbit
target: fpbs-mal-seed-density-towers-over-orbit-gapped-bases
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - fpbs-mal-sym-levels-embed-orbits-at-every-depth
artifacts:
  - experiments/fpbs-random-lift-twisted-gap-2026-09-17/random_lift_gap.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/spectral_sym.py
---

**Complete route, modulo the two imported theorems (K) and (SC).** They are
quoted verbatim in §0 of `fpbs-mal-twisted-level-seed-density-random-lift-proof`
and are the same imports; (SC) is repeated below.

That route proves the case `B = {pt}`. Its §1 (Lemma 1), §3 (the lift and the
old/new decomposition), §4 (Lemma 4 and `‖P_j(s, s^*)‖ = ρ`) and Lemma 6 are
stated and proved there for an **arbitrary** finite `L`-set `Q`, and are used
here unchanged. What changes is:
- the spectral quantity, which is now the orbit-wise top eigenvalue `μ_j`;
- Proposition 3, which is applied orbit by orbit;
- transitivity, which is now inherited from the base.

**(SC), verbatim.** C.-F. Chen, J. Garza-Vargas, J. A. Tropp,
R. van Handel, *A new approach to strong convergence*, Ann. of Math. 203
(2026); arXiv 2405.16026v3, Theorem 3.9: "Let d ≥ 2, and let P ∈ MD(C) ⊗
C⟨s, s∗⟩ be any self-adjoint noncommutative polynomial of degree q0. Then we
have P[‖P(S^N, S^N∗)‖ ≥ ‖P(s, s∗)‖ + ε] ≲ (D/N)(Kq0 log d/ε)^8 log(eK/ε) for
all ε < K − ‖P(s, s∗)‖, where K = ‖P‖_{MD(C)⊗C∗(Fd)}." Only the consequence
`P[‖P(S^N)‖ ≥ ‖P(s)‖ + ε] → 0` as `N → ∞` is used.

## 1. Proposition 3′: the percolation bound, orbit by orbit

**Additivity.** Every triple `T_y = (y, y·a, y·t_j)` lies in the
`L_j`-orbit of `y`. So the 2-of-3 closure of `S` meets each orbit `O` in the
closure of `S ∩ O` inside `O`. Hence `S` percolates `Q^{(j)}` iff `S ∩ O`
percolates `O` for every `O`, and `r(Q^{(j)}) = Σ_O r(O)`.

**Proposition 3′.** Let `λ' ∈ [−1, 1]` with `λ' ≥ μ_j(Q)`. Then
`r(Q^{(j)}) ≥ (1 − λ')|Q|/6`.

*Proof.* By additivity, it suffices to show `r(O) ≥ (1 − λ')n/6` for one
orbit `O`, where `n = |O|`.
- `n = 1`: `r(O) = 1 ≥ (1 − λ')/6`, since `1 − λ' ≤ 2`.
- `n ≥ 2`: Lemma 1 of the cited route uses only the triples, so it holds
  inside `O`. Lemma 2 holds inside `O` with `λ'` in place of `λ_j(Q)`: its
  proof writes `1_A = (m/n)1_O + f` with `f ∈ ℓ²_0(O)`, and uses only
  `⟨f, M_j f⟩ ≤ λ'‖f‖²`. That inequality holds because `λ' ≥ μ_j(Q)`, and
  `M_j` preserves `ℓ²(O)`. Now run the proof of Proposition 3 with
  `m = ⌊n/2⌋`:
  - if `|S| > m`, then `|S| > n/3 ≥ (1 − λ')n/6`, using `1 − λ' ≤ 2`;
  - otherwise `|S| ≥ (1 − λ')m(1 − m/n) ≥ (1 − λ')n/6`, using `1 − λ' ≥ 0`.

  ∎

## 2. Lemma 5′: one good lift keeps the orbit gap

Let `Q̃ = Q × [N]` be a lift as in §3 of the cited route, with
`ℓ²(Q̃) = Old ⊕ New`, where `Old = ℓ²(Q) ⊗ 1_N` and
`New = ℓ²(Q) ⊗ 1_N^⊥`. Both parts are invariant under every `U_g`.
`f ↦ f ⊗ 1_N/√N` is a unitary `ℓ²(Q) → Old` intertwining the two actions,
and `M_j|New = P_j(S^N)`.

**Lemma 5′.** Suppose `‖P_j(S^N)‖ ≤ λ_0 < 1`. Then:
- (a) `I_j(Q̃) = I_j(Q) ⊗ 1_N`;
- (b) `μ_j(Q̃) ≤ max(μ_j(Q), λ_0)`;
- (c) if `L` acts transitively on `Q`, it acts transitively on `Q̃`.

*Proof.*
- (a) `M_j f = f` iff `U_a f = f` and `U_{t_j} f = f`. Indeed, if
  `⟨M_j f, f⟩ = ‖f‖²`, then each of the four unitaries `U` has
  `Re⟨U f, f⟩ = ‖f‖²`, which forces `U f = f`. So `I_j` is the
  1-eigenspace of `M_j`. Both parts are invariant, so this eigenspace is
  the sum of the 1-eigenspaces of `M_j|Old` and `M_j|New`. The second is
  `0`, since `‖M_j|New‖ ≤ λ_0 < 1`. The first is `I_j(Q) ⊗ 1_N`.
- (b) By (a), `I_j(Q̃)^⊥ = (I_j(Q)^⊥ ⊗ 1_N) ⊕ New`. Both summands are
  invariant under the self-adjoint `M_j`. So the top of its spectrum there is
  the larger of the two tops. On the first summand it is `μ_j(Q)`, by the
  intertwiner. On `New` it is at most `‖P_j(S^N)‖ ≤ λ_0`. (If
  `I_j(Q̃)^⊥ = 0`, then `μ_j(Q̃) = −1` and there is nothing to prove.)
- (c) An `L`-invariant `f` on `Q̃` is `L_j`-invariant. By (a),
  `f = g ⊗ 1_N` with `g` on `Q`. Then `U_s f = (U_s g) ⊗ 1_N` for
  `s = a, b`, so `g` is `L`-invariant, hence constant. So `f` is constant,
  and `Q̃` is transitive. ∎

**Lemma 5 (probability), unchanged.** `P[‖P_j(S^N)‖ > λ_0] → 0` as
`N → ∞`. The proof in the cited route uses only §3–§4 and (SC), and §4
holds for every finite `Q`.

## 3. The tower over B

Fix `j`, `λ_0 ∈ (ρ, 1)` and `B` as in the target. Enumerate the nontrivial
elements of `L` as `w_1, w_2, …`, with lengths `ℓ_1, ℓ_2, …`. Put `Q_0 = B`.

Given `Q_m`, transitive with `μ_j(Q_m) ≤ λ_0`, choose `N = N_{m+1} ≥ 2` so
large that:
- `P[‖P_j(S^N)‖ > λ_0] < 1/2`, by Lemma 5 applied to `Q = Q_m`;
- `(m+1)·ℓ_i²/(N − ℓ_i) < 1/(4(m+1))` for all `i ≤ m+1`.

As in §6 of the cited route, Lemma 6 and Markov's inequality then give, with
probability `> 1/4`, a lift with:
- `‖P_j(S^N)‖ ≤ λ_0`;
- `fix_{Q̃}(w_i) ≤ 1/(m+1)` for every `i ≤ m+1`.

Let `Q_{m+1}` be such a lift. Its projection to `Q_m` is `L`-equivariant and
onto. By Lemma 5′:
- `μ_j(Q_{m+1}) ≤ max(μ_j(Q_m), λ_0) = λ_0`;
- `Q_{m+1}` is transitive.

So the induction continues, and every level is a transitive cover of `B`.

- **Essential freeness.** Let `X = lim Q_m` with the inverse-limit measure.
  It is non-atomic, since `|Q_m| ≥ 2^m`. For each `i`,
  `ν(Fix_X(w_i)) = lim_m fix_{Q_m}(w_i)`, where `ν` is the measure,, a non-increasing limit by the
  deterministic part of Lemma 6. It is at most `1/m` for every `m ≥ i`, so
  it is `0`.
- **Density.** By Proposition 3′ with `λ' = λ_0`,
  `r(Q_m^{(j)}) ≥ (1 − λ_0)|Q_m|/6` for every `m`, including `m = 0`, where
  `μ_j(B) ≤ λ_0` is the hypothesis. ∎

## 4. The instance B_j

By item 4 of [[fpbs-mal-sym-levels-embed-orbits-at-every-depth]], the
`L_j`-orbits of `B_j` are `{g, gα}`, with `U_a = U_{t_j}` acting on
`ℓ²({g, gα})` as the swap. On `ℓ²_0` of the orbit, the swap is `−1`, so
`M_j = −1` there and `μ_j(B_j) = −1 ≤ λ_0`. `B_j` is transitive, since
`(0 1)` and `(0 1 ⋯ j+1)` generate `Sym(j+2)`. The target applies with
`λ_0 = 0.9` and gives density `1/60` at every depth.

## 5. Relation to the point tower

With `B = {pt}`, `μ_j(pt) = −1`, and the construction is the tower of
`fpbs-mal-twisted-level-seed-density-random-lift-proof`. The only
difference is that `μ_j` is used in place of the norm `λ_j` on `ℓ²_0(Q)`.
Over a point, transitivity makes `I_j^⊥ = ℓ²_0`, and the proof of
Proposition 3 only ever used the top of the spectrum.
