# States on the ternary anti-central summand: sources and support filters

Lane `gk-l3-state`, 2026-09-12. Supports `anti-central-rank-models-kill-ternary-corner-witnesses`.

## 0. Setup

- `R = L_(F_3)(1,2)`, `G = R^x`, and `z = −1`, a central involution of `G`.
- `S = F_3[G]`, `eps_± = (1 ± [z])/2 = 2(1 ± [z])` (in characteristic three `1/2 = 2`), and `S_- = eps_- S`.
- `w = s0 t1 + s1 t0`, `d = s0 t0 − s1 t1`, `e = 2(1 + [w])`, and `e_- = eps_- e`.
- The target `ternary-anti-invariant-swap-corner-is-full` asks for `b, c` in `S_-` with
  `c e_- b = eps_-`.
- By `anti-central-state-obstruction-equals-stable-finiteness` and
  `twisted-leavitt-corner-fullness-equals-absence-of-k0-states`, the target holds exactly when
  `(K_0(S_-), [eps_-])` has no state.

This artifact constructs states from rank models of subgroups. Sections 1–3 give the theorem and its
consequences.

## 1. The halving inside a subgroup containing w, d, z

**Lemma 1.1.** In `G`, `w^2 = d^2 = 1` and `d w d^-1 = z w`.

*Proof.* With `t_i s_j = δ_ij`:
- `w^2 = s0 t1 s0 t1 + s0 t1 s1 t0 + s1 t0 s0 t1 + s1 t0 s1 t0 = s0 t0 + s1 t1 = 1`;
- `d^2 = s0 t0 + s1 t1 = 1`, since the cross terms vanish;
- `(s0 t0 − s1 t1)(s0 t1 + s1 t0) = s0 t1 − s1 t0`;
- `(s0 t1 − s1 t0)(s0 t0 − s1 t1) = −s0 t1 − s1 t0 = −w`.

So `d w d = −w = z w`, and `d^-1 = d`. QED

So `<w, d>` is dihedral of order eight with centre `<z>`, since `(wd)^2 = z`.

**Lemma 1.2.** Let `Γ <= G` contain `z`, `w` and `d`, and put `S_Γ = eps_- F_3[Γ]`.
- `e_-` is an idempotent of `S_Γ`.
- `[d] e_- [d]^-1 = eps_- − e_-`.
- `e_- (eps_- − e_-) = 0`.

So `eps_- = e_- ⊕ (eps_- − e_-)` with the two summands algebraically equivalent.

*Proof.*
- `e^2 = 4(1 + 2[w] + [w]^2) = 8(1 + [w]) = 2(1 + [w]) = e`, using `[w]^2 = 1` and `8 = 2` in `F_3`.
- `[d][w][d]^-1 = [z][w]`, and `eps_- [z] = −eps_-`. So `[d] e_- [d]^-1 = eps_- · 2(1 − [w])`.
- Adding gives `e_- + [d] e_- [d]^-1 = eps_- · 4 = eps_-`.
- Orthogonality follows from `e_-^2 = e_-`. QED

## 2. Anti-central rank models give states

A *rank algebra* here is an `F_3`-algebra `M` with a Sylvester rank function `ρ` such that `ρ(p) > 0`
for every nonzero idempotent `p`. Examples: `M_n(k)` with normalized rank, and a rank ultraproduct
`prod_ω M_(n_i)(k) / ker ρ` over a field `k` of characteristic three.

**Theorem 2.1.** Let `Γ <= G` contain `z`, `w` and `d`. Let `σ : Γ -> M^x` be a group homomorphism
into the units of a rank algebra, with `σ(z) != 1`. Then:
- (a) `f = 2(1 − σ(z))` is a nonzero idempotent commuting with `σ(Γ)`;
- (b) `x -> σ(x) f` extends to a unital ring homomorphism `φ : S_Γ -> fMf`;
- (c) `s([p]) = ρ(φ(p)) / ρ(f)`, on idempotent matrices `p` over `S_Γ`, is a state on
  `(K_0(S_Γ), [eps_-])`;
- (d) no `b, c` in `S_Γ` satisfy `c e_- b = eps_-`.

*Proof.*
- (a) `σ(z)^2 = 1`, so `f^2 = 4(2 − 2σ(z)) = 8(1 − σ(z)) = f`. Since `2` is invertible, `f = 0`
  exactly when `σ(z) = 1`. `σ(z)` commutes with `σ(Γ)` because `z` is central.
- (b) `σ(g) f` is a unit of `fMf` with inverse `σ(g^-1) f`, so `g -> σ(g) f` is a homomorphism
  `Γ -> (fMf)^x`, and it extends linearly to `F_3[Γ]`. Also `σ(z) f = 2(σ(z) − 1) = −f`. So `[z]`
  goes to `−f`, `eps_- = 2(1 − [z])` goes to `2(f + f) = f`, and `eps_+` goes to `0`. Restricted to
  `S_Γ`, the map is unital into `fMf`.
- (c) `ρ` extends to matrices over `fMf` as the rank of block matrices, and `ρ(f) > 0`.
  - On idempotents it is additive over orthogonal sums.
  - It is invariant under algebraic equivalence: if `p = xy` and `q = yx` with `x` in `pMq` and `y`
    in `qMp`, then `ρ(p) <= ρ(x) = ρ(xq) = ρ(xyx) <= ρ(q)`, and symmetrically.
  - Composing with `φ` gives a monoid homomorphism from `V(S_Γ)` to `R_(>=0)` sending `[eps_-]` to `1`.
- (d) Suppose `c e_- b = eps_-`, and put `x = c e_-`, `y = e_- b`.
  - Then `xy = eps_-`, and `p = yx = e_- b c e_-` is an idempotent with `p e_- = e_- p = p`.
  - So `s(eps_-) = s(p) <= s(e_-)`.
  - By Lemma 1.2, `s(e_-) = s(eps_- − e_-)` and the two sum to `s(eps_-) = 1`, so `s(e_-) = 1/2`.
  - This gives `1 <= 1/2`. QED

## 3. Consequences

**Corollary 3.1 (support filter).** Suppose `b, c` in `S_-` satisfy `c e_- b = eps_-`, and put
`Γ = <z, w, d, supp b, supp c>`. Then every homomorphism from `Γ` into the units of a rank algebra
sends `z` to `1`.
- Every finite-dimensional representation of `Γ` over a field of characteristic three kills `z`.
- Every finite quotient of `Γ` kills `z` (apply its regular representation over `F_3`). So `z` lies in
  the finite residual of `Γ`, and `Γ` is not residually finite.

*Proof.* `b` and `c` lie in `S_Γ`, because `eps_-` is in `F_3[Γ]` and `b = eps_- b`. Apply
Theorem 2.1 (d). QED

**Corollary 3.2 (comparison).** Corollary 3.1 implies `ternary-corner-witnesses-need-non-linear-sofic-support`.
- An `F_3`-linear sofic approximation of `Γ` separating `z` from `1` gives a homomorphism into a rank
  ultraproduct with `σ(z) != 1`.
- Corollary 3.1 excludes more: non-linear-sofic groups that have a single rank model moving `z`, for
  example any group with a finite quotient in which `z` survives.

**Corollary 3.3 (global form).** If `G` has a homomorphism into the units of a characteristic-three rank
ultraproduct with `σ(z) != 1`, then `ternary-anti-invariant-swap-corner-is-full` is false.
- Such a `σ` is injective. `G` is perfect and `G/<z>` is simple (`leavitt-gl-equals-el-and-perfect-unit-group`,
  `odd-leavitt-unit-groups-mod-scalars-are-fp-simple`), so a normal subgroup not killing `z` is trivial.
  This remark is not used in the proof of Theorem 2.1.
- So the counterexample target survives only if every characteristic-three rank model of `G` factors
  through `G/<z>`.
- Family R's instance claim `leavitt-el3-rank-models-over-finite-fields-are-trivial` at `p = 3` would
  make every such model trivial, which is consistent with the target. A single rank model of `G` moving
  `z` refutes it.

**What Sections 1–3 do not settle.**
- Whether some finitely generated `Γ` containing `z`, `w`, `d`, with `z` in every rank model's kernel,
  carries the corner equation.
- The signed Thompson group `E ⋊ V` of gk-l3-free has no finite-dimensional representations
  (`signed-thompson-group-has-no-finite-dimensional-representations`), so the finite-dimensional part of
  Corollary 3.1 says nothing there. A rank model of `E ⋊ V` moving `z` would need rank-metric
  approximation data for `V`, which is open.
