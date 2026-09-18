---
rg: 2
id: kk-witness-counterexample-locus-is-marked-closed-proof
kind: route
title: Reduced norms are suprema of finite-radius moments, a spectral gap is a norm inequality, and compactness of the space of marked groups does the rest
target: kk-witness-counterexample-locus-is-marked-closed
requires:
  - reduced-projection-iff-gapped-spectral-measure
  - hyperbolic-bcc-finite-wreath-products
artifacts:
  - experiments/kk-marked-compactness-2026-09-17/one_generator_torsion_bound.py
  - experiments/kk-marked-compactness-2026-09-17/one_generator_torsion_bound.out
---

Notation as in the claim. For `x = Σ x_w w ∈ C[F]` and `N ∈ M_d` put
`τ_N(x) = Σ_{w ∈ N} x_w`. This is the canonical trace of `λ_N(x)` in `C*_r(G_N)`, and it
depends only on `N ∩ supp(x)`, a finite set of words. So **`N ↦ τ_N(x)` is locally constant**
on `M_d`. Write `B_r ⊆ F` for the words of length `≤ r`, and
`U_r(N) = { N' ∈ M_d : N' ∩ B_r = N ∩ B_r }` for the basic clopen cylinders.

`M_d` is closed in `2^F`: the conditions `1 ∈ N`, `(u, v ∈ N ⇒ uv^{-1} ∈ N)` and
`(u ∈ N ⇒ g u g^{-1} ∈ N)` are each clopen, and a violation is witnessed by finitely many words,
so `M_d` is a `Π^0_1` class. `TF_d` is closed and `Π^0_1` for the same reason: it is the
intersection over `w ∈ F`, `m ≥ 1` of the clopen sets `{ w^m ∉ N or w ∈ N }`.

## Theorem A

**1. Lower semicontinuity.** Let `x ∈ C[F]` and `T = λ_N(x*x) ≥ 0` in the group von Neumann
algebra `L(G_N)`, with its faithful normal tracial state `τ`. Let `ν` be the spectral measure of
`T` for `τ`, a probability measure on `[0, ‖T‖]`. Since `τ` is faithful, `supp ν = spec T`, so
`max supp ν = ‖T‖`. The `L^k(ν)` norms of the function `t` are nondecreasing in `k` (Jensen,
`ν` is a probability measure) and converge to `max supp ν`. Hence

```text
‖λ_N(x)‖^2 = ‖T‖ = sup_k  τ_N((x*x)^k)^(1/k).
```

Each term is locally constant in `N`, so the supremum is lower semicontinuous. Moreover
`{N : ‖λ_N(x)‖ > R}` is the union over `k` of the clopen sets
`{N : τ_N((x*x)^k) > R^(2k)}`, and for `x ∈ Q[i][F]` and rational `R` these can be enumerated
together with finite-radius evidence.

**2. `P_ω` is closed and `Π^0_1`.** Let `A` be a rational number with `A ≥ ‖a‖_{ℓ^1(F)}`, so
`‖λ_N(a)‖ ≤ A` for every `N`. (The `ℓ^1` norm itself may be irrational for Gaussian-rational
coefficients. A rational upper bound keeps every comparison below exact.)

*Gap.* Put `y = (a - c)^2 - ε^2 ∈ Q[i][F]` and `β = (A + |c|)^2 + ε^2 ∈ Q`, so `‖λ_N(y)‖ ≤ β`.
The spectrum of `λ_N(a)` misses `(c-ε, c+ε)` iff `(t-c)^2 - ε^2 ≥ 0` on it, iff `λ_N(y) ≥ 0`.
For self-adjoint `z` with `‖z‖ ≤ β`, the operator `β - z` is positive, and `z ≥ 0` iff
`spec(β - z) ⊆ [0, β]` iff `‖β - λ_N(y)‖ ≤ β`. So

```text
Gap_ω = { N : ‖λ_N(β - y)‖ ≤ β }
```

is closed by item 1, and its complement is enumerated by the evidence
`τ_N((β - y)^(2k)) > β^(2k)`.

*Trace.* The set `J = [-A, c-ε] ∪ [c+ε, A]` is a disjoint union of at most two closed
intervals, and `1_{t<c}` is continuous on `J`. Extend it continuously to `[-A, A]` and use
Weierstrass to pick `q_j ∈ Q[t]` with `|q_j(t) - 1_{t<c}| ≤ 1/j` on `J`. If `N ∈ Gap_ω` then
`spec λ_N(a) ⊆ J`, so `‖q_j(λ_N(a)) - χ_{(-∞,c)}(λ_N(a))‖ ≤ 1/j` and, `τ` being a state,

```text
| τ_N(q_j(a)) - μ_{a,N}((-∞,c)) | ≤ 1/j .
```

Hence

```text
P_ω = Gap_ω  ∩  ∩_j { N : τ_N(q_j(a)) ∈ [δ - 1/j, 1 - δ + 1/j] }.
```

(`⊆` by the estimate. `⊇`: on `Gap_ω` the conditions give
`μ ∈ [δ - 2/j, 1 - δ + 2/j]` for all `j`.) Every set on the right is closed, and the complement of
each is enumerated with finite evidence. So `P_ω` is closed and a `Π^0_1` class in `2^F`.

**3. Exhaustion.** If `N ∈ P_ω`, the spectrum of `λ_N(a)` misses `(c-ε, c+ε)`, so
`χ_{(-∞,c)}(λ_N(a))` is a continuous function of `λ_N(a)`, hence a projection of `C*_r(G_N)`,
with trace in `[δ, 1-δ]`. It is neither `0` nor `1`.

Conversely let `C*_r(G_N)` contain a projection other than `0, 1`. By
`reduced-projection-iff-gapped-spectral-measure` (items 1 ⇒ 2 and the supplement
`supp μ_a = spec(a)`), some self-adjoint `a_0 ∈ Z[i][G_N]` has disconnected spectrum. Pick
words representing its support and let `ã ∈ Z[i][F]` be the resulting lift; then
`a = (ã + ã*)/2 ∈ Q[i][F]` is self-adjoint with `λ_N(a) = a_0`. A compact subset of `R` that is
not connected is not an interval, so some rational `c` in `(min spec, max spec)` lies outside the
spectrum, together with a rational `ε`-neighbourhood. Both `(-∞, c)` and `(c, ∞)` meet
`spec = supp μ`, so `μ((-∞,c)) ∈ (0,1)` and a rational `δ` exists. So `N ∈ P_ω`.

Hence the KK locus is `M_d \ ∪_ω P_ω`, a countable intersection of open sets.

**4. Radius.** If `G_N` has no nontrivial projection, `N ∉ P_ω`. Either the gap fails, and then
`τ_N((β - y)^(2k)) > β^(2k)` for some `k`; or the gap holds and the trace is `0` or `1`, and then
for `j > 2/δ` the number `τ_N(q_j(a))` lies outside `[δ - 1/j, 1 - δ + 1/j]`. Either evidence is
a finite computation of `τ_N` on an element supported in some `B_r`, and it holds for every
`N' ∈ U_r(N)`. That gives `r(N, ω)`. With a solvable word problem, the evidence can be searched
for, and the search halts.

**5. Genericity.** In the compact metrizable `Y`, the KK locus is a `G_δ` (item 3) and dense by
hypothesis, so it is a dense `G_δ` (Baire). For `Y` the closure of the torsion-free hyperbolic
marked groups: `Y ⊆ TF_d` because `TF_d` is closed, and torsion-free hyperbolic groups have no
nontrivial reduced projection. Indeed, by `hyperbolic-bcc-finite-wreath-products` they satisfy
Baum--Connes with coefficients, in particular surjectivity of the assembly map, and Kaad--Proietti,
*Index theory on the Miščenko bundle*, Kyoto J. Math. 62 (2022), Corollary 1.6, as used in
`rank-one-bcc-implies-charzero-idempotent-proof`, gives only trivial idempotents for torsion-free
groups with surjective assembly map.

**6. Fast limits.** Let `N_i = ker(F -> G(i))`, and `N_∞ = ∪ N_i` the limit. If the
injectivity radius of `G(i-1) -> G(i)` is at least `r`, then `N_i ∩ B_r = N_{i-1} ∩ B_r`: a word
`w ∈ N_i` of length `≤ r` represents an element of the `r`-ball of `G(i-1)` that maps to `1`,
so it is `1`. With `r_i` nondecreasing, induction gives `N_j ∩ B_{r_i} = N_{i-1} ∩ B_{r_i}` for
all `j ≥ i`, hence `N_∞ ∩ B_{r_i} = N_{i-1} ∩ B_{r_i}`, i.e. `N_∞ ∈ U_{r_i}(N_{i-1})`. For
`k ≤ i` we have `U_{r_i}(N_{i-1}) ⊆ U_{r(N_{i-1}, ω_k)}(N_{i-1})`, which misses `P_{ω_k}` by
item 4. Every `k` is `≤` some `i`, so `N_∞ ∉ ∪ P_ω`, and item 3 concludes.

## Theorem B

**(ST) ⇒ (KK).** A torsion-free `d`-marked group has no element as in (ST), so it lies in no
`P_ω`, so it has no nontrivial projection by A.3. The root already reduces to finitely generated
groups.

**(KK) ⇒ (ST).** For `n ≥ 1` let `T_n` be the set of `N ∈ M_d` for which some `w ∈ B_n \ N`
has `w^m ∈ N` for some `1 ≤ m ≤ n`. It is clopen (finitely many clopen conditions), increasing
in `n`, and `∪ T_n` is the set of marked groups with torsion. Under (KK), every `N ∈ P_ω`
has torsion, so `P_ω ⊆ ∪ T_n`. `P_ω` is compact (A.2), hence `P_ω ⊆ T_n` for one `n = N_ω`.

**Π^0_2.** Fix `(d, ω)`. The set `C_ω = P_ω ∩ TF_d` is a `Π^0_1` class in `2^F`: there is
an enumeration of cylinders `[σ_1], [σ_2], ...` (finite partial assignments of words to
`∈ N` / `∉ N`) whose union is `2^F \ C_ω`, namely the finite evidence of A.2 together with
violations of normality and of torsion-freeness. `C_ω = ∅` iff, by compactness of `2^F`, some
finite list `[σ_1], ..., [σ_s]` already covers `2^F`, which is decidable for a given list. So
"`C_ω = ∅`" is `Σ^0_1`, and (KK), which is `∀ d ∀ ω : C_ω = ∅` by A.3, is `Π^0_2`.

**Low counterexamples.** If (KK) fails, some finitely generated torsion-free group has a
nontrivial projection. By A.3, `C_ω ≠ ∅` for some `(d, ω)`. By the low basis theorem
(Jockusch--Soare, *Π^0_1 classes and degrees of theories*, Trans. AMS 173 (1972), Theorem 2.1),
a nonempty `Π^0_1` class has a member `N` with `N' ≤_T 0'`. That `N` is the word problem of a
torsion-free `d`-marked counterexample.

## Calibration: `d = 1`

**Proposition 5.** Let `a = Σ_{|k| ≤ K} a_k s^k = a*` in `Q[i][F_1]`, `f(θ) = Σ a_k e^{ikθ}`
(real-valued), `L = Σ |k||a_k|`. If some `1`-marked group `G` lies in `P_ω` for
`ω = (a, c, ε, δ)`, then `G = Z/n` with `n ≤ π L / ε`. So `N_ω = ⌊π L / ε⌋` works in (ST), with
the torsion element `s` of length `1`.

*Proof.* The marked groups are `Z` (`N = 1`), and `Z/n` for `n ≥ 1`. For `Z`, Fourier
transform identifies `C*_r(Z)` with `C(T)`, and `spec a = f([0, 2π])` is an interval, so
`P_ω` fails. For `Z/n`, `C*_r(Z/n) ≅ C^n` through the characters, and `spec a` is
`{f(2πj/n) : 0 ≤ j < n}` with uniform measure. In `P_ω`, some `f(2πj_0/n) ≤ c - ε` and some
`f(2πj_1/n) ≥ c + ε` (the masses on both sides are at least `δ > 0`). `|f'| ≤ L`, so
consecutive values along `j_0, j_0 + 1, ..., j_1 (mod n)` differ by at most `2πL/n`. If
`2πL/n < 2ε`, one of them lies in `(c - ε, c + ε)`, contradicting the gap. So `n ≤ πL/ε`. ∎

The script `one_generator_torsion_bound.py` checks the equivalent inequality
`n · ε_max(n) ≤ πL` (`ε_max(n)` = the largest half-width of an internal gap of the spectrum over
`Z/n`) on 300 random Laurent polynomials with Gaussian-integer coefficients, degree `≤ 4`,
`n ≤ 400`; output in `one_generator_torsion_bound.out`.

The method reproduces the known necessity of the torsion hypothesis. Over `Z/n`,
`a = Σ_{j<n} s^j` is `n` times the averaging projection, and its gap is detected, with torsion
of length `1` and order `n`. It proves nothing false: A.5 applies only on closed families where
KK groups are dense, and item 3 is an equivalence.

## Isolated points

`Γ(3) ⊴ SL_3(Z)` is finitely presented (an arithmetic lattice), so for large `r` the cylinder
`U_r(N_{Γ(3)})` consists of marked quotients of `Γ(3)`. By the Margulis normal subgroup theorem
each normal subgroup of the higher-rank lattice `Γ(3)` is finite or of finite index. It is
torsion-free, so a proper quotient is finite and nontrivial (the generators stay nontrivial in the
cylinder), hence has torsion. So `Γ(3)` is isolated in `TF_d`, and A.5 says nothing about it.
