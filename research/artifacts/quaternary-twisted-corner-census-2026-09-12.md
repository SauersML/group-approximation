# The characteristic-two twisted corner at (q, d, m) = (4, 2, 3)

Lane `w3-corner-f4`, 2026-09-12. Supports the Cairn claims
`twisted-rank-models-kill-visible-cyclic-corner-witnesses` and
`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`, with their routes, and records a census
for `leavitt-visible-cyclic-corner-is-full-on-some-host` at the host `L_(F_4)(1,2)^x`.

## 0. Setup

- `F_4 = {0, 1, ω, ω²}` with `ω² + ω + 1 = 0`. `L = L_(F_4)(1,2)`, `G = L^x`, `A = F_4[G]`,
  `pi : A -> L` the evaluation. `Z = F_4^x · 1`, central of order 3.
- A ternary Leavitt family: `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, `t_1 = t0`, `t_2 = t0 t1`,
  `t_3 = t1 t1`. Then `t_i s_j = δ_ij` and `Σ s_i t_i = s0 t0 + s1 (s0 t0 + s1 t1) t1 = 1`.
- `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, the 3-cycle permutation unit (order 3, coefficients 0 and 1).
- `δ = ω s_1 t_1 + ω² s_2 t_2 + s_3 t_3`, a unit with `δ g δ^(-1) = ω g`.
- Since `3 = 1` in characteristic two, the scalar-character idempotent of the inclusion character is
  `eps_iota = [1] + ω² [ω] + ω [ω²]`, and the isotypic idempotents of `⟨g⟩` inside `A_iota` are
  `e_ψ = (1 + ψ(g)^(-1) [g] + ψ(g)^(-2) [g²]) eps_iota`, with `e_1 = (1 + [g] + [g²]) eps_iota`.
- By `cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`, conjugation by `[δ]` permutes the
  three `e_ψ` cyclically, `A_iota ≅ M_3(T)` with `T = e_1 A_iota e_1`, and the target is a unital
  3-pair Cohn family in `T`, equivalently `c' e_1 b' = eps_iota` in `A_iota`.

## 1. Census at this host

What each standard invariant says about `eps_iota ≲ e_1`:

1. **Augmentation.** `epsilon(eps_iota) = 1 + ω² + ω = 0`. Silent: it vanishes on the whole factor.
2. **Commutative quotients.** None, since `A_iota ≅ M_3(T)`.
3. **Canonical trace** (identity coefficient). `tau(eps_iota) = 1`. For `e_ψ`, `[g^k][λ]` is the
   identity only for `k = 0, λ = 1`, because `g` is not a scalar (`t_2 g s_1 = 1` while
   `t_2 λ s_1 = 0`). So `tau(e_ψ) = 1` as well. In characteristic two `tau(eps_iota) = 3 tau(e_1)`
   holds with `3 = 1`, and fullness only asks for `[e_1] = [eps_iota] + [f]` with `tau(f) = 0`.
   Silent.
4. **Lifted 2-adic trace.** The Teichmüller lifts give identity coefficients `t(eps_iota) = 1/3` and
   `t(e_ψ) = 1/9`, consistent with `[eps_iota] = 3 [e_1]`. A witness would give a class `[f]` with
   `t = 1/9 − 1/3 = −2/9`. So the complement idempotent of a witness is never a finite-subgroup
   projective (`lifted-trace-detects-finite-subgroup-projectives`), which is the same constraint the
   ternary corner has, and nothing more.
5. **Frobenius.** `Φ(a [x]) = a² [φ(x)]`, with `φ` the coefficientwise Frobenius of `L`, is a
   semilinear ring automorphism of `A`. It fixes `eps_iota` (`λ -> λ²` permutes `F_4^x`) and `e_1`
   (`g` has coefficients in `F_2`), and sends `δ` to `δ^(-1)`. So the solution set is Frobenius-stable.
6. **Finite-dimensional images.** On a representation where `Z` acts through a character `chi`, the
   idempotent `eps_iota` acts as `δ_(chi, iota)`. So a finite-dimensional image of `A_iota` needs a
   vector on which every scalar `λ` acts by `λ`. Excluding all such images needs `G/Z` simple and `G`
   perfect over `F_4`; main records simplicity mod scalars only for odd `q` and for prime fields
   (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`,
   `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`). So at `q = 4` this item is open.
   The subgroup `R^x = L_(F_2)(1,2)^x` acts trivially in every finite-dimensional representation,
   being infinite, simple and finitely generated (Malcev), but it does not contain the scalars `ω`.

Conclusion: at `(4, 2, 3)` the standard invariants are as silent as at `(3, 2, 2)`. The characteristic-
three trace no-go for binary Leavitt families does not transfer (it used `tau = 2` on the unit of
`S_-`); here `tau(eps_iota) = 1`, so a unital binary Leavitt family in `A_iota` is not excluded by the
trace.

## 2. Rank models with a visible scalar component (every twisted host)

**Theorem 2.1.** Let `q = p^r`, `d >= 2`, `m >= 2` admissible with `p ∤ m` and `m | q − 1`, and let `g`,
`δ` and `e_ψ` be as in the cyclic-twist theorem. Let `Γ <= G` contain `Z`, `g` and `δ`, and put
`S_Γ = eps_iota F_q[Γ]`. Suppose `σ : Γ -> M^x` is a group homomorphism into an `F_q`-algebra `M`
carrying a Sylvester matrix rank function `r` that is positive on nonzero idempotents, and that the
linear extension `σbar : F_q[Γ] -> M` has `σbar(eps_iota) != 0`. Then:

1. `(K_0(S_Γ), [eps_iota])` has a state;
2. there are no `b', c'` in `S_Γ` with `c' e_1 b' = eps_iota`.

*Proof.* `σbar` is an algebra homomorphism, so the `σbar(e_ψ)` are `m` orthogonal idempotents with sum
`σbar(eps_iota)`. Conjugation by `σ(δ)^j` carries `σbar(e_1)` to `σbar(e_ψ)`, so all have the same
rank, and `r(σbar(eps_iota)) = m · r(σbar(e_1)) > 0`.
(1) `s([P]) = r(σbar(P)) / r(σbar(eps_iota))`, for idempotent matrices `P` over `S_Γ`, is additive,
invariant under equivalence, nonnegative, and normalized at `eps_iota`.
(2) If `c' e_1 b' = eps_iota`, then `σbar(eps_iota) = σbar(c') σbar(e_1) σbar(b')`, so
`r(σbar(eps_iota)) <= r(σbar(e_1)) = r(σbar(eps_iota)) / m`, which forces `r(σbar(eps_iota)) = 0` and
contradicts positivity. QED

**Instances.** `(3, 2, 2)` is `anti-central-rank-models-kill-ternary-corner-witnesses` (there `g = w`,
`δ = d`, and `σbar(eps_-) != 0` means `σ(z) != 1` has a `−1`-eigenvector part). `(4, 2, 3)` is the
characteristic-two host of Section 0.

**Corollary 2.2 (support filter).** If `c' e_1 b' = eps_iota` in `A_iota`, then on
`Γ = ⟨Z, g, δ, supp b', supp c'⟩` every such `σ` has `σbar(eps_iota) = 0`. In particular every
finite-dimensional representation of `Γ` over a field containing `F_q` has no nonzero vector on which
each scalar `λ` acts by `λ`.

## 3. The binary untwisted corner ascends to this host

Over `F_2` there is no twist and one factor. Let `g` be the permutation unit of the ternary family of
Section 0 inside `R = L_(F_2)(1,2)`, and `e = 1 + [g] + [g²]`, an idempotent of `F_2[R^x]` (`1/3 = 1`).

**Proposition 3.1.**
1. The image equation holds: `b = s_1 + s_2 + s_3` and `c = t_1 + t_2 + t_3` give `c pi(e) b = 1` in `R`.
2. If `c e b = 1` in `F_2[R^x]`, then `F_2[R^x]` is not directly finite: `α = c e` and `β = e b` satisfy
   `α β = 1`, and `β α = 1` would give `e = e β α = β α = 1`, so `[g] = [g²]`, which is false.
3. `x -> x · eps_iota(4)` is a unital ring homomorphism `F_2[R^x] -> A_iota(4)`, because `R^x <= G`
   and `eps_iota(4)` is central. It sends `e` to `e_1`. So `c e b = 1` gives a solution of the twisted
   corner at `(4, 2, 3)`.
4. Consequently a state on `(K_0(A_iota(4)), [eps_iota])`, or a rank model as in Theorem 2.1 on a
   subgroup of `G` containing `Z`, `g`, `δ` and the supports of `b`, `c`, rules out fullness of `e` in
   `F_2[R^x]`, even though `F_2[R^x]` always carries the augmentation state.

*Proof.* (1): `pi(g) b = b` and `c b = Σ_(i,j) t_i s_j = 3 = 1`. (2) and (3) are one-line computations.
(4): the contrapositive of (3) with `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` and
Theorem 2.1. QED

So the binary corner `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` is a genuinely binary
Kaplansky target, sitting below both `leavitt-unit-group-algebra-not-directly-finite` and the
quaternary twisted corner.
