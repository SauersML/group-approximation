---
rg: 2
id: leavitt-resolvent-ring-is-fp-simple-of-char-zero-proof
kind: route
title: Apply the Leavitt--Nekrashevych completion criteria to the resolvent ring
target: leavitt-resolvent-ring-is-fp-simple-of-char-zero
requires:
  - leavitt-nekrashevych-completion-simplicity-criterion
  - leavitt-nekrashevych-completion-embeds-and-is-fp
---

Lane proof, refereed PASS by gq-referee-a, gq-referee-b and gq-referee-c. Write `R = R_L`, `P = s_1 t_1`,
`E = s_2 t_2 = 1 - P`.

## 1. Commutation and resolvents
- From `N = N(P + E)` and `N s_2 = 0` we get `N = s_1 (N+1) t_1`. Hence
  `t_1 N = (N+1) t_1`, and `NP = PN = N`, `NE = EN = 0`.
- Inductively `(N+c) s_1 = s_1 (N+c+1)` and `t_1 (N+c) s_1 = N + c + 1` for `c ∈ Z`.
- Put `A_1 = A` and `A_c = t_1 A_(c-1) s_1`. Then `A_c` is a two-sided inverse of
  `N + c` for `c >= 1`. By induction:
  `A_c (N+c) = t_1 A_(c-1) P (N+c-1) s_1 = t_1 A_(c-1)(N+c-1) P s_1 = t_1 s_1 = 1`,
  using that `P` commutes with `N`, hence with `A_(c-1)`. The other side is the same.
  All `A_c` commute with `N` and with each other.

## 2. Q ⊆ R
Put `u_m = t_2 t_1^(m-1) A s_1^(m-1) s_2`. Since `N s_2 = 0`, `(N+m) s_2 = m s_2`, and
`(N+1) s_1^(m-1) = s_1^(m-1)(N+m)` by §1. So

    u_m · m = t_2 t_1^(m-1) A s_1^(m-1) (N+m) s_2 = t_2 t_1^(m-1) A (N+1) s_1^(m-1) s_2
            = t_2 t_1^(m-1) s_1^(m-1) s_2 = 1.

`m` is central, so every positive integer is a unit, `R` is a `Q`-algebra, and `Q -> R`
is injective once `R ≠ 0` (§5).

## 3. R ≅ O_ψ
Let `B = Q[N][(N+c)^(-1) : c >= 1]` and `ψ(f) = diag(f(N+1), f(0))`.
- `ψ` is a unital `Q`-algebra homomorphism `B -> M_2(B)`: shift and evaluation at `0`
  are homomorphisms, and `f(0) ∈ Q` because all poles lie at negative integers.
- `ψ` is injective, since `f(N+1) = 0` forces `f = 0`.

Maps in both directions:
- **`O_ψ -> R`.** `Q[N] -> R`, `N ↦ N`, sends each `N + c` (`c >= 1`) to the unit `N + c`
  with inverse `A_c` (§1, §2), so it extends to `φ: B -> R`. The map
  `κ(b) = s_1 φ(b(N+1)) t_1 + s_2 φ(b(0)) t_2` is a unital ring homomorphism, since
  `t_i s_j = δ_ij`. It agrees with `φ` on `N` (§1), hence on `Q[N]`, hence on the
  localization `B`. So covariance holds for all `b ∈ B`, and `φ` together with
  `s_i, t_i` defines `O_ψ -> R`.
- **`R -> O_ψ`.** Send `s_i, t_i` to themselves, `N ↦ N` and `A ↦ (N+1)^(-1) ∈ B`.
  Covariance for `N` reads `N = s_1(N+1)t_1`, which gives `N s_1 = s_1(N+1)` and
  `N s_2 = 0`. The other relations are clear.
- Both composites fix the generators. Note `(N+c)^(-1) ↦ A_c ↦ t_1^(c-1)(N+1)^(-1)s_1^(c-1)`,
  which equals `(N+c)^(-1)` in `O_ψ` by covariance.

So `R ≅ O_ψ`.

## 4. ψ-minimality
Let `I` be a nonzero ψ-saturated ideal and `0 ≠ b ∈ I`. Then `ψ(b)_(ii) ∈ I`, so
`b(N+1) ∈ I` and `b(0) ∈ I`. Iterating, `b(k) ∈ I` for all `k >= 0`. A nonzero rational
function in `B` vanishes at only finitely many `k >= 0`, so `I` contains a nonzero
rational constant, and `I = B`.

## 5. Aperiodicity
Let `y ∈ O_k`, `k > 0`, commute with the core `C`. Follow part 4 of the criterion's proof.
- **Level `L`.** Write `y = Σ_(|μ|=L+k, |ν|=L) s_μ Y_(μν) t_ν` with coefficients in `B`,
  unique by part 1 of the criterion. Commuting with the matrix units
  `s_a t_b ∈ C` (`|a| = |b| = L`) gives `y = Σ_(|ν|=L, |ω|=k) s_(νω) w_ω t_ν` with
  `w_ω ∈ B`.
- **Level `L + j`.** Padding with the diagonal `ψ` turns `s_(νω) w_ω t_ν` into
  `Σ_(|u|=j) s_(νωu) ψ_u(w_ω) t_(νu)`. Here `ψ_u` is the composite along `u`, and the
  index pairs are distinct. The same comparison at level `L + j` forces
  `ψ_u(w_ω) = 0` unless `ωu = uω'` for some `ω'`, that is, unless `u` is the length-`j`
  prefix of `ω^∞`.
- **Values at integers.** For `u = 1^a 2 x`, `ψ_u(b) = b(a)`, a constant: `a` shifts,
  evaluation at `0`, then `ψ_i(c) = c` on constants. Of the two words `1^a 2 1` and
  `1^a 2 2`, at most one is a prefix of `ω^∞`. So `w_ω(a) = 0` for every `a >= 0`, hence
  `w_ω = 0` and `y = 0`.
- **`k < 0`.** The anti-automorphism `s_i <-> t_i`, identity on `B`, is well defined
  because `ψ` is diagonal and `B` is commutative. It fixes `C` and maps `O_k` to
  `O_(-k)`.

## 6. Conclusion
- `R ≅ O_ψ` is simple, by the criterion, from §4 and §5.
- `R ≠ 0`, and `B` embeds in `R`: in the model on `Q^(X)` (see the claim), `b ∈ B` acts on
  `e_ξ` by the scalar `b(ℓ)`, where `ℓ` is the number of leading 1's of `ξ`. Every `ℓ >= 0`
  occurs, so the model is faithful on `B` (referee b, A2). This also gives part 2 of
  `leavitt-nekrashevych-completion-embeds-and-is-fp`, the only part of that node used here,
  without its general argument. So `Q ⊆ R` (§2).
- `M_2(R) ≅ R` via `(x_ij) ↦ Σ s_i x_ij t_j`, so `R ≅ R^n` as modules and `M_n(R) ≅ R`
  for all `n >= 1`.
- `GL_n(Q)` embeds in `SL_(n+2)(Q)` by `g ↦ diag(g, det(g)^(-1), 1)`. `SL_(n+2)(Q)` is
  perfect and lies in `GL_(n+2)(R) ≅ R^x`. So `GL_n(Q) <= [R^x, R^x]`, and no nontrivial
  element of it is central there: central elements commute with `SL_(n+2)(Q)`, hence
  are scalar in `M_(n+2)(Q)`. ∎
