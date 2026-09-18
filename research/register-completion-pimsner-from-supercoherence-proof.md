---
rg: 2
id: register-completion-pimsner-from-supercoherence-proof
kind: route
title: Pick one spine isometry as t_+, identify R with a corner skew Laurent ring, and run ABC 3.6 and 7.2
target: register-completion-pimsner-from-supercoherence
requires:
  - abc-twisted-laurent-k-theory-fibration
  - eventually-rational-register-ring-is-regular-supercoherent
---

Lane proof, not independently reviewed. Notation as in the claim.

## 1. The grading and the core
`R` is `ℤ`-graded by total letter length: `deg s_x = 1`, `deg t_x = −1`, `deg b = 0` for
`b ∈ B⁺`. All defining relations are homogeneous, so `R = ⊕_k R_k`. The **core** is
`R_0 = ⊕_ρ colim_n M_(P_ρ,n)(B⁺_ρ)`, spanned by the words `s_μ b t_ν` with `|μ| = |ν|`;
at level `n` the matrix units are `s_μ t_ν` for paths `μ, ν` of length `n` with the same
range, and the transition `M_n -> M_(n+1)` pads by `b ↦ Σ_x s_x σ_x(b) t_x`. This is the
standard core of a Leavitt-type ring, and it is a filtered colimit of matrix rings over
`B⁺`.

## 2. R is a corner skew Laurent ring
Pick a base type `ρ_0` and its spine letter `x_0 = x_(ρ_0)`, a loop at `ρ_0`
(strong connectivity lets us route the spine so that `x_0 : ρ_0 -> ρ_0`; otherwise replace
`x_0` by a spine cycle and regrade by that cycle length). Put `t_+ = s_(x_0) ∈ R_1` and
`t_- = t_(x_0) ∈ R_(-1)`.
- `t_- t_+ = t_(x_0) s_(x_0) = α_(x_0) = p_(ρ_0)`.

Restrict to the unital corner `p_(ρ_0) R p_(ρ_0)`, or, when there are several types, first
apply the standard reduction that a strongly connected finite type graph with a spine is
Morita equivalent to the single-type corner at `ρ_0` (collapse each type to `ρ_0` along the
spine; this is the row-finite reduction of ABC §5 in the coefficient-ring setting). On that
corner `t_- t_+ = 1`. By AGGP Lemma 2.4 (quoted in the claim), the corner is
`R_0'[t_+, t_-; φ]` with `φ(d) = t_+ d t_-` a corner isomorphism of its core `R_0'`. Morita
invariance of `K`-theory lets us compute on this corner and transport back.

## 3. H'-unitality and supercoherence
- `R_0'` is unital-on-each-level and a filtered colimit of matrix rings over `B⁺`, hence
  flat as a `ℤ`-module, hence H'-unital (ABC Remark 2.2: H'-unital = H-unital for
  `ℤ`-flat rings, and unital rings are H-unital; filtered colimits of H'-unital rings are
  H'-unital).
- `S = φ^(-1)R_0'` is the colimit of `R_0' →φ R_0' →φ ...`. Its unitization is regular
  supercoherent: `B⁺` is regular supercoherent by
  `eventually-rational-register-ring-is-regular-supercoherent`; matrix rings over a regular
  supercoherent ring are regular supercoherent; and the colimit maps `M_(P,n) -> M_(P,n+1)`
  are split inclusions of a free corner, hence flat, so ABC Proposition 7.1 applies
  verbatim with `B⁺` in the role of `k`.

## 4. The sequence
ABC Theorem 3.6 with `A = ℤ` gives
`K(R_0'[t_+, t_-; φ]) = NK_+ ⊕ NK_- ⊕ hocofiber(K(R_0') →(1−φ_*) K(R_0'))`. By §3 and
Lemma 7.2 the `NK`-terms vanish, so
`K(R) = hocofiber(K(R_0') →(1−φ_*) K(R_0'))`, i.e. the long exact sequence
`... -> K_n(R_0') →(1−φ_*) K_n(R_0') -> K_n(R) -> K_(n−1)(R_0') -> ...`.
- **Morita.** `R_0'` is a filtered colimit of matrix rings over `B⁺`, so
  `K_n(R_0') = K_n(B⁺)` compatibly with `φ_*`. Under this, `1 − φ_*` is `1 − [X]`, where
  `[X]` is the transfer of the register correspondence, by definition of the padding map in
  §1.
- **Injection.** The sequence gives a short exact
  `0 -> coker(1 − [X] : K_n(B⁺) -> K_n(B⁺)) -> K_n(R) -> ker(1 − [X] on K_(n−1)(B⁺)) -> 0`.
  So `coker(1 − [X])` injects into `K_n(R)` for every `n`. That is (P). ∎

## 5. Remark on the resolvent tension
Drop the resolvents. Then `B⁺` becomes the field `Q`, `R` becomes `L_Q(E_∞)` for the
infinite state graph, and ABC Theorem 7.6 (row-finite quivers over the regular supercoherent
`k = Q`, extended to the infinite case by `K`-theory's commuting with the filtered colimit
of finite complete subgraphs) gives (P) with no extra hypothesis. Adjoining the resolvents,
which is forced to make `1/m` exist, is exactly what replaces the coefficient field `Q` by
`B⁺` and turns supercoherence into the one remaining question.
