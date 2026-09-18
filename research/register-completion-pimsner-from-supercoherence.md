---
rg: 2
id: register-completion-pimsner-from-supercoherence
kind: claim
title: The Pimsner sequence (P) for a single-register completion follows from Ara--Brustenga--Cortiñas once the coefficient ring B+ is regular supercoherent
distinct_from:
  resolvent-register-units-give-rational-symbols: that states (P) as an assumption; this proves (P) from Ara--Brustenga--Cortiñas modulo one commutative-algebra hypothesis on B+.
  single-register-rings-divide-unit-at-finitely-many-primes: that is the divisibility theorem conditional on (P); this discharges (P) down to supercoherence of B+.
  abc-twisted-laurent-k-theory-fibration: that is the imported ABC theorem; this applies it to register completions and checks its hypotheses.
artifacts:
  - research/artifacts/gq-gq-k2-q-register-symbols.md
---

**ESTABLISHED** through `register-completion-pimsner-from-supercoherence-proof`
(lane proof, not independently reviewed; referee requests sent). It reduces hypothesis (P)
of `resolvent-register-units-give-rational-symbols` and
`single-register-rings-divide-unit-at-finitely-many-primes` to one commutative-algebra
statement, `eventually-rational-register-ring-is-regular-supercoherent`.

## The ingredients, verbatim
- **Corner skew Laurent ring** (Ara--González-Barroso--Goodearl--Pardo, *Fractional skew
  monoid rings*, arXiv:math/0307320, Lemma 2.4). "Let `D = ⊕_(i∈ℤ) D_i` be a `ℤ`-graded
  ring containing elements `t_+ ∈ D_1` and `t_- ∈ D_(-1)` such that `t_- t_+ = 1`. Then
  there is a corner isomorphism `α : D_0 -> t_+ t_- D_0 t_+ t_-` given by
  `α(d) = t_+ d t_-`, and `D = D_0[t_+, t_-; α]`."
- **The K-theory fibration** (Ara--Brustenga--Cortiñas, arXiv:0903.0056, Theorem 3.6, as
  in `abc-twisted-laurent-k-theory-fibration`). For a unital ring `R`, a corner isomorphism
  `φ : R -> pRp`, and `A` with `R ⊗ A` H'-unital,
  `K((R ⊗ A)[t_+, t_-; φ ⊗ 1]) = NK_+ ⊕ NK_- ⊕ hocofiber(K(R ⊗ A) →(1 − φ⊗1) K(R ⊗ A))`.
- **Nil-vanishing** (ABC Lemma 7.2 and Proposition 7.1). If `R` is regular supercoherent
  then the twisted `NK`-terms vanish; and, for the core of a Leavitt-type ring, the
  unitization of `S = φ^(-1)R_0` is regular supercoherent when the coefficient ring is,
  using flatness of the colimit maps.

## Setting
A **single-register completion** `R`, in the sense of
`single-register-rings-divide-unit-at-finitely-many-primes` (part 2):
- finitely many types, each with one register `N` valued in `ℕ`;
- an **always-available spine**: for every type `ρ` a letter `x_ρ` with
  `t_(x_ρ) s_(x_ρ) = p_ρ` (availability `α_(x_ρ) = p_ρ`), such that the spine letters make
  the type graph strongly connected;
- the coefficient ring `B⁺`: the `σ`-closed unital commutative ring of functions on states
  that are eventually rational in `N` at each type, with all register resolvents
  `(N + c)^(-1)`;
- letters acting on `N` by `N ↦ N + a` or `N ↦ c`, availability eventually constant.

## Statement
Let `R` be a single-register completion, and suppose
`eventually-rational-register-ring-is-regular-supercoherent`: the ring `B⁺` is regular
supercoherent. Then:
1. `R` is a corner skew Laurent ring `R_0[t_+, t_-; φ]` over its degree-`0` core `R_0`,
   with `t_+ = s_(x_(ρ_0))` for a base type `ρ_0`.
2. `R_0` is a filtered colimit of matrix rings over `B⁺`, so `R_0` and `R_0 ⊗ ℤ` are
   H'-unital, and the unitization of `S = φ^(-1)R_0` is regular supercoherent.
3. Hence ABC Theorem 3.6 with `A = ℤ`, plus Lemma 7.2, give the exact sequence
   `... -> K_n(R_0) →(1 − φ_*) K_n(R_0) -> K_n(R) -> K_(n−1)(R_0) -> ...`
4. By Morita invariance `K_n(R_0) = K_n(B⁺)`, and under this identification `φ_* = [X]`,
   the transfer of the register correspondence. So
   `coker(1 − [X] : K_n(B⁺) -> K_n(B⁺))` injects into `K_n(R)` for all `n`, which is (P).

So `single-register-rings-divide-unit-at-finitely-many-primes` and
`dilation-letters-cannot-divide-the-unit-class` become **unconditional** once `B⁺` is
regular supercoherent.

## What is not covered
- **The resolvents are essential.** Without them the ring is the Leavitt path algebra
  `L_Q(E_∞)` of the infinite state graph over the field `Q`, and (P) is already
  unconditional (ABC Theorem 7.6 over `k = Q`, extended to row-finite infinite quivers by
  the colimit). But then `1/m` is not available and `Q ⊄ R`. Adjoining the resolvents
  enlarges the coefficient ring from `Q` to `B⁺`, which is exactly what makes
  supercoherence a real hypothesis.
- **Availability idempotents that are not eventually constant** are outside the setting,
  and so is the two-register comparison shape, which is refuted for a different reason
  (`register-comparison-presentations-are-not-simple`).
