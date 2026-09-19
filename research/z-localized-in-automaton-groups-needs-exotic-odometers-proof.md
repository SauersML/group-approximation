---
rg: 2
id: z-localized-in-automaton-groups-needs-exotic-odometers-proof
kind: route
title: Period-smooth maps compose, so rough periods are invariant; values of orbit-span functions at rational points and finite-state odometer codings turn divisibility into Zsigmondy periods; activity is subadditive and translations by 1/l are fully active
target: z-localized-in-automaton-groups-needs-exotic-odometers
requires:
  - automaton-groups-see-only-smooth-periods
  - adder-hosts-linearize-odd-odometer-roots
---

Lane proof (bh-free-16, 2026-09-18). Notation as in the claim and in `automaton-groups-see-only-smooth-periods`
(Steps 1–4 there: periods, denominators, Zsigmondy primes).

## Item 1

- **Composition.** If `h, h'` are `s`-period-smooth, then `π(h h' x) | π(h' x)·N | π(x)·N'N`, and `N'N` is
  `s`-smooth. So every `g ∈ Γ` is `s`-period-smooth, and `ρ_s(g x) | ρ_s(x)`.
- **Invariance.** Applying this to `g^-1` gives equality.

## Item 2

- **A rational point where `ψ` is nonzero.** Let `ψ = Σ n_g g ∈ M(Γ)` be nonzero. Rational points are dense and `ψ`
  is continuous, so `ψ(y_0) ≠ 0` for some rational `y_0`. Each `g(y_0)` is rational, so `ψ(y_0) ∈ Q^×`.
- **Values of the span.** If `ψ/ℓ = Σ n'_g g ∈ M(Γ)`, then `ψ(y_0)/ℓ ∈ Z`-span`(Γ·y_0)`. Every point of `Γ·y_0` has
  period dividing `π(y_0)·N` with `N` `s`-smooth, so its denominator divides `m^(π(y_0) N) − 1`.
- **Excluding `ℓ`.** Take `ℓ` with `ord_ℓ(m) = n`, a prime with `n > s` and `n ∤ π(y_0)`. Then `ℓ` divides no such
  denominator (Steps 3–4 of the cited proof). So `ℓ` divides the numerator of `ψ(y_0)`, which happens for only
  finitely many `ℓ`. The finitely many `n` dividing `π(y_0)` exclude finitely many more.
- **Why `Z_(S)` cannot sit in `M(Γ)`.** A subgroup `Z_(S) ⊆ M(Γ)` would give a nonzero `ψ` with `ψ/ℓ ∈ M(Γ)` for
  all `ℓ ∉ S`, and in particular for infinitely many of these Zsigmondy primes.

## Item 3

- **The orbit coding.** `a` maps level-`n` prefixes to level-`n` prefixes. `Y_n`, the set of level-`n` prefixes of
  `Y`, is the `a`-orbit of the prefix `x_n`, so it is a single cycle, of length `c_n`. The restriction map
  `Y_(n+1) → Y_n` is an equivariant surjection of cycles, so `c_n | c_(n+1)`, and `r_n = c_(n+1)/c_n <= m`. The prefix
  of `a^k x` at level `n` depends only on `k mod c_n`, so `C(λ) = lim a^(λ_n) x` (for integers `λ_n → λ`) is well
  defined and continuous. It is injective because `c_n → ∞`, and onto `Y` by compactness. It maps digit cylinders to
  prefix cylinders, and its inverse is a synchronous level bijection whose sections are the inverses of those of `C`.
  So `C^-1` is finite-state when `C` is.
- **Roots in `Aut(T_m)`.** Let `ℓ > m` be prime and `r ∈ Aut(T_m)` with `r^ℓ = a`.
  - In each level quotient the order of `r` involves only primes `<= m` (the quotient is an iterated wreath
    product of `S_m`), so `ℓ` is invertible modulo it, and `r = r^(ℓℓ') = a^(ℓ')` there for some `ℓ'`.
  - So `r` lies in the closure `K` of `⟨a⟩`. `K` is procyclic of order prime to `ℓ`, so `r = a^(1/ℓ)` is unique.
  - `K` acts on `Y`, through `C`, by the translations of `Z_(r)`, with `a ↦ +1`. Multiplication by `ℓ` is
    bijective on `Z_(r)`, since `ℓ` is prime to every `c_n`. So `a^(1/ℓ)` acts as `+1/ℓ`, and
    `a^(1/ℓ)(x) = C(1/ℓ)`.
- **The digits of `1/ℓ`.** Let the radices be periodic from level `L` on, with period `R` and product `N >= 2`.
  (`N = 1` would make `Y` finite.) Let `λ_i ∈ Z_(r) ∩ Q` be the tail of `1/ℓ` at level `i`. Then
  `λ_(i+1) = (λ_i − d_i)/r_i`, with `d_i` the digit.
  - **Residues.** At block levels `i_j = L + jR` write `λ_(i_j) = u_j/ℓ`. Then `u_(j+1) = (u_j − ℓD_j)/N`, with
    `D_j` an integer, so `u_(j+1) ≡ N^-1 u_j (mod ℓ)`. Also `u_j ≢ 0`, since `u_0 ≡ (c_L)^-1 ≢ 0`.
  - **Finitely many tails.** The real sizes satisfy
    `|u_(j+1)|/ℓ <= (|u_j|/ℓ + N)/N <= |u_j|/(2ℓ) + 1`, so the tails take finitely many values. Hence the digits are eventually periodic.
  - **The digit period.** Tails are determined by the future digits and radices. So if the digits have eventual
    period `π`, the block tails repeat with period `P = lcm(π, R)/R`. Then `N^P ≡ 1 (mod ℓ)`, i.e.
    `ord_ℓ(N) | P`.
  - **So `n | π`.** If `n = ord_ℓ(N)` is a prime `> R`, then `n | lcm(π, R)` forces `n | π`.
- **Transport through `C`.** Let `t` be at least `m`, `R`, `s` and the numbers of states of `C` and `C^-1`,
  counted with the radix phase.
  - **`C` preserves rough periods.** Step 1 of `automaton-groups-see-only-smooth-periods-proof` runs verbatim for
    the synchronous transducers `C` and `C^-1`, reading `lcm(π, R)` digits per period. So `C` and `C^-1` multiply
    periods only by `t`-smooth factors, up to the `t`-smooth factor `lcm(π, R)/π`. Hence
    `ρ_t(C(λ)) = ρ_t(digits of λ)`.
  - **Comparing `x` and `a^(1/ℓ) x`.** `ρ_t(x) = ρ_t(C(0)) = 1`, whereas `ρ_t(C(1/ℓ))` is divisible by
    `n = ord_ℓ(N)` whenever `n` is a prime `> t`.
- **The contradiction.** Every generator of `Γ` has at most `s <= t` states, so item 1 applies with `t`:
  `ρ_t(a^(1/ℓ) x) = ρ_t(x) = 1`. So `a^(1/ℓ) ∉ Γ`.
  - For each prime `n > t`, Zsigmondy gives `ℓ` with `ord_ℓ(N) = n`. Then `ℓ ≡ 1 (mod n)`, so `ℓ > t >= m` and
    `ℓ ∤ N`, and distinct `n` give distinct `ℓ`.
  - So infinitely many `ℓ ∉ S` are excluded, and `Z_(S)` with `1 ↦ a` does not embed.
- **Automorphisms conjugate to the odometer.** If `a = C_0 τ_1 C_0^-1` with `C_0` a finite-state automorphism, and
  `x = C_0(0)`, then `a^λ x = C_0(λ)`. So the canonical orbit coding is `C_0`, with constant radix `m`.

## Item 5

- **(a) Activity.** `α_g(n)` is the number of level-`n` vertices with nontrivial section. The section of `gh` at `v` is
  `g|_(h v) · h|_v`, so `α_(gh)(n) <= α_g(n) + α_h(n)` and `α_(g^-1)(n) = α_g(n)`. Every section of `τ_(1/ℓ)` is a
  translation with denominator `ℓ`, hence nontrivial (cited proof, via `odometer-root-hosts-are-non-affine-and-non-contracting`,
  part 1). So `α_(τ_(1/ℓ))(n) = m^n`.
  - Fix one such `ℓ` and write `τ_(1/ℓ)` as a word of length `w` in the generators. Then
    `m^n <= w · max_i α_(h_i)(n)` for every `n`.
  - Some generator attains the maximum at infinitely many `n`, and for it `α(n) >= m^n / w`.
- **(b) Period creation.** Take `ℓ` outside the finite exceptional set with `ord_ℓ(m) = n` a prime `> s`
  (Zsigmondy). If every generator and its inverse were `s`-period-smooth, then by item 1
  `ρ_s(τ_(1/ℓ)(0)) = ρ_s(0) = 1`. But `π(1/ℓ) = ord_ℓ(m) = n` is a prime `> s`, a contradiction.
- **(c) Möbius pieces.** This is item 3 of `automaton-groups-see-only-smooth-periods`. ∎
