---
rg: 2
id: affine-relay-label-lift-proof
kind: route
title: Carry each output phase as an integral affine combination of window phases, invert the sparse system mod every prime power, and transport the lift to the augmentation shift
target: affine-relay-label-lifts-descend-to-two-symbols
requires:
  - binary-shifts-over-odd-fibers-split-off-the-augmentation-shift
  - free-orbit-label-lifts-need-count-raising-label-automata
artifacts:
  - experiments/affine-relay-lifts-2026-09-17/check.py
---

Notation as in the target.

**Imports.**
- **(S)** `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`, item 2 and item 4: for an odd prime `q`, a
  `ζ`-homogeneous injective, non-surjective automaton `θ` on `R_q^G` (`f(ζu) = ζf(u)`) gives, with `β = id`, a binary
  strict automaton over `G × C_q`.
- **(Dir)** Dirichlet: for every `o >= 1` there are infinitely many primes `q ≡ 1 mod o`. The case of residue `1` has
  an elementary proof via cyclotomic polynomials.
- **(Hall)** M. Hall, 1948: a family of finite sets has a system of distinct representatives iff every finite
  subfamily of size `r` has a union with at least `r` elements.

**Lemma (prime powers).** If (R3) holds, then `A_ℓ` is injective on `(Z/n)^act(ℓ)` for every `n >= 2`.
- By the Chinese remainder theorem it suffices to treat `n = p^k`. Entries of `A_ℓ` are integers and rows are finite
  sums, so reduction commutes with `A_ℓ`.
- Let `φ ≠ 0` with `A_ℓ φ = 0` mod `p^k`. The `p`-adic valuations of the values `φ(h)` lie in `{0, ..., k}`, so their
  minimum `j` is attained, and `j < k`. Write `φ = p^j ψ` with `ψ(h) ∈ Z/p^(k-j)` and `ψ(h₀) ≢ 0 mod p` for some `h₀`.
- Multiplication by `p^j` is injective from `Z/p^(k-j)` to `Z/p^k`. So `A_ℓ ψ = 0` mod `p^(k-j)`, hence mod `p`. By
  (R3) `ψ ≡ 0 mod p`, a contradiction.

**Item 1.**
- **Automaton.** The value at `g` depends on `c` restricted to `gM`, by the same rule at every `g`.
- **Commutes with `Z/n`.** Adding `k` to every phase changes an active output phase by `k·Σ_m a_m = k`, by (R2), which
  applies because the output is active. The symbol `0` is untouched. Clearly `σθ_n = τσ`.
- **Relay passes up.** For `θ_n` as a label automaton on `({0} ⊔ B × Z/n)^G`, put `a'(u') = a(σu')`. (R1) and (R2)
  hold, since `θ_n` outputs an active symbol exactly where `τ` does. The active sets of `ℓ'` and `θ_n(ℓ')` are those of
  `σℓ'` and `τ(σℓ')`, and the rows are the same, so `A'_ℓ' = A_(σℓ')` and (R3) holds.
- **Injective.** If `θ_n(c) = θ_n(c')`, applying `σ` gives `τ(σc) = τ(σc')`, so `σc = σc' = ℓ`. The phases then give
  `A_ℓ φ_c = A_ℓ φ_c'` mod `n`, and the Lemma gives `φ_c = φ_c'`. So `c = c'`.
- **Not surjective.** Choose `m` outside `τ(L^G)`, and `c` with `σc = m` (all phases `0`). Then `c` is not in the image,
  since `σθ_n(x) = τ(σx) ≠ m`.

**Item 2.** Put `a(u) = e_(d(u))` where `μ(u) ∈ B`, and `a(u) = 0` otherwise. (D1) gives (R1), and (R2) is clear. Now
`(A_ℓ φ)(g) = φ(D_ℓ(g))`. If some active `h` is no donor, `e_h` lies in the kernel mod every `p`. If every active `h`
is a donor, `φ(h)` is read off. So (R3) is (D2).

**Item 3.** Let `c = |B|`, odd, and `o = ord_c(2)`.
- **Choice of `q`.** By (Dir) there are infinitely many primes `q ≡ 1 mod o`, and all but finitely many are odd and
  larger than `c`. For such `q`, `o | q - 1` gives `c | 2^(q-1) - 1`, and Fermat gives `q | 2^(q-1) - 1`. Since `q` is
  a prime larger than `c`, `gcd(q, c) = 1`, so `c` divides `b_q = (2^(q-1) - 1)/q`. Put `t = b_q / c`.
- **Tags.** If `t >= 2`, let `τ' = θ_t` from item 1: strict, one rest symbol, `c·t = b_q` active symbols, relay `a∘σ`.
  If `t = 1`, let `τ' = τ`.
- **Phases.** Let `θ` be the lift of `τ'` by item 1 with `n = q`, on `C = {0} ⊔ B' × Z/q` with `|B'| = b_q`. It is
  strict and commutes with `Z/q`.
- **The augmentation module.** In `R_q = F_2[x]/(Φ_q(x))`, `ζ = [x]` has order `q`. For `0 < k < q`,
  `gcd(x^k - 1, x^q - 1) = x - 1` in `F_2[x]`, and `Φ_q(1) = q` is odd, so `x^k - 1` is coprime to `Φ_q` and `ζ^k - 1`
  is a unit. So `ζ^k u = u` forces `u = 0`: multiplication by `ζ` acts freely on `R_q \ {0}`, which has `2^(q-1) - 1`
  elements and hence `b_q` orbits.
- **Transport.** Choose representatives `r_b` of these orbits, indexed by `b ∈ B'`, and put `κ(0) = 0`,
  `κ(b, i) = ζ^i r_b`. This bijection `C → R_q` intertwines `+1` on `Z/q` with multiplication by `ζ`. Conjugating `θ`
  by `κ` sitewise gives a `ζ`-homogeneous strict automaton on `R_q^G`. By (S), `G × C_q` carries a binary strict
  automaton.

**Item 4.**
- Fix `ℓ`, a prime `p` and a finite `S ⊆ act(ℓ)`. The columns of `A_ℓ` indexed by `S` are independent mod `p`, since a
  dependence is a nonzero vector supported on `S` in the kernel. So some `|S| × |S|` minor is nonzero, and some term of
  its Leibniz expansion is nonzero. That term is an injection `S → act(τ(ℓ))` along nonzero entries. The entry at
  `(g, h)` is `a_(g^(-1)h)(ℓ_g)`, so these `g` satisfy the displayed condition.
- The candidate set of `h` is contained in `h M^(-1)`, which is finite. (Hall) gives the global injection.
- For strict `τ`, item 1 with `n = 2` gives a strict lift through free orbits of `Z/2` with one fixed symbol, and
  `free-orbit-label-lifts-need-count-raising-label-automata` gives the count statements.
