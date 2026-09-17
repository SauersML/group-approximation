---
rg: 2
id: donor-covering-phase-transport-proof
kind: route
title: Carry each active input phase on one relay output and read the labels through the given automaton
target: donor-covering-strict-automata-descend-to-two-symbols
requires:
  - binary-shifts-over-odd-fibers-split-off-the-augmentation-shift
  - passive-fixing-injective-automata-are-surjective
  - ec-groups-share-the-nonsurjunctive-alphabet-sizes
  - donor-covering-few-rest-automata-reach-admissible-types
artifacts:
  - experiments/donor-covering-descent-2026-09-17/check.py
---

Notation as in the target.

**Scope (audit 2026-09-17).** Items 1-5 below prove the target only for types `(2, b)` with `4 ∤ b` and `(1, b)`
with `b` odd. A referee refuted the target's "at most two rest symbols" scope. The last prerequisite,
`donor-covering-few-rest-automata-reach-admissible-types`, supplies the reduction from every type
`(z, b)` with `z <= 2` to those types on the same group. Then item 4 gives the first part of the title, and item 5
together with it gives the equivalence with universal binary descent.

**Imports, verbatim.**
- `binary-shifts-over-odd-fibers-split-off-the-augmentation-shift`, item 2: "In particular a `P`-equivariant
  injective, non-surjective `θ` gives a binary strict automaton over `G × P` (take `β = id`)." Here `I_P` is the
  set of `v ∈ F_2^P` with `Σ_t v(t) = 0`, and `P` acts by `(u·v)(t) = v(u^(-1) t)`.
- `passive-fixing-injective-automata-are-surjective`, Consequences: "For a finite group `F`, a binary automaton
  over `G × F` is an automaton on `({0,1}^F)^G` commuting with the translations of `F` along fibers."
- `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: "let `NS(K)` be the set of integers `n >= 2` such that some
  injective, non-surjective cellular automaton on `A^K` exists with `|A| = n`. Let `NS_all` be the union of `NS(G)`
  over all groups `G`."

**Item 1.**
- *Coordinates.* For each free orbit `b` fix a representative `rep(b) ∈ C`. For `c ∉ Z_C` let `φ(c)` be the unique
  `f ∈ F` with `c = f·rep(σ(c))`; it is unique because the action is free there. Then `φ(f·c) = f·φ(c)`. Identify
  each fixed point `z` with its label `σ(z)`.
- *Rule.* For `v ∈ C^M` put `u = σ∘v ∈ L^M`, and
  `Ψ(v) = μ(u)` if `μ(u) ∈ Z`, else `Ψ(v) = φ(v(d(u)))·rep(μ(u))`. This is well defined: when `μ(u) ∈ B`, (D1) at
  the identity site gives `u(d(u)) ∈ B`, so `v(d(u)) ∉ Z_C`. Let `Φ(y)(g) = Ψ((g^(-1)y)|_M)`. It is a cellular
  automaton with memory `M`.
- *Labels.* `σ(Ψ(v)) = μ(σ∘v)`, so `σ∘Φ = τ∘σ`. Writing `ℓ = σ∘y`, for `τ(ℓ)(g) ∈ B` we get
  `Φ(y)(g) = φ(y(D_ℓ(g)))·rep(τ(ℓ)(g))`.
- *Equivariance.* `σ(f·c) = σ(c)`, and `F` fixes `Z_C`. So `Ψ(f·v) = f·Ψ(v)` in both cases, using
  `φ(f·c) = f·φ(c)` in the second.
- *Injective.* Let `Φ(y) = Φ(y')`.
  - Applying `σ` gives `τ(σ∘y) = τ(σ∘y')`, so `σ∘y = σ∘y' =: ℓ` because `τ` is injective. In particular `D_ℓ` is
    the same for both.
  - If `ℓ(h) ∈ Z`, then `y(h) = ℓ(h) = y'(h)`.
  - If `ℓ(h) ∈ B`, (D2) gives `g` with `τ(ℓ)(g) ∈ B` and `D_ℓ(g) = h`. Then
    `φ(y(h))·rep(τ(ℓ)(g)) = Φ(y)(g) = Φ(y')(g) = φ(y'(h))·rep(τ(ℓ)(g))`. Freeness gives `φ(y(h)) = φ(y'(h))`, and
    with `σ(y(h)) = σ(y'(h))` this gives `y(h) = y'(h)`.
- *Not surjective.* `σ: C^G → L^G` is onto, e.g. by `ℓ ↦ rep∘ℓ` on active sites. If `Φ` were onto, `τ∘σ = σ∘Φ`
  would be onto, so `τ` would be onto. It is not.
- *Donor-covering.* For `v ∈ C^M`, `Ψ(v) ∉ Z_C` iff `μ(σ∘v) ∈ B`. Put `d'(v) = d(σ∘v)`, so `D'_y = D_(σ∘y)`. Then
  (D1) for `Φ` is (D1) for `τ`. For (D2): `y(h) ∉ Z_C` means `ℓ(h) ∈ B`, and (D2) for `τ` gives the relay.

**Item 2.** Let `F = C_t` act on `C = Z ⊔ (B × C_t)` by translating the second coordinate. It fixes `Z`, acts freely
on `B × C_t`, and `C/F = Z ⊔ B`. Item 1 gives a strict donor-covering automaton for the split
`C = Z ⊔ (B × C_t)`, of type `(z, bt)`.

**Item 3(a).** Let `C = {0,1}^(C_p)` with `C_p` acting by translation.
- The stabilizer of `v` is a subgroup of `C_p`, so it is trivial or all of `C_p`. It is all of `C_p` iff `v` is
  constant. So `Z_C` is the two constant vectors, the action is free elsewhere, and there are `(2^p - 2)/p` free
  orbits.
- Item 1 gives a strict automaton on `({0,1}^(C_p))^G` commuting with translation along fibers. By the second
  import this is a binary cellular automaton over `G × C_p`. It is the same map under
  `{0,1}^(G×C_p) = ({0,1}^(C_p))^G`, so it is still injective and not surjective.
- Directly: `Φ` is continuous. It commutes with `(h, 1)` because it is a cellular automaton over `G`. Translation
  by `(1, u)` acts on every fiber by `u`, and `Φ` commutes with that, since `Ψ(u·v) = u·Ψ(v)`. Curtis–Hedlund–Lyndon
  then applies.

**Item 3(b).** Let `C = I_(C_q)` with `q` an odd prime.
- A nonzero `v ∈ I_(C_q)` with nontrivial stabilizer is fixed by all of `C_q`, so it is constant: `v = 𝟙`. But
  `Σ_t 𝟙(t) = q = 1` in `F_2`, so `𝟙 ∉ I_(C_q)`. Hence `Z_C = {0}`, the action is free on the other `2^(q-1) - 1`
  vectors, and there are `(2^(q-1) - 1)/q` free orbits.
- Item 1 gives a `C_q`-equivariant injective, non-surjective automaton on `I_(C_q)^G`. The first import gives a
  binary strict automaton over `G × C_q`.

**Item 4, lemma.** Let `c >= 1` be odd.
- If `c = 1`, every odd prime works.
- Otherwise let `d = ord_c(2) >= 2`. Fix any `X >= c` and let `m = d·X!`, so `m >= 3`.
  - `|Φ_d(m)| = ∏ |m - ω| >= (m - 1)^(φ(d)) >= 2` over the primitive `d`-th roots `ω`, so `Φ_d(m)` has a prime
    divisor `r`.
  - Since `Φ_d | x^d - 1`, `r | m^d - 1`, so `r ∤ m`. Hence `r > X`, because every prime `<= X` divides `m`, and
    `r ∤ d`, because `d | m`.
  - Let `e = ord_r(m)`, so `e | d`. Suppose `e < d`. Over `F_r`, `x^d - 1 = ∏_(k|d) Φ_k(x)` and
    `x^e - 1 = ∏_(k|e) Φ_k(x)`. So `m` is a root of some `Φ_k` with `k | e`, `k < d`, and also of `Φ_d`. These are
    distinct factors of `x^d - 1`, so `m` is a repeated root of `x^d - 1` mod `r`. But its derivative
    `d·m^(d-1)` is nonzero mod `r`, a contradiction.
  - So `e = d` and `d | r - 1`. Let `q = r`. It is an odd prime with `q > c`, so `gcd(q, c) = 1`.
  - `2^(q-1) ≡ 1 (mod c)` since `d | q - 1`, and `q | 2^(q-1) - 1` by Fermat. So `qc | 2^(q-1) - 1`, i.e.
    `c | (2^(q-1) - 1)/q`. Since `X` is arbitrary, there are infinitely many such `q`.

**Item 4, types.** Write `N'_q = (2^(q-1) - 1)/q`, which is odd.
- *Type `(1, b)`, `b` odd.* Choose a prime `q` with `b | N'_q`. Item 2 with `t = N'_q / b` gives type `(1, N'_q)`,
  and item 3(b) gives `2 ∈ NS(G × C_q)`.
- *Type `(2, b)`, `4 ∤ b`.* Write `b = c` or `b = 2c` with `c` odd, and choose an odd prime `p` with `c | N'_p`.
  Then `b | 2N'_p = (2^p - 2)/p`. Item 2 with `t = 2N'_p / b`, then item 3(a), gives `2 ∈ NS(G × C_p)`.
- In both cases `2 ∈ NS_all`.

**Item 5.**
- Let `β` have rule `ν` with memory `M`. Put `L = A × {rest, active}`, `Z = A × {rest}`, `B = A × {active}`, and
  `τ(a, s) = (β(a), s)`, a cellular automaton with memory `M`.
  - It is injective because `β` is, and not surjective because its first coordinate misses what `β` misses.
  - `μ(u) ∈ B` iff `u(1) ∈ B`. With `d ≡ 1`, (D1) holds, and (D2) holds with `g = h`. So the type is `(|A|, |A|)`.
- If `2 ∈ NS_all`, a binary strict `β` gives type `(2, 2)`, and `4 ∤ 2`. The converse is item 4.
- For the second bullet: `NS_all ≠ ∅` iff some group carries a donor-covering strict automaton of some type
  `(k, k)`, by the construction above. `2 ∈ NS_all` iff some group carries type `(2, b)` with `4 ∤ b`, by the first
  bullet.
