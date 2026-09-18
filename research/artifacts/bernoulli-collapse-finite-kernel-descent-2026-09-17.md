# Bernoulli collapse descends along finite normal quotients

Date: 2026-09-17. Agent `swarm-0917-w5-gs-rokhlin-threshold`. Handwritten proofs, no computation. Unreviewed.

**Notation.**
- Groups are countably infinite, and `s(G) = h^Rok_sup(G)`.
- `X_h` is the Bernoulli shift over `G` of base entropy `h`, well defined by Seward's equal-entropy theorem
  (`bernoulli-shifts-with-equal-base-entropy-are-isomorphic`). `a ~_G b` means `X_a ≅ X_b` over `G`.
- `D(G)` is as in `bernoulli-isomorphism-collapse-set-is-a-subgroup`.
- `R(G)` and `r(G)` are as in `bernoulli-collapse-is-null-or-eventually-total`: `R(G)` is the set of non-rigid
  levels, and `r(G) = inf R(G)`.
- H2(G) is `bernoulli-rigidity-threshold-equals-rokhlin-supremum` at `G`: if `s(G) < ∞` then `r(G) = s(G)`.
- For `F ≤ G` finite and an F-space `Y`, `Coind(Y)` is as in
  `research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md`, Section 1.

**Cited result (Corollary D of `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli`, verbatim).**
"If `|F| >= 2`, `H(Y) < ∞` and `0 < H(K) < ∞`, then `Coind(Y) × K^G ≅ M^G` whenever `H(M) = H(K) + H(Y)/|F|`."
Here `G` is countably infinite and `F ≤ G` is finite. The proof supplies a free `F`-orbit from `K^F`, so the
action of `F` on `Y` may be trivial.

## 1. Generalized shifts over a quotient are co-induced

**Lemma 1.1.** Let `N ◁ Γ` be finite, `Q = Γ/N`, and `(L, λ)` a standard probability space. Let `Γ` act on
`L^Q` through `Q`: `(g.x)(q) = x(ḡ^-1 q)`, where `ḡ` is the image of `g`. Give `L` the trivial `N`-action.
Then `L^Q` with this `Γ`-action equals `Coind_N^Γ(L)`.

*Proof.* A point of `Coind(L)` is `x: Γ → L` with `x(tf) = f^-1 . x(t) = x(t)` for `f ∈ N`. So `x` is constant
on the left cosets `tN`. Since `N` is normal, these are the fibres of `Γ → Q`, and `x ↦ (x̄: q ↦ x(t), t ∈ q)` is a
bijection `Coind(L) → L^Q`. It intertwines the actions: `(g.x)(t) = x(g^-1 t)` corresponds to
`x̄(ḡ^-1 q)`. A left transversal of `Γ/N` is a set of representatives of `Q`, so the product measure `λ^R` on
`Coind(L)` is `λ^Q`. QED.

## 2. Theorem A: descent

**Theorem A.** Let `Γ` be countably infinite, `N ◁ Γ` finite with `n = |N|`, and `Q = Γ/N`. If
`0 < a, b < ∞` and `X_a ≅ X_b` over `Q`, then `X_(c + a/n) ≅ X_(c + b/n)` over `Γ` for every `c ∈ (0, ∞)`.

*Proof.*
1. If `n = 1`, then `Q = Γ` and translation (item 1 of `bernoulli-isomorphism-collapse-set-is-a-subgroup`)
   gives the claim. Assume `n ≥ 2`. `Q` is infinite, since `Γ` is infinite and `N` is finite.
2. Choose finite probability spaces `L_a`, `L_b` with `H(L_a) = a` and `H(L_b) = b`. By Seward's theorem over `Q`,
   `X_a ≅ L_a^Q` and `X_b ≅ L_b^Q`. So there is a `Q`-equivariant measure isomorphism `π: L_a^Q → L_b^Q`.
3. Let `Γ` act on both through `Q`. `π` is `Γ`-equivariant, because `g` acts as `ḡ`.
4. Choose a finite probability space `K` with `H(K) = c`. Then `π × id: L_a^Q × K^Γ → L_b^Q × K^Γ` is a
   `Γ`-isomorphism.
5. By Lemma 1.1, `L_a^Q = Coind_N^Γ(L_a)` with trivial `N`-action, and similarly for `L_b`.
6. Apply Corollary D with `G = Γ`, `F = N`, `Y = L_a` and `K`. The hypotheses hold: `|N| ≥ 2`, `H(L_a) = a < ∞`,
   and `0 < c < ∞`. So `L_a^Q × K^Γ ≅ X_(c + a/n)` over `Γ`. In the same way `L_b^Q × K^Γ ≅ X_(c + b/n)`.
7. Chaining the three isomorphisms gives `X_(c + a/n) ≅ X_(c + b/n)` over `Γ`. QED.

**Sanity check.** Over an amenable `Γ`, the Kolmogorov–Sinai entropy of `L^Q` along Følner sets `N·F_m` is
`H(L)/n`, so both sides have entropy `c + H(L)/n`. This matches, as it must.

**Corollary A.1.** Under the hypotheses of Theorem A:
1. `D(Q)/n ⊆ D(Γ)`;
2. if `a ∈ R(Q)`, then `(a/n, ∞) ⊆ R(Γ)`, so `r(Γ) ≤ r(Q)/n`;
3. `s(Γ) ≤ r(Q)/n`;
4. if `D(Γ) = {0}` (base entropy classifies over `Γ`), then `D(Q) = {0}`.

*Proof.*
1. Let `0 ≠ d ∈ D(Q)` with witness `h`: `X_h ≅ X_(h+d)` and `h, h + d ≥ 0`. Both levels are positive, since
   `X_0` is trivial and `X_d` is not. Both are finite by the definition of `D`. Theorem A gives
   `X_(c + h/n) ≅ X_(c + h/n + d/n)` over `Γ` for each `c > 0`, so `d/n ∈ D(Γ)`.
2. Take `b ≠ a` with `X_a ≅ X_b` over `Q`. Theorem A makes every level `c + a/n` with `c > 0` non-rigid over `Γ`.
3. `R(Γ) ⊆ [s(Γ), ∞)` by item 3 of `bernoulli-collapse-is-null-or-eventually-total`. Combine with part 2.
4. This is the contrapositive of part 1.

**Position relative to the transfer calculus.** Theorem A is not a step of the class `T` of
`rokhlin-excess-never-drops-under-bernoulli-transfers` (translation, co-induction, finite-index restriction). It
moves a pair from `Q` to `Γ` and divides its levels by `n`, up to an arbitrarily small translation `c`. On a host
with `Γ/N ≅ Γ` and `s(Γ) = 0`, the excess `min(a, b) − s` is divided by `n`. So the Lyapunov function of that node
is not monotone under descent.

## 3. Theorem B: a 0–∞ law on self-similar kernels

**Theorem B.** Let `Γ` be countably infinite, and suppose `Γ` has a finite normal subgroup `N` with `n = |N| ≥ 2`
and `Γ/N ≅ Γ`. Then:
1. `r(Γ) ∈ {0, ∞}`. Equivalently, `R(Γ)` is `∅` or `(0, ∞)`.
2. `d ∈ D(Γ)` implies `d/n ∈ D(Γ)`.
3. If `D(Γ) ≠ {0}`, then `s(Γ) = 0`, every level in `(0, ∞)` is non-rigid, and H2(Γ) holds.
4. If `s(Γ) < ∞`, then H2(Γ) holds iff `s(Γ) = 0` and `D(Γ) ≠ {0}`. In particular, if `0 < s(Γ) < ∞`, then
   `D(Γ) = {0}` and H2(Γ) fails.
5. If `s(Γ) = 0`, then `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` at `Γ` (T1) holds iff `D(Γ) = R`,
   that is, iff all Bernoulli shifts over `Γ` above some finite base entropy are isomorphic.

*Proof.*
- **Transport.** An isomorphism `φ: Q = Γ/N → Γ` carries `L^Q` to `L^Γ` for every base `L`, and carries free
  ergodic actions to free ergodic actions with the same Rokhlin entropy. So `D(Q) = D(Γ)`, `R(Q) = R(Γ)`,
  `r(Q) = r(Γ)` and `s(Q) = s(Γ)`.
- **Item 1.** Corollary A.1(2) gives `r(Γ) ≤ r(Γ)/n` with `n ≥ 2`, so `r(Γ) ∈ {0, ∞}`. If `r(Γ) = 0`, then `R(Γ)`
  contains levels below every `ε > 0` and is upward closed (item 3 of `bernoulli-collapse-is-null-or-eventually-total`),
  so `R(Γ) = (0, ∞)`. If `r(Γ) = ∞`, then `R(Γ) = ∅`.
- **Item 2.** Corollary A.1(1) with `D(Q) = D(Γ)`.
- **Item 3.** `D(Γ) ≠ {0}` makes `R(Γ)` non-empty (item 3 of the same node), so `r(Γ) = 0` by item 1. Since
  `R(Γ) ⊆ [s(Γ), ∞)`, `s(Γ) = 0 = r(Γ)`.
- **Item 4.** Suppose `s(Γ) < ∞` and H2(Γ). Then `r(Γ) = s(Γ) < ∞`, so `r(Γ) = 0` by item 1. So `s(Γ) = 0` and
  `R(Γ) ≠ ∅`, hence `D(Γ) ≠ {0}`. The converse is item 3. If `0 < s(Γ) < ∞`, then H2 fails, and item 3 gives
  `D(Γ) = {0}`.
- **Item 5.** By item 4 of `bernoulli-collapse-is-null-or-eventually-total`, T1 holds iff `D(Γ) = R` and
  `r(Γ) = s(Γ)`. If `s(Γ) = 0` and `D(Γ) = R`, then item 3 gives `r(Γ) = 0 = s(Γ)`. QED.

**Remark.** Composing `Γ → Γ/N ≅ Γ` with itself gives surjections `Γ → Γ` whose kernels are finite normal
subgroups of order `n^j`. Item 4 says that on such a host a finite positive supremum means complete rigidity. No
group with `0 < s < ∞` is known, and nothing here decides whether such a host can exist.

## 4. The Gottschalk hosts `P × G`

Let `P = ⊕_(n ≥ 1) Z/nZ`, let `G` be a countably infinite group, and put `Γ = P × G`.

**Lemma 4.1.** For every `k ≥ 2`, let `N_k = Z/kZ × 1`, the `k`-th summand of `P`. It is a finite normal subgroup
of `Γ` of order `k`, and `Γ/N_k ≅ Γ`.

*Proof.* `N_k` is central, so normal. `Γ/N_k ≅ P' × G` with `P' = ⊕_(n ≠ k) Z/nZ`. By the Chinese remainder
theorem each `Z/nZ` is the direct sum of the `Z/p^e Z` with `p^e ‖ n`. So `P` and `P'` are direct sums of cyclic
groups of prime-power order. The multiplicity of `Z/p^e Z` in `P` is the number of `n ≥ 1` with `p^e ‖ n`, which is
countably infinite (take `n = p^e q` for primes `q ≠ p`). Removing the single index `k` changes each multiplicity by
at most one, so every multiplicity in `P'` is also countably infinite. Two direct sums of the same summands with
the same multiplicities are isomorphic by matching summands. So `P' ≅ P`, and `Γ/N_k ≅ Γ`. QED.

**Theorem 4.2.** For every countably infinite group `G`, with `Γ = P × G`:
1. `D(Γ)` is a `Q`-vector subspace of `R`, and `R(Γ)` is `∅` or `(0, ∞)`.
2. `D(G) ⊆ D(Γ)`. So a single nontrivial Bernoulli isomorphism over `G` makes every level over `Γ` non-rigid.
3. Suppose `s(G) < ∞`. Then `s(Γ) = 0`, and the following are equivalent:
   - H2(Γ);
   - `zero-rokhlin-supremum-forces-bernoulli-collapse` at `Γ`, i.e. some `X_a ≅ X_b` over `Γ` with `a ≠ b`;
   - `D(Γ) ≠ {0}`.

   Moreover, `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic` at `Γ` is equivalent to
   `eventual-bernoulli-collapse-at-finite-rokhlin-supremum` at `Γ`, i.e. to `D(Γ) = R`.
4. If `s(G) = ∞`, then `s(Γ) = ∞`, and both H2(Γ) and T1(Γ) are vacuous.

*Proof.*
1. `D(Γ)` is an additive subgroup (item 3 of `bernoulli-isomorphism-collapse-set-is-a-subgroup`). By Lemma 4.1 and
   Theorem B(2), it is closed under division by every `k ≥ 2`, so it is a `Q`-subspace. The second part is
   Theorem B(1).
2. This is item 7 (permanence to overgroups) of `bernoulli-isomorphism-collapse-set-is-a-subgroup`, together with
   Theorem B(3).
3. `s(Γ) = 0` is item 1–2 of `rokhlin-supremum-of-torsion-products-is-zero-or-infinite` (Seward's Theorem 1.11).
   The equivalences are Theorem B(4) with `s(Γ) = 0`. The second statement is Theorem B(5).
4. This is item 2 of `rokhlin-supremum-of-torsion-products-is-zero-or-infinite`. QED.

## 5. Consequences for the formal models

Section 5 of `research/artifacts/bernoulli-collapse-null-or-eventually-total-2026-09-16.md` gives two one-group
relations that satisfy the one-group calculus.
- **Threshold model** `a ≈ b` iff `a = b` or `a, b ≥ M`, with `M > s`. Its set of non-rigid levels is `[M, ∞)`, with
  `M > 0`. Theorem B(1) excludes it on every self-similar-kernel host, and in particular on every `P × G`. So the
  obstruction "the calculus has a model with eventual collapse and a positive gap above the supremum" does not
  apply to these hosts once descent is added to the calculus.
- **Dense-subgroup model** `a ≈ b` iff `a = b`, or `a, b > s` and `b − a ∈ C`, for a countable dense subgroup `C`.
  With `s = 0` and `C = Q`, it is closed under descent by any `n`, because `C/n = C`. So descent does not give
  eventual collapse, and item 2 of `bernoulli-collapse-is-null-or-eventually-total` still separates the two halves
  at `P × G` into "some collapse" and "eventual total collapse".

**Net effect on the Gottschalk cone.** The route `positive-rokhlin-via-classification-and-collapse` uses
`zero-rokhlin-supremum-forces-bernoulli-collapse` at the hosts `P × G` with `s(G) < ∞`. By Theorem 4.2(3), at those
hosts that prerequisite is equivalent to the rigidity threshold H2, and T1 is equivalent to eventual total
collapse. So on the hosts that matter for Gottschalk, the threshold half of T1 adds nothing: it is the weak
collapse. What remains open is whether any Bernoulli collapse exists over `P × G`.
