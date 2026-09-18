---
rg: 2
id: coset-field-rank-failure-gives-relative-bernoulli-deficit
kind: claim
title: A rank-condition failure over a generalized Bernoulli rational function field on a coset space is a relative Rokhlin deficit of a Bernoulli shift over the generalized Bernoulli action, and over the Kun-Thom pair it would refute Seward's direct-product conjecture
distinct_from:
  bernoulli-field-rank-failure-gives-rokhlin-deficit: that evaluates variables indexed by G at iid points and gets an absolute deficit of a Bernoulli shift, refuting INF(G); this indexes the variables by a coset space G/Γ, where the points form the generalized Bernoulli action and are free only relative to it, so the deficit is relative and refutes Seward's direct-product conjecture instead of INF (the Kun-Thom G is residually finite).
  twisted-linear-profile-deficits-are-rank-condition-failures: that turns any rank failure into a non-equivariant entropy profile, which only defeats profile proofs; this turns a coset-field failure into an actual generating partition of an explicit free p.m.p. action.
  kun-thom-nonsofic-action-carries-full-bernoulli-entropy: that is the binary-base test (a)-(d); this proves that the q-ary-base variant of (a) and (b) is at least as strong as the rank condition of the coset field, so a coset-field witness refutes the variant.
  seward-direct-product-relative-rokhlin-entropy-conjecture: that is the conjecture for all free X, Y; this reduces its instance X Bernoulli, Y a Kun-Thom generalized Bernoulli action, to a ring-theoretic statement.
---

**ESTABLISHED (unreviewed)** by [[coset-field-rank-failure-gives-relative-bernoulli-deficit-proof]].

**Setting.** `G` countable, `Γ < G` of infinite index, `H = G/Γ`, `m >= 1`, `k` a field, and

    K_H(k) = k(x_(c,i) : c ∈ H, i <= m),     σ_g(x_(c,i)) = x_(gc,i),

with `K_H(k) ⋊ G` the skew group ring (trivial cocycle; the action on `H` may have a kernel). For a finite field
`F_Q` put `Y^(Q,m)_Γ = ((F_Q^m)^H, uniform)`, `(gω)(c) = ω(g^{-1}c)`, and `X_(Q,d) = ((F_Q^d)^G, uniform)`.

**Theorem.** Suppose some `G`-stable subfield of `K_H(k)` has matrices `A` (`d x r`) and `B` (`r x d`) over its
skew group ring with `AB = I_d` and `r < d`. Then there are a finite field `F_(q_0)` and `C < ∞` such that for
every power `Q` of `q_0`

    h_G( X_(Q,d) × Y^(Q,m)_Γ  |  B(Y^(Q,m)_Γ) )  <=  r log Q + (C d / Q) log Q,

which is `< d log Q` once `Q > C d`. Only the index set of the variables changes from
`bernoulli-field-rank-failure-gives-rokhlin-deficit`; the new points are that the evaluation points are free
because they are measurable relative to the factor, and that the `h_2` term disappears.

**Corollaries.** Take `Γ < G` the Theorem E pair of `kun-thom-free-nonsofic-action` over `F_ℓ` with
`gcd(r_KT, ℓ - 1) = 1` (for example `ℓ = 2`). Suppose `F_p(x_c : c ∈ G/Γ) ⋊ G` fails the rank condition for
some `p`, or `K_H(k) ⋊ G` does for some field `k` and some `m`. Then, for `Q` large:
1. **Seward's direct-product conjecture fails.** `X_(Q,d)` and `Y^(Q,m)_Γ` are both free, and
   `h_G(X_(Q,d) × Y | B(Y)) < d log Q = h_G(X_(Q,d))`. This refutes
   `seward-direct-product-relative-rokhlin-entropy-conjecture` over a residually finite Kazhdan group.
2. **Absolute deficit.** `h^Rok_G(X_(Q,d) × Y^(Q,m)_Γ) < d log Q = h^Rok_G(X_(Q,d))`. So the `Q`-ary-base
   analogue of test (a) in `kun-thom-nonsofic-action-carries-full-bernoulli-entropy` fails. The free ergodic
   extension then has strictly smaller Rokhlin entropy than its Bernoulli factor.
3. **Characteristic reduction.** A failure over any `k` gives one over some `F_(q_0)`. In characteristic 0
   there is no failure at all, for every `G` and `Γ`: `Emb(K_0, C)` carries the invariant iid measure, which is
   survival case (c) of `field-crossed-product-rank-condition-survival-cases`. So only the characteristic-`p`
   coset fields are live. Their rank condition is `kun-thom-coset-field-crossed-product-has-the-rank-condition`.

**Why it matters.**
- This is a new decomposition. The `Q`-ary relative test at the Kun–Thom pair implies `RC(F_p(x_c) ⋊ G)` for
  every `p`, and each can fail on its own.
- Point-model certificates cannot supply the ring statement: `kun-thom-coset-field-has-no-finite-field-point-models`.
- A witness for `some-field-crossed-product-fails-the-rank-condition` over a coset field gives an explicit free
  action with a Rokhlin deficit, not only a profile.

**Where it stops.** The binary base `Y_Γ = {0,1}^(G/Γ)` of test (a) is not reached. Relative to a coarser
factor the entropy can only be larger, and `Y^(Q,m)_Γ` for `Q = 2^j` is `Y_Γ^(jm)`, not `Y_Γ`.
