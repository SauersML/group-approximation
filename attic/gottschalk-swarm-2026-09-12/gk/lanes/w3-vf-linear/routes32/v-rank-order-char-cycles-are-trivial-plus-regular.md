---
rg: 2
id: v-rank-order-char-cycles-are-trivial-plus-regular
kind: claim
title: In characteristic p every rank function on F[V] gives each clopen p-cycle the Jordan profile rk((1 - [s])^j) = (1 - phi_V)(p - j)/p for 1 <= j <= p
distinct_from:
  v-rank-models-are-trivial-plus-free-on-odd-cycle-trees: that is the torsion law for odd primes different from the characteristic, where group algebras of cycle trees are semisimple; this is the characteristic prime itself, where 1 - [s] is nilpotent and the profile is p-sensitive.
  char-uniform-identities-cannot-force-v-rank-triviality: that proves a gate proof must use a p-sensitive identity; this proposes the first p-sensitive structure theorem such a proof could build on.
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

**OPEN.** Let `char F = p > 0`, `rk` a Sylvester matrix rank function on `F[V]`, and `phi_V = 1 - rk col(1 - [s_i])`
over a generating set. A clopen `p`-cycle is an element of order `p` that permutes `p` disjoint nonempty clopen sets
cyclically and is the identity on their complement, which must be nonempty. All of them are conjugate in `V`. The
claim: for every clopen `p`-cycle `s` and `1 <= j <= p`,

```text
rk((1 - [s])^j) = (1 - phi_V)(p - j)/p.
```

At `j = 0` the rank is `1`. Equivalently, the drops `d_i = rk((1 - [s])^i) - rk((1 - [s])^(i+1))` are
`d_0 = phi_V + (1 - phi_V)/p` and `d_i = (1 - phi_V)/p` for `1 <= i < p`: weight `phi_V` of the trivial module plus
weight `1 - phi_V` of the regular module `F[Z/p]`.

**Why it matters.**
- **`p`-sensitive.** `char-uniform-identities-cannot-force-v-rank-triviality` shows a proof of V's rank gate must use
  a `p`-sensitive identity. The nilpotency `(1 - [s])^p = 0` of clopen `p`-cycles is the natural one.
- **What the law does.** It is the `p = char F` analogue of the torsion law. The augmentation and sofic values satisfy
  it, while over `C` the von Neumann values `(p - 1)/p` for all `j >= 1` break the pattern. So it separates
  characteristic `p` from characteristic `0`.
- **What it doesn't do.** It doesn't imply the gate.

## Attempts

- **Proved on paper** (w5-v-nonamenable, artifact Proposition 4.2). With `y = 1 - [s]` and
  `d_i = rk(y^i) - rk(y^(i+1))`:
  - **(a)** `rk(y^j)` doesn't depend on the clopen `p`-cycle, since all are conjugate.
  - **(b)** `d_0 >= ... >= d_(p-1) >= 0` and `sum d_i = 1`, by the Frobenius inequality
    `rk(ABC) + rk(B) >= rk(AB) + rk(BC)` together with `y^p = 0`.
  - **(c)** `rk(y^j) <= (p - j)/p` and `rk(y) <= 1 - phi_V`, the second because `1 - [s]` is a combination of the
    `1 - [s_i]`. Averaging the last `p - j` of `d_1, ..., d_(p-1)`, whose sum is `rk(y)`, gives
    `rk(y^j) <= (1 - phi_V)(p - j)/(p - 1)` for `j >= 1`.
  - **(d)** The augmentation values (`phi_V = 1`) and the sofic values `1 - j/p` (the law with `phi_V = 0`) satisfy
    the law.
  - **What's missing:** the lower bound `rk(y^j) >= (1 - phi_V)(p - j)/p` and the sharper upper bound. (b) and (c)
    give only `rk(y^j) <= min((p - j)/p, (1 - phi_V)(p - j)/(p - 1))` for `j >= 1`.
- **Single-level data don't force it** (artifact Section 4, for `p >= 3`). On `F_p[(Z/p)^r]/m^2` every nonidentity
  element has Jordan type `[2, 1^(r-1)]`, with normalized ranks `1/(r+1)` and `0`, the same at one level. This
  normalization isn't compatible across the tree embeddings `E_r ⊆ E_(r')` inside `V`. So a proof has to use
  compatibility across levels or depth-changing elements.
- **Next test.** Decide whether a rank function on `F_p[E_infinity]` can be invariant under every disjoint-support
  endomorphism (each basis cycle mapped to a product of cycles with disjoint index sets) without being trivial plus
  regular. Every clopen `p`-cycle tuple of this shape whose supports leave a nonempty complement is jointly conjugate
  in `V`. In characteristic `2` the relevant identity is `rk(x_1 + x_2) = rk(x_1)` for `x_i = 1 + [t_i]` with
  disjoint clopen transpositions `t_i` whose supports leave a nonempty clopen complement. Then
  `x_1 + x_2 = [t_1](1 + [t_1 t_2])` with `t_1 t_2` conjugate to `t_1` (w3-vf-linear, Section 31.3).
- **Correction** (w5-v-nonamenable, after 27fa7efbff). The first version stated the law for `0 <= j <= p`. That fails
  at `j = 0` whenever `phi_V > 0`, the augmentation rank included, since `rk(y^0) = 1`. The range is `1 <= j <= p`.
- **Candidate proof for every prime** (w7-v-cycle-c2; artifact
  `research/artifacts/thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md`). Held OPEN until
  `w3-vf-linear` re-derives it.
  - **Route.** The law is Corollary 1.2 of `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`. On every
    finite subgroup `G <= V`, in every characteristic, `rk(A) = phi_V rank_F eps(A) + (1 - phi_V) rank_F Reg(A)/|G|`.
    For `G = <s>` in characteristic `p`, left multiplication by `(1 - [s])^j` on `F[Z/p]` has rank `p - j`.
  - **Inputs.** The odd torsion law on an auxiliary group `Q = (Z/q)^Pi` of odd `q`-cycles normalized by `G`, for
    primes `q != char F` tending to infinity, and `v-rank-torsion-constant-equals-global-fixed-rank`. There is no
    matricial step.
  - **Cross-check for `p = 2`** (artifact Section 2, no characters).
    - Take a dihedral pair `t c t = c^(-1)` with `c` a clopen `q`-cycle, and let `e = sum_i [c]^i`.
    - The identity `1 - e = u(1 + [t]) + (1 + [t])[t]u[t]` with `u = sum_(i=1)^((q-1)/2) [c]^i`, together with the
      square-zero corner bound, gives `(1 - phi_V)(q - 1)/(2q) <= rk(1 + [t]) <= (1 - phi_V)(q + 1)/(2q)`.
  - **Next test decided: such a function exists** (artifact Section 3).
    - **Construction.** `rho(t_i) = 1 + lambda_i e_12` over `F_2(lambda_1, lambda_2, ...)` gives a rank function on
      `F_2[E_infinity]`.
    - **What it satisfies.** It is invariant under every injective endomorphism, and `rk(1 + [g]) = 1/2` for all
      `g != 1`. So `rk(x_1 + x_2) = rk(x_1)` holds.
    - **Why it is not trivial plus regular.** Its joint fixed rank is `1/2` at every level.
    - **Consequence.** Invariance inside the 2-group can't prove the law. The proof has to use odd cycles normalized
      by it.
- **Next test for `p >= 3`: invariant models violate even the single-element law** (w7-v-cycle-c3; artifact
  `research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md`, Section 2; candidate
  `p-cycle-tree-invariance-cannot-force-order-char-law`). Held OPEN until `w3-vf-linear` re-derives it.
  - **The models.** `rho_m([g]) = exp_m(lambda(g) u)` in `L[u]/(u^m)` for `1 <= m <= p`, with `L = F(t_i)` and
    `lambda(tau_i) = t_i`. `rk_m` is the normalized `L`-rank. For `p = 2` and `m = 2` this is the model of
    w7-v-cycle-c2's Section 3.
  - **Coherent.** `rk_m` is invariant under every injective endomorphism, prefix refinement and disjoint-support
    endomorphisms included. For `m = 2` over `F_p` it is an ultralimit of generic dimension-2 quotients of the
    `A/m^2` models above.
  - **Not the law.** For `2 <= m < p`, `rk_m((1 - [g])^j) = max(m - j, 0)/m`, which is not `(1 - phi)(p - j)/p` for
    any `phi`. So for `p >= 3` invariance fails to force the profile of a single cycle, not only the joint fixed rank.
  - **Every allowed profile occurs.** Mixtures of `rk_1, ..., rk_p` realize every drop sequence that Proposition
    4.2(b) above allows. So (b) together with coherence inside the `p`-group gives nothing sharper.
  - **First premise broken.** For `2 <= m < p`, induce to the wreath configuration `E_p ⋊ <s>`, with `s` a clopen
    `p`-cycle permuting the supports. `s` gets the regular profile and `tau_1` the profile of `u`, which breaks
    single-element `V`-conjugacy. For `m = p` single elements agree, and only the joint fixed rank rules it out.

*Verification by `w3-vf-linear` (2026-09-12), Section 31.3 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: Proposition 4.2 (a)-(c), the single-level calibration and the 77400e393 correction PASS. Re-derived: the Frobenius drops and their telescoping sum; the corrected range `1 <= j <= p` with drops `d_0 = phi_V + (1 - phi_V)/p`, `d_i = (1 - phi_V)/p`; and the tail-average bound `rk(y^j) <= min((p - j)/p, (1 - phi_V)(p - j)/(p - 1))` for `j >= 1`. The law itself stays OPEN.*

*Verification by `w3-vf-linear` (2026-09-12), §32.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS on w7-v-cycle-c2 ce8be16cd1. Corollary 1.2 of the cylinder-group artifact proves the law for every prime, `p = 2` and `p = 3` included. The Section 2 dihedral bounds give `p = 2` independently. The planned route may land this node ESTABLISHED.*
