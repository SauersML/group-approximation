---
rg: 2
id: injective-limit-trace-flexible-hs-repair-is-strict-proof
kind: route
title: Transfer the trace to the flexible correction, pad to the input dimension, conjugate by Jung tubularity
target: injective-limit-trace-flexible-hs-repair-is-strict
requires: []
---

## Imports

- **Jung**, *Amenability, tubularity, and embeddings into R^ω*,
  arXiv:math/0506108. The abstract, verbatim: "Suppose M is a tracial von
  Neumann algebra embeddable into R^ω ... and X is an n-tuple of selfadjoint
  generators for M. Denote by Γ(X;m,k,γ) the microstate space of X of order
  (m,k,γ). We say that X is tubular if for any ε>0 there exist m ∈ N and γ>0
  such that if (x_1,...,x_n), (y_1,...,y_n) ∈ Γ(X;m,k,γ), then there exists a
  k×k unitary u satisfying |ux_iu^* - y_i|_2 < ε for each 1 ≤ i ≤ n. We show
  that the following conditions are equivalent: 1) M is amenable (i.e.,
  injective). 2) X is tubular; 3) Any two embeddings of M into R^ω are
  conjugate by a unitary u in R^ω." Only (1) ⇒ (2) is used. In the body this
  is Lemma 2.9, (1) ⇔ (2), under the standing assumption that M embeds into
  R^ω.
  - **Microstate spaces (§1).** Γ(X;m,k,γ) is the set of n-tuples of
    selfadjoint k×k matrices whose normalized mixed moments of order at most
    m are within γ of those of X. No norm bound is imposed.
  - **Every k.** Tubularity is used for every k: the proof of Lemma 2.4 reads
    "for any k ∈ N, if ξ, η ∈ Γ(F; m(p), k, m(p)^(-1)), then there exists a
    u ∈ U_k ...".
- **Connes**: an injective tracial von Neumann algebra with separable predual
  is hyperfinite, hence embeds into `R^ω`.
- **Standard.** Tracial ultraproducts `M = ∏_ω (M_(d_n), tr)` are finite von
  Neumann algebras with faithful trace `τ_ω = lim_ω tr` (Hadwin--Shulman
  arXiv:1706.08405v3, §1). GNS uniqueness: a unital trace-preserving
  `*`-homomorphism from `(C[Γ], τ)` into a tracial von Neumann algebra with a
  faithful trace extends to a normal trace-preserving isomorphism of
  `π_τ(Γ)''` onto the generated algebra.

Notation: `tr` is the normalized trace, `||x||_2 = tr(x^*x)^(1/2)`, and
`|tr x| <= ||x||_2`.

## Step 1. The limit trace is carried by the flexible correction

Fix `g` and write `V = π_n(g)`, `P = P_n`, `d = d_n`, `D = D_n`. Then

```text
tr_D(V) = (d/D) tr_d(PVP) + (1/D) Tr((1-P)V(1-P)),   |Tr((1-P)V(1-P))| <= D-d,
```

so

```text
| tr_D(V) - tr_d(α_n(g)) | <= ||α_n(g) - PVP||_(2,d) + 2(1 - d/D).
```

By (F), `τ(g) = lim_ω tr_(D_n) π_n(g)` for every `g`.

## Step 2. A sequence of finite-dimensional characters converging to τ

Enumerate `Γ = {g_1, g_2, ...}`. By Step 1, for each `k` the set of `n` with
`|tr π_n(g_i) - τ(g_i)| < 2^(-k)` for all `i <= k` lies in `ω`, so it is
infinite. Choose `n_1 < n_2 < ...` inductively from these sets, as in the proof
of Hadwin--Shulman Theorem 3. Then `σ_k := π_(n_k)` are genuine
representations, of dimensions `e_k := D_(n_k)`, with `tr σ_k -> τ` pointwise.

## Step 3. Genuine representations of dimension exactly d_n with limit trace τ

*Case A: `d_n` is bounded on a set in `ω`.* Then `d_n = d` is constant on some
`A ∈ ω`. As `U(d)^S` is compact, `β(s) = lim_ω α_n(s)` exists. For every word
`w` representing `g`, `||w(α_n(S)) - α_n(g)||_2 -> 0`, because `α_n` is
asymptotically multiplicative and `w` is fixed. Hence two words representing
the same element have equal limits, so `β` defines a homomorphism
`Γ -> U(d)` with `lim_ω α_n(g) = β(g)`. Take `ρ_n = β` on `A`; the claim
follows directly and Steps 4--6 are not needed.

*Case B: `lim_ω d_n = ∞`.* Let `k(n) = max{k <= n : e_k^2 <= d_n}` (and
`ρ_n` trivial if there is no such `k`). For each `K`, the set of `n >= K` with
`d_n >= max_(k<=K) e_k^2` lies in `ω`, and on it `k(n) >= K`; so
`lim_ω k(n) = ∞`. Write `d_n = q_n e_(k(n)) + r_n` with `0 <= r_n < e_(k(n))`
and set

```text
ρ_n = σ_(k(n))^(⊕ q_n) ⊕ 1^(⊕ r_n) : Γ -> U(d_n).
```

Then `|tr ρ_n(g) - tr σ_(k(n))(g)| <= 2 r_n/d_n <= 2 d_n^(-1/2)`. Hence
`lim_ω tr ρ_n(g) = τ(g)` for every `g`.

## Step 4. Two embeddings of L_τ(Γ) with the same trace

Put `α(g) = (α_n(g))_ω` and `ρ(g) = (ρ_n(g))_ω` in `M = ∏_ω (M_(d_n), tr)`.
Both are homomorphisms `Γ -> U(M)`: `α` because `α_n` is asymptotically
multiplicative, `ρ` exactly. Both satisfy `τ_ω ∘ α = τ = τ_ω ∘ ρ`. By GNS
uniqueness, `g ↦ α(g)` and `g ↦ ρ(g)` each extend to trace-preserving normal
isomorphisms from `L_τ(Γ)` onto `α(Γ)''` and `ρ(Γ)''`.

## Step 5. Tubularity conjugates the matrix models

Let `X = (Re π_τ(s), Im π_τ(s))_(s∈S)`, a finite tuple of selfadjoint
generators of `L_τ(Γ)`. By (I) and Connes, `L_τ(Γ)` is injective and embeds
into `R^ω`, so Jung (1) ⇒ (2) says `X` is tubular.

The matrix tuples `x^α_n = (Re α_n(s), Im α_n(s))_s` and
`x^ρ_n = (Re ρ_n(s), Im ρ_n(s))_s` have operator norm at most one. Every
mixed moment of either tuple is a fixed linear combination of normalized
traces of words in the `α_n(s)`, `α_n(s)^*` (resp. `ρ_n(s)`, `ρ_n(s)^*`).
In `M`, `α(s)^* = α(s^(-1))` and `ρ(s)^* = ρ(s^(-1))`, so along `ω` these
traces converge to `τ` of the corresponding group elements. Those are exactly
the corresponding moments of `X` in `(L_τ(Γ), τ)`. So for each `(m,γ)` the set
of `n` with both `x^α_n, x^ρ_n ∈ Γ(X; m, d_n, γ)` lies in `ω`.

Given `ε > 0`, take `(m,γ)` from tubularity. On that set there is
`u_n ∈ U(d_n)` with `||u_n x^α_n(i) u_n^* - x^ρ_n(i)||_2 < ε` for each
coordinate `i`, hence

```text
|| u_n α_n(s) u_n^* - ρ_n(s) ||_2 < 2ε      for all s ∈ S.
```

This is the only place same dimensions are needed: tubularity compares
microstates of one size `k = d_n`, and Step 3 produced `ρ_n` of exactly that
size.

## Step 6. Diagonalize

Let `η_n = min_(u ∈ U(d_n)) max_(s∈S) ||u α_n(s) u^* - ρ_n(s)||_2`, attained by
compactness. Step 5 gives `lim_ω η_n <= 2ε` for every `ε > 0`, so
`lim_ω η_n = 0`. With minimizers `u_n`, the homomorphisms
`ρ'_n = u_n^* ρ_n u_n : Γ -> U(d_n)` satisfy
`lim_ω max_s ||α_n(s) - ρ'_n(s)||_2 = 0`. For `g` a word of length `ℓ` in `S`,

```text
||α_n(g) - ρ'_n(g)||_2 <= ℓ max_s ||α_n(s) - ρ'_n(s)||_2 + ||α_n(g) - w(α_n(S))||_2,
```

and the last term tends to zero. So `lim_ω ||α_n(g) - ρ'_n(g)||_2 = 0` for
every `g`. ∎

## Remarks

- Without (F), Steps 1--2 are replaced by the hypothesis that `τ` is a pointwise
  limit of finite-dimensional characters. That is Hadwin--Shulman's
  approximation property (∗), and for amenable `Γ` the conclusion is their
  Theorem 4. The use of (F) here is that the ratio condition `D_n/d_n -> 1`
  already forces (∗) for the one trace that matters.
- The ratio condition is essential in Step 1. Weak ucp-stability
  (`llp-implies-weak-ucp-stability`) allows infinite-dimensional
  compressions, and every amenable group has it by Choi--Effros. Yet an
  amenable group that is not residually finite is not flexibly HS-stable
  (Dogon arXiv:2211.10492v3, p. 4).
