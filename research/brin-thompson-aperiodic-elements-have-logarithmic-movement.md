---
rg: 2
id: brin-thompson-aperiodic-elements-have-logarithmic-movement
kind: claim
title: An element of nV with a non-periodic point moves some coordinate by more than K within 2^(n(L+2K+1)) steps, so its exponent sums are at least logarithmic infinitely often
distinct_from:
  bs12-images-in-nv-have-logarithmic-table-length: that is an upper bound, O(log N), on the exponent sums and table lengths of proper-power conjugates in nV; this is a lower bound, valid for every element with a non-periodic point.
  higman-images-in-brick-hosts-have-iterated-log-growth: that bounds the exponent sums of Higman images from above along N = 2^m and asks for a growth gap; this proves the gap at all times, at rate log N, and shows that only sparse times such as N = 2^m remain open.
  bg-in-isometric-brick-hosts-needs-unbounded-exponents: that shows bounded exponent sums force equicontinuity; this is its quantitative, pointwise form in nV, and it fails in 2V_tau, whose odometer has zero exponent sums and no periodic points.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**ESTABLISHED** (lane proof, elementary, not independently reviewed; no priority
claimed; it is the brick analogue of the counting bound for the head speed of Turing
machines).

## Setting

`nV`, tables, `L(g)` and the exponent cocycle `δ_g` are as in
`bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`. For `x ∈ C^n` put
`S_t(x) = δ_(g^t)(x) ∈ Z^n` and `E_g(t) = sup_x |S_t(x)|_∞`.

## Statement

Let `g ∈ nV`, `L = L(g)`, and let `x ∈ C^n` be a point that is not `g`-periodic.

1. **Pointwise pumping.** For every integer `K ≥ 0` there is
   `0 ≤ t < 2^(n(L+2K+1))` with `|S_t(x)|_∞ > K`.
2. **Logarithmic movement.** For every `M ≥ 1`,
   `max_(0 ≤ t ≤ M) E_g(t) ≥ (log_2(M+1)/n − L − 1)/2`. Hence
   `limsup_(N→∞) E_g(N) / log_2 N ≥ 1/(2n)`.
3. **No slow counters in `nV`.** No element of `nV` with a non-periodic point has
   `E_g(N) = o(log N)`. In particular none has unbounded but `o((log log N)^2)` exponent
   sums at all times.

## Proof

**Reading lengths.** Let `ℓ_t(x) ∈ N^n` be least such that `g^t` acts on the brick of
`x` with prefix lengths `ℓ_t(x)` as a prefix replacement. The step "Reading lengths" in
the proof of item 2 of `bg-in-isometric-brick-hosts-needs-unbounded-exponents` is
pointwise in `x`, and in `nV` all sections are the identity. It gives
`ℓ^j_(t+1)(x) ≤ max(ℓ^j_t(x), L − S^j_t(x))` and `ℓ_0 = 0`.

**Item 1.** Suppose `|S_t(x)|_∞ ≤ K` for `0 ≤ t ≤ T`. Put `R = L + K`.
- By the recursion, `ℓ^j_t(x) ≤ R` for all `j` and all `t ≤ T + 1`.
- So for `t ≤ T`, `g^t` maps the brick `Π_j C(x_j[1..R])` by a prefix replacement
  `(u_j w_j) ↦ (v^(t)_j w_j)`, with `u_j = x_j[1..R]` and `|v^(t)_j| = R + S^j_t(x)`.
  Refining a prefix replacement gives a prefix replacement, so this holds on this
  brick.
- Hence `g^t x = (v^(t)_j w_j)_j`, with the tails `w_j` of `x` fixed, and it is
  determined by the tuple `(v^(t)_j)_j`. Each `v^(t)_j` is a word of length in
  `[L, L + 2K]`, so there are fewer than `2^(n(L+2K+1))` tuples.
- Since `x` is not periodic, the points `g^t x`, `0 ≤ t ≤ T`, are distinct. So
  `T + 1 < 2^(n(L+2K+1))`. Item 1 is the contrapositive.

**Item 2.** Take `K = ⌊(log_2(M+1)/n − L − 1)/2⌋`, so that `2^(n(L+2K+1)) ≤ M + 1`. If
`K ≥ 0`, item 1 gives `t ≤ M` with `E_g(t) ≥ |S_t(x)|_∞ ≥ K + 1`. If
`E_g(N) ≤ (1/(2n) − ε) log_2 N` for all `N ≥ N_0`, this fails for large `M`.

**Item 3.** Immediate from item 2. ∎

## Scope and consequences

- **Which elements.** Item 3 of `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`
  shows that every infinite-order `g ∈ nV` with `f g^k f^-1 = g^l`, `|k| ≠ |l|`, has a
  non-periodic point. So the lemma applies to the base of every `BS(1,m)` in `nV`, and to
  every generator of a nontrivial image of Higman's group in `nV`
  (`higman-group-images-in-nv-force-zero-entropy-bs12-cycles`, item 3).
- **Two-sided bound for Baumslag–Solitar bases.** For the base `s` of any `BS(1,m)` in `nV`
  (for example SMART's `BS(1,3) ≤ 3V`, `bs13-embeds-in-brin-thompson-3v`),
  `bs12-images-in-nv-have-logarithmic-table-length` gives `E_s(N) ≤ c log N`. Item 2 gives
  `limsup E_s(N)/log_2 N ≥ 1/(2n)`. So the movement of a Baumslag–Solitar base in `nV` is
  exactly logarithmic, in the limsup sense.
- **Higman's group.** For a nontrivial `H4 → nV`, every generator satisfies both
  `max_(t ≤ 2^m) E_i(t) ≥ m/(2n) − O(1)` (item 2) and
  `E_i(2^m) = O((log m)^2)` (`higman-images-in-brick-hosts-have-iterated-log-growth`,
  item 3). The displacement at the times `2^m` has to be far smaller than at some
  earlier time. This is not a contradiction. The growth gap of that node is therefore
  open only along sparse times, and a slow counter that refutes it would have to be
  slow at the times `2^m` alone.
- **It fails with infinite section groups.** In `2V_tau`, `s = tau × id` has `δ_s ≡ 0` and
  no periodic points. The proof breaks exactly at "determined by the tuple", because
  the sections `tau^k` of `s^t` range over an infinite group. The same proof works in any
  brick group whose sections lie in a finite group closed under restriction, with an
  extra factor `|F|^n`.
