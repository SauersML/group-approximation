---
rg: 2
id: wold-multiplicity-blinds-commutant-packing-sizes
kind: claim
title: Wold multiplicity blinds every packing-profile size of approximate Kazhdan commutants to the compression shift
distinct_from:
  invariant-size-collapse: that is the abstract lemma that a conjugation-invariant, strictly monotone size forbids strict compression, stated for subgroups and von Neumann subalgebras; this works with finite-stage 2-norm packing numbers of approximate commutant microstates, which are not sizes of the limit algebras, and proves that the shift part can never register on them at a scale where the commutant is finite-dimensional.
  commutant-density-trace-blind: that computes the normalized dimension of exact commutants of exact or asymptotic representations; this bounds the covering entropy of the approximate commutant sets themselves, at every fixed radius, and adds the Wold-multiplicity inequality at all subquadratic scales.
  summit-wreath-intrinsic-lattice-commutant-is-abelian: that proves quadratic entropy-nullity for one intrinsic commutant in the summit wreath factor; this proves it for the approximate commutant microstates of every trace-preserving model of any infinite Gamma, and treats scales other than d^2.
  atlas-entropy-and-cmi-stop-at-face-emptiness: that fences covering entropy of Atlas relator microstate spaces against CE-face emptiness; this fences packing sizes as a tool for comparing a Kazhdan commutant with its compressed copy.
  kazhdan-commutant-compression-stability-is-finitary: that turns normalization into a uniform finite-dimensional inequality; this shows that one natural way to prove that inequality, comparing packing profiles of the two approximate commutants, cannot detect the defect.
---

**ESTABLISHED (fence).** Proof: `wold-multiplicity-commutant-packing-proof`.

## Setting

- `Gamma <= G` countable groups, `S` a finite symmetric generating set of `Gamma`,
  and `u in G` with `u Gamma u^-1 <= Gamma`.
- For each `s in S` fix a word `w_s` in `S` with `u s u^-1 = w_s` in `G`. Put
  `L = max(1, max_s |w_s|)`.
- `sigma: G -> U(M^omega)`, where `M^omega = prod_omega M_(d_n)` and `f(d_n) -> infinity` is
  any normalizing scale.
- `sigma_n: F(S cup {u}) -> U(d_n)` are free-group homomorphisms lifting `sigma`.
- `tr` is the normalized trace, and `||x||_2 = tr(x^* x)^(1/2)`.
- Fix `R >= 1`, and put `T_n = Ad sigma_n(u)^-1`.

Define the microstate sets:

```text
X_n(eps)  = { x in M_(d_n) : ||x||_op <= R,  max_s ||[sigma_n(s), x]||_2 <= eps }      (A-microstates)
X^B_n(eps) = T_n^-1 X_n(eps)                                                          (B-microstates)
D_n(theta) = { y in X_n(theta^2) : |tr(y^* T_n w)| <= theta^(1/2) for all w in X_n(theta) }   (shift microstates)
```

- `X_n(eps)` lifts `A = sigma(Gamma)' cap M^omega`.
- `X^B_n(eps)` lifts `B = sigma(u) A sigma(u)^*`, the commutant of `u Gamma u^-1`.
- `D_n(theta)` lifts the Wold shift space `D = L^2(A) ⊖ L^2(sigma(u)^* A sigma(u))` of
  `un-tracial-support` §0.

Write `P_delta` for the maximal size of a `delta`-separated subset in `||.||_2`, and define the
packing profiles

```text
h_A^f(delta) = inf_(eps>0)       lim_omega log P_delta(X_n(eps))   / f(d_n),
h_B^f(delta) = inf_(eps>0)       lim_omega log P_delta(X^B_n(eps)) / f(d_n),
h_D^f(delta) = liminf_(theta->0) lim_omega log P_delta(D_n(theta)) / f(d_n).
```

## Statements

**(WH1) Wold multiplicity inequality.** For every `delta in (0,1]`, every integer `K >= 1` and
every scale `f`:

```text
h_A^f( delta / (sqrt 2 K) )  >=  K h_D^f(delta).
```

Consequently:
- If `h_D^f(delta_0) = c > 0`, then `h_A^f(t) >= c delta_0 / (2 sqrt 2 t)` for all
  `t <= delta_0/sqrt 2`.
- In particular, if `h_A^f(t) = o(1/t)` as `t -> 0`, for instance if `A` has finite upper box
  dimension at scale `f`, then `h_D^f` vanishes identically.

This part uses neither property (T) nor any trace condition.

**(WH2) Quadratic nullity.** Suppose `Gamma` is infinite and `tau(sigma(gamma)) = 0` for
`gamma != 1` in `Gamma`, as for every trace-preserving `sigma`. Then for every `delta > 0` and
every `R`:

```text
h_A^(d^2)(delta) = 0,   hence h_B^(d^2) = h_D^(d^2) = 0.
```

Quantitatively, if `W` is a symmetric set of `N` words of length at most `L_W`, with fibres of
size at most 2 in `Gamma`, and `2 L_W eps <= delta <= R`, then

```text
limsup_omega d_n^-2 log P_(4 delta)(X_n(eps)) <= (16/N) log(3R/delta).
```

**(WH3) Exact invariance.** `h_B^f = h_A^f` for every scale `f`.

**(WH4) Faithfulness, under (T).** Suppose `(Gamma, S)` has Kazhdan constant `kappa`. Let
`y in D` with `||y||_op <= R`, and let `(y_n)` be a lift with `||y_n||_op <= R`. For every
`theta < kappa^2/R^2`, `y_n in D_n(theta)` for `omega`-almost every `n`. So a nonzero `D`
does put nonzero elements into the shift microstates.

## What this kills

Take the *packing transcription of the Hamming proof* of
`hyperlinear-groups-kill-rigid-compression-defects`. By
`rigid-compression-defect-normalization-dichotomy` it suffices to treat trace-preserving `sigma`.
The transcription measures both commutants by finite-stage covering or packing counts at some
scale `f`. It then argues that a nonzero shift `D` makes the `B`-count strictly larger than the
`A`-count, while conjugation by `sigma(u)` makes them equal.

Every member dies at the strict-increase step:

- **Scale `d^2`.** Both profiles are identically 0 (WH2), so nothing registers at all.
- **Any scale where the `A`-profile is `o(1/t)`.** Orthogonal splitting `B ⊇ A ⊕ sigma(u) D sigma(u)^*`
  lower-bounds the `B`-profile only by the `D`-profile, which is 0 by WH1. Meanwhile
  `h_B = h_A` exactly (WH3).
- **Remaining scales.** Here the `A`-profile grows like `1/t`, so `A` has infinite box dimension
  at that scale. A contradiction must come from a non-product part of the packing counts.

The named invariant is the *Wold multiplicity*: `T_n` places `K` asymptotically orthogonal
copies of the shift microstates inside the commutant microstates, for every `K`.

The Kun--Thom Hamming argument and `commutant-no-growth` escape because they compare
exact per-stage counts with no ultralimit, so no shift exists at any finite stage. Those
escapes are the exactification attempts already recorded on the claim.

## Scope

- This does not show that normalization fails, and it does not show that (T) cannot be used.
- It says nothing about sizes that are not packing counts of these microstate sets, for
  example spectral multiplicities of the averaging operators of WH2 or orbital and 1-bounded
  entropies with subtracted baselines.
- WH4 shows these microstate sets are the right ones: a genuine defect does occupy them.
