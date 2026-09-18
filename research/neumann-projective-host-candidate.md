---
rg: 2
id: neumann-projective-host-candidate
kind: claim
title: A residually finite projective thickening of SL_d(Z[1/2]), d ≥ 3, contains Neumann's group and escapes both known finite-presentation obstructions; whether it is finitely presented is open
distinct_from:
  affine-thickening-hosts-are-never-fp: that proves every affine thickening is infinitely presented by periodizing over an invariant sublattice; this is a non-affine thickening where that mechanism is unavailable by the normal subgroup theorem.
  neumann-doubling-host-candidate: that was the one-dimensional affine candidate, since refuted; this is the higher-rank projective candidate.
  neumann-alternating-product-group-embeds-in-fp-rf-group: that is Minasyan's open question; a finite presentation of this candidate would answer it affirmatively.
---

**ESTABLISHED** for items (1)–(3). **REFUTED as a host:** `Γ_P` is not finitely presented, by the
Schur multiplier obstruction in `schur-multiplier-obstruction-kills-thickening-hosts`
(infinitely many coordinate Schur classes survive in `H_2(N)_Γ`). Lane bh-free-59,
written inline, not independently reviewed. The Margulis normal subgroup theorem and the
congruence subgroup property for `SL_d(Z[1/2])` are cited as textbook inputs, not
re-read.

## The candidate

Let `d ≥ 3`, `Q = SL_d(Z[1/2])`, and let `M` be the odd integers `m ≥ 5`. Then `Q` acts on
`X_m = P^{d-1}(Z/m)`, the unimodular vectors of `(Z/m)^d` modulo units, because `2` is
invertible mod `m`. In each `X_m`, let `α` be the 3-cycle
`([e_2], [e_1+e_2], [2e_1+e_2])`. Put

    Γ_P = ⟨Q, α⟩ ≤ ∏_{m∈M} Sym(X_m).

## Proven properties

**(1) Γ_P is finitely generated, residually finite, and contains Neumann's group G.**
- `Q` is finitely generated, and `Γ_P` lies in a product of finite groups.
- Let `u = I + E_{12}`. The affine line `ℓ_m = {[xe_1 + e_2] : x ∈ Z/m}` consists of
  distinct points, and `u` acts on it by `x ↦ x+1`. On `ℓ_m`, `⟨α, u⟩` is Neumann's
  coordinate `m`.
- Off `ℓ_m`, `α` is trivial. So a word acts off `ℓ_m` as `u^σ`, where `σ` is its
  `u`-exponent sum. Every relator of `G` has `σ = 0` (`neumann-group-is-locally-finite-by-z-and-not-fp`).
- Hence `⟨α, u⟩ ≅ G`, exactly with Neumann's degree set `M`.

**(2) The co-infinite obstruction does not apply.** The maximal coordinate set for `Q` is
the odd moduli, and `M` is co-finite in it. Over `SL_d(Z)` one would have to use all `m`.
Its odd-only version is **not** finitely presented, by the argument of
`neumann-doubling-host-candidate`: words supported on a single even coordinate exist by
the window proposition. That is why `Z[1/2]` is used here.

**(3) No periodization fake over a normal subgroup exists.** The fakes of
`affine-thickening-hosts-are-never-fp` periodize `α` over an infinite subgroup `D`,
normalized by `Q`, that acts freely on the limit set `P^{d-1}(Q)`. In the affine case,
`D = kA^d`. Here no such `D` exists inside `Q`:
- By the normal subgroup theorem, a normal subgroup of `Q` is central, hence `±1`, which
  acts trivially on `P^{d-1}`, or of finite index.
- By the congruence subgroup property, a finite-index normal subgroup contains some
  `I + nE_{12}`, `n ≠ 0`, which fixes `[e_1]`.

## Why the other fake family also looks blocked (heuristic, not proved)

The sparse-orbit fakes of `neumann-doubling-host-is-not-fp` need a sparse set of cluster
positions invariant under the centralizer `C_Q(α)`. Here `C_Q(α)` fixes the three points
of the line `P(⟨e_1,e_2⟩)`, so it acts on that plane as `±1`. It still contains the
unipotent radical `Hom(⟨e_3,…,e_d⟩, ⟨e_1,e_2⟩)`, whose orbits off the line are large.
No sparse invariant configuration is visible. This paragraph is a heuristic, not a
theorem about all fakes.

## What was open (now decided: not finitely presented)

With `H_K = ⟨qαq^{-1} : q ∈ B_K(Q)⟩`, Step 2 of `affine-thickening-hosts-are-never-fp`
applies verbatim: `Q` is finitely presented for `d ≥ 3`, and the normal closure of `α` is
locally finite. So

    Γ_P is finitely presented  ⟺  Γ_P = ⟨gens(Q), α | rels(Q), rels(H_K)⟩ for some K.

The content is arithmetic. Two triples `qT_0`, `q'T_0` collide mod `m` exactly for the
`m` dividing explicit minors, so relations among the `α_q` record divisibility. A finite
presentation must derive all of them from finitely many, using `SL_d(Z[1/2])`. Two
possible levers:
- Steinberg commutators `[e_{13}(a), e_{32}(b)] = e_{12}(ab)` relate configurations whose
  invariants multiply.
- Prime invariants have no such factorization, and are the first test.

A yes answers MO 491978 (Minasyan) affirmatively, and with it Minasyan's title question.

## Lesson for general BH

**Design rule for residually finite thickening hosts.** Take the acting group `Q` to be a
higher-rank lattice. Then the normal subgroup theorem and the congruence subgroup property
remove every periodic structure that could fake truncated presentations. What remains is
an **arithmetic incidence problem**: can finitely many relations over `SL_d(Z[1/2])`
generate all the divisibility data of `P^{d-1}(Z/m)`? This is the same shape of question
as finite presentability of congruence quotients, so tools from `S`-arithmetic
presentations (Steinberg relations, bounded generation) are the natural ones for
residually finite Boone–Higman hosts.
