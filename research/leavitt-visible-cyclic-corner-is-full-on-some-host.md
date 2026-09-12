---
rg: 2
id: leavitt-visible-cyclic-corner-is-full-on-some-host
kind: claim
title: On some finite-field Leavitt host the cyclic averaging idempotent is full in the Leavitt-visible factor
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the single host q = 3 with d = m = 2; this asks for any prime power q, arity d and admissible cycle length m, and every solution of that claim is a solution of this one.
  projective-ternary-swap-idempotent-is-full: that is the corner equation on the trivial-character factor F_3[PG], where the Leavitt evaluation vanishes; this is the corner equation on the Leavitt-visible factor of any host.
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

**OPEN.** Exhibit:
- a prime power `q = p^r`;
- an arity `d >= 2`;
- an admissible cycle length `m = 1 + j(d-1)`, `j >= 1`, with `p` not dividing `m`;
- elements `b', c'` of the Leavitt-visible factor `A_iota` of `F_q[L_(F_q)(1,d)^x]` with

      c' e_H b' = eps_iota,   e_H = eps_iota (1/m) sum_k [g^k],

  where `g` is the `m`-cycle permutation unit of an `m`-ary Leavitt family.

When `m` divides `q - 1`, this is a unital `m`-pair Cohn family in the corner `T = e_H A_iota e_H`
(`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`).

## Attempts

- **The image equation holds on every host.** `b = sum_i s_i` and `c = (1/m) sum_i t_i` satisfy
  `c . pi(e_H) . b = 1` in the Leavitt algebra. The lift to `A_iota` is open. Direct finiteness does
  not pass to quotients (`direct-finiteness-not-inherited-by-quotients`), so the image solution alone
  transports nothing. This is where it dies today.
- **Monotone in the field.** A solution over `F_q` gives one over every `F_(q^r)` with the same
  `(d, m)`: multiply by the refined central idempotent (Proposition 4 of the artifact). So work in the
  colimit over finite fields. A finitely supported solution there lives over one finite field.
- **The gate.** If `L_(F_q)(1,d)^x` is `F_q`-linear sofic, then `F_q[G]` is stably finite
  (`linear-sofic-group-algebra-is-stably-finite`) and this host dies. Property (T) gives no rank
  rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`), so the
  gate is not settled that way.
- **What stays silent under the twist.** Augmentation, commutative quotients and the lifted trace. The
  lifted trace forbids `e_H ~ eps_iota` but not `1 <= e_H`.
- **Exact reformulation, with no idempotent** (`cyclic-separated-one-sided-pairs-equal-full-corners`).
  It suffices to find a one-sided pair `c a = eps_iota` in `A_iota` whose cyclic cross terms
  `c [g^i] a`, `0 < i < m`, all vanish. When `m` divides `q - 1` this is also necessary. So a
  solution need not lift the image solution: any one-sided pair with vanishing cross terms will do.
- **Fullness is the absence of states** (lane gk-l3-obstruct, 2026-09-12).
  - *On one twisted host.* When `m | q - 1`, this corner is full iff the visible factor fails the rank
    condition, iff its unit class is nonpositive in `K_0`, iff `(K_0(A_iota), [eps_iota])` admits no
    state (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`).
  - *Across finite fields.* The question for all finite fields of one characteristic and arity is one
    colimit ring (`leavitt-visible-states-are-factorwise-and-colimit-stable`).
  - *The obstruction hypothesis.* `leavitt-visible-colimit-factors-admit-k0-states` would refute this
    claim.
- **The characteristic-two host (4, 2, 3)** (lane w3-corner-f4, 2026-09-12; artifact
  `research/artifacts/quaternary-twisted-corner-census-2026-09-12.md`).
  - *Census.* `eps_iota = [1] + ω² [ω] + ω [ω²]` and `e_1 = (1 + [g] + [g²]) eps_iota`. Augmentation,
    commutative quotients, the canonical trace (`tau(eps_iota) = tau(e_1) = 1`) and the lifted 2-adic
    trace (`1/3` against `1/9`) are silent. The characteristic-three trace no-go for binary Leavitt
    families does not transfer. Finite-dimensional images stay open at `q = 4`, because simplicity mod
    scalars is recorded only for odd `q` and prime fields.
  - *States from rank models, every twisted host.* A rank model with nonzero visible scalar component
    gives a state and kills witnesses (`twisted-rank-models-kill-visible-cyclic-corner-witnesses`).
  - *A binary feeder.* Fullness of `1 + g + g²` in `F_2[R^x]`
    (`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`) ascends to this host by multiplying
    with `eps_iota`, and by itself refutes Kaplansky for `R^x`.
  - *Where lifts die.* Phase lifts `E_p = 1 + ω² [1 + ω² p] + ω [(1 + ω² p)²]` give a crossed product
    `C(M_iota, F_4) ⋊ V` over `Z/3`-valued finitely additive measures of total mass 1. The Fourier unit
    `h = Σ ω^(ij) s_i t_j` conjugates `e_1` to a clopen of Haar measure `1/3`, so every honest compression
    dies. The mod-2 Haar trace gives `1` on both sides. A witness needs non-function idempotents with
    mod-2 cancellation, or units outside the phase-Thompson group.
