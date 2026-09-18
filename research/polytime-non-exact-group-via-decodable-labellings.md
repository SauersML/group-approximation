---
rg: 2
id: polytime-non-exact-group-via-decodable-labellings
kind: route
title: Run Dehn's algorithm with a decoder and a short-path oracle on the few components of girth below twice the word length
target: non-exact-group-with-polytime-word-problem-exists
requires: [decodable-small-cancellation-families-give-polytime-wp]
---

This route proves `decodable-small-cancellation-families-give-polytime-wp`. The target
then follows as soon as a family with (SC), (Dec) and (Short) exists, which is OPEN.

**Greendlinger step.** Take the same inputs as `decidable-graphical-non-exact-groups-proof`
step 5: Gruber's Lemma `lem:graphical_simple`, with the Lyndon--Schupp V.4.5 argument
transferred to graphical minimal diagrams. Let `w` be nonempty, cyclically reduced, and
`= 1` in `G(Γ)`. Then some cyclic conjugate `w = u w_2` has an arc `u` with
`|u| > |c|/2` of a simple cycle `c` in some `Γ_n`.
- Write `c = P·Q`, where `P` carries `u` from `x` to `y` and `Q` runs from `y` back to
  `x`. Then `|Q| < |u|`, and `g_n ≤ |c| < 2|u| ≤ 2|w|`.

**The algorithm.** Repeat until `w` is empty (answer `w = 1`) or no step applies (answer
`w ≠ 1`):
1. Freely and cyclically reduce `w`.
2. For each cyclic subword `u`, with `O(|w|^2)` choices, and each `n` with `g_n < 2|w|`
   (at most `2|w|` choices, since `g_n ≥ n`):
   - apply (Dec) to `(n,u)`, which is allowed since `|u| > g_n/2`;
   - if it returns a path from `x'` to `y'`, apply (Short) to `(n, y', x', |u|)`;
   - if that returns a path label `v` with `|v| < |u|`, then `u v` is closed in `Γ_n`, so
     `u = v^(-1)` in `G(Γ)`. Replace `u` by `v^(-1)`, which strictly shortens `w`, and
     restart.

**Correctness.**
- **Soundness.** Every replacement preserves the value of `w`. So an answer `w = 1` is
  correct.
- **Completeness.** Suppose `w = 1` and `w` is nonempty. Take the Greendlinger `(u, n, P, Q)`.
  - Suppose (Dec) returns a path `P'` carrying `u` other than `P`. If `P'` is not the
    image of `P` under a label-preserving automorphism `φ`, then `P, P'` form an
    essential piece of length `|u| > |c|/2` inside the simple cycle `c`, contradicting
    (SC). So `P' = φ(P)`.
  - Then `φ(Q)` is a path from `y'` to `x'` of length `< |u|`, so (Short) succeeds and a
    step applies.
- **Termination and time.** Each step shortens `w`, so there are at most `|w|` rounds.
  Each round makes `O(|w|^3)` calls to (Dec) and (Short). Every call has input size
  `poly(|w|)`, since the vertex descriptions come from (Dec). So the total time is
  polynomial.

**Non-exactness.**
- (SC) with Gruber's framework, as in Osajda arXiv:1406.5015 Lemma `l:remb`, citing
  Ollivier Thm 1 and Gruber 5.10, embeds each `Γ_n` isometrically in the Cayley graph.
- A family of finite graphs of degree between 3 and `D` with girth `→ ∞` has no property A
  (Willett; used this way in Osajda's Theorem `t:main`). Property A passes to subspaces.
- So `G(Γ)` has no property A. `∎`

**Scope.** The proof inherits the Greendlinger transfer from
`decidable-graphical-non-exact-groups-proof`, which is flagged there for a referee.
(Short) is only ever called with `ℓ = |u|` and with a promise that the distance is below
`ℓ`, so a promise version of (Short) suffices.
