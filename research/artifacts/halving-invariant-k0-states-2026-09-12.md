# Halving-invariant states on twisted Leavitt factors

Lane `w3-corner-module`, 2026-09-12. Supports `twisted-leavitt-k0-states-can-be-chosen-halving-invariant`.

## 0. Why this lane lands a state theorem and not a lift

The directive was to reach `ternary-anti-central-unit-class-is-nonpositive` through module isomorphisms
`S_-^r ~= S_-^r (+) S_-^k (+) Q` lifting `R ~= R^2`. Main already settles that route:
- *No room from stabilization.* Theorem E of `ternary-anti-central-invariant-census-2026-09-12.md`
  (3 => 2) reduces every size, multiplicity and complement to one two-pair Cohn family (census §9.1).
- *Orbit reduction.* Lifting reduces to the rows `(s0, s1)` and `(s0, s1 s0)`; the obstruction is
  invertibility of `1 + E` with `E` kernel-valued (census §9.2–9.3).
- *The matrix copy.* It supplies `[eps_-] = 2[e_-]` and no isometry from `eps_-` into `e_-`; the halving
  endomorphism has no intertwiner (`ternary-corner-state-sources-2026-09-12.md` §5).
- *Two-sided lifts.* A lift of `(s0, s1)` that is both left and right invertible would give
  `S_- ~= S_-^2`, excluded by the trace (`anti-central-ternary-summand-has-no-binary-leavitt-family`).
  So every Cohn-family lift has a nonzero defect idempotent.

By Theorem E the only alternative to a lift is a state. This artifact proves that states can be taken
self-similar under the halving map, which pins down what any obstruction must look like.

## 1. Setting

Take the Theorem E setting (census §7): `A = A_iota`, unit `eps_iota`, twist order `m >= 2`, corner
`T = e_H A e_H` with `A ~= M_m(T)`, and the unital ring homomorphism `psi(x) = e_H D(x)` from `A` to `T`.
Let `V(A)` be the monoid of finitely generated projective right `A`-modules, `u = [A]`, and
`K_0(A)` its Grothendieck group with positive cone `K_0^+ = image of V(A)`.

Census §7.2 gives a monoid homomorphism `F: V(A) -> V(A)`, induced by `Phi = M_m(psi)` followed by
`M_m(T) ~= A` and the Morita identification, with `F(m·u) = u` (census §7.2 writes this as `F(mu) = u`).
Put `x = F(u)`; then `m·x = u`.

Verified: `w3-vf-linear` passed the theorem at 71bbad41b1 (Section 8.1 of
`w3-vf-linear-verification-2026-09-12.md`).

A *state* on `(K_0(A), u)` is an additive map `s: K_0(A) -> R` with `s(K_0^+) >= 0` and `s(u) = 1`.

## 2. Theorem

**Theorem.** If `(K_0(A), u)` admits a state, it admits a state `s` with

    s(F_*(a)) = s(a) / m     for every a in K_0(A),

where `F_*` is the group endomorphism extending `F`. In particular `s(F_*^k(u)) = m^(-k)` for all `k >= 0`.

**Proof.**
1. *`F_*` is order-preserving.* A monoid homomorphism `V(A) -> V(A)` extends uniquely to a group
   endomorphism of the Grothendieck group, and it maps the positive cone into itself.
2. *`Phi_s = m · s o F_*` is a state.* It is additive and nonnegative on `K_0^+` by step 1. For the
   normalization, `m·x = u` gives `m·s(x) = s(u) = 1`, so `Phi_s(u) = m·s(F(u)) = m·s(x) = 1`.
3. *The state space is compact convex.* View states inside `R^(K_0(A))` with the product topology.
   - Convexity and closedness are immediate from the defining conditions.
   - Boundedness: every `a = [P] - [Q]` with `P, Q` summands of `A^n` satisfies `-nu <= a <= nu`
     in the preorder, so `|s(a)| <= n` for every state. By Tychonoff the state space is compact.
4. *Fixed point.* `s -> Phi_s` is affine and continuous (each coordinate `Phi_s(a) = m·s(F_* a)` is a
   coordinate projection). A continuous affine self-map of a nonempty compact convex subset of a locally
   convex space has a fixed point (Markov–Kakutani). Explicitly: the Cesàro means
   `M_N = (1/N) sum_(k<N) Phi^k(s)`, with `Phi^k(s) = m^k · s o F_*^k`, are states, and
   `Phi(M_N) - M_N = (Phi^N(s) - s)/N`. If `n_a` bounds `|t(a)|` over all states `t` (step 3), then
   `|Phi(M_N)(a) - M_N(a)| <= 2 n_a / N`. So any limit point `s_inf` of the `M_N` satisfies
   `m · s_inf o F_* = s_inf`.
5. *Tower values.* Iterating, `s(F_*^k(u)) = m^(-k) s(u) = m^(-k)`. QED

## 3. Consequences

- *Exact form of the dichotomy.* With Theorem E (1 <=> 5): the cyclic corner is full iff `(K_0(A), u)`
  admits no halving-invariant state. At `(q, d, m) = (3, 2, 2)` this reads: the ternary corner holds iff
  no state `s` on `(K_0(S_-), [eps_-])` satisfies `s o F_* = s/2`.
- *Normalizing state sources.* A characteristic-three rank model moving `z` gives a state
  (`anti-central-rank-models-kill-ternary-corner-witnesses`); its Cesàro average along `F_*` is
  halving-invariant. So a proof that the corner fails may always target an invariant state.
- *Forced values.* An invariant state takes the value `m^(-k)` on every tower idempotent `F^k(u)`, the
  class of `Phi^k(e_11) A`. Any candidate state source that cannot realize these values is excluded.

## 4. Where it stops

This is a normalization, not a decision. No state on `(K_0(S_-), [eps_-])` is known, invariant or not,
and no Cohn family is known. The theorem says an obstruction, if it exists, can be chosen compatible
with the self-similar structure of the Leavitt host.
