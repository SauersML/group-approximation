---
rg: 2
id: ternary-anti-central-unit-class-is-nonpositive
kind: claim
title: Some positive multiple of the unit class of the ternary anti-central summand is nonpositive in K_0
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the corner equation c e_- b = eps_-; this is its K_0 positivity form, equivalent to it by twisted-leavitt-corner-fullness-equals-absence-of-k0-states, and equivalently failure of the rank condition for the anti-central summand.
  leavitt-group-algebra-not-stably-finite: that is failure of stable finiteness for the binary group algebra over F_2; this is a K_0 positivity failure on the anti-central summand of the ternary group algebra, a condition that implies non-stable-finiteness of that summand.
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

**OPEN.** Let `S_- = eps_- F_3[L_(F_3)(1,2)^x]`. Exhibit `k >= 1`, `r >= 0` and a finitely generated
projective `Q` with

    S_-^r ~= S_-^r (+) S_-^k (+) Q,

that is, `k[eps_-] <= 0` in `K_0(S_-)`. Equivalent forms:
- `[eps_-] <= 0`;
- `S_-^(n+1)` is a direct summand of `S_-^n` for some `n`, that is, `S_-` fails the rank condition.

**Why it matters.**
- *It refutes Gottschalk.* By `nonpositive-unit-class-refutes-ternary-surjunctivity`, it gives a
  one-sided pair in `M_r(F_3[G_3])` and hence a strict automaton on `G_3`.
- *It is exactly what no state can see.* By `anti-central-state-obstruction-equals-stable-finiteness`,
  a state on `(K_0(S_-), [eps_-])` exists iff this claim fails.
- *It is equivalent to the corner equation.*
  - The corner equation implies it with `k = 1` (`anti-invariant-corner-gives-nonpositive-unit-class`).
  - Conversely, it gives the corner (`nonpositive-unit-class-gives-anti-invariant-corner`).
  - Mechanism: `delta(h) = s0 h t0 + s1 h t1` commutes with `w`, so `x -> e_- delta(x)` is a unital
    homomorphism `S_- -> T`. The induced map on projectives halves the unit class and shrinks any
    failure of the rank condition to size one (Theorem E of the artifact).

## Attempts

- *Correction (later on 2026-09-12).* The first version said this condition is weaker than the corner
  equation, with more room through stabilization. That is withdrawn: the two are equivalent, and
  stabilization adds nothing.
- *Image.* In `R = L_(F_3)(1,2)` the isomorphism holds trivially, since `R ~= R (+) R`.
- *Obstructions ruled out.*
  - Every additive invariant is inert on its own, since the target's only `K_0` consequence is
    `[eps_-] <= 0` (Theorem B(i) of the artifact).
  - `S_-` has no finite-dimensional images
    (`ternary-anti-central-summand-has-no-finite-dimensional-images`).
  - The only possible obstruction is a state. Its natural source, a rank function from an
    `F_3`-linear sofic approximation of `G_3` with `z` acting as `-1`, is the open gate, and property
    (T) gives no rank rounding over finite fields.
- *Lifting form* (Section 9 of the artifact).
  - Every size reduces to a two-pair Cohn family in `S_-`.
  - Every solution type over `R` reduces to lifting `(s0, s1)` or `(s0, s1 s0)`, through lifts of
    `GL_1(R) = G` and `GL_2(R) = EL_2(R)`.
  - The obstruction is invertibility of `1 + E` for a kernel-valued `E`.
- *Where it dies today.* No lift with invertible `1 + E` is known, and no state on `K_0(S_-)` is
  known. By Theorem E exactly one of the two exists.
- *Halving endomorphism* (gk-l3-state; artifact `ternary-corner-state-sources-2026-09-12.md`, Section 5).
  - `w` and `d` centralize `δ(G)`, so `ψ(x) = e_- δ_*(x)` is a unital map `S_- -> e_- S_- e_-`.
  - Through `M_2(δ(S_-)) ⊂ S_-` it gives only `[eps_-] = 2[e_-]`, which a state allows.
  - An intertwiner implementing `ψ` would give `eps_- ~ e_-` and so `[eps_-] <= 0`. But it would satisfy
    `V[g] = [δ(g)]V`, and so `V = 0` (`self-similar-leavitt-intertwiners-have-no-exact-lift`).
  - Any isomorphism with `k >= 1` is the Cohn-family lift.
- *State side* (gk-l3-state, 38533db3fe). The only concrete source of a state is a characteristic-three
  rank model moving `z` on each finitely generated subgroup containing `z`, `w`, `d`
  (`anti-central-rank-models-kill-ternary-corner-witnesses`). By compactness local models suffice, and
  their existence is as open as this claim.
- *Module route audited again; halving-invariant states* (lane w3-corner-module, artifact
  `halving-invariant-k0-states-2026-09-12.md`).
  - The module-isomorphism start gives nothing beyond census §9: stabilization reduces to one Cohn
    family, the lift orbits reduce to two rows, and a lift that is both left and right invertible would
    give `S_- ~= S_-^2`, excluded by the trace.
  - New normalization: if `(K_0(S_-), [eps_-])` admits any state, it admits one with `s o F_* = s/2`,
    where `F` is the halving map of census §7.2. Proof by Markov–Kakutani, or Cesàro averaging along
    `F_*` (`twisted-leavitt-k0-states-can-be-chosen-halving-invariant`).
  - So this claim holds iff no halving-invariant state exists. Such a state is forced to take the value
    `2^(-k)` on the tower `F_*^k([eps_-])`, and any state source can be averaged into one.
  - Where it stops: no state and no Cohn family is known.
- *States are forced on the signed Thompson group* (lane w4-hadamard-f3, artifact
  `hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md`, Section 2).
  - Every state on `(K_0(S_-), [eps_-])` gives Haar measure on the clopen indicators of `M_-`. On every
    idempotent matrix over `eps_- F_3[K]`, for `K` a finite subgroup of `E x| V` or a conjugate of one, it gives
    the lifted trace `2 dim / |K|` (`anti-central-k0-states-equal-lifted-trace-on-signed-thompson`).
  - So a state has no freedom on the locally finite part of the signed Thompson group. This claim holds iff
    that forced data does not extend to a state.
  - Where it can see `h`: the semidihedral group `<w, d, h>` is not conjugate into `E x| V`, and the split of
    a state between its evaluation block and its twisted block is not forced. Whether it is `1/2` is open.
  - Also: the F_9 Hadamard corner is the swap corner conjugated by a constant unit
    (`hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent`), so it adds no room.
- *Relative positivity of the lifted trace* (lane w4-trace-state, artifact
  `lifted-trace-state-extension-2026-09-12.md`).
  - The additive 3-adic lifted trace `s_3 = 2 t_3` is defined on all of `K_0(S_-)`, and it obeys every known state
    law:
    - `s_3([eps_-]) = 1`;
    - the lifted trace on every finite subgroup, including Haar measure on clopens;
    - `s_3 o F_* = s_3/2` and `s_3 o alpha_* = s_3`.
  - So no equality relation among finite-subgroup projectives changes the lifted trace.
  - A state exists iff the lifted trace is nonnegative on positive classes spanned by signed-Thompson finite-subgroup
    projectives (`anti-central-state-exists-iff-lifted-trace-relatively-positive`). So this claim holds iff some stable
    isomorphism `P (+) S_-^r ~= Q (+) X (+) S_-^r`, with `P, Q` over finite subgroups of `E x| V`, has
    `trl(P) < trl(Q)`. The negation is the open `anti-central-lifted-trace-is-relatively-positive`.
  - The complement `X` has negative rational lifted trace. By Kaplansky positivity it has no finite-support
    idempotent lift over `Z_3[G]`.
  - Where it stops: no positivity principle is known for traces of infinite-support `Z_3` idempotent lifts.
