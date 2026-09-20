---
rg: 2
id: brin-thompson-2v-lifts-el2-laurent-linear-ca-generators
kind: claim
title: "Some prime p, some continuous affinely spanning phi : C^2 -> (F_p^2)^Z, and finitely many elements of 2V lift affine maps of (F_p^2)^Z whose linear parts generate a group containing EL_2(F_p[t,t^-1])"
distinct_from:
  char-p-burger-lamp-realizations-refute-haagerup: that proves the criterion, that such a realization in any nV refutes Haagerup, and lifts h alone; this is the existence of the full realization in 2V, the dynamical input the criterion needs
  brin-thompson-2v-is-not-a-t-menable: that is the analytic conclusion; this is a purely symbolic-dynamical existence statement which implies it, and could be refuted without affecting that claim
  piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts: that kills every realization whose torus lift is piecewise baker; this asks for a realization, which must therefore use a lift of h with no power nV-conjugate to a piecewise local baker map
---

Notation is as in `char-p-burger-lamp-realizations-refute-haagerup`:
- `R = F_p[t,t^-1]`;
- `M^ = (F_p^2)^Z`, with `γ ∈ GL_2(R)` acting by `(γ^-1)^T(σ)`.

**Claim.** There exist:
- a prime `p`;
- a continuous `φ : C^2 → M^` such that no nonzero `m ∈ R^2` makes `x ↦ φ(x)(m)` constant;
- elements `g_1, ..., g_k ∈ 2V` and affine maps `a_i(ξ) = γ_i·ξ + v_i`;

such that `φ∘g_i = a_i∘φ` and `⟨γ_1, ..., γ_k⟩ ⊇ EL_2(R)`.

It suffices to lift, with one common `φ`, the five maps `e_12(1)`, `e_12(t)`, `e_21(1)`, `e_21(t)`
and `h = diag(t,t^-1)`, each up to translation. By Theorem R, this claim implies that `2V`, and
hence every `nV` with `n ≥ 2`, is not Haagerup. The implication is recorded as the route
`brin-thompson-2v-not-a-t-menable-via-char-p-lamp-lifts`.

The claim is false in `V` (the case `n = 1`), since `V` is Haagerup. So one-dimensional versions
cannot be used to test it.

**OPEN.**

## Attempts

- 2026-09-19 (swarm-0917-w17-w17-nv-break), in `char-p-burger-lamp-realizations-refute-haagerup`:
  - `h` lifts through a surjective `φ` by the baker power `B^k`. This is Proposition B there.
  - For `p ≥ 3`, `injective-char-p-lamp-realizations-miss-fixed-points` rules out an injective,
    conjugacy-type `φ`.
- 2026-09-19 (swarm-0917-w21, swarm branch only, commit 2f3311cc29): if the lift of `h` is
  `nV`-conjugate to one global baker power, the reading is globally side-split. Then every lift is
  diagonal, so there are no shears and no `w`.
- 2026-09-20 (swarm-0917-w22-w22-z-follow): `piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts`
  (ESTABLISHED) extends this kill.
  - *Scope.* It applies if **any** lift of any affine map with linear part `h` has a power that is
    `nV`-conjugate to a piecewise local baker map. The boxes may have independent sides and signs.
  - *Invariant.* Each lamp entry deep down reads one digit coordinate on each box (its side), and
    `nV` pieces preserve coordinate tails.
  - *Failure step.* A shear `e_12(r)` adds `α`-entries into `β`. So on some box it would have to
    equate a function of one coordinate's deep tail with a function reading that coordinate only
    shallowly. The recurrence lemma and affine spanning forbid this.
  - *Sharpness.* A two-box baker in 2V lifts `h` and `w` for `p = 2`. So monomial linear parts are
    realizable, and exactly one kind of generator, the shear, is missing.
  - *What a realization now needs.* A lift of `h` that is not piecewise baker, or a variant without
    a torus element (the one-sided `F_p[t]` version, which needs countably many lifts). Both are
    untested.
- 2026-09-20 (swarm-0917-w23-w23-z-follow): `one-sided-three-shear-lamp-criterion-drops-the-torus`
  (ESTABLISHED) reframes this claim as a strictly weaker, torus-free lifting problem.
  - *Criterion.* Lifting three one-sided linear CAs of `(F_p^2)^N` through one affinely spanning
    `φ` already refutes Haagerup for `nV`, for every `p` including `p = 2`. The CAs are
    `e_12(1)`, `e_12(t)` and `e_21(t)`. For `p ≥ 3` two suffice.
  - *Relative (T).* For `Γ_0 = ⟨e_12(1), e_12(t), e_21(t)⟩`, a mean on the nonzero dual that is
    invariant would put mass `1/2` on each of the sectors `deg x − deg y = ±1`, and then mass
    `1/2` more on `= 0`.
  - *Restriction.* Any realization of this claim restricts to one of that criterion by forgetting
    negative indices. So the wave-22 survivor "one-sided variant, countably many lifts" becomes
    three lifts, and the side-split kill (which needs `h`) does not reach it.
  - *Not done.* No lifts are constructed. Whether a piecewise-baker lift of a hyperbolic element
    such as `e_12(1)e_21(t)` forces a virtually abelian linear group is left as a spark.
