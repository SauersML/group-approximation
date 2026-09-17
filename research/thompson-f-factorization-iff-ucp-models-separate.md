---
rg: 2
id: thompson-f-factorization-iff-ucp-models-separate
kind: claim
title: Thompson's F has the factorization property exactly when compressions of honest representations by almost-invariant projections do not almost commute
distinct_from:
  thompson-f-hyperlinear-iff-relator-system-hs-unstable: that is the unitary form, where the models are arbitrary unitary almost-solutions of the two relators and the property is hyperlinearity; this is the ucp form, where the models are compressions V*pi(.)V of genuine representations of F (relators exact upstairs) and the property is Kirchberg's factorization property. The gap between the two is exactly the lifting gap between Connes-embeddable and amenable traces on C*(F).
  hyperlinear-groups-have-factorization-property: that is the refuted general implication; this is a finitary characterization of the stronger property for one group, obtained from its character simplex.
  normal-state-free-near-representation-forces-factorization: that says normal-state near representations with regular character already give factorization for any group; this handles arbitrary mixtures for F, where the character simplex upgrades any non-abelian amenable limit to the regular one.
---

**ESTABLISHED (unreviewed).** Let `F = <a, b | [ab^-1, a^-1ba], [ab^-1, a^-2ba^2]>`. The following are
equivalent.

1. `F` has Kirchberg's factorization property, i.e. the canonical trace `tau_reg` on `C*(F)` is amenable.
2. **ucp form.** There is `epsilon > 0` such that for every `delta > 0` there are `n` and a ucp map
   `phi : C*(F) -> M_n` with
   `1 - tr_n(phi(s)phi(s)^*) < delta` for `s in {a, b}` and `||phi(a)phi(b) - phi(b)phi(a)||_2 >= epsilon`.
3. **Stinespring form.** There is `epsilon > 0` such that for every `delta > 0` there are a unitary
   representation `pi` of `F` on `K` and a projection `P` of finite rank `n` on `K` with
   `||[pi(s), P]||_HS < delta sqrt(n)` for `s in {a, b}` and
   `||[P pi(a) P, P pi(b) P]||_HS >= epsilon sqrt(n)`.

In 2 and 3 one may take any `epsilon < sqrt 2` when they hold.

**Mechanism** (route `thompson-f-factorization-iff-ucp-models-separate-proof`).
- **Subadditive defect.** The generator defect `D(g) = ||P pi(g)(1-P)||_HS / sqrt n` is subadditive and
  symmetric, and it bounds the multiplicative error of `V*pi(.)V`. So ucp maps that are almost unitary on
  `a, b` are asymptotically multiplicative on all of `C*(F)`, and their limit traces are amenable.
- **Face.** Amenable traces form a face of the trace space. The positive functional `x (x) y^op -> tau(xy)`
  on `A (x)_max A^op` dominates `t` times that of any summand of `tau`, and domination preserves vanishing
  on the kernel of the quotient onto `A (x)_min A^op`.
- **Simplex.** A limit trace is `t tau_reg + (1-t) chi_ab` (`thompson-f-character-simplex`), and
  `||[phi(a),phi(b)]||_2^2 -> 2t`. So separation means `t > 0`, and the face gives `tau_reg` amenable.

**Impact.** Together with `llp-makes-hyperlinear-traces-amenable`, this splits
`thompson-f-is-not-hyperlinear` into two independently failable statements
(`thompson-f-not-hyperlinear-from-llp-and-no-factorization`):
- `thompson-f-lacks-factorization-property`, a uniform collapse statement about compressions of honest
  representations;
- `thompson-f-full-c-star-algebra-has-llp`, a lifting statement.

It also fixes what every compression-model argument can reach. Jones, Pythagorean, Koopman and `O_2`
compressions are all of form 3, so a uniform collapse theorem for them proves exactly the failure of the
factorization property and nothing more without a lifting input. A positive compression-model proof of
hyperlinearity proves the factorization property. If `F` is nonamenable, that in turn makes `C*(F)`
nonexact (`nonamenable-factorization-groups-have-nonexact-full-cstar`).
