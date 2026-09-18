---
rg: 2
id: delta-e-adjoint-msg-is-fd-uniform-gap
kind: claim
title: Model-generic Kesten gaps in delta_e adjoint coronas are exactly corona gaps for every model, and they force a uniform spectral gap of L across all finite-dimensional representations of G
distinct_from:
  model-spectral-gap-quantifier-ladder: its item 4 absorbs Ad W of any model W as a null corner and so reaches only adjoint coronas; this places every model U itself, not its adjoint, as an exact reducing block via V (+) (V tensor U), proves the two-sided dichotomy "(MSG) for all delta_e adjoints iff no delta_e model or T_MF(G,L)", and converts T_MF into a uniform finite-dimensional gap, that is relative property (tau), for L.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates (MSG) as the only Kazhdan input and calibrates one free-group failure; this identifies the exact strength of a model-generic proof of that input as a better-studied statement about the finite-dimensional unitary dual of G.
  amenable-subgroup-fixed-projection-is-never-in-adjoint-corona: that proves (MSG) false outright for amenable L with an infinite class; this handles every L, amenable or not, and shows the generic statement is a uniform gap on Rep_fd(G) restricted to L.
  corona-fixed-projection-membership-is-finite-markov-gap: that rewrites membership of P_L in the corona as a finite Markov gap; this computes which spectral gap a model-generic argument must actually supply.
  tracial-model-spectral-gap-is-character-gap-weaker-than-t: that studies the tracial rung, where the trace sees only characters; this is the operator-norm corona rung, where the tensor block is invisible to the trace but reducing in norm.
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an
obstruction to a class of approaches and a reduction to a better-studied
statement.  Proof route: `delta-e-adjoint-msg-is-fd-uniform-gap-proof`.

**Setting.**  Notation follows `kesten-spectral-gap-replaces-kazhdan-projection-per-model`
and `corona-fixed-projection-membership-is-finite-markov-gap`.
- `G` is countable, `L<=G` is finitely generated, and `S` is a finite
  symmetric generating set of `L` with `e in S`.
  `h_S=(1/|S|) sum_(s in S) u_s`.
- A *model* is a sequence `U_n:G->U(b_n)` with
  `||U_n(gh)-U_n(g)U_n(h)||->0` in operator norm. Its corona homomorphism
  is `[U_n]` in `prod M_(b_n)/(+)` (sup norm modulo null sequences).
- A model is *`delta_e`-profile* if `tr U_n(g)->delta_e(g)`.
- For a `delta_e`-profile model `V`, `sigma~_V=[Ad V_n]` acts in the
  adjoint corona `B_V=prod B(M_(a_n),||.||_2)/(+)`.
- `(MSG)` for a homomorphism `rho` means that `1` is not an accumulation
  point of `sp(rho(h_S))`.
- `T_MF(G,L)`: `(MSG)` on `L` holds for the corona homomorphism of
  **every** model of `G`, of any trace profile.

**Theorem A (tensor saturation).**  Exactly:

```text
(MSG) on L for sigma~_V for every delta_e-profile model V of G
   <=>   G has no delta_e-profile model   OR   T_MF(G,L).
```

The invariant is an exact reducing block.  Fix one `delta_e` model `V` and
any model `U`, and put `M=V (+) (V tensor U)`.  Then `M` is a
`delta_e`-profile model.  Inside `Hom(C^(a_n), C^(a_n) tensor C^(b_n))`,
the operators `X_xi: eta -> eta tensor xi` satisfy `Ad M_n(g) X_xi =
X_(U_n(g) xi)` exactly, with `||X_xi||_2 = sqrt(a_n)|xi|`.  So `[U_n]` is
a reducing corner of `sigma~_M`.  The block has normalized rank `0` and is
invisible to every trace, but not to the norm.

**Theorem B (finite-dimensional uniform gap).**  If `T_MF(G,L)` holds, then
there is `c>0` such that for **every** finite-dimensional unitary
representation `pi` of `G`,

```text
sp(pi(h_S)) cap (1-c, 1) = empty.                                  (FD-gap)
```

In particular, for every family of finite quotients `G->G/N_k`, the
images `L N_k/N_k` form an expander family with respect to `S`.  This is
property `(tau)` for `L` relative to `{L cap N_k}`.  On permutation
representations it is a uniform Kesten gap for `S` acting on the
`L`-orbits of every finite quotient `G/N_k` (off the constants).

**Corollary C (the class it kills).**  By Theorem A, any proof of the
transport input "`(MSG)` on `L` in the adjoint corona of every
`delta_e`-profile model of `G`" is a proof of

```text
(exists a delta_e-profile model of G)  =>  T_MF(G,L)  =>  (FD-gap) for L in Rep_fd(G).
```

(FD-gap) does not mention models.  So in the proof by contradiction that
the transport is designed for, the model-generic step must turn the
assumed `delta_e` model into a uniform spectral gap for `L` on the whole
finite-dimensional unitary dual of `G`.  That includes representations
that have nothing to do with the assumed model.
- For the Jacobson hole `jacobson-regular-character-not-mf-without-property-t`
  (`G=EL_5(J)`), (FD-gap) includes `(tau)` for the image of `L` in all
  finite quotients of `SL_5(F_2[z^(+-1)])`. The symbol `pi_+` maps `G`
  onto `SL_5(F_2[z^(+-1)])`
  (`jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`,
  (MQ1)), so each of these quotients is a finite quotient of `G`.
- For nonamenable `L` this is a relative `(tau)` statement of
  superstrong-approximation type. The standard proofs for elementary
  groups over rings go through property `(T)` or relative property `(T)`
  (Ershov--Jaikin-Zapirain, Kassabov, Shalom). This note does not claim
  that no Kazhdan-free proof exists, only that one is required.
- For amenable `L` with infinitely many finite-quotient images, (FD-gap)
  is false by Lubotzky--Weiss. This recovers the amenable obstruction
  independently.
- Every member dies at the same step: specialization to
  `M=V (+) (V tensor pi)` for a finite-dimensional `pi` with an
  `L`-eigenvalue `1-delta`, `delta` small, where the reducing block
  `X_xi` carries `pi`.

**Escape clause (what survives).**  `V tensor U` does not extend any
structure that `V` has and `U` lacks.  So the kill does not reach
arguments that use a property of `V` destroyed by adding the tensor block:
- no nonzero normalized-rank-zero reducing blocks;
- genuine extension of `V` to the ambient `Delta` or to the Leavitt group,
  when `U` does not extend;
- a lower bound on the normalized rank of every spectral projection near
  `1`, which is the tracial rung.

Only these model-specific arguments can remove `(T)` from the transport.

## Impact

The transport input is not "a spectral gap in one clever model".
Model-generically, it is a uniform spectral gap for `L` across the whole
finite-dimensional unitary dual of `G`, which is a better-studied
statement and a `(tau)`-type theorem.  A `(T)`-free proof of the goal via
the manuscript transport must therefore do one of two things:
- (i) prove relative `(tau)`/superstrong approximation for a nonamenable
  `L <= EL_5(F_2[z^(+-1)])` without Kazhdan input, which is open in
  general and not easier than the goal; or
- (ii) use a normalized-rank or extension property of `delta_e` models
  that is destroyed by `V (+) (V tensor U)`.

Direction (ii) is the tracial rung of
`tracial-model-spectral-gap-is-character-gap-weaker-than-t`.  That rung
is weaker than `(T)` and remains the only live door.
