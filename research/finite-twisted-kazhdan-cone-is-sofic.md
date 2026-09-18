---
rg: 2
id: finite-twisted-kazhdan-cone-is-sofic
kind: claim
title: The finite twisted Kazhdan cone of the Theorem E pair, twisted by evaluation at the origin, is sofic
distinct_from:
  twisted-diagonal-cones-need-a-profinitely-invisible-core: that proves every twisted cone with a visible twist is nonsofic and reduces the rest to this group; this is the one remaining soficity question, for a single explicit group.
  kt-pair-group-double-is-nonsofic: that is the untwisted double G *_Gamma G; this group is an amalgam of G with a finite extension F x| Gamma of Gamma, in which no element outside Gamma centralises Gamma or any finite-index level of it.
---

**OPEN.**  Let `Gamma = EL_r(F_q[x_1..x_d]) ≤ G = EL_r(F_q[x^(±1)]) x| SL_d(Z)` (`r, d ≥ 3`) be the
Kun-Thom Theorem E pair.  Let `psi : Gamma -> F = PSL_r(F_q)` be evaluation at the origin followed by
projection.  Is

```text
T = (F x Gamma) *_(Gamma_psi) G  =  (F * G) / << g f g^-1 = psi(g) f psi(g)^-1 : g in Gamma, f in F >>
```

sofic?  Equivalently `T = (F x|_(c∘psi) Gamma) *_Gamma G`, where `Gamma` acts on `F` by the inner
automorphisms `c_(psi(g))`.  Here `Gamma` has index `|F|` in the left vertex group.

**Why it is the whole question.**  By [[twisted-diagonal-cones-need-a-profinitely-invisible-core]]:
- every twisted-diagonal cone `X(H, psi')` over this pair, with `psi'` factoring through `psi` and `H ⊇ F`,
  contains `T`;
- any cone whose twist is visible to the finite quotients of `G` is nonsofic;
- `T` is not residually finite: every finite quotient kills `F`.

So if `T` is nonsofic, then every twisted-diagonal cone through evaluation at the origin is nonsofic, and the
twisted-cone route of [[kazhdan-double-cones-add-one-sigma1-bit]] to
[[sofic-recognition-finite-presentations-is-pi2-complete]] needs a different invisible finite quotient of
`Gamma`.  If `T` is sofic, the proof must use sofic approximations of `G` that are not finite quotients.  It
would then be the first soficity theorem for an amalgam over a Kun-Thom subgroup that is not a free factor.

**What does not decide it.**
- *Double embedding.*  For `f ∈ F \ 1`, `G` and `f G f^-1` share only
  `M_f = psi^-1(C_F(f)) ≠ Gamma`.  The element `f` centralises `M_f`, but `<G, f G f^-1>` need not be the free
  amalgam over `M_f`.  For example, take `f = e_23(1)` and `a ∈ Gamma` with `psi(a) = e_12(1)`.  Then
  `a (f a f^-1) a^-1 (f a f^-1)^-1` is reduced but trivial, because `e_12(1)` commutes with its `f`-conjugate.
  A double over `M_f` would need a subgroup `G'' ≤ G` with `G'' ∩ Gamma = M_f` whose double is nonsofic.
- *Levels.*  The finite-index argument of (V2) needs a level `G_1` with `psi(Gamma ∩ G_1)` having a nontrivial centraliser in `F`, and (V5) shows
  that `psi(Gamma ∩ G_1) = F` at every level.
- *Theorem C of Kun-Thom on generalised Bernoulli actions `T ↷ K^(T/F)`.*  `Gamma` has only infinite orbits
  on `T/F`, so it has no nonconstant invariants there.  The useful coset space is `T/(F x Gamma)`, and
  soficity of its Bernoulli action is not known.

**Sufficient criterion for nonsoficity (subpair form of (V2)).**  The proof of (V2) never uses that `G_1` is
normal or has finite index.  It uses only a subgroup `B ≤ G` with `B ∩ Gamma = Gamma''` and
`B *_(Gamma'') B` nonsofic.  So `T` is **nonsofic** if some subgroup `G'' ≤ G` has both of these properties:

- its trace `Gamma'' = G'' ∩ Gamma` satisfies `C_F(psi(Gamma'')) ≠ 1`, for example `psi(Gamma'') = 1`;
- `(G'', Gamma'')` is a Kun-Thom pair, or more generally has a nonsofic double.

The levels are excluded by (V5), which leaves non-normal and infinite-index `G''`.  The natural candidates
are relative groups `EL_r(R, I) x| Stab(I)` over ideals `I` of `R = F_q[x^(±1)]` whose zero set meets the
closure of the torus at the origin.  An example is `I = (x_1 + x_2)`: every element of `I ∩ R_+` vanishes at
`0`, so `ev_0` is trivial on `EL_r(R_+, I ∩ R_+)`.  The open point is whether any such relative pair is
Kazhdan and infranormal, and also meets `Gamma` inside `ker ev_0`.
