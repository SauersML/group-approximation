---
rg: 2
id: level-groups-need-not-concentrate-on-monomial-lines
kind: claim
title: For a level group E ⊇ U_k in SL_3 of the Laurent ring, a fixed point in the weight-w building is equivalent to w lying in the dual of the trace Newton cone, and unboundedness always concentrates on monomial curves but need not concentrate on any monomial line, even up to Gamma-conjugation; so no argument intrinsic to E_B closes the level class of the rank-three cone
distinct_from:
  weight-bounded-level-subpairs-cannot-certify-rank-three: that proves W(E_B) ⊆ K0^∨ and kills E_B bounded at one strictly positive weight; this computes W(E_B) exactly as the rational dual of the trace Newton cone, and shows that the survivors it leaves cannot be killed by any statement about E_B alone.
  level-subpair-line-sections-are-bounded-or-cofinite: that is the one-variable dichotomy (L1) for line sections; this applies (L1) to monomial curve images instead, where it always fires, and proves that the line-section version cannot be reached from unboundedness.
  subring-level-subpairs-cannot-certify-rank-three-cone: that kills subring-elementary E_B through the compressors of B; the counterexample E_θ here is a relative elementary group of that kind, so it is killed there, and this explains why: only B, never E_B, can kill it.
  rank-three-finite-twisted-kazhdan-cone-is-sofic: that is the open question; this refutes the proposed line-concentration step on its level-containing nonsofic side and names the statement about normalisers that must replace it.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: [[level-groups-need-not-concentrate-on-monomial-lines-proof]].
It is a method obstruction on the nonsofic side of [[rank-three-finite-twisted-kazhdan-cone-is-sofic]].  It
refutes the step proposed at the end of [[weight-bounded-level-subpairs-cannot-certify-rank-three]]:
unboundedness of `E_B` in `X_(1,..,1)` does **not** concentrate on a monomial line, even after conjugating
by `Gamma`, so (L2) of [[level-subpair-line-sections-are-bounded-or-cofinite]] cannot be reached that way.

## Setting

As in [[weight-bounded-level-subpairs-cannot-certify-rank-three]]: `R_+ = F_q[x_1..x_d]`, `d ≥ 2`, `R` the
Laurent ring, `Gamma = SL_3(R_+)`, `U_k = < e_ab(x^m) : a ≠ b, m ∈ N^d, |m| ≥ k >`.  A **level group** is a
subgroup `U_k ≤ E ≤ SL_3(R)`.  For `w ∈ Q^d \ 0`, `v_w` is the monomial valuation, `K_w` the completion and
`X_w` the Bruhat-Tits building of `SL_3(K_w)`; `W(E)` is the set of `w` for which `E` fixes a point of `X_w`.

- The **trace Newton set** is `N(E) = ∪_(g ∈ E) supp(tr g) ⊆ Z^d`, and `Ncone(E)` its closed convex cone.
- For `a ∈ Z^d` with `gcd(a) = 1`, the **monomial curve map** `φ_a : R → F_q[t^(±1)]`, `x^m ↦ t^(<a, m>)`, is a
  ring homomorphism.  The **curve image** of `E` is `φ_a(E) ≤ SL_3(F_q[t^(±1)])`.
- For `m ∈ Z^d \ 0` primitive, `t = x^m`, the **line section** is `Δ_m = E ∩ SL_3(F_q[t^(±1)])`, as in (L2).

## Theorem

**(Z1) Trace criterion.**  For every level group `E` and every `w ∈ Q^d \ 0`:

```text
E fixes a point of X_w   ⟺   v_w(tr g) ≥ 0 for all g ∈ E   ⟺   <w, p> ≥ 0 for all p ∈ N(E).
```

So `W(E) = (Ncone(E)^∨ ∩ Q^d) \ 0`: the fixed-point data of all weight buildings is one closed convex cone.
If `B ⊇ U_k` with projection `H_B`, then `N(E_B)` is `H_B`-invariant and contains `2 N^d_(|m|≥k)`, so
`Ncone(E_B) ⊇ K0`; this recovers (Y1).

**(Z2) Unboundedness always concentrates on monomial curves.**  Let `E` be a level group and `a ∈ Z^d_(>0)`
primitive.  If `φ_a(E)` is unbounded at `t = 0`, it has finite index in `SL_3(F_q[t^(±1)])`, by (L1).  If
`a ∉ W(E)`, then every `a'` in a neighbourhood of the ray of `a`, off finitely many rational hyperplanes, has
`φ_(a')(E)` unbounded, hence of finite index.  So for a survivor of (Y2) (where `W(E_B)` misses the open
orthant) the curve images `φ_a(E_B)` have finite index for all primitive `a > 0` outside a locally finite
union of rational hyperplanes.

**(Z3) Unboundedness need not concentrate on any monomial line.**  Let `θ ∈ R^d_(>0)` have Q-linearly
independent coordinates, `P_θ = { p ∈ Z^d : <θ, p> > 0 } ∪ {0}`, `S_θ = F_q[P_θ] ⊆ R`, `I_θ` the ideal of
`S_θ` spanned by `x^p`, `p ∈ P_θ \ 0`, and `E_θ = E_3(S_θ, I_θ)`, the relative elementary group.  Then:

1. `U_1 ≤ E_θ`, and `E_θ ≤ SL_3(S_θ, I_θ)`, so `e_ab(1) ∉ E_θ` and `ev_0(E_θ ∩ Gamma) = 1`;
2. `E_θ` is normal in `SL_3(S_θ) ⊇ Gamma`, so it is `Gamma`-conjugation invariant;
3. `W(E_θ) = ∅`: `E_θ` fixes no point of `X_w` for any rational `w ≠ 0`;
4. every line section `Δ_m`, for **every** primitive `m ∈ Z^d \ 0`, lies in `SL_3(F_q[s], s F_q[s])` for
   `s = x^(±m)`: pole order `0` at the end where `<θ, ±m> > 0`, and the section is bounded;
5. every curve image is everything: `φ_a(E_θ) = SL_3(F_q[t^(±1)])` for every primitive `a ∈ Z^d`.

So `E_θ` has every property that (L1), (L2), (Y1)-(Y3) and (Z1)-(Z2) can see in a survivor, and more: it is
unbounded at every weight, cofinite on every monomial curve, and pole-free on every monomial line, including
after conjugation by any element of `Gamma`.  The proposed line-concentration step is false.

**(Z4) What kills `E_θ`, and the obstruction.**  `E_θ` is not the elementary part of a certificate: any
`u σ ∈ G` normalising `E_θ` has `σ^T θ ∈ R_(>0) θ`, and the stabiliser of the irrational ray `R_(>0) θ` in
`SL_d(Z)` embeds in `R_(>0)^×`, so it is abelian.  A Kazhdan `B` then has finite `H_B`, and (X2) of
[[subring-level-subpairs-cannot-certify-rank-three-cone]] makes an infranormal `C` normal.  The kill uses the normaliser, not `E`.  Hence **every implication of
the form "a level group `E` with no fixed point in any `X_w`, `w > 0`, has an element, or a `Gamma`-conjugate
of an element, with a pole on a monomial line; or contains `e_ab(1)`; or has `ev_0(E ∩ Gamma) = F`" is
false**, with `E_θ` as the counterexample (its `ev_0(E_θ ∩ Gamma) = 1` even satisfies the centraliser
condition).  No statement about `E_B` alone, of the kind (L2), (Y1)-(Y3) and (Z1)-(Z2) prove, closes the
level class.  A closing argument must use `H_B`.

## Mechanism

1. *(Z1).*  `E ⊇ U_k` spans `M_3(K_w)` (the `x^m E_ab` and their products `x^(2m) E_aa`).  If all traces are
   in `O_w`, the `O_w`-span `Λ` of `E` is a ring whose elements have traces in `O_w`.  Dual-basis against the
   trace form on nine elements of `E` spanning `M_3(K_w)` puts `Λ` inside a finite free `O_w`-module (Bass's
   lemma), so `Λ O_w^3` is an `E`-stable lattice.  Conversely, point stabilisers are parahorics, contained in
   conjugates of `SL_3(O_w)`.  Since `v_w` of a Laurent polynomial is the minimum of `<w, p>` over its support
   (no cancellation), the second equivalence is immediate.
2. *(Z2).*  `φ_a(U_k)` contains `e_ab(c t^j)` for all `j ≥ n` (the values `<a, m>`, `|m| ≥ k`, contain every
   large integer because `gcd(a) = 1`), so (L1) applies to `φ_a(E)` exactly as to `Δ_m`.  Unboundedness of
   `φ_a(E)` is a pole of `φ_a(tr g)`.  Given `g` with `v_a(tr g) < 0`, a perturbation `a'` for which the minimum
   of `<a', ·>` on `supp(tr g)` is attained once prevents cancellation, so `φ_(a')(tr g)` has a pole.
3. *(Z3).*  `P_θ` is a pointed monoid containing `N^d \ 0`.  For rational `w ≠ 0` the open cone
   `{ <θ, p> > 0 > <w, p> }` is nonempty, because `w` is not a positive multiple of the irrational `θ`; a lattice
   point `p` in it gives `e_12(x^p) e_21(x^p) ∈ E_θ` with trace `3 + x^(2p)` of `v_w`-value `2<w, p> < 0`.  On a
   line, `S_θ ∩ F_q[t^(±1)] = F_q[s]` and `I_θ ∩ F_q[s] = s F_q[s]`.  For a curve, `<a, p>` takes every integer
   value on `P_θ \ 0`, so `φ_a(E_θ)` contains all `e_ab(t^j)`, which generate `SL_3(F_q[t^(±1)])`.
4. *(Z4).*  The closed Newton cone is an invariant of the normaliser: `Ncone(u σ̂(E) u^-1) = σ Ncone(E)`.  For
   `E_θ` it is the half-space `{ <θ, ·> ≥ 0 }`.  A matrix fixing the ray of `θ` and trivial on it fixes the
   smallest rational subspace containing `θ`, which is `R^d`.

## Calibration

- `E = Gamma`: `N ⊆ N^d`, `W = Q^d_(≥0) \ 0`, curve images `SL_3(F_q[t])` bounded; (Z1)-(Z2) agree.
- `E = E_w`, `w > 0`: `W ∋ w`; curve images for `a` near `w` are bounded, for `a` far away cofinite.  So (Z2)
  is sharp: curve concentration depends on the direction.
- `E = EL_3(R)`: `W = ∅`, lines and curves cofinite, `e_ab(1) ∈ E`.  `E_θ` differs from it only on lines.
- `d = 1`: `θ` cannot have independent coordinates, and indeed (L1) makes line and curve the same thing; the
  counterexample needs `d ≥ 2`, which the problem has.

## What is left

The level class of the nonsofic side is now reduced to a statement about **normalisers**: whether
`H_B = pr(N_G(E_B) ∩ B)` can be infinite, Kazhdan and nonnegatively generated with invariant core `R^M` while
`E_B ⊇ U_k` has bounded monomial line sections and `e_ab(1) ∉ E_B`.  The invariant that sees the obstruction
for `E_θ` is the Newton cone `Ncone(E_B)` with its `H_B`-action: it contains `K0 ⊇ R^M`, and its dual `D` is an
`H_B^T`-invariant closed cone in the weight orthant whose rational points are exactly `W(E_B)` (by (Z1)).  The
next step: show that a nonnegative `σ ∈ H_B` of infinite order, acting on a trace `tr g` with a monomial `x^p`,
`<w, p> < 0`, moves the negative part of `σ^n p` onto a monomial ray (Perron-Frobenius on `σ`), and that the
conjugates `u_n σ̂^n(g) u_n^-1 ∈ E_B` then produce a line section with a pole deeper than `2n`, reaching (L2).
For `E_θ` this fails exactly because no such `σ` normalises it.  Otherwise, the positive side.
