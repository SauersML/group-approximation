---
rg: 2
id: fpbs-fiid-uniform-finite-energy-fkg-collapse-family
kind: claim
title: Collapse families that are FIID (mixing of all orders), uniformly finite energy and Harris-FKG exist on every Cayley graph of a nonamenable group with a central Z inside a Z2
distinct_from:
  fpbs-finite-energy-fkg-collapse-over-central-z2-slabs: that family selects whole cosets of H by an H-invariant rule, so it is not mixing, and its deletion tolerance is only qualitative; here the spine is an iid field of short thin planar sticks at infinitely many scales, so the family is FIID and every edge has conditional probability in a fixed interval [t, t+(1-t)q]
  fpbs-soft-collapse-iff-invariant-sparse-spines: that gives collapse families from invariant sparse spines with no energy or correlation control; this builds one with uniform finite energy, FKG and mixing
  fpbs-sparse-spine-cost-bound: that bounds cost from an FIID spine; this constructs an FIID collapse percolation family and is consistent with that bound because class Z has fixed price 1
---

**ESTABLISHED (class-killing obstruction).** Proof in
`fpbs-fiid-uniform-finite-energy-fkg-collapse-family-proof`.

**Setting.** Class `Z` is as in
`fpbs-finite-energy-fkg-collapse-over-central-z2-slabs`: `Gamma` is finitely
generated and nonamenable, with a central element `t` of infinite order and an
element `g` such that `<g> ∩ <t> = 1`, so `H = <g,t> ≅ Z^2`. Examples are
`Lambda x Z`, `B_n` with `n >= 3`, and unit tangent bundle groups. Let `S` be a
finite symmetric generating set, `G = Cay(Gamma,S)`, and let `p_c = p_c(G)`
refer to Bernoulli bond percolation. The standard coupling is
`xi_t = {e : U_e <= t}`.

**Theorem.** For every `Gamma in Z` and every `S` there is a probability space
with iid variables `(U,B,lambda)` indexed by `Gamma`-sets with finite
stabilizers, a constant `q in (0,1)`, and an equivariant factor family
`(omega_t)_{t in [0,1]}` of edge sets of `G` with the following properties.

1. **Monotone coupling.** `xi_t ⊆ omega_t ⊆ omega_{t'}` whenever `t <= t'`.
2. **Bernoulli below p_c.** `omega_t = xi_t` for all `t <= p_c`. So the joint
   law on `[0,p_c]` is the standard coupling.
3. **FIID.** Every `omega_t` is a factor of an iid process, so it is mixing of
   all orders.
4. **Uniform finite energy.** For every `t`, edge `e` and `P`-a.e.
   configuration, `t <= P(e in omega_t | omega_t restricted to E \ {e}) <= t + (1-t) q`.
5. **Harris–FKG.** Every `omega_t` is an increasing function of independent
   variables. So increasing events are positively correlated.
6. **Collapse.** For every `t > p_c`, `omega_t` has exactly one infinite
   cluster a.s. Also `theta(t) = P(o in infinite cluster of omega_t) -> 0` as `t ↓ p_c`.

**Consequence: obstruction.** Suppose a proof of `p_c < p_u` on `Cay(Gamma,S)`
uses only the coupling structure (1)–(2), invariance, ergodicity or mixing,
insertion and deletion tolerance with uniform constants, FKG, and the
absence of percolation at `p_c`. Such a proof also applies to `omega_t` and
yields a window. So it is false for every `Gamma in Z`. This settles the open
question left by `fpbs-finite-energy-fkg-collapse-over-central-z2-slabs`:
**mixing, uniform finite energy and FKG together do not force a window.**

Any valid proof must use a property that is exact for the product measure
above `p_c` and fails for `omega_t`. Examples are negative-dependence or
disjoint-occurrence bounds (BK/Reimer), Russo's formula for the product
measure, or differential inequalities of Aizenman–Barsky, Menshikov or
Hutchcroft type, which bound the growth of `theta` from above.

**Calibration.** The same construction runs on `Z^2`, where `p_c = p_u`, so it
proves nothing false there. `F_2` is not in `Z`, and it has a window. `F_2 x Z`
lies in `Z` and has a window for some `S`
(`fpbs-simple-generating-set-with-gap-exists`). This is consistent, because
above `p_c` the family is not Bernoulli. Class `Z` has fixed price 1, which is
consistent with `fpbs-sparse-spine-cost-bound`.

## Attempts

- sw-123 (flagship-2026-09-17): construction by planar sticks at infinitely
  many scales inside `Z^2` cosets, thinned by independent Bernoulli(`q`) edge
  marks. Uniqueness comes from indistinguishability with marks (Lyons–Schramm
  1999, Thm 3.3, marked form Aldous–Lyons 2007, Thm 6.15).
