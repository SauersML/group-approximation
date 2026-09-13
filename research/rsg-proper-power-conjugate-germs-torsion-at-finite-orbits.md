---
rg: 2
id: rsg-proper-power-conjugate-germs-torsion-at-finite-orbits
kind: claim
title: In a rational similarity group with finite nucleus, an element conjugate to a proper power has finite-order germs at its rational periodic points with finite orbit under the conjugator
distinct_from:
  graph-path-almost-automorphism-proper-power-is-equicontinuous: that proves equicontinuity of the whole cyclic group inside almost-automorphism groups of graph path spaces, through a locally constant exponent cocycle; this is a pointwise germ statement for rational similarity groups with non-isometric local actions, where that cocycle is unavailable.
  finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous: that is the open equicontinuity statement for rational similarity groups with finite nucleus; this settles only rational periodic points whose orbit under the conjugator is finite.
artifacts:
  - research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.** `Σ_Γ` is a subshift of finite type and `E ⊆ Σ_Γ` is a nonempty clopen
set. `G ≤ R_{Γ,E}` is a rational similarity group (RSG) with finite nucleus, in the
sense of Belk--Bleak--Matucci--Zaremsky, arXiv:2309.06224v3. Rational points and
groups of germs are as defined there. A point is *rational* if it is eventually
periodic. `[G]_z = Stab_G(z)/Fix^0_G(z)`, where `Fix^0_G(z)` is the set of
elements that are the identity on a neighbourhood of `z`.

**Statement.** Let `f, g ∈ G` and nonzero integers `k, l` with `|k| ≠ |l|` satisfy
`f g^k f^-1 = g^l`. Let `z ∈ E` be a rational point with `g^p(z) = z` for some
`p ≥ 1`, and suppose the orbit `{f^n(z) : n ∈ Z}` is finite. Then the germ
`[g^p]_z` has finite order. Equivalently, some `g^(pm)` with `m ≥ 1` is the
identity on a neighbourhood of `z`.

**Consequences.**
- **Baumslag--Gersten group.** Let `BG = < a, t | b a b^-1 = a^2 >` with
  `b = t a t^-1`, and take any homomorphism `BG → G`. At every rational point that
  is periodic for the image of `a` and has a finite orbit under the image of `b`,
  some power of the image of `a` is the identity nearby.
- **Higman's group.** The same holds in
  `H4 = < g_0, …, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2 >`, with `g_(i+1)` in place of
  `a` and `g_i` in place of `b`.
- **Where attracting dynamics must live.** In an embedding of either group into a
  finite-nucleus RSG, a rational periodic point at which a power of `a` (or of
  `g_(i+1)`) acts like a nontrivial canonical shift has an infinite orbit under
  `b` (or `g_i`).
- **Example.** `dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg` applies
  this at a common fixed point.

**Scope.**
- The statement says nothing at irrational periodic points.
- It says nothing at rational periodic points whose orbit under the conjugator is
  infinite.
- It does not give equicontinuity.

The proof is `rsg-proper-power-germ-torsion-via-cyclic-germ-groups`.
