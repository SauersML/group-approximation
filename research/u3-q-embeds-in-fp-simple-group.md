---
rg: 2
id: u3-q-embeds-in-fp-simple-group
kind: claim
title: The rational Heisenberg group U_3(Q) embeds in a finitely presented simple group
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is GL_n(Q) itself; this is its unipotent subgroup U_3(Q) <= GL_3(Q), a stepping stone that the root at n = 3 implies (route u3-q-via-gl-3-q).
  heisenberg-group-embeds-in-some-brin-thompson-group: that asks for the integral H_3(Z) inside some Brin--Thompson group mV; H_3(Z) already embeds in finitely presented simple groups through GL_3(Z), and this asks for its divisible hull U_3(Q) in any finitely presented simple group.
  rational-heisenberg-fd-radical-is-commutator-and-mf: that computes the finite-dimensional radical and MF property of the same group UT_3(Q); this is an embedding question.
---

**OPEN.** The group `U_3(Q)` of upper unitriangular `3 x 3` rational matrices
embeds in a finitely presented simple group.

Stepping stone for `gl-n-q-embeds-in-fp-simple-group`. `U_3(Q) <= GL_3(Q)`, so
the root at `n = 3` implies this claim (`u3-q-via-gl-3-q`). It is the smallest
nonabelian divisible nilpotent test. The survey (arXiv:2306.16356v3,
Theorem 5.1) lists as known: countable abelian groups, countable locally finite
groups, and f.g. virtually nilpotent groups. None of these is a torsion-free
nonabelian nilpotent group that is not finitely generated.

## Structure used below

Write `x = e_12(1)`, `y = e_23(1)`, `z = e_13(1)`, and `x^a = e_12(a)` and so on,
so `[x^a, y^b] = z^{ab}` and `Z(U_3(Q)) = [U_3(Q), U_3(Q)] = z^Q ≅ (Q,+)`.

- **Directed union of integral Heisenberg groups.** For `N >= 1` put
  `H_N = {x^{a/N} y^{b/N} z^{c/N^2} : a, b, c ∈ Z} = ⟨x^{1/N}, y^{1/N}⟩ ≅ H_3(Z)`.
  Every finitely generated subgroup lies in some `H_N`, and
  `U_3(Q) = ⋃_N H_{N!}`. The inclusion `H_N <= H_{kN}` is the dilation
  `x -> x^k, y -> y^k, z -> z^{k^2}`, realized in `GL_3(Q)` by conjugation with
  `diag(k, 1, 1/k)`.
- **Finitely generated subgroups are fine.** Each `H_N ≅ H_3(Z) <= SL_3(Z)`, and
  `GL_3(Z)` embeds in Scott's finitely presented simple group (survey
  Theorem 4.8). So every finitely generated subgroup of `U_3(Q)` embeds in a
  finitely presented simple group. The problem is the union.
- **U_n(Q).** `U_3(Q) <= U_n(Q) <= GL_n(Q)` for `n >= 3`. By Mal'cev's theory of
  completions (standard, not re-verified here), every countable torsion-free
  nilpotent group of finite Hirsch length embeds in some `U_n(Q)`. So the
  statement for all `U_n(Q)` is the statement for all such groups.

## Obstructions: what cannot host U_3(Q)

- **Residually finite groups** (root O1): the centre is divisible.
- **V** and every `V_n`: `thompson-v-has-no-heisenberg-subgroup`.
- **VA, T-bar, Brin's A**: root O4 (no distorted cyclic subgroups; `z` is
  quadratically distorted in `H_3(Z)`).
- **Central or covering lifts of groups without (Q,+)**:
  `lifts-add-no-unipotent-divisibility`.
- **BFFHZ free-product and mapping-torus closures**:
  `bffhz-closures-cannot-create-gl-n-q`.
- **Permutational wreath products with abelian lamps and finite point
  stabilizers**: `abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q`. `U_3(Q)`
  must already lie in the top group.
- **Circle groups, even with Q in the base**: see Attempt 1. `U_3(Q)/⟨z⟩` has no
  faithful action by orientation-preserving circle homeomorphisms.

## Brin–Thompson hosts

`nV` is finitely presented and simple, and contains `(Q,+)` for `n >= 2`
(Kojima–Sheng, arXiv:2603.18410v3). A copy of `U_3(Q)` in some `nV` would settle
this claim. It needs `heisenberg-group-embeds-in-some-brin-thompson-group`
(OPEN in both directions; its negation is
`heisenberg-group-embeds-in-no-brin-thompson-group`). By
`heisenberg-in-nv-forces-drift-free-central-element` the centre must be
drift-free, and `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`
excludes the triangular subgroups. Distortion elements exist in `mV`,
`m >= 2` (`brin-thompson-mv-contains-a-distortion-element`), so O4 does not
exclude `mV`.

## Attempts

1. **Circle actions (2026-09-17, lane gq-heis-q; elementary, not independently
   reviewed).** *Lemma.* If `f, g, c ∈ Homeo_+(S^1)`, `c = f g f^-1 g^-1`, and
   `c g = g c`, then the rotation number `ρ(c)` is `0`. If `c` also has finite
   order, then `c = id`.
   - *Proof.* `f g f^-1 = c g`. Rotation number is conjugation-invariant, and
     additive on commuting pairs, so `ρ(g) = ρ(c) + ρ(g)` in `R/Z` and
     `ρ(c) = 0`. Then `c` has a fixed point `p`. A finite-order
     orientation-preserving homeomorphism of `S^1 - {p} ≅ R` is the identity.
   - *Consequence.* In `U_3(Q)/⟨z⟩` the element `z^{1/2}⟨z⟩` has order 2 and
     equals `[x^{1/2}, y]`, which commutes with `y`. So `U_3(Q)/⟨z⟩` embeds in
     no group of orientation-preserving circle homeomorphisms. The same holds
     for `H_3(Z)/⟨z^k⟩` with `k >= 2`.
   - So a T-bar-style route (a circle group containing `U_3(Q)/⟨z⟩`, lifted to
     `R` so that `z` becomes the deck translation) is dead even when the base
     contains `(Q,+)`. This complements `lifts-add-no-unipotent-divisibility`,
     which needs a base without `(Q,+)`.
2. **Abelian-lamp wreath products.** Dead; see the obstruction above.
3. **Spark, not pursued: a central extension over a distortion-free base.**
   Every finitely generated subgroup of `U_3(Q)/⟨z⟩` is a quotient
   `H_N/⟨z⟩ ≅ H_3(Z)/⟨ζ^{N^2}⟩` (`ζ` the central generator of `H_N`), which is
   virtually `Z^2`. So `U_3(Q)/⟨z⟩` has no distorted cyclic subgroups, and O4
   does not exclude it from `VA`. `U_3(Q)` is a central extension of it by
   `⟨z⟩ ≅ Z`, and the distortion lives only in that extension. A route in the
   pattern `Q <= T-bar <= A <= VA` would need:
   - (a) `U_3(Q)/⟨z⟩ <= Γ` for a finitely presented `Γ`, for example `VA`;
   - (b) a central extension `1 -> Z -> Γ~ -> Γ -> 1` restricting to
     `U_3(Q) -> U_3(Q)/⟨z⟩`, a condition on `H^2(Γ; Z) -> H^2(U_3(Q)/⟨z⟩; Z)`;
   - (c) `Γ~` in a finitely presented simple group with distorted elements
     (not `VA`, by O4).

   Attempt 1 shows that `Γ` cannot be a circle group, and (a) is untested for
   `VA`. `V` itself contains `H_3(Z)/⟨z^k⟩`: a finite Heisenberg "clock and
   shift" pair on `k` cones, times two commuting infinite-order elements.
