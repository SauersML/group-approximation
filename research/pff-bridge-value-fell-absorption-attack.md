---
rg: 2
id: pff-bridge-value-fell-absorption-attack
kind: claim
title: A PFF bridge value supplies the actual finite representations Fell absorption needs, reducing the HNN gap to strong convergence of the combined model
distinct_from:
  hnn-form-of-gkmp-attempt: that reduced the HNN edge to uniform Fell absorption for a residually finite C; this upgrades C to PFF (achievable, B3(1) embeds in F_2 x F_2) so Fell absorption applies with genuine finite reps, and isolates the final gap as strong convergence / freeness of the conjugator.
  bidirectional-hnn-bridge-trivial-value-is-residually-finite: that proves the bridge value is residually finite and embeds in F_2 x F_2; this observes that the embedding upgrades it to PFF and feeds that into the Fell-absorption attack.
---

OPEN (a concrete attack on [[hnn-form-of-gkmp-attempt]] Step 6; steps graded).

**Upgrade the bridge value to PFF.**  `[PROVED]`  The three-generator bridge
value `B3(1) = (F_oo x F_oo) rtimes Z` embeds in `F_2 x F_2`
([[bidirectional-hnn-bridge-trivial-value-is-residually-finite]], map `(BB3)`).
`F_2 x F_2` is a RAAG, hence virtually special, hence PFF (GKMP Cor 1.4), and
PFF is closed under subgroups, so `B3(1)` is **PFF**.  Use `B3` (not `B2`) as
the bridge, so on the `INF` branch `C = B3(1)` is PFF: there is a sequence of
homomorphisms `beta_n : C -> Gamma_n` (finite groups) whose induced unitary
representations strongly converge to the regular representation of `C`.

**Fell absorption with genuine reps.**  `[PROVED at each level]`  Set
`v_n = (beta_n composed with a unitary rep of Gamma_n) circ phi`, an *actual*
finite-dimensional unitary representation of the free group `L` (not an
approximate one), converging to `v = rho_C circ phi`.  Let `pi_n` be the
regular representation of `L` at matching dimension (available: `L <= K_e`, a
product of free groups, which is PFF, so its regular model is a strong limit
of finite reps too).  By **Fell's absorption principle** for the free group,
`pi_n (x) v_n cong pi_n (x) 1_{dim v_n}` via an explicit unitary `W_n`; in the
commutant picture this is exactly `W_n pi_n(l) W_n^* = pi_n(l) v_n(l)`.

**The combined model.**  Put `S = [W_n] in Q`.  Then, at every level and hence
in `Q`, `S pi(l) S^* = pi(l) v(l) = rho(l, phi(l))`, so `S` implements the HNN
edge on `L`.

## The remaining gap, now singular and concrete

`[GAP]`  Two things must be checked to conclude `R` is MF, and they are the
whole content that remains:

1. **Freeness / Britton norms.**  `S` must be free enough from `rho(G x C)`
   that the reduced-HNN normal form norms are reproduced (a Britton-reduced
   word `a_0 s^{e_1} a_1 ... s^{e_k} a_k` must have the correct reduced norm).
   Fell's `W_n` is built from the regular representation of `L`; one must show
   `[W_n]` is `*`-free from the `G`-copy amalgamated over `L`, using the GKMP
   selflessness of the ambient model.  This is plausible because `S` acts as
   a shift-with-shear on the `L`-adapted corners (Step 2 tower), but it is not
   proved.

2. **Strong (operator-norm) convergence.**  The level-`n` model
   `(rho_n(G x C), W_n)` must strongly converge, i.e. the polynomial norms
   must converge to `C*_r(R)`; here PFF of both `C` and `K_e` supplies strong
   convergence of the pieces (Fell `W_n` is a genuine finite-dimensional
   unitary at each level, so the whole level-`n` datum is finite), and the
   remaining point is that the free product of two strongly convergent
   families over the shared `L` is strongly convergent -- which is exactly
   the GKMP strong-convergence output for the amalgam, now applied to the
   `S`-shifted picture.

## Why this is genuinely closer than "adapt GKMP"

Both remaining points are now about a model in which every level is a genuine
finite-dimensional representation (PFF everywhere) plus an explicit Fell
unitary -- not an abstract free-independence existence statement.  The
free-entropy obstruction of [[fp-forces-hnn-edge-into-free-entropy-obstruction]]
is dissolved by using PFF `C`: the shear `v` is a strong limit of
finite-dimensional reps, and Fell absorption makes each such shear an *exact*
coboundary, so the generic free-entropy non-uniqueness (which is about generic
`v`, not finite-dimensional ones) does not apply.  What is left is a strong-
convergence / freeness assembly, the same kind GKMP prove, but now with the
conjugator handed to us explicitly by Fell.

## Attempts

Steps graded above.  The PFF upgrade and level-wise Fell absorption are
proved; the two remaining points (freeness of `S`; strong convergence of the
combined model) are the open assembly, and they are a single strong-
convergence statement about an explicit finite-level model.
