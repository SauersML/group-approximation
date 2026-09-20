---
rg: 2
id: krein-corner-modules-unitarize-on-the-root-centralizer
kind: claim
title: Every definite-corner Krein module, of any signature, is an honest unitary representation of the root centralizer on its rank-one odd part, so the Leavitt corner hole has no indefinite content
distinct_from:
  root-corner-star-reps-are-definite-krein-modules: that builds the Krein-module dictionary and claims, in (C1)-(C3), that the hole splits into two independent parts (R+) and (R-), that (T) does not reach (R-) or countably generated (R+), and that the class "unitarize, then apply unitary rigidity" dies at positivity; this proves that every such module, indefinite or not, restricts to a unitary representation of C(z) with z -> -1, which refutes those three consequences and leaves the dictionary (K1)-(K5) intact.
  leavitt-mf-null-root-corner-is-equivalent-to-the-goal: that proves, in Hecke-algebra language, that the corner hole is equivalent to the goal and is true via (T); this is the same restriction written on Krein modules, and uses it to calibrate the Krein node, which was established later and contradicts that node's Property (T) corollary.
  leavitt-root-corner-algebra-is-mf-null: that is the open corner hole; this does not settle it T-freely, and shows its only T-free content is z in Rad_MF(C_Delta(z)).
  mf-null-corner-criterion-needs-faithful-ce-trace: that proves MF-null corner implies z in Rad_MF(G) and kills tracial certificates; this proves the other direction, from the centralizer to the corner, at the level of Krein modules over any unital C*-algebra.
artifacts:
  - research/krein-corner-modules-unitarize-on-the-root-centralizer-proof.md
---

**ESTABLISHED** (route `krein-corner-modules-unitarize-on-the-root-centralizer-proof`, swarm-0917-w21-w21-ptl-follow,
2026-09-20, written proof, unreviewed). This is a calibration of
`root-corner-star-reps-are-definite-krein-modules`. The goal `property-t-free-leavitt-full-mf-radical` stays OPEN, and
so does `leavitt-root-corner-algebra-is-mf-null` as a T-free statement.

## Setting

The setting is that of `root-corner-star-reps-are-definite-krein-modules`:

- `Gamma` is a group, `z` in `Gamma` an involution, `P = (1 - z)/2`, `B = P C[Gamma] P`.
- `D` is a unital C*-algebra.
- `(M, sigma, xi)` is a definite-corner Krein module of `Gamma` over `D`. Its form `[.,.]` may be indefinite, and
  (KM) says `sigma(P) M = xi D`.
- `C = C_Gamma(z)` is the centralizer of `z`.

## Statement

**(U) Odd-part unitarization, for any group.** For every definite-corner Krein module `(M, sigma, xi)` over `D`, of
any signature, and every `h` in `C`:

1. `sigma(h) xi = xi u(h)` for a unique `u(h)` in `D`, namely `u(h) = [xi, sigma(h) xi] = rho(P h P)`.
2. `u : C -> U(D)` is a group homomorphism into the unitary group of `D`, with `u(z) = -1`.
3. On the odd part `xi D`, which carries the positive form `d* e`, `sigma|_C` is the unitary representation `u`
   acting by left multiplication.

Equivalently, for every unital star homomorphism `rho : B -> D`, the map `h -> rho(P h P)` is a unitary
representation of `C` with `z -> -1`. No positivity of `M`, no completely positive extension, and no Hilbert-module
dilation is used.

**Novelty.** The algebra form of (U) is Step 1 of `leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof`,
stated there for `D = Q_k`. What is new here is the Krein-module form, the observation that it holds for every
signature, and the consequences (X1)-(X4) below for the later Krein node, which did not take Step 1 into account.

**(V) The Leavitt root.** Let `Delta = St_20(L_(F_2)(1,2))` and `z = x_13(s_1 t_1)`. Let `M_18` be the copy of
`St_18` inside `C_Delta(z)` of `leavitt-mf-null-root-corner-is-equivalent-to-the-goal`.

- Every definite-corner Krein module of `Delta` over `Q_k`, of any signature, gives a homomorphism
  `u : C_Delta(z) -> U(Q_k)` with `u(z) = -1`. Its restriction `u|_(M_18)` is a homomorphism from a group isomorphic
  to `Delta`.
- The Property (T) theorem `leavitt-st20-t-free-holes-hold-via-kazhdan` (`Rad_MF(Delta) = Delta`) kills `u|_(M_18)`,
  so `u(x_lm(1)) = 1`. The two Steinberg commutators `x_1m(q) = [x_1l(q), x_lm(1)]` and `z = [x_1m(q), x_m3(1)]`,
  all of whose entries lie in `C_Delta(z)`, then give `u(z) = 1`, a contradiction.
- So `Delta` has no definite-corner Krein module over any `Q_k`. Both (R+), including countably generated modules,
  and (R-) hold via (T), and (T) is applied only to an honest homomorphism `M_18 -> U(Q_k)`.

## Consequences for `root-corner-star-reps-are-definite-krein-modules`

That node's (K1)-(K5) are unaffected. Its consequences (C1)-(C4) are corrected as follows.

**(X1) (C2) is false.** It states that (T) "does not reach (R-) at all", that it does not reach countably generated
`X`, and that MF-nullity of the root corner "is not known to follow from (T)". By (V), (T) reaches every module of
either signature and rank. The corner hole as literally stated is a theorem, as the equivalence node already recorded
in its section "The Property (T) corollary". The sentence of `mf-null-corner-criterion-needs-faithful-ce-trace` that
(C2) calls a heuristic is correct.

**(X2) The (C3) class obstruction is refuted.** The class "take `rho`, unitarize, apply a unitary rigidity theorem"
contains the complete proof (V). Its death step, "every such proof must first prove the positivity (K3.3) for all
corner representations", is false. Unitarization is needed only on `C_Delta(z)`, where (U) makes it automatic, and
never on `Delta`. The (K4) witness does not transfer, because `C_(D_inf)(z) = <z>` is finite. The death step is valid
only for the subclass that unitarizes on all of `Gamma`.

**(X3) (C1)'s split is not a decomposition.** (R+) and (R-) are not independently failable prerequisites. Both
follow from the single unitary statement `z in Rad_MF(C_Delta(z))`, which is item 3 of (E) and is T-freely
equivalent to the goal.

**(X4) (C4)'s last sentence is withdrawn.** It says a Kazhdan-free proof of the hole "must control indefinite
asymptotic representations of `Delta`". By (U), a T-free proof of `z in Rad_MF(C_Delta(z))` proves the hole, and that
statement is only about unitary homomorphisms.

## What this changes

- The Krein reformulation of the corner hole isolates no new T-free difficulty. The T-free content of
  `leavitt-root-corner-algebra-is-mf-null` is exactly `z in Rad_MF(C_Delta(z))`, which is the goal.
- Class-level rule: a corner certificate at an involution `z` is at least as strong as a unitary statement about
  `C_Gamma(z)`. Indefinite corner representations matter only when the centralizer is too small to carry the radical,
  as in (K4).
- What survives of (C4) is its first half: by (K5), no exact finite-dimensional model can witness or refute the hole.
