---
rg: 2
id: nonamenable-trace-does-not-exclude-mf-regular-character
kind: claim
title: "A non-amenable canonical trace does not exclude an MF regular character, even for EL_n over a simple ring; the LLP bridge overshoots to non-hyperlinearity"
distinct_from:
  elementary-group-trace-amenable-iff-ring-residually-finite: that proves the canonical trace of EL_n(R) is non-amenable when R is not RF; this shows that conclusion cannot be converted into (H1), because the simple Kazhdan LEF group satisfies it and still has an MF regular character.
  simple-kazhdan-group-lacks-factorization-property: that places G_X outside the factorization class; this uses G_X as a witness that the implication from non-amenable to non-MF fails, and turns that into an obstruction for the Jacobson lane.
  hyperlinear-trace-not-mf-trace: that separates hyperlinear from MF traces in the other direction (a hyperlinear trace that is not MF); this separates MF from amenable (an MF regular character that is not amenable).
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that is the LLP dichotomy for non-RF Kazhdan groups; this applies it to show the LLP bridge from amenability to MF, used on EL_5(J), proves non-hyperlinearity of EL_5(J), which is strictly more than (H1).
---

**ESTABLISHED (composition of established nodes; unreviewed).** Call a trace
`tau` on `C*(G)` an *MF character* if it is `tr_omega o pi` for a
`*`-homomorphism `pi : C*(G) -> prod M_{d_k} / (+) M_{d_k}`. Equivalently,
there are maps `sigma_k : G -> U(d_k)` with operator-norm asymptotic
multiplicativity and `tr sigma_k(g) -> tau(g)`. The regular character
`delta_e` is MF exactly when (H1) of
`jacobson-regular-character-not-mf-without-property-t` fails for `G`.

**(i) Witness.** Let `X` be an infinite minimal subshift and let
`G_X = EL_3(LC(X,F_2) rtimes Z)`. Then:
- `delta_e` is an MF character of `G_X`;
- the canonical trace `tau_{G_X}` on `C*(G_X)` is not amenable;
- `tau_{G_X}` is therefore not quasidiagonal.

So neither "`tau_G` is not amenable" nor "`tau_G` is not QD" implies
"`delta_e` is not MF". This holds even inside the class of elementary groups
`EL_n(R)`, `n >= 3`, over finitely generated simple infinite rings, which is
the class covered by Corollary A of
`elementary-group-trace-amenable-iff-ring-residually-finite`.

**(ii) Lifting lemma (no property T).** If `C*(G)` has Kirchberg's LLP, then
every MF character of `G` is an amenable trace. The same holds for every
trace that factors through a tracial ultrapower `prod M_{d_k} / J_omega`.

**(iii) Consequence for the Jacobson lane.** Let `E = EL_5(J)`. By
`elementary-group-trace-amenable-iff-ring-residually-finite`, `tau_E` is not
amenable. So a route of the form

> (A) `tau_E` is not amenable, and (B) every MF character of `E` is amenable,
> hence (H1)

is sound, but it is blocked in two precise ways.

1. *(B) is where the whole difficulty sits.* (A) also holds for `G_X`. Its
   ring embeds unitally in `prod_omega M_N(F_2)` (Corollary C of
   `elementary-group-trace-amenable-iff-ring-residually-finite`), so it is
   stably finite and has no one-sided-inverse defect. Yet `delta_e` is MF for
   `G_X`. So (A) cannot be what excludes `delta_e`: the pair "(A) and not (B)"
   occurs. (B) fails for `G_X`, so any proof of (B) must use a property of
   `J` that `LC(X,F_2) rtimes Z` lacks. That property is the one-sided inverse
   `TS = 1`, `ST != 1`, used exactly. This agrees with the mirror-LEF
   obstruction recorded on `property-t-free-jacobson-head-collapse`.
2. *The only general bridge overshoots.* A bridge for (B) that does not
   distinguish the operator-norm corona from the tracial ultrapower, such as
   LLP of `C*(E)` via (ii), also makes every hyperlinear trace of `E`
   amenable. With (A) this shows `E` is not hyperlinear, which settles
   `non-hyperlinear-group`. Equivalently, via
   `llp-non-rf-kazhdan-group-is-non-hyperlinear`: `E` is Kazhdan and not RF,
   so LLP of `C*(E)` forces `E` to be non-hyperlinear. A bridge through
   LLP, or through any lifting principle that is blind to the tracial
   ultrapower, is at least as hard as the first non-hyperlinear group.

*Invariant.* The ucp-liftability of the corona `*`-homomorphism, that is,
amenability of the trace.

*Step where the class dies.* The transfer from "`tau` is not amenable" to
"`tau` is not MF". It is false in general, as `G_X` shows. For `E` it can only
come from an operator-norm-specific input that sees `TS = 1` exactly. A
tracially blind input (LLP, local liftability, Hilbert--Schmidt permanence)
proves non-hyperlinearity instead.

Proof route: `nonamenable-trace-does-not-exclude-mf-regular-character-proof`.
