---
rg: 2
id: coset-wreath-microstates-carry-excess-entropy
kind: claim
title: If the summit coset wreath group is hyperlinear its microstate spaces carry a macroscopic non-conjugate parameter family
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  no-spherical-leak-in-matrix-ultraproducts: that asks to EXCLUDE one enemy unitary in the commutant; this asks to MULTIPLY enemies - to show that hyperlinear models of the wreath, if any exist, must come in d^2-scale non-conjugate families - an existence-of-moduli target with the opposite polarity, played against the Cartan entropy ceiling.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that is an exact characterization of carrier hyperlinearity by one amalgamated-free Haar unitary; this is a counting strengthening on the wreath side, whose payoff is a contradiction with strong 1-boundedness rather than with the collapse.
---

Claim (OPEN): if `W_3` — the coset Bernoulli wreath over
`(SL_3(Z[1/3]), SL_3(Z))` — is hyperlinear, then

```text
h(L(W_3)) > 0,                                                   (EX1)
```

i.e. some (equivalently, by Jung generator-independence, every)
generating tuple of `L(W_3)` admits, at some precision epsilon and
scale `d -> infinity`, at least `exp(c d^2 log(1/epsilon))` pairwise
non-conjugate microstates.

Together with the THEOREM
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`
(`h(L(W_3)) <= 0` unconditionally), (EX1) makes `W_3` non-hyperlinear:
this claim is exactly as strong as the goal on this branch, but its
mathematical content is of a genuinely different species from every
other open hole of the program — a LOWER bound on microstate counting
(construct many models) instead of an exclusion (kill one model).

What a witness must produce: for each large `d` in a sequence, an
almost-representation `pi_d` of `Gamma` with regular-ish trace, an
equivariant commuting lamp family realizing the Bernoulli moments, AND
a `c d^2`-parameter deformation of the pair that (a) stays a microstate
for the WHOLE group (all mixed lamp-group moments), (b) survives the
quotient by unitary conjugation (no absorption), at a fixed positive
precision.

## Attempts

- **Congruence-commutant dimension counting (where the moduli live).**
  For microstates of the regular trace of `Lambda = SL_3(Z)` factoring
  approximately through `SL_3(Z/m)`, the commutant of `pi_d|_Lambda`
  has dimension `>= c_m d^2` — macroscopic room for the lamp `k` at
  every fixed level.  Dies, so far, at constraint (a): the cross-coset
  commutations `[k, gamma k gamma^{-1}] ~ 0` and the vanishing of mixed
  Bernoulli moments cut the torsor by an amount nobody has bounded
  below; and at (b): a `U(pi(Lambda)')`-family can be partially absorbed
  by conjugations fixing `pi(Gamma)` approximately.  The quantitative
  question — does a positive-dimension quotient survive — is precisely
  the hole.
- **Freeness inside is not enough (calibration).**  `h` is not monotone
  under subalgebras: `L(F_2) subset L(F_2) tensor R` with
  `h(ambient) = 0`.  So free subgroups of `Gamma`, or the Bass–Serre
  freeness of mixed lamp words (the kernel-loop observation that the
  free multi-block choice reproduces the regular trace of the carrier
  `H`), do NOT by themselves force (EX1).  Any attempt must count
  moduli of models of ALL of `W_3`, not exhibit free structure inside.
- **Amalgam lower bounds blocked by the non-amenable edge.**  For the
  `SL_2` wreath, `W = (A rtimes Lambda) *_{A rtimes C} (A rtimes
  Lambda')` from Serre's amalgam `SL_2(Z[1/2]) = SL_2(Z) *_{Gamma_0(2)}
  SL_2(Z)'`; all known free-entropy lower bounds for amalgamated free
  products (Brown–Dykema–Jung style) need an AMENABLE edge algebra, and
  the edge here is `A rtimes Gamma_0(2)`, non-amenable.  At `SL_3`
  there is no splitting at all ((T) implies (FA)).  So current
  technology cannot prove (EX1); the hole calls for a relative/local
  entropy count of the lamp torsor given the base, or an auxiliary
  algebra whose entropy is computable from CE of `W_3`.
- **Two-sidedness, honestly.**  If `W_3` is hyperlinear then by the
  companion theorem `h(L(W_3)) = 0` — i.e. (EX1) is then FALSE and this
  claim is exactly the goal disjunct.  The route's practical value is
  the moduli-flip: every constructive enemy probe (e.g. the p = 2 flat
  tower with its Weyl-cohomological torsor and in-band automorphism
  freedom) now doubles as an (EX1)-witness attempt — if the
  construction's recorded freedom survives conjugation at scale
  `c d^2`, the construction refutes hyperlinearity instead of
  supporting it.  Constructions should therefore always report their
  moduli count modulo conjugation.
