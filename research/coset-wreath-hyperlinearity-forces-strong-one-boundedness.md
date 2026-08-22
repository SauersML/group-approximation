---
rg: 2
id: coset-wreath-hyperlinearity-forces-strong-one-boundedness
kind: claim
title: If the summit coset wreath group is hyperlinear its factor is strongly 1-bounded, so enemy microstates carry no macroscopic moduli
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterizes hyperlinearity of the HNN carrier by an amalgamated-free Haar unitary inside a matrix model of the base; this is an unconditional entropy CEILING on the wreath group's own factor, constraining the totality of its matrix models rather than characterizing their existence.
  sl3-p3-pair-relative-commutant-collapse: that is the p=3 collapse whose truth would make W_3 non-hyperlinear through the commutant route; this claim is an unconditional theorem about the OTHER branch - what the world must look like if W_3 IS hyperlinear - and is the engine of the new excess-entropy route, consuming no collapse.
---

Let `W_3` be the summit coset wreath group over
`(Gamma, Lambda) = (SL_3(Z[1/3]), SL_3(Z))`.  Claim (THEOREM):

```text
h(L(W_3)) <= 0   unconditionally;                                  (SB1)
W_3 hyperlinear ==> L(W_3) strongly 1-bounded, h(L(W_3)) = 0,
                    delta_0(any generating tuple) <= 1.            (SB2)
```

Proof: `L(W_3)` is a II_1 factor with the lamp Cartan
(`coset-wreath-algebra-has-a-lamp-cartan`), so
`cartan-algebras-are-strongly-one-bounded` applies verbatim.

**Why this matters (new attack surface).**  Quantitatively, (SB2) says
the microstate spaces of a fixed generating tuple of `W_3`, modulo
unitary conjugation, admit epsilon-nets of subexponential-in-`d^2`
cardinality: hyperlinearity of `W_3` is incompatible with any
`c d^2`-parameter family of pairwise non-conjugate matrix models.  Every
enemy configuration of the collapse lane — an almost-representation of
`Gamma` with an equivariant commuting lamp family `k_x in pi(Stab x)'`
carrying the Bernoulli mixed moments — is a microstate of `W_3`.  So:

- **Moduli flip.**  The Lambda-exact-face campaign repeatedly found
  torsor freedom in candidate enemy constructions (Weyl-cohomological
  selection, in-band automorphisms, congruence-commutant freedom of
  dimension `c_m d^2` at fixed level `m`).  If any construction realizes
  such freedom as genuinely non-conjugate microstates at scale
  `c d^2`, then `h(L(W_3)) > 0`, contradicting (SB1) under CE — and
  `W_3` is NON-hyperlinear.  A hyperlinear-side construction can only
  succeed rigidly.  This converts the constructive probes (the p = 2
  flat tower) into a second refutation instrument: measure the moduli.
- **Consistency guard.**  This does not contradict Kun–Thom Cor. D
  (`coordinate-action-not-sofic`): that theorem concerns the Kun–Thom
  pair, and by `arithmetic-integral-subgroup-is-incompressible` its
  infranormality hypothesis FAILS for the arithmetic pair — the
  soficity of `W_3` and of its coset action is genuinely open, and the
  Cartan lives in the limit algebra either way.  Nor does it
  separate the wreath from its base by a naive count: `L(Gamma)` is
  itself strongly 1-bounded by property (T)
  (Hayes–Jekel–Kunnawalkam Elayavalli, arXiv:2107.03278, JIMJ).  The
  open content of the excess-entropy route is therefore a RELATIVE
  count — the lamp torsor given the base — recorded as
  `coset-wreath-microstates-carry-excess-entropy`.

Same statement holds for the `SL_2(Z[1/2])` wreath after splitting the
central `{+-1}` (both summands have lamp Cartans; direct sums of
strongly 1-bounded algebras are strongly 1-bounded).
