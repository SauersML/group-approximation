---
rg: 2
id: binary-leavitt-unit-group-is-not-hyperlinear
kind: claim
title: The unit group of the binary Leavitt algebra over F_2 is not hyperlinear
distinct_from:
  binary-leavitt-unit-group-hyperlinear: That is the positive assertion for the same group; this records the negative assertion as a separate possible refuter.
  leavitt-channel-rounding-forces-nonhyperlinearity: That is a conditional implication from unrestricted channel rounding; this is the group conclusion itself.
  leavitt-steinberg-hs-stable: That is normalized-HS stability of a Steinberg group; this directly excludes canonical matrix models of the Leavitt unit group, with equivalence supplied by separate structural theorems.
  kun-thom-lamp-wreath-is-not-hyperlinear: That concerns the binary Kun--Thom wreath; this concerns a different explicit group with direct native internality and compression proofs, not a wreath embedding.
artifacts:
  - research/artifacts/liu-leavitt-direct-internality-and-consequences-2026-09-20.md
  - research/artifacts/liu-leavitt-direct-internality-cross-review-2026-09-20.md
  - research/artifacts/leavitt-direct-normalization-obstruction-2026-09-20.md
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
---

For R=L_(F_2)(1,2), the countable group H=R^x is not hyperlinear.
**ESTABLISHED through the accepted Jihao Liu internality chain and the independently checked direct Leavitt deduction.** The short normalization route is a second proof using Andreas Thom's conditional theorem. This is a written mathematical derivation with explicit imports, not a new Lean build.
Equivalently, there is no homomorphism

```
pi:H -> U(prod_omega (M_(d_n),tr_(d_n)))
```

whose trace is the regular character, `tau(pi(g))=0` for every g!=1.

## Attempts

2026-09-20, completion: `leavitt-nonhyperlinear-from-internal-commutants` removes the heat, SOS and time-selection machinery. A bounded Poincare-defect argument selects a canonical model with scalar full commutant, and native internality contradicts it via the existing finite central-height lemma. Independent cross-review passed. Alternatively, `leavitt-nonhyperlinear-from-compressor-normalization` kills the nontrivial native root x_13(e) directly; simplicity then makes every matrix-ultraproduct homomorphism of H trivial. The all-fields specialization supplies another broader route. The earlier heat route remains a correct alternative, not a remaining obligation.

Historical initial pass:

2026-09-20: `leavitt-nonhyperlinear-from-kazhdan-heat-rounding` records the
audited conditional deduction. Universal rounding of admissible Kazhdan
heat first selects a canonical H-model with scalar full global commutant.
Rounding the native L=EL_3(R) heat in that selected model then creates a
nonzero trace-zero central height, a contradiction. The rounding premise
depends on `kazhdan-commutants-are-internal`, which was then open under
independent review and is now established by the written chain. Neither the stronger arbitrary-channel conjecture nor
an embedding of the Kun--Thom wreath in H is assumed.

The group's finite presentation, infinite simplicity and property (T) have
separate structural proofs/imports. Finite presentation is not needed for
this nonhyperlinearity deduction; the stability corollary has its own
equivalence prerequisite.

**Attribution.** The essential new analytic input is Jihao Liu,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7, with the expectation-lift interface of Proposition 3.1.
The Leavitt conclusion here is Cairn's conditional application of Liu's
analytic theorem, not a theorem claimed in his paper. Andreas Thom retains priority for the conditional normalization used by the alternate proof. The distinct two-use
Leavitt argument is credited to the September 8 Cairn artifacts cited above.
Acceptance of the upstream analytic chain and the independently reviewed consumer routes, rather than attribution alone, now closes this claim.
