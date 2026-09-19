---
rg: 2
id: sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical
kind: claim
title: Some torsion-free word-hyperbolic Kazhdan group is sofic and has no nontrivial MF quotient
distinct_from:
  automorphic-sofic-kazhdan-kernel-with-full-mf-radical: that asks for any sofic Kazhdan full-radical K with a finite automorphic presentation, aimed at infinitely presented kernels in region (IO); this is the word-hyperbolic, finitely presented special case with the identity automorphism, which lands in region (AT).
  fp-sofic-kazhdan-group-not-residually-finite: that is Alekseev--Thom 6.1 and asks only for failure of residual finiteness; this asks for no nontrivial MF quotient at all, and for word-hyperbolicity.
  nonsofic-hyperbolic-group: that asks for a hyperbolic group that is not sofic; this asks for a sofic hyperbolic group with full MF radical, and by the trichotomy of non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group one of the two holds as soon as some torsion-free hyperbolic group is not MF.
  non-mf-hyperbolic-group: that asks for one non-MF hyperbolic group; this asks for one with full MF radical, property (T), no torsion and soficity together.
artifacts:
  - research/non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group.md
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
---

**OPEN.** There is a group `Q` that is:
- nontrivial, torsion-free and word-hyperbolic (hence finitely presented);
- Kazhdan;
- sofic;
- of full MF radical: `Rad_MF(Q) = Q`, that is, `Q` has no nontrivial homomorphism to an MF group.

`exact-mf-radical-over-z-via-sofic-hyperbolic-kernel` turns any such `Q` into the witness
`(Q × Z, Q × 0)` of `torsion-free-sofic-exact-mf-radical-over-z`.

## How this splits (from `non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group`)

This claim holds if both of the following hold:
- **(H1)** some torsion-free hyperbolic group is not MF;
- **(H2)** every torsion-free hyperbolic Kazhdan group is sofic.

In fact (H2) is needed only for one quotient `Q` of a fixed torsion-free cocompact `Sp(2,1)` lattice.

Each half can fail on its own:
- **If (H1) fails,** the claim fails, since any `Q` here is itself a torsion-free non-MF hyperbolic
  group.
- **If (H2) fails,** `nonsofic-hyperbolic-group` is settled.

## Consequences

Any `Q` here answers:
- Alekseev--Thom 6.1, being finitely presented, sofic, Kazhdan and without finite quotients;
- `torsion-free-non-residually-finite-hyperbolic-group`;
- `non-mf-hyperbolic-group`.

So this claim is at least as hard as Gromov's residual finiteness question for hyperbolic groups.
It is **not** harder than (H1) plus the hyperbolic soficity question.

## Attempts

- **2026-09-19, swarm-0917-w16-w16-titz-follow (reframing).** Isolated as the hyperbolic product
  branch of the flagship. No attempt at (H1) or at soficity of the Olshanskii quotients was made
  here.
