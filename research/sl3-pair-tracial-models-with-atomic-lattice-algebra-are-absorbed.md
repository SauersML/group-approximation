---
rg: 2
id: sl3-pair-tracial-models-with-atomic-lattice-algebra-are-absorbed
kind: claim
title: In every tracial model of the S-arithmetic SL3 group whose integral-lattice algebra is atomic, the whole group is absorbed by the lattice algebra, by character rigidity
distinct_from:
  sl3-atomic-ambient-is-absorbed-by-lattice: that assumes the AMBIENT algebra amenable, so that property (T) of the ambient group makes it atomic; this assumes only the LATTICE algebra atomic inside an arbitrary finite tracial ambient, and reaches the ambient hypothesis through the Bader--Boutonnet--Houdayer--Peterson character dichotomy, which forbids a regular-character corner.
  sl3-pair-admits-exterior-atomic-model: that was the refuted positive hypothesis in the hyperfinite factor; this closes its natural weakening to Connes-embeddable non-amenable ambients.
  amenable-kazhdan-models-absorb-compression: that uses a compressor and trace-mass conservation; this uses no compressor at all, only character rigidity of the S-arithmetic group and the finite-block matching of the ambient-amenable case.
---

Fix a prime `p`, `Lambda = SL_3(Z) < Gamma = SL_3(Z[1/p])`.  Let
`pi : Gamma -> U(N)` be a homomorphism into a von Neumann algebra `(N, tau)`
with faithful normal tracial state, and suppose `P = pi(Lambda)''` is atomic
(equivalently amenable, by `kazhdan-generated-amenable-algebra-is-atomic`).

**Theorem.**  `pi(Gamma)'' = P`.  In particular no such model, in any
Connes-embeddable ambient, satisfies the exteriority condition (EXT) of
`sl3-pair-admits-exterior-atomic-model`, and the amenable-edge amalgamation
theorem `exterior-hyperfinite-edge-model-amalgam-hyperlinear` has no instance
on the arithmetic pair.

**Input.**  Character rigidity for `Gamma`: every character (extreme tracial
state of `C^*(Gamma)`) is either finite-dimensional -- the normalized trace
of a representation with finite image -- or is supported on the (finite)
center.  For irreducible lattices in higher-rank products such as
`SL_3(Z[1/p]) < SL_3(R) x SL_3(Q_p)` this is the theorem of Bader,
Boutonnet, Houdayer and Peterson, *Charmenability of arithmetic groups of
product type*, Invent. Math. 229 (2022) (arXiv:2009.09952), extending
Bekka's theorem for `SL_n(Z)` and Peterson's for real higher-rank lattices;
cited at statement level, theorem numbers not re-verified against the PDF
in this session.

**Why it closes the weakening.**  A tracial positive-definite function is an
integral of characters, so `tau o pi = sum_i lambda_i chi_i + lambda_infty
chi_infty` with `chi_i` finite-dimensional and `chi_infty` supported on the
center.  If `lambda_infty > 0`, the corresponding central summand of
`pi(Gamma)''` is a corner of `L(Gamma)` (mod center) on which `Lambda` has its
regular character, so `pi(Lambda)''` has a diffuse corner -- but a corner of
an atomic algebra under a central projection of a larger algebra is a
quotient of an atomic algebra, hence atomic.  So `lambda_infty = 0`,
`pi(Gamma)''` is atomic, hence amenable, and
`sl3-atomic-ambient-is-absorbed-by-lattice` applies.

**Scope of the exterior mechanism after this.**  The amenable-edge theorem
can only bite on pairs `Gamma < G` where `G` carries a character whose
restriction to `Gamma` is atomic while the character itself is not: no
strict compressor (`amenable-kazhdan-models-absorb-compression`) and no
character rigidity (this claim).  Neither the Kun--Thom pair nor the
arithmetic pair qualifies.
