---
rg: 2
id: atlas-solvable-by-a5-gl4-exhaustion-proof
kind: route
title: Exhaust perfect solvable-by-A5 images in GL4(3)
target: atlas-no-perfect-solvable-a5-action-on-f3-four-space
requires:
  - atlas-no-split-perfect-2-extension-of-a5-acts-on-f3-four-space
  - atlas-q1920-universal-seam-splits-over-a5
artifacts:
  - experiments/atlas_a4_q1920_all_solvable_A5_gl4_classification.g
  - experiments/verify_atlas_q1920_finite_certificates.py
  - research/artifacts/atlas-a4-q1920-all-solvable-a5-gl4.json
---

The split seam theorem supplies the fixed `A5` complement.  For a faithful
irreducible four-dimensional characteristic-three action, a nontrivial
normal 3-subgroup has nonzero fixed vectors and hence, by normality and
irreducibility, acts trivially.  Thus a faithful candidate has trivial
3-core.  The exact ambient order gives residual exponent bounds

```text
0 <= v_2(R) <= 9-v_2(60)=7,
0 <= v_3(R) <= 6-v_3(60)=5.
```

There is no residual prime 13.  A normal 13-core is cyclic and centralized
by the perfect action because `Aut(C13)` is abelian.  Every nontrivial
irreducible `F3[C13]` constituent has dimension `ord_13(3)=3`; centrality
makes the restriction homogeneous, contradicting ambient dimension four.  If
the 13-core is trivial, the Fitting centralizer theorem makes a residual
13-action act faithfully on a 2-group of order at most `2^7`; but any such
odd automorphism prime occurs in some `GL_d(2)`, `d<=7`, whereas the exact
multiplicative order of two modulo thirteen is twelve.

It remains to inspect the finite orders `60*2^a*3^b` in the stated ranges.
The complete GAP perfect-group census finds 29 split solvable-by-`A5`
candidates.  Twenty have nontrivial 3-core and are excluded by the fixed-space
argument.  The remaining nine are precisely the 2-group-radical cases from
the established split census; direct modular computation gives image order
sixty for every four-dimensional irreducible module, killing the nontrivial
radical.  Thus no nontrivial solvable radical acts faithfully.  The stdlib
audit recomputes both exponent bounds, `ord_13(2)=12`, and `ord_13(3)=3`, checks the
`20+9=29` partition, and binds the complete source and output by checksum.
