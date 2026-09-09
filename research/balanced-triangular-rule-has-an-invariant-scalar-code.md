---
rg: 2
id: balanced-triangular-rule-has-an-invariant-scalar-code
kind: claim
title: An infinite balanced triangular rule admits a continuous invariant scalar code
artifacts:
  - research/artifacts/gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md
  - research/artifacts/gottschalk-controlled-symmetry-linear-code-extension-and-complement-collision-2026-09-08.md
  - research/artifacts/gottschalk-finite-support-reversible-completion-of-invariant-code-2026-09-08.md
  - research/artifacts/gottschalk-prefix-symmetry-group-elementary-amenability-2026-09-08.md
---

For G=A_4 x Z, t=(123), h=(12)(34), and A=I+R_h,
the two-track involution F_A(x,y)=(x+A Q_t(y),y) admits
a continuous injective Q-intertwiner into a proper scalar
binary invariant code over a countable group Lambda. Its
induced map on the code is a continuous equivariant involution,
hence a reversible cellular automaton on that code. The source
has nonzero (I-E)AE, with E=I+R_t+R_t^2.

This is an actual infinite-source encoding and is compatible
with the finite-source exclusion. The code excludes the scalar
all-zero configuration. Over the controlled enlargement below,
a finite-block completion gives a zero-preserving nonlinear
reversible extension to the entire scalar full shift; see
`balanced-invariant-code-has-a-reversible-full-shift-extension`.

An order-preserving extension is impossible, including any
coordinate permutation. Adjoining one controlled source symmetry
K gives an enlarged group Lambda_tilde and an exact two-term
linear-feedback extension x+(R_r+R_{Kr})Q_s of the enlarged
code map. This extension is explicitly noninjective: <s,K> is
A_4, r commutes with s, and a tetrahedral orientation produces
complementary colliding configurations. This does not establish
linear-span membership over the original Lambda.

An injective extension constrained to x+B Q_s remains unresolved,
potentially through different coefficients or linear operators
that vanish on Q_s of the code. Such an extension could provide
a reversible control. The entire current source symmetry group
is now proved elementary amenable, so every full-shift cellular
automaton over it is surjunctive, even with an infinite memory
subgroup. See `current-prefix-symmetry-group-is-elementary-amenable`.
Neither the code nor an extension within this group can refute
Gottschalk's conjecture.
