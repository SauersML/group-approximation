---
rg: 2
id: literal-mark-quotient-not-mf-parity-proof
kind: route
title: Translation parity makes the moved lamp's orbit commute modulo the sign
target: literal-mark-quotient-not-mf
requires: []
artifacts:
  - GroupApproximation/Sofic/LiteralSignFreeQuotient.lean
  - GroupApproximation/Endpoint/SignFreeCompressionAudit.lean
  - non_mf_groups_exist.tex
---

## Why sufficient

A complete proof that needs no structure theory for the lamp kernel of `E`,
and therefore no `literal-lamp-kernel-clifford-block-amalgam`.  The whole
argument is the commuting-orbit hypothesis (W3) of the involutive collapse,
checked by a finite parity computation in the base.

Work in `H = E/<w>` with `L` the image of the base `B`, `s = q(t)`, and
witness `k = dbar`, the image of `d = tct^{-1}`.

* (W1) `dbar^2 = 1` from `c^2 = 1`.
* (W2) `[d, t iota(B) t^{-1}] = 1` already in `E`: `c` commutes with the base
  by the defining relators; conjugate by `t`.
* (W3) is the content, and it reduces to eight cases.  The rotation letters
  satisfy `t x t^{-1} = x`, so each of `x, y, z` commutes with `d`; the
  compression relators `t v_i t^{-1} = v_i^2` make each `v_i^2` commute with
  `d` as well.  Hence `iota(g) d iota(g)^{-1}` depends only on the exponent
  vector of the translation part of `g` mod 2 — eight conjugates, indexed by
  `(Z/2)^3`.

The marked word is exactly the commutator attached to the class of `v_1`,

```text
w = [d, iota(v_1) d iota(v_1)^{-1}] .
```

The six rotation words `x, x^2, z, yz, yx, y^2x` carry that class onto the
six remaining nonzero classes (validated numerically over `GL_3(F_2)` before
transcription), and each commutes with `d`; conjugating the displayed
identity by the corresponding `iota(r)` exhibits every nonzero parity
commutator as a conjugate of `w`.  The zero class contributes `[d, d] = 1`.
Centrality of `w` puts all eight in `<w>`, which dies in `H`, and one further
conjugation reduces an arbitrary pair of conjugates to this case.

The involutive collapse then places `[q(iota(v_1)), dbar]` in `Rad_MF(H)`.
Nontriviality is the witness homomorphism `E -> W` of `prop:witness`, which
sends the commutator to a product of lamp basis elements at two distinct
sites and sends `<w>` into `<zeta>`, whose configuration coordinate is zero.

## What it costs

Nothing external.  The Lean endpoints are
`LiteralSignFreeQuotient.signFree_collapse`,
`signFreeQuotient_not_isCDEOperatorMF`,
`signFreeQuotient_not_isOperatorMF`,
`exists_finitelyPresented_signFree_not_isOperatorMF`, and
`commutator_not_zpow_mark`; the
base identification they consume, `LiteralBaseCompleteness.baseAffineEquiv`,
is itself proved in-repo.

## Why the older route is kept

`literal-mark-quotient-not-mf-proof` reaches the same conclusion through the
block-amalgam normal form and explains where the obstruction lives
geometrically.  This route is the one that compiles.
