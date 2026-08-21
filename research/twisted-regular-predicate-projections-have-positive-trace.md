---
rg: 2
id: twisted-regular-predicate-projections-have-positive-trace
kind: claim
title: Every nonzero twisted-regular predicate projection has positive canonical trace
artifacts:
  - research/artifacts/section-three-quantitative-no-go-audit-2026-08-21.md
distinct_from:
  regular-trace-blocks-exact-local-predicate-return: that computes one Boolean atom in an untwisted group von Neumann algebra; this treats every finite-support projection in an arbitrary twisted group algebra and transfers it to an honest central-character corner.
  twisted-group-basis-forces-affine-context-support: that classifies joint laws of commuting involutions chosen from a projective basis; this needs no commutativity or Boolean basis assumption and uses only faithfulness of the twisted regular trace.
---

**ESTABLISHED.**  Let `omega` be a normalized scalar `2`-cocycle on a
discrete group `Gamma`, and let `L_omega(Gamma)` have canonical projective
unitaries `u_g` and trace

```text
tau_omega(u_g)=1_(g=1).                                 (TRP1)
```

If a finite-support element

```text
p=sum_g c_g u_g
```

is a projection, then

```text
tau_omega(p)=||p||_2^2=sum_g |c_g|^2.                  (TRP2)
```

In particular every nonzero predicate projection in the twisted group
algebra has strictly positive canonical trace.

The same obstruction is available in an honest group representation.  If
`omega` is realized by a finite central extension `A -> Gamma_tilde -> Gamma`
and central character `chi`, put

```text
q_chi=|A|^(-1) sum_(a in A) conjugate(chi(a)) a.       (TRP3)
```

The normalized corner `q_chi L(Gamma_tilde)q_chi` is the corresponding
twisted group von Neumann algebra.  Therefore a universal exact group-word
construction cannot bound a nonzero twisted predicate projection by defining
relator energy: in this corner all relators have zero energy while `(TRP2)`
is positive.

This does not rule out a finite-matrix-only predicate decoder.  It rules out
promoting a cocycle or projective packet to a trace-functorial exact return in
every tracial representation.
