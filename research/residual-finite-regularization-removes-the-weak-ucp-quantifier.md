---
rg: 2
id: residual-finite-regularization-removes-the-weak-ucp-quantifier
kind: claim
title: Exact finite-dimensional regularization removes the separating-sequence quantifier from weak ucp stability
invalidates:
  - sl3-weak-ucp-via-separating-only-shortcut
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that rounds the Stinespring corner of an ALREADY separating approximation; this first tensors an arbitrary asymptotic representation with an exact regular finite-dimensional packet, then untensors a ucp correction without normalized-Hilbert--Schmidt loss.
  llp-implies-weak-ucp-stability: that produces coordinate ucp lifts from a quotient lifting property; this is an elementary tensor/contragredient argument and assumes the selected hyperlinear approximations are already ucp-correctable.
  finite-quotient-fell-untwisting-leaves-kernel-cocycle: that tries to untwist a finite quotient inside one actor representation and retains its kernel cocycle; this tensors two representations and recovers the first by the invariant maximally entangled vector.
---

**ESTABLISHED.**  Let `Gamma` admit genuine finite-dimensional unitary
representations

```text
sigma_n:Gamma -> U(e_n),       tr_(e_n)(sigma_n(g)) -> delta_(g,e).
                                                                  (RUR1)
```

(Every residually finite group has such a sequence: use regular
representations of finite quotients separating an exhausting family.)  If
every hyperlinear approximation of `Gamma` is pointwise normalized-HS close
to the restriction of ucp maps on `C^*(Gamma)`, then the same ucp-correction
conclusion holds for **every** asymptotic representation of `Gamma`, whether
or not it is separating.

Indeed, for an arbitrary asymptotic representation
`alpha_n:Gamma -> U(d_n)`, the tensor product

```text
beta_n(g)=alpha_n(g) tensor sigma_n(g)                    (RUR2)
```

is a hyperlinear approximation: exact multiplicativity of `sigma_n`
preserves the multiplicative defect of `alpha_n`, while `(RUR1)` forces the
nonidentity traces of `(RUR2)` to vanish.  A ucp correction of `beta_n`
untensors to a ucp correction of `alpha_n` with **constant one** in normalized
Hilbert--Schmidt norm.  The recovery uses the coproduct and the maximally
entangled vector fixed by `sigma_n tensor bar(sigma_n)`; the exact formula is
in `maximally-entangled-ucp-untensoring-proof`.

Consequently, if `Gamma` is hyperlinear and Kazhdan and is weakly ucp-stable
in Dogon's separating-sequence sense, then it is flexibly HS-stable for all
asymptotic representations.  To see this without assuming `(RUR1)`, first
apply weak ucp-stability and Kazhdan corner rounding to one separating
hyperlinear approximation.  This produces genuine finite-dimensional
representations satisfying `(RUR1)` (the flexible padding has relative
dimension `o(1)`, so their normalized characters remain regular).  Apply the
preceding regularization to an arbitrary asymptotic representation, then
round its recovered ucp maps by the same Kazhdan argument.

In particular, because `SL_3(Z)` is residually finite and has property `(T)`,

```text
SL_3(Z) weakly ucp-stable
    iff
SL_3(Z) flexibly HS-stable for ALL asymptotic representations.    (RUR3)
```

Thus the regular/separating quantifier is not a smaller positive route for
this lattice.  The remaining possible advantage of the ucp formulation is
the positive-definite-kernel language itself, not a reduced class of input
sequences.

This theorem does **not** turn the known failure of LLP for
`C^*(SL_3(Z))` into a failure of weak ucp-stability.  The LLP witness is a
norm-lifting obstruction and may be supported on normalized-HS invisible
corners; `(RUR2)` preserves a pre-existing normalized-HS ucp obstruction but
does not manufacture one from a norm-only obstruction.
