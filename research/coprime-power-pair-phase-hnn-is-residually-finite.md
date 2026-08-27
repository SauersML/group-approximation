---
rg: 2
id: coprime-power-pair-phase-hnn-is-residually-finite
kind: claim
title: Coprime power-pair phase HNN extensions are residually finite
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  power-pair-phase-hnn-has-finite-heisenberg-mark-models: that constructs one explicit family of compatible finite quotients preserving the first commutator; this separates every nonidentity word by characteristic finite p-group quotients.
  graph-endomorphism-phase-hnn-embeds-formanek-procesi: that keeps one faithful coordinate fixed and places an injective endomorphism in the other coordinate; both coordinates here undergo different non-surjective power substitutions.
  partial-phase-graph-hnn-is-residually-finite: that keeps the same finitely generated support subgroup in a faithful coordinate at both ends; the target support here is nonprimitive and power-distorted.
---

Let `F=F(x_1,...,x_r)`, `r>=1`, and for a nonzero integer `k` let

```text
phi_k:F->F,                    phi_k(x_i)=x_i^k.
```

If `m,n` are nonzero and coprime, then

```text
E_(m,n)=<F_x times F_y,t |
 t(a,1)t^(-1)=(phi_m(a),phi_n(a)), a in F>             (CPH1)
```

is residually finite.

More precisely, fix any prime `p` not dividing `mn`.  Every finite collection
of forbidden Britton pinches in `(CPH1)` survives in one quotient

```text
F_x times F_y -> Q times Q                              (CPH2)
```

where `Q` is a finite `p`-group and both `phi_m` and `phi_n` induce
automorphisms of `Q`.  The edge map consequently descends to `(CPH2)`, and
the word remains Britton reduced in an HNN extension of a finite group.

Thus the first genuinely nonprimitive signed-Hecke power-pair return is still
an exact finite-quotient geometry.  Nonprimitivity of both support maps and
failure to extend the edge map to an ambient automorphism do not suffice for
finite-dimensional mark collapse.  Any live HNN return must fail the
coprime pro-`p` graph-intersection mechanism proved here, or leave this
power-pair class.
