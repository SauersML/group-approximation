---
rg: 2
id: defect-saturation-from-arithmetic-source
kind: route
title: Saturate the arithmetic affine defect with no Fournier-Facio input at all
target: defect-saturation-full-mf-radical
requires:
  - affine-congruence-source-is-kazhdan
  - two-generated-single-element-hull-router
  - torsion-free-hyperbolic-kazhdan-partner-exists
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineFreeProductSource.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

## Why sufficient

**Source.**  `affine-congruence-source-is-kazhdan` gives `P = Gamma(3) ltimes Z^3`
finitely presented, torsion-free and Kazhdan, with the dilation
`alpha(g,v) = (g, m v)` injective and proper.  Form `B = P x <c>` and the HNN
extension

```text
E = <B, t | t p t^-1 = alpha(p),  p in P>,
```

finitely presented, and torsion-free by `hnn-torsion-theorem`.  With
`p_0 notin alpha(P)` put

```text
w = [t c t^-1, p_0].
```

The word `t c t^-1 p_0 t c^-1 t^-1 p_0^-1` is Britton-reduced — `c^{\pm 1}` is
outside `P` so neither `t c^{\pm 1} t^-1` pinches, and `p_0` is outside
`alpha(P)` so `t^-1 p_0 t` does not — hence `w != 1`.  This is the same
length-four commutator, at the same source, that
`concrete-compression-source-proof` certifies in Lean.  The compression core is
`(P hookrightarrow E, t, c)` and `w` is one explicit generator of its defect.

**Acylindricity is imposed.**  Put `R = E * F_2`.  The Bass--Serre action on
the free-product tree has trivial edge stabilizers, so it is acylindrical and
non-elementary and `R` is acylindrically hyperbolic, finitely presented and
torsion-free; `w != 1` survives the factor embedding.  Nothing is asked of the
HNN geometry itself.

**Routing.**  Take `H` from `torsion-free-hyperbolic-kazhdan-partner-exists` and
apply `two-generated-single-element-hull-router` with `A = H`, `B = R`, `u = w`,
protecting `w`.  It returns `q : R ->> Q` and `q_H : H ->> Q` with `Q`
two-generated, finitely presented, torsion-free and acylindrically hyperbolic,
`q(w) != 1`, and

```text
<<q(w)>>^Q = Q.
```

`Q` is Kazhdan because it is a quotient of `H`, and nontrivial because `q(w)`
survives.

**Saturation.**  Write `bar t = q(t)`, `bar c = q(c)`, `iota = q|_P`.  The
compression relations descend: `bar t iota(P) bar t^-1 = iota(alpha(P)) <=
iota(P)` and `[bar c, iota(P)] = 1`.  Injectivity of `iota` is never used; the
machine-checked kill theorem takes the existential compression form.  Since
`q(w) = [bar t bar c bar t^-1, iota(p_0)]` lies in the defect `D_Q`,

```text
Q = <<q(w)>>^Q <= D_Q <= Q,   so   D_Q = Q.
```

**Detector.**  Apply `normal-kazhdan-defect-non-mf` with source `P`, ambient
`Q` (countable, being finitely presented) and normal Kazhdan subgroup `K = Q`:
nontrivial, normal, Kazhdan, and inside the defect.  Every homomorphism from
`Q` to the unitary group of a norm matrix corona is trivial, so
`Res_MF(Q) = Q`.  Full MF residual passes through surjections
(`coronaMFResidual_eq_top_of_surjective`), so every nontrivial quotient of `Q`
again has full MF residual and is non-MF.  That is the target claim in full.

## Why this is a different route and not a restatement

`defect-saturation-full-mf-radical-proof` reaches the same target from
`fournier-facio-torsion-free-skeleton`, whose defect is certified by a finitely
presented simple torsion-free group sitting inside it, and whose survival
argument is protection by simplicity.  `defect-saturation-from-single-shadow-word`
reaches it through the shadow-residual compiler, whose input is an analytic
condition on the word rather than mere nontriviality.

This route uses neither.  Its dependency set drops, entirely:

- Fournier--Facio, *A torsion-free non-sofic group* (arXiv:2608.02025);
- every finitely presented simple torsion-free group (Burger--Mozes, Hyde--Lodha);
- every universal torsion-free host (Higman, Belegradek--Szczepanski, Chiodo);
- every simplicity-protection argument — Britton gives `w != 1` outright, and
  saturation itself forces `q(w) != 1`.

What it keeps, and what the comparison should not hide: Hull's
small-cancellation machinery, Osin's s-normality lemma, and the hyperbolic
Kazhdan partner, all three of which the Fournier--Facio route also uses.  The
gain is a strictly smaller trust surface on the source side, with the source
half now kernel-checked rather than cited.

Property (T) is not removed from the program.  It is removed from the
*construction and routing* problem — none of the group theory above uses it —
and survives only because the available detector is the normal-Kazhdan
compression theorem, which needs (T) of the source and of the routed normal
subgroup.  A (T)-free version would need a new operator-norm rigidity theorem
replacing the detector, not a further rearrangement of the group theory; the
construction above would survive such a theorem unchanged.
