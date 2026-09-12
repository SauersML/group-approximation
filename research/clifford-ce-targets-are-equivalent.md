---
rg: 2
id: clifford-ce-targets-are-equivalent
kind: claim
title: The full, even-core, and one-character Clifford CE targets are the same problem
distinct_from:
  kun-thom-clifford-crossed-product-ce: That is the open question of whether the Clifford crossed product is Connes embeddable; this says that three natural-looking reformulations of it are equivalent, so it is graph hygiene rather than progress on the question.
  kun-thom-clifford-radical-phase: That establishes the exact Clifford phase detector for the sofic-radical word; this compares the possible ambient algebras in which one might realize it.
artifacts:
  - notes/PERFECT_CORE_KUN_THOM_WREATH.md
---

Write `M_full = Cl(X) crossed_product G` for the negative full Clifford
crossed product over `X = G/Gamma`, `A_CAR crossed_product G` for its even
subalgebra crossed with `G`, `E_(Cl,0)` for the perfect even Clifford cover,
and `tau_can` for the canonical trace on `A_CAR crossed_product G`. Then:

```text
M_full Connes embeddable
  <=> A_CAR crossed_product G Connes embeddable            (Prop 4)
```

and the following are equivalent (Theorem 6, "no character shortcut"):

1. `E_(Cl,0)` has a Connes-embeddable character `chi` with `chi(z) != 1`;
2. it has a Connes-embeddable character `chi_-` with `chi_-(z) = -1`;
3. the canonical trace `tau_can` is Connes-embeddable.

## Why this belongs in the graph

Three formulations of the Clifford CE problem look like independent attack
surfaces and are not. The corpus states the hazard directly:

> Thus the full-Majorana formulation and the perfect even-core formulation
> are two presentations of the same CE problem.  The full formulation makes
> the relative wall \(C_o\in\pi(\Gamma)'\) visible; the even formulation keeps
> the nonsofic witness perfect and exposes the canonical CAR trace.  **They
> must not be counted as independent construction routes.**

Theorem 6 closes the third apparent surface: one might hope that producing
*some* Connes-embeddable character merely nontrivial on `z` is cheaper than
producing the canonical trace, since the former asks only for a nonzero
negative corner rather than a specific trace value. It is not — compressing to
the negative central corner and renormalizing upgrades any such character to
one with `chi_-(z) = -1`, and Lemma 5 then pins it to `tau_can`.

## What each formulation is still good for

The equivalences are about difficulty, not about usefulness. Each presentation
exposes something different and is worth keeping as a *view*:

- `M_full` makes the relative wall `C_o in pi(Gamma)'` visible, which is what
  connects to `kun-thom-clifford-relative-wall`;
- the even core keeps the nonsofic witness perfect, which matters for the
  simple/perfect envelope consequences;
- `tau_can` is the concrete object a construction would actually have to embed.

What is not allowed is to treat progress on one as independent evidence about
another, or to open three routes and count them as three chances.
