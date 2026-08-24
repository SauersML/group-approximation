---
rg: 2
id: one-two-three-fibre-product-theorem
kind: claim
title: The 1-2-3 theorem -- the fibre product of a finitely presented group over a type F_3 quotient with finitely generated kernel is finitely presented
distinct_from:
  hnn-extension-finite-presentation-permanence: that is finite-presentation permanence for HNN extensions along finitely generated associated subgroups; this is finite presentability of a subdirect product and its hypotheses are finiteness properties of a QUOTIENT, not of an associated subgroup pair.
  mihailova-nonseparable-coset-stabilizer: that builds a fibre product whose coset stabilizer is nonseparable, using a free group over a quotient with no finiteness property at all; this is the positive theorem that says when a fibre product is finitely presented, and the Mihailova examples are exactly the case where its F_3 hypothesis fails.
  fiber-product-conjugation-action-lemma: that computes the orbit data of an action of the fibre product and says nothing about presentations; this says the fibre product is finitely presented and says nothing about actions. A route needs both and they are independent.
  fp-quotient-iff-kernel-finitely-normally-generated: that characterizes finite presentability of a QUOTIENT of a finitely presented group by finite normal generation of the kernel; this produces finite presentability of a SUBGROUP of a direct product and its hypothesis is a higher finiteness property of the quotient rather than a generation property of the kernel.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let

    1 -> N -> T -pi-> Q -> 1

be exact with `N` finitely generated, `T` finitely presented and `Q` of type
`F_3`.  Then the fibre product

    T x_Q T  =  { (a,b) in T x T : pi(a) = pi(b) }

is finitely presented.

Baumslag--Bridson--Miller--Short, *Fibre products, non-positive curvature,
and decision problems*, Comment. Math. Helv. 75 (2000).

**Verification status.**  Statement located 2026-08-24 through secondary
sources (the subdirect-product literature, e.g. arXiv:1107.2590 and
arXiv:1302.2745, which restate it as the "1-2-3 theorem" in exactly this
form).  The primary paper was not read.  The three numbers name the three
hypotheses: `N` of type `F_1`, `T` of type `F_2`, `Q` of type `F_3`.

**Attribution note.**  An asymmetric strengthening -- two different finitely
presented groups `T_1, T_2` with isomorphic type `F_3` quotients and only one
of the two kernels required finitely generated -- is due to
Bridson--Howie--Miller--Short.  Nothing in this graph needs it: the routes
here take both factors to be the same group `T`, which is the symmetric case
stated above.  Where an external source calls the step "the asymmetric 1-2-3
theorem", the symmetric form is what is actually used.

## Where the graph uses it

Exactly once, in `boone-higman-via-fiber-product-criterion`, to supply the
second clause of `type-a-action-gives-boone-higman-for-subgroups` -- finite
presentability of the acting group.  It is the only clause of type (A) that
the fiber-product construction does not get from
`fiber-product-conjugation-action-lemma` by pure computation, and it is the
reason the criterion carries an `F_3` hypothesis on `Q` rather than mere
finite presentability.
