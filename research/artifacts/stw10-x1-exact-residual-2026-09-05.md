---
rg: 2
title: The exact-algebra residual of STW Problem X(1) after its refutation (2026-09-05)
kind: artifact
---

# Purpose

`stw99-problem-x1-amenable-traces-quasidiagonal` is refuted in the graph by
the literal group's full group algebra.  This record (a) pins the verbatim
statement of Problem X and the surrounding text, so the refuted target is
the problem as printed and not a paraphrase; (b) isolates the case STW
themselves single out as the substantive residual, amenable traces on
**exact** C*-algebras; (c) proves that no group-algebra construction, and in
particular no quotient of the literal-group algebra, can reach that
residual; and (d) wires the residual as a root claim with STW's own
reduction as a route.  Nothing here changes the status of any existing node.

# Verbatim primary text

Source: C. Schafhauser, A. Tikuisis, S. White, *Nuclear C*-algebras: 99
problems*, arXiv:2506.10902, PDF fetched and text-extracted on
5 September 2026 (`pdftotext -layout`).  Line breaks are the PDF's.

```text
Problem IX. (1) Let A be a separable nuclear C ∗ -algebra with a faithful trace. Is
    A quasidiagonal?
(2) Let A be a separable exact C ∗ -algebra with a faithful quasidiagonal trace. Is A
    AF-embeddable?
   Nate Brown developed the concept of quasidiagonal traces appearing in Problem
IX(2) above by converting the Hilbert–Schmidt norm approximations used to define
amenability of traces to a stronger operator norm condition ([52]). His prediction
that quasidiagonal traces would prove important objects in the classification pro-
gramme proved very accurate, particularly through the combination of [137, 417].
In Brown’s framework, Rosenberg’s conjecture naturally extends to traces. If Prob-
lem X(1) below (cf. [52, Discussion before Proposition 3.5.1]) has a positive answer,
it would imply a positive answer to Problem IX(1). It seems likely to us that for
not necessarily exact C ∗ -algebras, the heart of matter is whether the trace on the
hyperfinite II1 factor is quasidiagonal (it is certainly an amenable trace). Using that
R has a unique trace and the trace is faithful, this is equivalent to Problem X(2).
   24Quasidiagonality for such C ∗ -algebras is commonly referred to as Rosenberg’s conjecture (see
[60, 325], for example) and is now a theorem ([417, Theorem C]).
                           NUCLEAR C ∗ -ALGEBRAS: 99 PROBLEMS                                   15


Problem X. (1) Are amenable traces on C ∗ -algebras necessarily quasidiagonal?
(2) Is the hyperfinite II1 factor quasidiagonal?
   Note that Problem X(1) easily reduces to the case of separable C ∗ -algebras.
Further, for exact C ∗ -algebras, Problem X(1) can be reduced to the case of faithful
traces. Indeed, every trace τ on a C ∗ -algebra A induces a faithful trace on πτ (A),
where πτ denotes the GNS representation. Further, when A is exact, amenability
of τ is equivalent to injectivity of πτ (A)′′ ,25 and so τ is amenable on A if and only
if the induced trace on πτ (A) is amenable. It follows that if Theorem 11 holds
without the UCT, then Problem X holds for exact C ∗ -algebras.26
   In addition to those traces covered by the quasidiagonality theorem ([417, 165,
379]), there is a positive answer for all amenable traces on cones. This is essentially
a result of Gabe ([165]) but is recorded as [53, Propositon 3.2]. But outside these
frameworks, little is known. For example, the amenable traces always form a face

[footnotes 25 and 26, same page]
   25That this holds follows from [52, Corollary 4.3.4], which is a consequence of Connes’ theorem,
and Kirchberg’s theorem that exact C ∗ -algebras are locally reflexive (see [54, Corollary 9.4.1]).
   26This reduction actually requires something a bit stronger than Theorem 11: namely, that the
AF-embedding can be arranged so that the given faithful amenable trace extends to a trace on
the AF algebra. This stronger statement is what is proven under the UCT in [380].
```

So Problem X(1) is asked for all C*-algebras, and the paper itself records
the exact case as the one that a UCT-free Theorem 11 would settle.

# The residual and its reductions

Root claim: `amenable-traces-on-exact-cstar-algebras-are-quasidiagonal`.
Leaf claim: `exact-faithful-amenable-trace-extends-to-af-embedding`
(Theorem 11 without the UCT, in Schafhauser's trace-extending form).
Route: `exact-x1-via-uct-free-trace-extending-af-embedding`.

The route is footnote 26 written out.  Its three ingredients are all in the
graph or classical: amenability descends through the locally liftable GNS
quotient of an exact algebra
(`amenable-trace-descends-through-locally-liftable-quotient`); every trace on
an AF algebra is quasidiagonal (Arveson extension onto finite-dimensional
stages plus rational approximation of the stage trace); and quasidiagonality
of traces restricts to subalgebras and pulls back along surjections.

# Why the refutation cannot be pushed into the exact class

Let `E` be the literal group and `tau_E` the canonical trace of `C*(E)`,
which is amenable (`literal-group-factorization-property`) and not
quasidiagonal (`literal-canonical-trace-hyperlinear-not-quasidiagonal`).

1. `C*(E)` is not exact, because a full group algebra is exact only for
   amenable groups and `E` contains a Kazhdan base.
2. Suppose `A` is an exact quotient of `C*(E)` through which `tau_E`
   factors, with induced trace `tau`.  The GNS representation of `tau_E` is
   the left regular representation, so `pi_tau(A) = pi_(tau_E)(C*(E)) =
   C*_r(E)` and `pi_tau(A)'' = L(E)`.  For exact `A`, `tau` is amenable if
   and only if `pi_tau(A)''` is injective (Brown, Corollary 4.3.4; STW
   footnote 25).  `L(E)` is not injective, so `tau` is not amenable on `A`.
   The amenability of `tau_E` is a property of the full algebra only.
3. If `G` is any group with `C*(G)` exact, then `G` is amenable, `C*(G)` is
   nuclear and satisfies the UCT (Tu), and all its amenable traces are
   quasidiagonal by Tikuisis--White--Winter and Gabe.

So the group-algebra mechanism behind the refutation is confined to the
nonexact world, exactly as STW's remark predicts.

# Relation to Problem X(2)

For a separable exact `S` inside the hyperfinite II1 factor `R`, the
restriction of `tau_R` is faithful and has injective GNS closure, hence is
amenable.  The exact residual therefore implies that every such restriction
is quasidiagonal, which is the exact-subalgebra part of X(2).  The converse
direction is not automatic: quasidiagonality of the algebra `pi_tau(A)` does
not by itself give quasidiagonality of the trace.

# Status

The universal X(1) is refuted; the exact case is open with one recorded
route; the group-algebra route into the exact case is closed by the argument
above.  No literature search beyond the STW text was performed for this
record.
