---
rg: 2
id: stw07-separating-qd-quotients-force-quasidiagonality
kind: claim
title: A separable C*-algebra with a separating family of quasidiagonal quotients is quasidiagonal, so a Blackadar-Kirchberg counterexample has a nonzero quasidiagonal radical
distinct_from:
  stw07-primitive-mf-traces-force-quasidiagonality: that builds MF traces on primitive quotients and needs nuclearity to pass from MF to quasidiagonal; this takes quasidiagonal quotients directly, needs no nuclearity, and allows any separating family of ideals.
  stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness: that embeds a pullback in a direct sum of two coordinates and also tracks nuclearity; this is the arbitrary separating-family statement, with the radical and the C(X)-algebra consequence.
  stw07-local-qd-subalgebras-force-quasidiagonality: that approximates the algebra from inside by quasidiagonal subalgebras; this detects norms through quasidiagonal quotients.
---

**ESTABLISHED.**  Let `A` be a separable C\*-algebra and `(J_i)` a family of
closed two-sided ideals with `∩_i J_i = 0` such that every `A/J_i` is
quasidiagonal.  Then `A` is quasidiagonal.

Consequences.

1. **Quasidiagonal radical.**  Put `R_qd(A) = ∩ {J : A/J quasidiagonal}`.
   Then `A/R_qd(A)` is quasidiagonal.  So it is the largest quasidiagonal
   quotient, every quasidiagonal quotient of `A` factors through it, and `A` is
   quasidiagonal iff `R_qd(A) = 0`.
2. **C(X)-algebras.**  A separable C(X)-algebra `A` over a compact Hausdorff
   space `X` is quasidiagonal as soon as every fibre `A_x = A/C_0(X\{x})A` is.
   No continuity of the field and no nuclearity is needed.
3. **Blackadar--Kirchberg.**  A negative answer to STW Problem VII is never a
   C(X)-algebra with quasidiagonal fibres, never residually finite-dimensional,
   and never has a separating family of quotients that are each separable,
   nuclear, UCT and faithfully traced (Tikuisis--White--Winter), or each
   separable, exact, stably finite and traceless (Gabe, Corollary C).  Every
   counterexample `E` has `R_qd(E) != 0`, and
   `R_qd(E) ⊆ J_tau` for every tracial state `tau` whose trace-kernel quotient
   `E/J_tau` satisfies the UCT.

So the "C(X)-algebras whose fibres are quasidiagonal but whose global
structure is not" candidate family for a counterexample is empty.  More
generally, non-quasidiagonality is never detected by quotients: whatever
obstructs `E` survives in every quasidiagonal quotient's kernel.  Against
this, quasidiagonality does not pass to quotients.  The cone over `O_2` is
quasidiagonal with quotient `O_2`.  And sums of quasidiagonal ideals need not
be quasidiagonal.  The asymmetry locates the problem in how ideals are glued,
not in how quotients separate.
