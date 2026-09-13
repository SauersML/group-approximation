---
rg: 2
id: bk-counterexample-trichotomy-via-qd-radical
kind: claim
title: A Blackadar-Kirchberg counterexample has no quasidiagonal quotient, or a smaller counterexample as radical, or a quasidiagonal radical carrying a nonzero Ext class that survives every quasidiagonal hull
distinct_from:
  stw07-qd-radical-criterion-compact-open: that is the spectral criterion for the radical to be harmless; this sorts counterexamples by what the radical is and wires the third case to the extension conjecture and the UCT problem.
  stw07-trace-obstruction-forces-nonqd-trace-and-non-uct: that prices one explicit mechanism (a trace-positive class); this prices every counterexample through its quasidiagonal radical.
  stw07-qd-trace-positive-class-kills-qd-extension: that is one sufficient mechanism producing a counterexample from a single K_0-class; this is a structure theorem every counterexample satisfies.
---

**ESTABLISHED.**  Let `E` be separable, nuclear, stably finite and not
quasidiagonal, and let `R = R_qd(E)` be its quasidiagonal radical, the smallest
ideal with quasidiagonal quotient
(`stw07-separating-qd-quotients-force-quasidiagonality`).  Exactly one of the
following holds.

1. **QD-perfect.**  `R = E`: no nonzero quotient of `E` is quasidiagonal.
2. **Descent.**  `0 != R != E` and `R` is not quasidiagonal.  Then `R` is a
   counterexample strictly inside `E`, its own radical is nonzero, and it again
   contains a compact ideal carrying a nontrivial lower semicontinuous trace.
3. **Gluing.**  `R` is quasidiagonal.  Then `E` is a stably finite,
   nonquasidiagonal extension `0 -> R -> E -> E/R -> 0` of its largest
   quasidiagonal quotient by a quasidiagonal ideal, and:
   - the stabilised Busby class `[γ^s] ∈ Ext(K⊗E/R, K⊗R) ≅ KK^1(E/R, R)` is
     nonzero.  Its push-forward along every approximately unital embedding of
     `R` into a quasidiagonal algebra is still nonzero.  In particular `R` is not
     KK-contractible, `R ≇ R⊗W` for the Razak--Jacelon algebra `W`, and
     `Prim(R)` has a nonempty compact open subset;
   - either `E/R` fails the UCT, giving a negative answer to STW Problem II
     (`nuclear-algebra-without-uct-exists`), or `E` refutes
     `blackadar-kirchberg-for-uct-quotient-extensions`.  In the latter case `R`
     lacks the K_0-embedding property, so
     `every-separable-nuclear-qd-algebra-has-k0-hahn-banach` is false;
   - `R` contains a compact ideal with a nontrivial lower semicontinuous trace
     (`stw07-qd-radical-criterion-compact-open`).

So, apart from the two "worse" shapes (1) and (2), a counterexample to Problem
VII is exactly a failure of the UCT-quotient extension conjecture or a non-UCT
algebra, glued along a traced compact ideal with a nonvanishing Ext class.
