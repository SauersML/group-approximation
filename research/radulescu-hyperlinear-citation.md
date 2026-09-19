---
rg: 2
id: radulescu-hyperlinear-citation
kind: route
title: Import Radulescu's equivalence and unwind the embedding into microstates with vanishing traces
target: hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
requires: []
---

**(1) ⟺ (2): citation.**  Rădulescu (2008, arXiv:math/0004172) defines a
group to be hyperlinear when it embeds into `U(R^omega)` and proves this
is equivalent to a trace-preserving embedding `L(G) -> R^omega`; the
nontrivial direction (1) ⟹ (2) uses that the embedded unitaries
`u_g in U(R^omega)` can be replaced by unitaries whose traces vanish off
the identity (amplify by tensoring with a faithful trace-zero
perturbation, or use the ultrapower of `R` to realize the left regular
representation's trace), so that `tau(u_g) = delta_(g,e)` and the von
Neumann algebra they generate is `L(G)` with its canonical trace.  Pestov
(2008), Section 5, gives an expository proof.

**(2) ⟹ (3).**  Let `theta : L(G) -> R^U = prod_U M_(d_n) / I_tau` be
trace preserving.  Each unitary `theta(u_g)` has a representing sequence
`(x_n(g))_n` of operators with `|| x_n(g) ||_op <= 1` and
`|| x_n(g)^* x_n(g) - 1 ||_2 -> 0` along `U`; replacing `x_n(g)` by the
unitary part of its polar decomposition (extended arbitrarily on the
kernel) changes it by `o(1)` in `||.||_2`, so the classes are represented
by unitaries `U_n(g)`.  Multiplicativity of `theta` on `u_g u_h = u_(gh)`
and continuity of the trace on `R^U` give `|| U_n(g) U_n(h) - U_n(gh) ||_2 -> 0`
and `tr U_n(g) -> tau(u_g) = delta_(g,e)` along `U`; passing to a
subsequence converts convergence along `U` to ordinary convergence for
the countably many `g, h`.

**(3) ⟹ (2).**  Microstates define a unital `*`-homomorphism
`pi : C^*(G) -> R^U`, `u_g -> [U_n(g)]`, since the defect vanishes in the
quotient.  The state `tau_(R^U) o pi` on `C^*(G)` is `delta_(g,e)` on group
elements, i.e. the canonical trace, so the von Neumann algebra generated
by `pi(C^*(G))` inside `R^U`, with the restricted (faithful, normal)
trace, is `*`-isomorphic to `L(G)` by uniqueness of the GNS completion of
a faithful trace: `pi` extends to a trace-preserving embedding
`L(G) -> R^U`.
