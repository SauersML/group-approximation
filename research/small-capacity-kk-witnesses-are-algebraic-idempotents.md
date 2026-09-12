---
rg: 2
id: small-capacity-kk-witnesses-are-algebraic-idempotents
kind: claim
title: A Kadison--Kaplansky witness whose spectrum has capacity below one is a nontrivial idempotent of the algebraic group ring
distinct_from:
  reduced-projection-iff-gapped-spectral-measure: that is the exact spectral reformulation of a reduced projection for every group; this constrains the shape of such a witness, forcing an algebraic idempotent whenever the gapped spectrum has capacity below one.
  rank-one-lattice-kadison-kaplansky-and-charzero-idempotents: that proves both conjectures for one class of groups through Baum--Connes; this is a group-free reduction of small-capacity analytic witnesses to algebraic idempotents.
---

**ESTABLISHED** by `small-capacity-kk-witness-idempotent-proof`.

Let `G` be any countable group and `a in Z[i][G]` self-adjoint with disconnected
spectrum in `C*_r(G)`, the witness shape of `reduced-projection-iff-gapped-spectral-measure`.
If `cap(sigma(a)) < 1`, then `sigma(a)` is finite, and for every atom `lambda`
the spectral projection `chi_({lambda})(a)` is a polynomial in `a` over `Q(lambda)`.
So `e = chi_({lambda})(a)` is an idempotent of `Qbar[G]` other than `0` and `1`,
with rational trace strictly between `0` and `1`.

**Consequences for Kadison--Kaplansky.** For torsion-free `G`:
- a small-capacity counterexample to `kadison-kaplansky-torsion-free` already
  refutes Kaplansky's idempotent conjecture for `Qbar[G]` in characteristic zero;
- contrapositive: if `Qbar[G]` has no nontrivial idempotents, every witness in
  `Z[i][G]` has `cap(sigma(a)) >= 1`. In particular its spread is at least `4`,
  and a symmetric two-interval spectrum `[-b,-a] ⊔ [a,b]` needs `b^2 - a^2 >= 4`.

**Where the analytic content must sit.** The algebraic idempotent conjecture is
at least as hard as the analytic one on this shape, so a genuinely analytic
counterexample (one not already algebraic) needs spectrum of capacity at least one.

**Scope.** Nothing here rules out a trace-`1/2` idempotent over a torsion-free
group. The two-atom measure `(delta_2 + delta_(-2))/2` passes every moment and
zeta-integrality test on main; see `integral-spectra-of-small-capacity-are-finite`.
