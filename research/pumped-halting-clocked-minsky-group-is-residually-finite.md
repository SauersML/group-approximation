---
rg: 2
id: pumped-halting-clocked-minsky-group-is-residually-finite
kind: claim
title: The pumped group of a universally halting clocked Minsky machine is residually finite
distinct_from:
  kms-arbitrarily-hard-fp-rf-groups: that imports residually finite outputs for sym-universally halting machines as a black box for word-problem hardness; this proves residual finiteness for the clocked pumped machines, where KMS's intermediate semigroup quotient does not separate and is replaced.
  pumped-divergent-minsky-word-lies-in-profinite-kernel: that is the negative half for divergent machines; this is the positive half for universally halting ones.
---

ESTABLISHED.  The group was changed to `G_0` on 2026-09-13, after review by
`ex-verify-logic-quantum`.

Let `M` be a simple deterministic Minsky machine
clocked by `tau`: each command number carries one Add, or a Sub/zero-test pair
on one glass.  Suppose `M` is universally halting, i.e. every forward
computation from every configuration is finite.  Then `G_0(P(M))`, the KMS
group of `P(M)` with the stop relations `x_(q_0 w) = 1`
([[kms-group-with-stop-relations-simulates-all-words]]), is residually finite.
For `P(M)` and its notation, see
[[pumped-divergent-minsky-word-lies-in-profinite-kernel]].

1. **Finite classes.**  Every nonzero element of `S(M)` has finitely many
   representative words.  Forward computations of partial configurations are
   prefixes of halting ones; backward computations have length at most
   `2 l_tau + 1`.
2. **Classification.**  A nonzero `q`-element of `S(P(M))` is determined by
   the class of its `M`-part, its `A`-letters, and `iota = e_pi - e_rho -
   e_tau`.  It is zero iff its `M`-part is zero, or it carries `A_pi A_rho`
   and `iota = -l_tau` at some member of the class.
3. **One finite quotient.**  Impose `a_pi^D = a_pi^(2D)` and
   `a_rho^D = a_rho^(2D)`, and take the Rees quotient by the ideal of
   `M`-exponents `>= R`.  For `D` and `R` large this is finite and keeps any
   prescribed finitely many elements distinct and nonzero.
4. **Transfer.**
   - The quotient defines a normal subgroup `F` of finite index in the basis group `T_1`
     (clause 6 of [[kms-minsky-machine-groups-simulate-their-machines]]).
   - The image `T_0` of `T` in `G_0` is isomorphic to `T_1` (clause 3 of
     [[kms-group-with-stop-relations-simulates-all-words]]).
   - `Ḡ/F` is a split extension of a finite group by a finitely generated metabelian group,
     hence residually finite.
   - Elements outside `T_0` survive in `G_0/T_0` (P. Hall).

**Correction (stop relations).**  The transfer step needs `T -> T_1` to be
injective.  For `G(P(M))` under KMS's displayed relations G1--G8 it is not:
`x_(q_0 A_0)` is nontrivial there but maps to `1`.  With the stop relations it
is an isomorphism, and B4 of the artifact holds as written with `G_0` in place
of `G`.  See `research/artifacts/ex-review-logic-quantum-2026-09-12-part1.md`
§1.5.

DERIVATION
[[pumped-halting-clocked-minsky-group-is-residually-finite-proof]]
