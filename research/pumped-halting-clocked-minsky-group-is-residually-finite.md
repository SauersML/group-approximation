---
rg: 2
id: pumped-halting-clocked-minsky-group-is-residually-finite
kind: claim
title: The pumped group of a universally halting clocked Minsky machine is residually finite
distinct_from:
  kms-arbitrarily-hard-fp-rf-groups: that imports residually finite outputs for sym-universally halting machines as a black box for word-problem hardness; this proves residual finiteness for the clocked pumped machines, where KMS's intermediate semigroup quotient does not separate and is replaced.
  pumped-divergent-minsky-word-lies-in-profinite-kernel: that is the negative half for divergent machines; this is the positive half for universally halting ones.
---

ESTABLISHED (unreviewed).  Let `M` be a simple deterministic Minsky machine
clocked by `tau`: each command number carries one Add, or a Sub/zero-test pair
on one glass.  Suppose `M` is universally halting, i.e. every forward
computation from every configuration is finite.  Then `G(P(M))` is residually
finite (notation of
[[pumped-divergent-minsky-word-lies-in-profinite-kernel]]).

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
4. **Transfer.**  The quotient defines a normal subgroup `F` of finite index in
   the basis group `T_1` (clauses 5--6 of
   [[kms-minsky-machine-groups-simulate-their-machines]]).  Then `Ḡ/F` is a
   split extension of a finite group by a finitely generated metabelian group,
   hence residually finite, and elements outside `T` survive in `G/T`
   (P. Hall).

DERIVATION
[[pumped-halting-clocked-minsky-group-is-residually-finite-proof]]
