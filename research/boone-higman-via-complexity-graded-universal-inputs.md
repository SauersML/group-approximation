---
rg: 2
id: boone-higman-via-complexity-graded-universal-inputs
kind: route
title: Dead - reduce Boone-Higman to one decidable universal host per complexity bound
target: boone-higman-conjecture
requires:
  - complexity-graded-universal-decidable-hosts-exist
---

**Dead.**  Invalidated by
`no-decidable-group-contains-every-polynomial-dehn-fp-group`; its premise
`complexity-graded-universal-decidable-hosts-exist` is refuted.

**The decomposition.**  Every decidable `G = <X>` has word problem in `F(t_G)`,
where `t_G(n)` is the maximal running time of its decider on words of length
`<= n`, a recursive function.  So Boone--Higman would follow from two
prerequisites, each of which could fail on its own.

- **(i) Graded universal hosts.**  For every recursive `T` a finitely generated
  `U_T` with solvable word problem contains every group with word problem in
  `F(T)`.  This is `complexity-graded-universal-decidable-hosts-exist`.
- **(ii) Boone--Higman for the hosts.**  Each `U_T` embeds in a finitely
  presented simple group.

Given both, `G <= U_(t_G) <= S`.  The attraction is that (ii) is a statement
about countably many specially built groups, which could be engineered for
Thompson-type or Leavitt-type hosts, while (i) is pure computability.

**Where it dies.**  At (i), for `T(n) = 2^((n+1)^37)`.  The effective BORS family
`H_e` (`polynomial-dehn-fp-groups-have-nonuniform-word-problem`) lies in `F(T)`
uniformly, but `[x_e, y_e] = 1` in `H_e` iff `phi_e(0)` halts.  A decidable
host of all `H_e` makes non-halting r.e. by searching for homomorphisms
`H_e -> U_T` that keep `[x_e, y_e]` nontrivial
(`uniform-hosts-force-uniform-word-problem`, clause (H)).

**The class of approaches killed.**  Any route in which the host, or the
envelope, depends on the input only through data from which the word problem
is not uniformly decidable.  This covers:

- a complexity class of the input;
- a Dehn bound known up to `≼`;
- the finite presentation;
- a polynomial-time acceptor with unknown constant
  (`fp-simple-envelopes-not-computable-from-presentations`).

Refining the grading does not help: the exact-time version of (i) fails at the
same `T`, because finitely many exceptional words can be tabulated in a machine's
states.  What survives is hosts that depend on a total decision procedure of
the input.  That is the shape of every known positive envelope construction.
