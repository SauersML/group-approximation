---
rg: 2
id: sofic-recognition-finite-presentations-is-pi2-complete
kind: claim
root: true
title: Soficity of finitely presented groups is Pi-zero-two complete
distinct_from:
  sofic-recognition-finite-presentations-arithmetical-position: that is the unconditional strict-interval placement; this is the completeness statement, which additionally needs a sofic-safe compiler.
  mf-recognition-finite-presentations-is-pi2-complete: that is the MF theorem; this is the sofic one, whose positive branch cannot be certified in operator norm.
  sofic-recognition-two-generator-recursive-is-pi2-complete: that is established for recursive presentations; this asks the same for finite presentations.
---

OPEN.  `SOFIC_fp` is `Pi^0_2`-complete and `NONSOFIC_fp` is
`Sigma^0_2`-complete under computable many-one reductions.

Membership is [[sofic-recognition-has-a-pi2-upper-bound]] and hardness on
recursive presentations is
[[sofic-recognition-two-generator-recursive-is-pi2-complete]]; what is
missing is the finite-output compiler
[[sofic-safe-finite-presentation-compiler]].

## Attempts

- **sw-111, 2026-09-17: edge kill and collapse gadgets.**
  - *Result.*  [[sofic-fp-hard-for-every-finite-difference-level]] gives unconditional hardness for every level
    `D_n` and for omega-c.e., so `SOFIC_fp in Pi^0_2 \ BC(Sigma^0_1)`; in particular `SOFIC_fp` is not r.e.
  - *Gadgets.*  Each is a finite graph of groups over `Z` joining a residually finite seed-release group, a
    solvable machine group and `BS(1,2)` vertices.  Each carries one r.e. bit, as a kill (OR) or a collapse
    (AND-NOT), and none needs the rope.
  - *Obstruction to Pi^0_2.*  Pumping infinitely many bits through a stable letter `sigma c_n sigma^-1 =
    c_(n+1)` spreads triviality both ways, so "finitely many `w_n = 1`" collapses as well.
  - *What is missing.*  An infinite family of collapse gadgets glued so that a kill at stage `n` does not
    propagate to stages `< n`: a one-way propagator.  Or an argument that no such gadget calculus exists.
- **w3-111, 2026-09-17: ceiling for the gadget calculus (obstruction).**
  - *Result.*  [[amenable-edge-assemblies-have-delta2-sofic-locus]] answers sw-111's "or an argument that no
    such gadget calculus exists".  Take any computable family of finite graph-of-groups assemblies whose edge
    maps may be non-injective, with edge groups that are amenable, satisfy max-n and have uniformly decidable
    quotient word problems (cyclic, abelian, polycyclic, metabelian), and whose vertex soficity table is
    `Delta^0_2`.  Its sofic locus is `Delta^0_2`, so no such family reduces `INF`.
  - *Tame cyclic edges.*  With an omega-c.e. vertex table the locus is omega-c.e. with a computable bound.  That
    exactly matches sw-111's lower bound.
  - *Exact step.*  Normalising the edge kernels with a `0'` oracle stops after finitely many steps by max-n, and
    each step is a `Sigma^0_1` question once the quotient word problem is decidable.
  - *What remains.*  A `Pi^0_2`-hardness proof needs at least one of:
    - a non-amenable edge (the rope);
    - an amenable edge with an undecidable word problem, such as a Kharlampovich-Myasnikov-Sapir machine group
      used as an **edge**;
    - a non-`Delta^0_2` vertex table;
    - a construction that is not a colimit (lamp modules).
