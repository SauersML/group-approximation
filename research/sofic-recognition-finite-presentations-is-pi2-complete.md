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
- **w5-111, 2026-09-18: KMS edges and Kazhdan double cones are not one-way propagators (obstruction).**
  - *Result.*  [[kazhdan-double-cones-add-one-sigma1-bit]] closes two of the escapes left by w3-111.
  - *KMS edges.*  An assembly's presentation uses only the generators of each edge group, never its
    relators.  So a KMS machine group used as an **edge** is the free edge on the same words.  It adds only
    an amenability certificate for the image subgroup in the vertex, and a KMS-edge propagator is equivalent
    to a vertex-side one.
  - *Kazhdan cones.*  For a double pair `Gamma ≤ G` (with `G *_Gamma G` nonsofic, as in Kun-Thom v3), the cone
    `X(H,C) = (H * G)/<<[C, Gamma]>>` is sofic iff `H` is sofic and `C = 1`.  It is finitely presented iff `C`
    is finitely generated.  So any computable nest of cones adds one `Sigma^0_1` conjunct and keeps a
    `Delta^0_2` locus `Delta^0_2`.
  - *Calibration.*  With `C` infinitely generated and recursively enumerated, the cone gives a new proof of
    `Pi^0_2`-hardness for recursive presentations.
  - *Exact step.*  Finite presentation forces `C` to be finitely generated.  This is the double-form
    counterpart of the Cornulier obstruction to the wreath amplifier.
  - *What survives.*  Twisted-diagonal cones `(H x Gamma) *_(Gamma_psi) G`.  They are finitely presented with
    a possibly infinitely generated centraliser `C_H(psi(Gamma))`, and nonsofic when that centraliser is
    nontrivial.  Their positive branch needs a soficity theorem for amalgams over a Kazhdan subgroup that is
    not a free factor, and no such theorem is known.
- **w6-111, 2026-09-18: twisted-diagonal cones need a profinitely invisible core (obstruction).**
  - *Result.*  [[twisted-diagonal-cones-need-a-profinitely-invisible-core]] kills the twisted-cone route of
    w5-111 for every twist that the finite quotients of `G` can see.
  - *Mechanism.*  Restricting a Kun-Thom pair to a finite-index normal level `G_1` gives a Kun-Thom pair
    `Gamma ∩ G_1 ≤ G_1`.  So `(H x Gamma) *_(Gamma_psi) G` contains the double `G_1 *_(Gamma ∩ G_1) G_1`, and is
    nonsofic, as soon as `C_H(psi(Gamma ∩ G_1)) ≠ 1` at some level.
  - *Consequence.*  For amenable `H`, such as the machine group, the twist `psi` has finite image, and the
    deciding invariant is `C_H(F_inf)`, where `F_inf` is the invisible core `∩_levels psi(Gamma ∩ G_1)`.  It is
    not `C_H(psi(Gamma))`.  Visible twists, or twists with abelian cores, always give nonsofic cones, on INF as
    well as on FIN.
  - *Exact loophole.*  Evaluation at the origin on the Theorem E pair has core `PSL_r(F_q)` (simple and
    centreless), and every cone through it contains the finite twisted cone
    [[finite-twisted-kazhdan-cone-is-sofic]].  That cone is not residually finite.  Its soficity is now the
    single question the route rests on.
