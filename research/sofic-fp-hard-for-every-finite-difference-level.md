---
rg: 2
id: sofic-fp-hard-for-every-finite-difference-level
kind: claim
title: Nonsofic finite presentations are hard for every finite level of the difference hierarchy, so sofic ones are neither r.e. nor a Boolean combination of r.e. sets
distinct_from:
  sofic-recognition-finite-presentations-arithmetical-position: that places SOFIC_fp in Pi^0_2 minus Pi^0_1 (the Adian-Rabin side only); this adds the missing other side, that SOFIC_fp is not Sigma^0_1, and pushes further to every level D_n, so SOFIC_fp lies outside BC(Sigma^0_1).
  sofic-recognition-finite-presentations-is-pi2-complete: that is the open completeness statement; this is an unconditional strict lower bound above both one-quantifier classes, proved without any sofic-safe compiler.
  sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group: that is a dichotomy conditional on the rope; this is unconditional and uses no rope. It does rule out any Boolean-combination-of-r.e. upper bound, one of the routes that node mentions.
  amenability-of-finite-presentations-is-pi1-hard: that is the open amenable analogue of Pi^0_1-hardness; the gadgets here do not transfer to it, because amalgams over Z are not amenable (see the calibration below).
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `sofic-fp-hard-for-every-finite-difference-level-proof`.

**Theorem.**  Uniformly in `n >= 1`, every `n`-c.e. set (level `D_n` of the Ershov difference hierarchy)
many-one reduces to `NONSOFIC_fp`.  The same holds for every omega-c.e. set with a computable change bound.

**Corollaries.**
- `SOFIC_fp` is `Pi^0_1`-hard.  So the sofic finite presentations are **not recursively enumerable**, which
  complements the kernel-checked fact that they are not co-r.e.
- `SOFIC_fp` is in no `D_n` and in no co-`D_n`.  So it is not a Boolean combination of r.e. sets, and a
  "finitely many mind changes" certificate for soficity cannot exist.
- Together with (SP1): `SOFIC_fp in Pi^0_2 \ BC(Sigma^0_1)`.

**Method: amenable-edge kill and collapse gadgets.**
- *Seed release.*  Fix the kernel-checked finitely presented nonsofic group `D = <X | r_1..r_m>`.  Then
  `B_D = F(X u Y) x|_phi <z>` with `phi(y_i) = r_i y_i` is finitely generated free-by-cyclic, hence
  residually finite, hence sofic.  Its generator `z` has infinite order, and `B_D/<<z>> = D * F(Y)`.
- *Machine edge.*  `V_U = G(M) * <t>`, where `G(M)` is a finitely presented solvable group simulating a
  universal Minsky machine.  Its words `w_n` satisfy `w_n = 1` iff `n` is accepted, and `[w_n,t]` has
  infinite order otherwise.
- *Kill.*  `K(P,w) = P * (B_D *_{z = [w,t]} V_U)` is nonsofic iff `P` is nonsofic or `w = 1`.
- *Collapse.*  `C(P,w)` is a finite graph of groups with `Z` edges, joining `P * <s>`, `V_U` and
  Baumslag-Solitar vertices `BS(1,2)` through a chain `c ~ [w,t]`, `y ~ y_h`, `h~ ~ h`.  It is nonsofic
  iff `P` is nonsofic and `w != 1`: if `w = 1`, every vertex group dies and the group is free.
- *Levels.*  Alternating the kill and collapse gadgets along nested r.e. sets `A_1 ⊇ A_2 ⊇ ... ⊇ A_n` gives
  `NONSOFIC(P_n(e))` iff `e in (A_1 - A_2) u (A_3 - A_4) u ...`.

The two-sided transfer of soficity holds because soficity is preserved by fundamental groups of finite graphs
of groups with amenable edge groups (Elek-Szabo, Paunescu, Ciobanu-Holt-Rees).

**Paradigm rule.**
- *Change of object.*  The Rice and compiler routes need a positive branch group, the rope, whose soficity
  is itself open.  Here the object is a one-bit gadget whose positive branch is a graph of groups over `Z`.
  Soficity of such groups is a theorem, so the positive branch costs nothing.  The price is that each gadget
  carries only a Sigma^0_1 bit, so finitely many gadgets reach exactly the finite difference levels.
- *First falsifiable step.*  `B_D/<<z>> = D * F(Y)` with `z` of infinite order in the residually finite
  group `B_D`.  This is checked by a direct presentation computation.
- *Calibration.*
  - The collapse gadget alone, `C(D, w_n)`, reproduces the Adian-Rabin Sigma^0_1-hardness of `NONSOFIC_fp`.
  - For amenability the kill gadget fails, since `B_D *_Z V_U` is never amenable.  This is consistent with
    [[amenability-of-finite-presentations-is-pi1-hard]] being open.

**Limit.**  Finite nests stay inside `Delta^0_2`, so `Pi^0_2`-completeness of
[[sofic-recognition-finite-presentations-is-pi2-complete]] needs infinitely many gadgets.  The obvious pumping,
a stable letter `sigma` with `sigma c_n sigma^-1 = c_(n+1)`, propagates kills in both directions because
conjugation is invertible.  This destroys the branch where only finitely many `w_n` vanish.  A one-way
propagator is the missing piece; see `## Attempts` on the target.
