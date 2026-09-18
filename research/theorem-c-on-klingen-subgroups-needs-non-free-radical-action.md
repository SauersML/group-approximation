---
rg: 2
id: theorem-c-on-klingen-subgroups-needs-non-free-radical-action
kind: claim
title: Theorem C inside a Klingen subgroup needs a non-free radical action, and a trivially acting center untwists
distinct_from:
  sp4-isw-theorem-c-embeddable-twist-data-exists: that runs Theorem C on all of Sp_4(Z) with Lambda = Sp_4(Z) and the Bernoulli/Maslov supply, blocked by Connes embeddability; this constrains the parabolic rerun (Gamma = H x| Sigma, Lambda inside the amenable radical), where the Bernoulli supply is dead outright and the E^{1,1} solenoid supply untwists.
  klingen-center-kills-isw-condition-one: that kills Lambda = Z for SCALAR Theorem A; this is the operator-valued Theorem C with Lambda of finite index in the whole radical.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that is the scalar (point-space) supply; this is L^0(X,T)-valued supply for nontrivial actions.
---

**Setting.**  Ioana--Spaas--Wiersma Theorem C (arXiv:2006.01874, line
262) asks for the following data:

- a relative-(T) pair `(Gamma, Lambda)`;
- a p.m.p. action `sigma` of `Gamma` with `sigma|Lambda` ergodic;
- cocycles `c_n` in `Z^2(Gamma, L^0(X,T))` with `||c_n(g,h) - 1||_2 -> 0`
  and `c_n|Lambda` not a coboundary.

The conclusion is that `C*(Gamma)` fails the LP, and fails the LLP if
the twisted crossed products embed in `R^omega`.  If such data existed
for a subgroup `Gamma` of `Sp_4(Z)`, then `C*(Sp_4(Z))` would fail the
LLP, by subgroup permanence, and `sp2g-z-full-c-star-algebra-has-llp`
would be refuted at `g = 2`.

**CLAIM.**

```text
(TK1)  For ANY Gamma: if Lambda is amenable (or treeable) and sigma|Lambda
       is essentially free, the Theorem C hypotheses are inconsistent.

(TK2)  Let Gamma = H x| Sigma be as in
       klingen-heisenberg-pair-has-relative-property-t, and let Lambda < H
       have finite index, so (Gamma, Lambda) has relative (T) by (KHT).
       Suppose sigma|Lambda is ergodic, c_n -> 1 and some z^k (k >= 1)
       acts trivially on X.  Let N = <z^j> be the subgroup of Lambda
       acting trivially (j >= 1).  Then for all large n, c_n|Lambda is
       cohomologous in Z^2(Lambda, L^0(X,T)) to the inflation of a
       2-cocycle on Lambda/N, a finite central extension of a rank-2
       free abelian group.
```

**Consequences for the Klingen rerun of Theorem C.**

1. The Bernoulli action, and every action free on the radical, supply
   nothing.  Neither does the Jiang supply of
   `sp4-maslov-circle-survives-in-bernoulli-l0-cohomology`.
2. The candidate supply
   `H^2(H, L^0) ~ E^{1,1} = H^1(Z^2, L^0(X,T))`, for actions where the
   center acts trivially (for example the rational 2-solenoid or `T^2`
   with `Z^2` translating by `alpha v`), untwists.  Relative (T) turns
   the commutator 1-cocycle `g -> c(g,z^j)c(z^j,g)^*` into a coboundary
   on `Lambda`.  So every surviving class there factors through the
   virtually abelian `Lambda/N`.
3. What survives is a sharp problem:
   - (S1) the center acts with a trivial power, and the class is
     inflated from `Lambda/N` but not in the kernel `T * e_N` of
     inflation; or
   - (S2) the center acts essentially freely, but the radical does not.
     Stabilizers then meet the center trivially and so are abelian.

   Both are open.  The Connes-embeddability half is expected to be easy
   in this setting (amenable radical, virtually free Levi), but it is
   not established here.
