---
rg: 2
id: hecke-corner-uniform-lattice-transfers-embeddability
kind: claim
title: Hecke algebras of a group with a uniform lattice are corners of matrix algebras over the lattice's group von Neumann algebra
distinct_from:
  non-ru-bcs-is-satisfiable-in-a-group-factor: that asks for a model of the non-RU constraint system in a corner of some group von Neumann algebra; this shows that Hecke algebras of totally disconnected groups with a uniform lattice are already such corners, so they add no new host class.
  amenable-edge-graph-corners-cannot-groupify-a-nonce-game: that proves hyperlinearity of amenable-edge graphs of hyperlinear groups; this uses it only for the free products of Z/2 that act simply transitively on regular trees.
  hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower: that is the dictionary between hyperlinearity and Connes embeddability of L(G); this transfers Connes embeddability from one uniform lattice to every Hecke algebra of the ambient group.
---

**ESTABLISHED.**  No novelty is claimed: this is an elementary induction
argument, and some version of it is likely folklore.

**Setting (HC0).**  Let `G` be a group and `X` a transitive `G`-set with base
point `x_0`.  Let `Gamma <= G` be a countable subgroup acting on `X` with
finitely many orbits, with representatives `x_1, ..., x_m`, and finite point
stabilizers `F_i = Gamma_(x_i)`.  Let `pi : G -> U(l^2 X)` be the permutation
representation and put

```text
M = pi(G)'  (in B(l^2 X)),   tau(T) = <T delta_(x_0), delta_(x_0)>,
c = sum_i 1/|F_i|.                                                (HC0)
```

**(HC1) Corner embedding.**  `tau` is a faithful normal tracial state on `M`.
There are a projection `Q` in `M_m(L(Gamma))` and a unital, injective, normal
*-homomorphism `Phi : M -> Q M_m(L(Gamma)) Q` such that

```text
(Tr_m (x) tau_Gamma)(Phi(T)) = c * tau(T)   for all T in M.           (HC1)
```

**(HC2) Transfer.**  If `Gamma` is hyperlinear, then `(M, tau)` embeds
trace-preservingly into a tracial matrix ultraproduct.  So for every *-algebra
`A` and every unital *-homomorphism `rho : A -> M`, the tracial state
`tau o rho` is Connes-embeddable.  Contrapositively, a unital *-homomorphism
into `M` from a *-algebra with no Connes-embeddable tracial state forces
`Gamma` to be nonhyperlinear.  An example of such a *-algebra is the BCS algebra
of `mipstar-bcs-tracial-nonru-exists`.

**(HC3) Totally disconnected groups.**  Let `G` be locally compact and totally
disconnected, `K <= G` compact open, and `Gamma <= G` a uniform lattice
(discrete, with `Gamma\G` compact).  Then `X = G/K` with `x_0 = K` satisfies
(HC0), and `M_(G,K) := pi(G)'` on `l^2(G/K)` is the Hecke von Neumann algebra
of `(G, K)`.  Unimodularity is not needed.

**(HC4) All or none.**  If `G` has one hyperlinear uniform lattice, then
`M_(G,K)` is Connes-embeddable for every compact open `K`.  A Hecke-algebra
certificate of nonhyperlinearity can therefore exist only in a `G` with no
hyperlinear uniform lattice at all, and it then certifies every uniform
lattice of `G` at once.

**(HC5) Products of regular trees.**  Let `a, b >= 2` and `W_a = *_(i=1)^a Z/2`.
`W_a x W_b` is a hyperlinear uniform lattice in `Aut(T_a) x Aut(T_b)`, and in
every closed subgroup containing it.  So none of their Hecke algebras can host a
*-algebra without Connes-embeddable traces.  In particular the Hecke transfer
through `Aut(T_a) x Aut(T_b)` cannot certify nonhyperlinearity of the
Burger--Mozes or Radu lattices (`radu-bmw-lattice-sofic`).

## Remaining room, not claimed

The route of `research/artifacts/ideas-2026-09-13/nh/nh-groupify-factor.md`
(A6) survives only through a non-discrete closed `G` that contains a uniform
lattice but no hyperlinear uniform lattice.

- Products `G_1 x G_2` of closed cocompact unimodular subgroups of tree
  automorphism groups are probably also excluded. If each `G_i` contains a
  uniform tree lattice (Bass--Kulkarni, *Uniform tree lattices*, JAMS 1990;
  not checked here), that lattice is a finite graph of finite groups (Bass--Serre
  theory, not re-checked), hence hyperlinear by
  `amenable-edge-graph-corners-cannot-groupify-a-nonce-game`.
- A discrete `G = Gamma` with trivial `K` gives `M = L(Gamma)` back, so it
  adds nothing.

No candidate host of the remaining kind is known.

## Attempts

- **The imprimitivity crossed-product form (A6 step 2).**  It is not needed.
  The permutation representation on `l^2(G/K)` restricted to `Gamma` gives
  the corner directly, with an explicit trace constant `c`.  The Plancherel
  weight, the crossed product `L^infty(G/Gamma) rtimes G` and the von Neumann
  Green isomorphism never enter.
- **Single trees and amenable `G`.**  Killed as in A6.  Given (HC4), a uniform
  lattice that is virtually free, or amenable, makes every Hecke algebra
  Connes-embeddable.  Both facts about lattices are standard and were not
  re-checked here, so they stay outside the established statement.
