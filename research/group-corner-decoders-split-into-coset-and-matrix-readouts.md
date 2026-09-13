---
rg: 2
id: group-corner-decoders-split-into-coset-and-matrix-readouts
kind: claim
title: Exact group-corner decoders with abelian readouts factor through coset refinements, while matrix readouts realize every perfect matrix model and meet no support or pair-algebra firewall
distinct_from:
  group-corner-exact-compilers-force-source-affine-safety: that assumes an affine decoder and gets affine-safe source supports; this allows any decoder on abelian contexts and gets only the coset-refinement conditions, and shows that decoders through nonabelian finite groups meet neither.
  coset-refinement-forces-rectangular-central-splitting: that gives necessary conditions for a trace that factors through a coset refinement; this proves that every abelian-readout group-corner decoder produces such a factorization, and that matrix-readout decoders need not.
  relabelable-coset-systems-are-solution-group-corners: that turns a relabelable coset system into a solution-group corner; this goes the other way, extracting a coset refinement of the source context game from an abelian-readout decoder into any central-character corner.
  no-ce-hecke-host-needs-an-fd-invisible-type: that constrains the host group of a finite-subgroup corner model of a non-CE algebra; this constrains the source traces such models induce, and separates abelian from nonabelian readouts.
  sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm: that realizes one four-outcome PVM in a rational abelian character corner; this realizes a whole perfect matrix model of a constraint system in one finite Heisenberg corner.
---

**ESTABLISHED** by `group-corner-decoders-split-into-coset-and-matrix-readouts-proof`.
Not independently reviewed. The Weyl-basis isomorphism in (CD2) is standard,
and no novelty is claimed for it.

## Setting

Use the notation of `group-corner-exact-compilers-force-source-affine-safety`:
`Gamma` countable, `J` central of order exactly `n`, `omega` a faithful
character of `<J>`, `p_omega` as in (GC1), answer projections `e_chi` as in
(GC2), and `X_A(omega)` the characters of a finite abelian `A <= Gamma` that
equal `omega` on `A cap <J>`. `B` is a finite Boolean constraint system with
contexts `V_c` and allowed sets `C_c`, and `G_B` is its context game.

An *exact decoder* of `B` into the corner is a family of self-adjoint
unitaries `x_v in C[Gamma] p_omega` that commute within contexts and satisfy
every constraint polynomial, i.e. a unital *-homomorphism
`A(B) -> C[Gamma] p_omega`. The canonical corner trace is faithful on
`C[Gamma] p_omega`, so for finitely supported observables this is condition 2
of (CS2), exactness on every trace.

The decoder has *abelian readouts* if every context `c` has a finite abelian
subgroup `A_c <= Gamma` with `x_v in C[A_c] p_omega` for all `v in V_c`. Then

```text
x_v = sum_(chi in X_(A_c)(omega)) (-1)^(D_c(chi)_v) e_chi              (CD0)
```

for a unique map `D_c : X_(A_c)(omega) -> F_2^(V_c)`. The affine decoders of
(CS2) are the case where every `D_c` is affine; here `D_c` is arbitrary.

## (CD1) Abelian readouts are coset refinements

Given an exact decoder with abelian readouts, put `K_c = X_(A_c)(omega)`
(a torsor of the annihilator of `A_c cap <J>`, made a group by a base point)
and `beta_c = D_c`. For contexts `c != c'` put `H_(cc') = A_c<J> cap A_(c')<J>`
and

```text
R_(cc') = {(chi, chi') in K_c x K_(c') : chi~ = chi'~ on H_(cc')},     (CD1a)
```

where `chi~` extends `chi` to `A_c<J>` by `omega` on `<J>`. Then:

1. `D_c(chi) in C_c` for every `chi in K_c`;
2. `(K_c, beta_c, R_(cc'))` is a coset refinement of `G_B` in the sense of
   `coset-refinement-forces-rectangular-central-splitting`;
3. `p_c^chi -> e_chi` defines a unital *-homomorphism from its coset-system
   algebra `A(R)` to `p_omega C*(Gamma) p_omega`, and the decoder is the
   pushforward `A(G_B) -> A(R)` followed by it.

So every source trace induced by an abelian-readout decoder factors through a
coset refinement. It satisfies (RCS) of
`coset-refinement-forces-rectangular-central-splitting` and (HL) of
`hidden-labels-import-cross-context-commutation`.

## (CD2) Matrix readouts realize every perfect matrix model

Let `H_d` be the Heisenberg group on `Z_d^3` with
`(a,b,k)(a',b',k') = (a+a', b+b', k+k'+ba')`, `J = (0,0,1)` and
`omega(J) = exp(2 pi i/d)`. The Weyl representation gives a *-isomorphism

```text
C[H_d] p_omega ~= M_d(C),   normalized canonical trace |-> tr_d.        (CD2a)
```

Hence every perfect model of `B` by self-adjoint unitaries in `M_d(C)` is an
exact decoder into the corner of `H_d`, with `n = d`.

## (CD3) Separation

The perfect model in `M_3(C)` under **Model tests** of
`hidden-labels-import-cross-context-commutation` (`c = {u,w}` with NAND,
`c' = {u,y}`, `c'' = {w,z}`) is an exact decoder into the corner of `H_3`, by
(CD2a). By Corollary 1 of that claim its trace factors through no coset
refinement. So by (CD1) no exact decoder with abelian readouts, into any group
corner, induces it. Consequently:

- (RCS), (HL) and the affine safety of (CS2) are not necessary conditions for
  exact group-corner decoders;
- a condition on source traces that every exact group-corner decoder forces
  holds for every perfect model in `M_d(C)` with `tr_d`.

## (CD4) Finite-dimensional conjuncts do not matter

Let `B_0` have an exact decoder into a corner of `Gamma_0`, and let `F` have a
perfect model in `M_d(C)`. Then `B_0 disjoint-union F` has an exact decoder
into a corner of `(Gamma_0 x H_d)/K` for a finite central subgroup `K`. If `F`
has an abelian-readout decoder into a finite group corner and `B_0` one into
`Gamma_0`, the same construction gives abelian readouts. Conversely a decoder
for the union restricts to one for `B_0`.

For `B_tilde = B_0 disjoint-union B_MS^AND` of
`matrix-conj-forces-unsafe-support`, the block has abelian readouts through the
magic-square solution group, the extraspecial group of order 32. The AND
context `(A,B,Y)` reads from `A_c = <A,B,J>` with `D_c(a,b) = (a, b, ab)`. So
`B_tilde` has an exact decoder, with abelian readouts or without, iff `B_0`
has one. The (CS2) firewall for `B_tilde` comes only from affinity.

## (CD5) Several central characters add nothing for affine decoders

(CS1) and (CS2) hold with `<J>` replaced by any finite central subgroup `Z`
and `omega` by any character of `Z`. They also hold summand by summand for a
central projection `p_Omega = sum_(omega in Omega) p_omega`: each summand
trace is a tracial state of `p_Omega C*(Gamma) p_Omega`, and (CS2) applied to
it gives an affine-safe perfect model.

## What remains of break (2b)

For a tracial non-`R^U` source `B_*`, break (2b) of
`research/artifacts/exact-lcs-compilation-map-2026-09-13.md` splits in two.

- **Abelian readouts.** The corner trace induces a tracial state of a coset
  refinement of `G_(B_*)`, so (RCS) and (HL) must pass. These are necessary
  conditions only. By Corollary 3 of
  `forbidden-pair-splits-are-central-rectangle-splittings` the forbidden-pair
  split passes for every perfect trace of constraint-variable presentations,
  and no exclusion of this sector is known.
- **Nonabelian readouts.** By (CD3) no support or pair-algebra condition
  applies. The known constraint is on the host. By
  `no-ce-hecke-host-needs-an-fd-invisible-type`, with `K = <J>` and
  `q = p_omega`, every finite-dimensional representation of `Gamma` kills
  `p_omega`, so `Gamma` is not maximally almost periodic.

So a firewall against `non-ru-bcs-is-satisfiable-in-a-group-factor` along this
route must hold on every perfect matrix model.
