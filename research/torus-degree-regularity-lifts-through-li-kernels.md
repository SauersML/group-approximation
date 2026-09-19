---
rg: 2
id: torus-degree-regularity-lifts-through-li-kernels
kind: claim
title: Degree regularity of an injective torus automaton lifts from G/N to G through every locally indicable normal subgroup N, so torus surjunctivity is closed under LI-kernel extensions and a counterexample may be assumed to have no LI normal subgroup
distinct_from:
  injective-torus-automata-have-regular-degree: that is C2 for every group (OPEN); this reduces C2 over G to C2 over G/N whenever N is an elementary-admissible normal subgroup (locally indicable, locally normal p, finite nilpotent or f.g. residually finite-nilpotent factors), and proves it for LI-by-(residually finite) groups.
  torus-degree-regular-on-prime-power-residual-support: that uses only epsilon(D) and needs <supp D> residually prime-power, hence residually finite when f.g.; this uses the fixed torus of an arbitrary normal subgroup, of infinite index, and covers LI-by-finite groups with torsion such as BS(2,3) x A_5, which are not residually finite.
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that pins p_N(D) only for finite-index N; this takes the regularity of p_N(D) for any normal N as input and lifts it to D, turning that node's residually finite case into the quotient hypothesis of an extension theorem.
  every-group-is-torus-surjunctive: that is torus surjunctivity for every group (OPEN); this shows it suffices to prove it for groups with trivial locally indicable radical.
artifacts:
  - research/artifacts/torus-degree-li-kernel-descent-2026-09-19.md
---

**Setting.**
- `tau` is an injective continuous `G`-equivariant self-map of `(T^d)^G`, with degree matrix
  `D = D(tau) in M_d(Z[G])`, so `tau^* xi = xi D` on `H^1 = Z[G]^d`.
- For `N <| G` of any index, `tau` preserves `Fix(N) = (T^d)^(G/N)`. The restriction
  `tau_N` is an injective torus automaton over `G/N` of degree `p_N(D)` (artifact
  Lemma 0.1).
- `𝒞` is the class of groups over which every injective torus automaton, at every `d`, has
  regular degree. By `torus-automata-with-regular-degree-are-surjective`, `𝒞` is the class
  of groups that are torus-surjunctive at every `d`.

**Claim.**
1. **(Algebraic LI descent.)** If `N <| G` is locally indicable and `p_N(D)` is regular over
   `Q[G/N]`, then `D` is regular over `Q[G]`, for every `D in M_d(Z[G])`. The proof applies
   Strebel's class `D(Z) = LI` to `r_D` on finite blocks of `N`-cosets.
2. **(Descent theorem.)** Call `N <| G` *elementary-admissible* if it has a finite series
   `1 = N_0 <= ... <= N_r = N` of normal subgroups of `G` in which each
   `N_i/N_(i-1) <| G/N_(i-1)` is of one of these types:
   - locally indicable;
   - finite nilpotent;
   - finitely generated and residually finite-nilpotent;
   - locally normal `p` (every finite subset lies in a finite normal `p`-subgroup).

   For such `N`, if `D(tau_N)` is regular, then `D(tau)` is regular and `tau` is a
   homeomorphism.
3. **(Extension closure.)** If `N` is elementary-admissible and `G/N in 𝒞`, then `G in 𝒞`.
   In particular LI-by-`𝒞` groups are in `𝒞`.
4. **(Hosts.)** `G in 𝒞` whenever `G` has an elementary-admissible normal subgroup with
   quotient residually finite, or with quotient locally residually prime-power. This
   includes every virtually locally indicable group.
   - New examples: `BS(2,3) × A_5` and `F × A_5` (Thompson's `F`). These are finitely
     presented, not residually finite, not LEF, have torsion, and have no nontrivial finite
     normal `p`-subgroup.
5. **(Reduction.)** If C2 (equivalently torus surjunctivity) fails over `G` at dimension
   `d`, it fails at dimension `d` over `G/M`, where `M` is a maximal locally indicable normal
   subgroup, and `G/M` has no nontrivial locally indicable normal subgroup. So **C2 for all
   groups is equivalent to C2 for groups with trivial LI radical**. Those groups have no
   nontrivial normal free, torsion-free abelian or bi-orderable subgroup.

**Limit.**
- If `N` contains a finite subgroup of non-prime-power order, the Bezout element `D` has
  `p_N(D) = 1` and is a zero divisor. So no descent through such a kernel can use `p_N(D)`
  alone.
- On `Alt_fin(N)` every kernel-descent argument is therefore dead.
- DA for infinite ascending unions of admissible kernels is open.

**ESTABLISHED 2026-09-19** by [[torus-degree-regularity-lifts-through-li-kernels-proof]].
Items 1–3 and 5 are fully proved in the route. Item 4's examples additionally use the
standard facts listed in artifact Section 4 (Brodskii–Howie, orderable implies LI, Mal'cev).
