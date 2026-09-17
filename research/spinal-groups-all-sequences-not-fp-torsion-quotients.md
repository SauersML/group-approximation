---
rg: 2
id: spinal-groups-all-sequences-not-fp-torsion-quotients
kind: claim
title: No spinal group with varying section maps is a quotient of a finitely presented torsion group, and its finitely presented covers contain free subgroups
distinct_from:
  self-similar-spinal-groups-not-fp-torsion-quotients: that is the constant-sequence (self-similar) case; this lets the spine automorphism and the section maps change level by level, which covers non-self-similar families such as the odd-p analogues of the groups G_omega
  fp-covers-of-grigorchuk-groups-are-large: that imports the large-cover theorem for the first Grigorchuk group and the 2-groups G_omega; this proves the weaker free-subgroup conclusion for every spinal system, including the odd-p families that import does not cover
---

**ESTABLISHED** (proposed; proof in `spinal-groups-all-sequences-not-fp-torsion-quotients-proof`).

**Setting.** Let `X` be a finite set with `|X| = d >= 2` and `x_0 in X`. Let
`A <= Sym(X)` be transitive, acting on `X*` by rooted automorphisms, and let
`B` be a finite group. A *spinal system* is a sequence `(rho_n, omega_n)`,
`n >= 1`, of automorphisms `rho_n` of `B` and tuples
`omega_n = (omega_{n,y})_{y != x_0}` of homomorphisms `B -> A`. For `k >= 0`
define `b -> b^(k)` in `Aut(X*)` level by level: `b^(k)` fixes level 1, its
section at `x_0` is `(rho_{k+1}(b))^(k+1)`, and its section at `y != x_0` is
the rooted automorphism `omega_{k+1,y}(b)`. By induction on the level each
`b -> b^(k)` is a homomorphism. Put `J_k = < A u B^(k) >`. Assume, for every
`k >= 0`:

- (S1) `b -> b^(k)` is injective;
- (S2) `U_y omega_{k+1,y}(B)` generates `A`.

A constant sequence gives exactly the self-similar spinal groups of
`self-similar-spinal-groups-not-fp-torsion-quotients`.

**Examples.**

- *Grigorchuk's 2-groups `G_omega`.* `d = 2`, `A = C_2`, `B = V_4 = {1,b,c,d}`,
  `rho_n = id`, and `omega_{n,0}` is the epimorphism `V_4 -> C_2` whose kernel is
  the letter named by `omega_n in {0,1,2}`. (S2) always holds. The kernel of
  `b -> b^(k)` is the intersection of the kernels along the tail, so (S1)
  holds iff `omega` is not eventually constant.
- *`p`-analogues of `G_omega`.* `d = p`, `A = C_p`, `B = C_p^2`, `rho_n = id`, one
  coordinate `omega_{n,y}` an epimorphism `B -> C_p` and the others trivial.
  (S1) holds iff every tail uses two epimorphisms with different kernels.
- *Self-similar cases.* The first Grigorchuk group, the Gupta-Sidki and GGS
  groups, and the Sunic groups with invertible spine map.

**Theorem.** Let `F` be free on `(A\1) u (B\1)` and `N_0 = ker(F -> J_0)`.
There are normal subgroups `M_0 <= M_1 <= ... <= N_0` with `U_j M_j = N_0`,
`F/M_0 = A * B`, every `F/M_j` containing an element of infinite order, and,
unless `|A| = |B| = 2`, a non-abelian free subgroup. `M_j` depends only on
`(rho_n, omega_n)` for `n <= j`. Consequently:

1. every finitely presented group that maps onto `J_0` has an element of
   infinite order, so **no spinal group is a quotient of a finitely presented
   torsion group**;
2. unless `|A| = |B| = 2`, every finitely presented group that maps onto `J_0`
   contains a non-abelian free subgroup;
3. `J_0` is a marked limit of the non-torsion groups `F/M_j`, and `F/M_j` is
   built from the first `j` terms of the system alone.

**What it kills for Zaremsky Problem 1.11.** A finitely presented infinite
torsion group `P` has a just-infinite torsion quotient. The theorem says
that no such quotient, nor any quotient of `P` at all, is a spinal group for any
spinal system. This covers uncountably many torsion branch groups, and whole
families of them are not self-similar: every torsion `G_omega` and every
torsion group in the `p`-analogue families. The route "finitely presented torsion cover of
a known torsion branch group" is dead on the whole spinal class. A
counterexample must have all of its just-infinite branch quotients outside it.

**Calibration.** A nontrivial finite `J_0` would be a counterexample to
item 1. It is excluded: the section at `x_0` maps `St_{J_k}(1)` onto `J_{k+1}`
(by (S2), transitivity and `rho_{k+1}` onto), and `St_{J_k}(1)` is proper. If
`J_0` were finite, then every `J_k` would be finite with
`|J_k| > |J_{k+1}|`, which is impossible. For eventually constant `omega`,
`G_omega` fails (S1) and the theorem says nothing; for constant `omega` it is
the infinite dihedral group, which does have elements of infinite order.
