# Serre's question for SL_3(Z): incoherence-side analysis, part 1 (2026-09-13)

Lane z3-04-sl3z-incoherent (ZP swarm). Root: `zaremsky-3-04-sl3z-coherent`.
All claims below are unreviewed. "Recalled" marks literature statements that
were not re-read from the source in this session: WebSearch was exhausted and
the arXiv API was rate limited.

## 1. What is on main (landed this session)

| node | status | content |
|---|---|---|
| `zaremsky-3-04-sl3z-coherent` | open root | verbatim Problem 3.4, two answer routes |
| `sl3z-is-coherent`, `sl3z-is-incoherent` | open | the two answers |
| `sl3z-infinite-order-centralizers-are-solvable` | established (proof route) | eigenvalue case analysis |
| `sl3z-products-of-infinite-subgroups-are-polycyclic` | established (route from the centralizer claim) | no `Z x F_2`, no `F_2 x F_2` |
| `sl3z-contains-f2-times-f2` | refuted | its route `sl3z-incoherent-via-f2-times-f2` is dead |
| `sl3z-non-zariski-dense-fg-subgroups-are-fp` | established (proof route) | witnesses are thin |
| `sl3z-contains-cd2-euler-positive-fibered-subgroup` | open | criterion 1 prerequisite |
| `sl3z-incoherent-via-euler-fibered-subgroup` | route | Wang-sequence proof |
| `sl3z-contains-rfrs-cd2-subgroup-with-positive-b2` | open | criterion 2 prerequisite |
| `sl3z-incoherent-via-rfrs-cd2-positive-b2` | route | via `virtually-rfrs-cd2-coherence-characterization` (Fisher–Linton–Sánchez-Peralta, arXiv:2603.16763v1, Cor. 4.1) |
| `sl3z-dense-with-unipotent-lattice-has-finite-index` | open pending citation | Venkataramana-type statement for SL_3, self-contained modulo Tits' `E(m)` finite index |
| `sl3z-congruence-elementary-generators-have-finite-index` | open (citation to check) | Tits 1976, recalled |

## 2. Profile of any witness

Let `N <= SL_3(Z)` be finitely generated and not finitely presented.

1. `N` is Zariski dense and of infinite index (thin).
2. No two commuting infinite subgroups of `N` generate a non-polycyclic group.
   In particular `N` has no `Z x F_2`, no infinite normal solvable subgroup,
   and every infinite-order element has polycyclic centralizer.
3. `N` meets the integral points of every maximal-parabolic unipotent radical
   in rank at most one, and contains no finite-index subgroup of a rational
   conjugate of the integral Heisenberg group. This is conditional on the
   Tits citation.
4. If `N = ker(G -> Z)` for a finitely presented `G <= SL_3(Z)`, then `G` is
   thin too. `G/N` embeds in `Out(N)`, because the centralizer of the
   Zariski-dense `N` is trivial. The monodromy fixes the conjugacy class of
   the inclusion `N -> SL_3(C)`: all traces are invariant under it.

## 3. Criteria for a witness

- **(C1) Fibration with nonzero Euler characteristic.** `G` of type FP,
  `cd G = 2`, `chi(G) != 0`, with an epimorphism onto `Z` whose kernel is
  finitely generated. Then the kernel is not finitely presented (proof in the
  route). Recalled, not re-verified: Gaboriau's theorem gives
  `b_1^(2)(G) = 0` here, so `chi(G) = b_2^(2)(G) > 0`.
- **(C2) Virtually RFRS.** `G` finitely generated, virtually RFRS,
  `cd_Q G <= 2`, `b_2^(2)(G) > 0`. Then `G` is incoherent. No fibration is
  needed. By the same characterization, `G` is coherent iff it is virtually
  free-by-cyclic.
- (C1) and (C2) overlap when `G` is RFRS: Kielak's theorem recovers a virtual
  fibration from `b_1^(2) = 0` (recalled).

## 4. Candidate classes and where each stands

### 4.1 Products and right-angled patterns: dead

`F_2 x F_2`, `Z x F_2` and RAAGs `A_Gamma` in which some vertex has two
non-adjacent neighbours all contain `Z x F_2`, so none embeds. The RAAGs that
survive are free products of `Z` and `Z^2`, which are coherent.

Polygons of groups with abelian vertex groups and infinite cyclic edge groups
die for the same reason. An edge element lies in two abelian vertex groups
that generate a non-solvable subgroup of its centralizer.

### 4.2 Square complexes with positive Euler characteristic: constrained

For a compact nonpositively curved square complex,
`chi = sum_v (1 - |V(lk v)|/2 + |E(lk v)|/4)` (four corners per square). So
`chi > 0` forces some vertex link to be a triangle-free graph with
`|E| > 2|V| - 4`. Triangle-free planar graphs have `|E| <= 2|V| - 4`, so such a
link is non-planar (e.g. `K_{3,3}`, `K_{3,4}`).

If every link is complete bipartite, the complex is covered by a product of
trees. If it is also virtually special, it is virtually a product of free
groups (recalled), hence contains `Z x F_2`: dead. The live case is links that
are dense and non-planar but not complete bipartite, with no `Z x F_2` in
`pi_1`. No example is known inside `SL_3(Z)`.

### 4.3 Hyperbolic groups of cohomological dimension two with chi > 0: live, the main (C2) candidates

Example: torsion-free C'(1/6) groups with at least as many relators as
generators. They have cd 2 and `chi = 1 - g + r > 0`. They are cubulated
(Wise) and hyperbolic, hence virtually compact special (Agol) and virtually
RFRS.

Question: does any one-ended hyperbolic group of cd 2 with `chi > 0` embed in
`SL_3(Z)`?

- Obstruction lead, recalled: Canary–Tsouvalas, *Topological restrictions on
  Anosov representations*. A projective Anosov subgroup of `SL_3(R)` is
  virtually free or virtually a surface group. So any embedding of such a
  group must fail to be Anosov: no uniform singular-value gap, or not a
  quasi-isometric embedding.
- Thin subgroups containing unipotent elements are the natural non-Anosov
  source. Relatively Anosov restrictions in `SL_3(R)` are to be checked.
- Known thin subgroups of `SL_3(Z)`: free groups; Zariski-dense surface groups
  (Long–Reid–Thistlethwaite, images of triangle groups; recalled). Neither has
  `chi > 0`.

### 4.4 Free-by-free groups F_n x| F_m, n, m >= 2: live, the main (C1) candidates

They have cd 2 and `chi = (n-1)(m-1) > 0`. Fibrations with finitely generated
kernel exist for many free-by-free groups (Kropholler–Walsh, recalled).

Inside `SL_3(Z)`:

- `F_n` is Zariski dense, and `F_m` acts through the stabilizer in `Out(F_n)`
  of the character `[rho]` of the inclusion. So `[rho]` is an integral point of
  the `SL_3` character variety of `F_n` with a non-abelian free stabilizer.
- In rank one (`PSL_2(C)`) this is impossible: a finitely generated normal
  subgroup of infinite index in a Kleinian group has virtually cyclic quotient
  (tameness and fibration theorems, recalled). For `SL_3` no analogue is known.
- Test first: do `Out(F_2) = GL_2(Z)`-stabilizers of Zariski-dense, discrete,
  faithful, integral characters in `X(F_2, SL_3)` contain free groups? This
  can be probed on small integral characters, with bounded MSI search allowed
  by RULES §5.

### 4.5 Amalgams of finitely presented subgroups along infinitely generated intersections: live, no candidate yet

If `B_0, B_1 <= SL_3(Z)` are finitely presented and generate `B_0 *_C B_1`
with `C` not finitely generated, then that subgroup is finitely generated and
not finitely presented. Intersections inside parabolic subgroups are finitely
generated: GL_2(Z) is virtually free, and free groups have the Howson
property. So `C` must be thin. Combination theorems for thin subgroups of
`SL_3` would be needed.

## 5. Sharpest next targets

1. Verify Tits' `E(m)` finite-index theorem from the source and land the
   citation route; that establishes `sl3z-dense-with-unipotent-lattice-has-finite-index`.
2. Decide whether one-ended hyperbolic groups of cd 2 with `chi > 0` admit
   discrete faithful representations into `SL_3(R)`, first at all, then with
   integral image. A general "no" would push (C2) to non-hyperbolic RFRS
   groups (4.2).
3. Decide whether thin free-by-cyclic subgroups `F_n x| Z` of `SL_3(Z)` with
   finitely generated fibre exist at all. That is a prerequisite for 4.4 and
   is interesting in its own right.
