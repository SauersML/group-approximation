# Radu's BMW lattice: amalgam splittings, the edge-group filter, and finite-subgroup defects

Lane `w4-radu-f2`, 2026-09-12. Handwritten proofs, nothing run. Supports
`radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups`,
`nonsofic-subgroups-of-radu-lattice-have-nonamenable-edge-groups`,
`radu-lattice-defect-idempotents-avoid-finite-subgroups`, and the Attempts of
`radu-bmw-lattice-group-algebra-not-stably-finite`.

## 0. Setup

Conventions and the host follow `radu-lattice-strict-automaton-screens-2026-09-12.md`:

    Gamma_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>,

acting simply transitively on the vertices of `X = T_h x T_v`. `A = <a,b,c>` and `V = <x,y,z>` are both
`C_2 * C_2 * C_2`. The vertical tree is `T_v = Gamma_R / A` (vertices: reduced words in `x,y,z`; root
stabilizer `A`), and the horizontal tree is `T_h = Gamma_R / V` (root stabilizer `V`).

Relations used below, each read off one relator:

    xa = ax,  ya = ay,  xb = bx,  yb = cy,  yc = by,
    za = bz,  zb = az,  cx = zc,  xc = cz,  zc = cx,  cy = yb,  by = yc,  az = zb,  bz = za.

## 1. Two amalgam splittings

**First-level actions.**
* `A` on the neighbours `xA, yA, zA` of the root of `T_v`: `a` and `b` fix all three (`ax = xa`,
  `az = zb`, `bx = xb`, `bz = za`), and every letter fixes `yA` (`ay = ya`, `by = yc`, `cy = yb`). The
  letter `c` swaps `xA` and `zA` (`cx = zc`, `cz = xc`). So `A -> Sym{x,y,z}` is `c -> (x z)`, `a, b -> id`.
* `V` on the neighbours `aV, bV, cV` of the root of `T_h`: `x -> id` (`xa = ax`, `xb = bx`, `xc = cz`),
  `y -> (b c)` (`ya = ay`, `yb = cy`, `yc = by`), `z -> (a b)` (`za = bz`, `zb = az`, `zc = cx`). The
  image is `S_3`. This agrees with `radu-horizontal-projection-kills-delta-squared`: `y` substitutes
  `b <-> c`, `z` swaps `a <-> b` in the even `c`-blocks, `x` in the odd ones, and the first letter of a
  word sits in block zero.

**Subgroups.**
* `A_ev = ker(A -> C_2)`, where `c -> 1` and `a, b -> 0`. It is `<a, b, cac, cbc>`, and by Kurosh it is
  `C_2 * C_2 * C_2 * C_2`, with Euler characteristic `-1`.
* `P_y = <A, y> = A ⋊ <y>`, where `y` fixes `a` and swaps `b <-> c` (screens, Theorem 6).
* `E_x = <A_ev, x> = A_ev ⋊ <x>`, where `x` fixes `a` and `b` and swaps `cac <-> cbc`:
  `x(cac)x = (xc) a (cx) = cz a zc = c(zaz)c = cbc`.
* `V_a` is the preimage of `{id, (b c)}` under `V -> S_3`. It has index three in `V`. Kurosh gives
  `V_a = C_2^(*5)`: `x` has three fixed cosets and `y`, `z` one each, and the Euler characteristic
  `-3/2` leaves no free part.
* `E_a = <V_a, a> = V_a ⋊ <a>`.

`x` normalizes `A_ev`: for `h` in `A_ev`, `h.xA = xA` gives `hx = xh'` with `h'` in `A`, so `xhx = h'`,
and `h'.xA = xhxxA = xhA = xA` puts `h'` in `A_ev`. The same argument shows `a` normalizes `V_a`.

**Theorem A.**
1. `Gamma_R = P_y *_(A_ev) E_x`, with `A_ev <= A <= P_y` of index four and `A_ev <= E_x` of index two.
2. `Gamma_R = V *_(V_a) E_a`, with indices three and two.

*Proof of 1.* `Gamma_R` acts on `T_v` transitively on vertices, and the root stabilizer is `A`. The
edges at the root go to `xA`, `yA`, `zA`. The `A`-orbits on them are `{yA}` and `{xA, zA}`, so there
are two edge orbits.
* `y` inverts `{A, yA}`. Its setwise stabilizer is `A_y ∪ y A_y`, where `A_y = A` because every letter
  of `A` fixes `yA`. So it is `P_y`.
* `x` inverts `{A, xA}`. Its setwise stabilizer is `A_x ∪ x A_x`, where `A_x = A_ev` because the
  first-level action is the parity of `c`. So it is `E_x`.

Subdivide the inverted edges. The subdivided tree has three vertex orbits: vertices, `y`-midpoints
and `x`-midpoints. It has two half-edge orbits, with stabilizers `A ∩ P_y = A` and `A ∩ E_x = A_ev`.
The quotient graph is the segment `[m_y] -- [o] -- [m_x]`, so it is a tree. It lifts to the path
from the midpoint of `{A, yA}` through `A` to the midpoint of `{A, xA}`. The Bass–Serre structure
theorem gives `Gamma_R = P_y *_A A *_(A_ev) E_x = P_y *_(A_ev) E_x`.

*Proof of 2.* On `T_h` the root stabilizer is `V`. `V` acts transitively on the edges at the root,
because the image is `S_3`, so there is one edge orbit. `a` inverts `{V, aV}`, whose setwise
stabilizer is `V_a ∪ a V_a = E_a`. The quotient of the subdivided tree is `[o] -- [m_a]`, so
`Gamma_R = V *_(V_a) E_a`. QED

**Euler characteristic check.**
* From 1: `chi(P_y) + chi(E_x) - chi(A_ev) = -1/4 - 1/2 + 1 = 1/4`.
* From 2: `chi(V) + chi(E_a) - chi(V_a) = -1/2 - 3/4 + 3/2 = 1/4`.
* From the complex: one free vertex orbit, six edge orbits (the letters) with stabilizer `C_2`, and
  nine squares per vertex, each with four vertices, acting freely on vertices. That gives
  `1 - 6/2 + 9/4 = 1/4`.

**Corollary A′ (algebras).** For every commutative ring `k`,

    k[Gamma_R] = k[P_y] *_(k[A_ev]) k[E_x] = k[V] *_(k[V_a]) k[E_a]

as amalgamated coproducts of `k`-algebras. The group-algebra functor is left adjoint to the unit-group
functor, so it carries the pushout of groups to the pushout of algebras. Each factor is free over the
base on both sides, on coset representatives.

**Reading.**
* Both factors in each splitting are virtually free, and so is the base. The lattice is not
  residually finite because the finite quotients of the two factors cannot be matched on the base:
  `(xz)^4` lies in the finite residual.
* The screens' letter subgroups are the vertex groups here: `P_y` is a midpoint stabilizer, and
  `P_xz = <A, x> ⊇ E_x`.
* The torsion-free case of this picture is Section 9 of `vh-lattice-table-hosts-2026-09-12.md`.
  Here the splittings are explicit.
* In characteristic two the base `F_2[A_ev]` is not semisimple: it contains `F_2[C_2] = F_2[t]/(t^2)`.
  The coproduct K-theory that works over semisimple bases, Bergman's coproduct theorems, which
  I have not re-read, gives no information over this base.

## 2. The edge-group filter

**Theorem B.** Let `S <= Gamma_R` be finitely generated and not sofic.
1. *Vertical.* `S` fixes no vertex, no edge midpoint and no end of `T_v`. In the finite graph of groups of
   `S` on its minimal subtree of the subdivided `T_v`, some edge group contains a nonabelian free group.
   Each such edge group has the form `S ∩ gAg^(-1)` or `S ∩ gA_ev g^(-1)`.
2. *Horizontal.* The same holds on `T_h`, with edge groups `S ∩ g V_a g^(-1)`.

In particular `S ∩ gAg^(-1)` and `S ∩ hVh^(-1)` contain nonabelian free groups for some `g` and `h`.

*Inputs.*
* **Locality.** A group is sofic iff its finitely generated subgroups are, directly from the definition.
* **Virtually free pieces.** Subgroups of virtually free groups are locally virtually free, hence sofic.
  Such a subgroup is amenable iff it contains no nonabelian free group: its finitely generated subgroups
  are virtually free, and a union of virtually cyclic groups is amenable.
* **Amenable quotients:** `sofic-kernel-amenable-quotient-permanence`.
* **Combination theorem.** The fundamental group of a finite graph of groups with sofic vertex groups and
  amenable edge groups is sofic. Amalgams are Elek–Szabó, and HNN extensions and graphs of groups are
  Ciobanu–Holt–Rees, as cited in `amenable-envelope-magnus-piece-sofic-proof`. This lane did not re-read
  the sources.
* **Tree facts.**
  * A finitely generated group acting on a tree with every element elliptic fixes a vertex (Serre, *Trees*).
  * A finitely generated group acting minimally without inversions on a tree has a finite quotient graph
    (Bass–Serre).

*Proof of 1.* Subdivide the inverted edges of `T_v`, so that `S` acts without inversions.
* **Stabilizers.** Vertex stabilizers are `S` intersected with conjugates of `A`, `P_y` or `E_x`, all of
  them sofic. Half-edge stabilizers are `S` intersected with conjugates of `A` or `A_ev` (Theorem A).
* **Every element elliptic.** Then `S` fixes a vertex and lies in a vertex group, so it is sofic.
* **A hyperbolic element and a fixed end `omega`.**
  * The Busemann homomorphism `beta : S -> Z` has kernel `K` consisting of elliptic elements, each fixing
    a ray to `omega`.
  * Finitely many rays to `omega` share a subray, so each finitely generated subgroup of `K` fixes a
    vertex. So `K` is locally virtually free, hence sofic.
  * `S/K <= Z` is amenable, so `S` is sofic.
* **A hyperbolic element and no fixed end.**
  * The union of the axes is the unique minimal invariant subtree, with finite quotient graph.
  * Bass–Serre theory writes `S` as a finite graph of groups with sofic vertex groups and the half-edge
    stabilizers as edge groups.
  * If every edge group were amenable, the combination theorem would make `S` sofic.
  * So some edge group is nonamenable, hence contains a nonabelian free group.

*Proof of 2.* The same argument on `T_h`, with vertex groups inside conjugates of `V` and `E_a`, and
half-edge groups inside conjugates of `V_a`.

The final sentence follows because `A_ev <= A` and `V_a <= V`. QED

**It recovers the letter screen.** Theorem 6 of the screens artifact follows:
* `P_y ∩ V = <y>`, so `P_y` has finite vertex groups on `T_h`;
* `P_xz ∩ V = <x, z> ≅ D_infinity`, so `P_xz` has amenable vertex groups on `T_h`;
* in both cases part 2 fails, so both subgroups are sofic.

The vertical filter alone does not exclude `P_xz`: it preserves the `x/z` line of `T_v`, with edge
groups conjugate to `A_ev`.

**Consequences.**
* **Linear target** (`radu-bmw-lattice-group-algebra-not-stably-finite`). Suppose `B A = I_n != A B`
  over `M_n(F_p[Gamma_R])`. The entries' supports then generate a finitely generated nonsofic `S`, by
  the screens' support filter, so Theorem B applies to `S`.
* **Nonlinear target** (`radu-bmw-lattice-nonsurjunctive`). In any factorization of a strict automaton, a
  strict factor has memory generating such an `S`. This uses screens Lemmas 2 and 3 and
  `sofic-groups-are-surjunctive`.
* **What the filter demands.** A witness must contain free subgroups inside a conjugate of `A` and inside
  a conjugate of `V`. It must also split over a nonamenable edge group in both tree directions, where
  the two embeddings of the base disagree.
* **Scope.** Nothing here is specific to `Gamma_R` beyond virtually free stabilizers. The same filter
  holds for any group acting on a tree with virtually free vertex stabilizers.
