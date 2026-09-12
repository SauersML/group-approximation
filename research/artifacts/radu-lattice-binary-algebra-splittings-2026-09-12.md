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
