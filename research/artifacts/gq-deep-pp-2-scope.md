# Piecewise-projective hosts for GL_n(Q): what survives (lane gq-deep-pp-2, 2026-09-17)

Target: `gl-n-q-embeds-in-fp-simple-group`. This note scopes family C (piecewise-projective and related
one-dimensional hosts) after the landed obstructions. Lane-proved statements are marked; none is refereed.

## 1. The obstructions and what each kills

| Obstruction | Kills | Leaves |
|---|---|---|
| O1 (root) | every residually finite intermediate group | non-RF hosts |
| `germ-extensions-omit-standard-gl-n-q` (4a58a2b5b) | standard (analytic) copies in piecewise-projective/affine groups over R, Q_p or the finite adeles, and in all their finite germ extensions, any dimension | nonstandard copies |
| O4 (root, 2688d4128) | VA and all its subgroups (V, T-bar, Brin's A), for n >= 2 | hosts with distorted cyclic subgroups |
| `gl-n-q-hosts-cannot-act-on-one-manifolds` (this lane) | every copy, standard or not, in groups acting faithfully on a one-manifold with finitely many components, for n >= 3; line and interval groups also for n = 2 | circle groups for n = 2; Cantor-set and higher-dimensional hosts |

The last row uses Witte (Proc. AMS 122 (1994) 333–340): finite-index subgroups of SL(n,Z), n >= 3, act on
the circle only through finite groups. It is the only obstruction here that sees nonstandard copies. It
removes F, T, T-bar, Stein's F_{2,3} and T_{2,3}, the Lodha–Moore groups, Monod's H(A), PL and
piecewise-projective circle groups, and Homeo(S^1) as hosts for n >= 3, however GL_n(Q) sits inside them.
(Brin realized Aut(F) as a group of homeomorphisms of (0,1), IHES 1996; if that realization is faithful, as
stated there, Aut(F) is excluded too. Not re-checked here. Lane `gq-lit-q-embeddings`, 1d1ec4d78, excludes
Aff(Q) and GL_2(Q) from Aut(F) by other means.)

## 2. What survives in family C

1. **n = 2 on the circle.** SL_2(Q) acts faithfully on the circle of rays in R^2, so circle groups are not
   excluded for n = 2. A host must hold a nonstandard copy (germ node), must not lie in VA (O4), and must
   contain torsion of orders 3, 4, 6 (from SL_2(Z)) and distorted cyclic subgroups (BS(1,2)).
   *Spark (not pursued):* SL_2(Z[1/p]) is an irreducible lattice in SL_2(R) x SL_2(Q_p). Circle-rigidity
   theorems for such lattices (Burger–Monod bounded cohomology; Bader–Furman–Shaker) should force every
   faithful circle action to be semiconjugate to the standard one through the SL_2(R) factor. Precise
   statement and hypotheses not checked. Even so, semiconjugacy does not preserve piecewise-projective
   structure (Minkowski's ? conjugates PPSL_2(Z) to the dyadic PL group T), so no contradiction follows
   directly.
2. **n >= 3: only Cantor-set or higher-dimensional hosts.** In family C that means RP^{n-1} or spheres
   (lane `gq-pp-higher`) and p-adic or adelic projective spaces. In all of them the standard copy is dead,
   so a nonstandard mechanism for divisibility is required.
3. **p-adic projective lines (my variant).** For a dense finitely generated subring R of Q_p (for example
   Z[1/p]), let G_p(R) be the homeomorphisms of the Cantor set P^1(Q_p) that are piecewise in PGL_2(R) on
   finite clopen partitions.
   - It contains PGL_2(R), so BS(1,p) and distortion (O4 is no obstacle). It contains the p-adic odometer
     o = (x -> x+1 on Z_p, identity off Z_p), which V does not contain.
   - *Lemma (lane-proved).* In G_p(Z[1/p]) the odometer o has no root of order k > 1.
     Proof: let h^k = o. Then h commutes with o, so h preserves supp(o) = Z_p. On Z_p, commuting with
     x -> x+1 gives h(x+m) = h(x)+m for all integers m, so h(x) = x + h(0) by density of Z in Z_p and
     continuity. So h is translation by c on Z_p with kc = 1. If p | k this has no solution in Z_p. If not,
     c = 1/k, and h agrees with x -> x + 1/k on the open set Z_p. So that Möbius map is a piece of h, but
     1/k is not in Z[1/p]. Contradiction.
   - Moral: in hosts that are everywhere locally in a quasi-analytic group with finitely generated piece
     group, roots of minimal equicontinuous pieces are forced to be standard, so equicontinuous (odometer)
     dynamics does not supply divisibility either. A p-adic host would need singular points (a finite germ
     extension of G_p(R)) whose germ groups carry a nonstandard Q; by the germ node those germs cannot be
     analytic.

## 3. Net state for family C

No surviving shape has a candidate mechanism for divisibility. The two known nonstandard mechanisms are
T-bar's rotation-number lifts and Kojima–Sheng's Q <= nV (arXiv:2603.18410v3). T-bar is one-dimensional,
so it is dead for n >= 3 by Witte and dead inside VA for n >= 2 by O4. Kojima–Sheng is a Cantor-set
construction and is not piecewise-projective. The live directions for G are therefore outside dimension
one: nV (distortion unsettled), germ extensions with exotic non-analytic germs, and type (A) actions.

## 4. Needs (for other lanes)

- A nonstandard source of divisibility inside a Cantor-set or higher-dimensional piecewise-projective group
  containing SL_3(Z).
- For n = 2: whether some finitely generated circle group outside VA contains Q with distortion and torsion
  of order 3 (T_{2,3}-type groups?).
