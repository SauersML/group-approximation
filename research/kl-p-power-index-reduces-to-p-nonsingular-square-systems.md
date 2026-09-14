---
rg: 2
id: kl-p-power-index-reduces-to-p-nonsingular-square-systems
kind: claim
title: Over a group with a normal subgroup of p-power index, an equation of degree prime to p injects iff one p-nonsingular square system over that subgroup is solvable
distinct_from:
  kl-cyclic-orbit-perfect-kernel: that passes to the kernel of the degree map onto C_m over a simple coefficient group, with m orbit relators and one variable; this passes to the kernel of a finite p-group quotient of the coefficients, with |Q| relators and |Q| variables whose exponent matrix is invertible mod p.
  krstic-p-nonsingular-equations-inject-locally-p-indicable-groups: that solves such systems when the coefficient group is locally p-indicable; this reduces an arbitrary torsion-free-by-p-group coefficient group to its normal subgroup, where no systems theorem is available unless that subgroup is locally p-indicable.
  klyachko-kl-holds-when-all-coefficients-have-infinite-order: that handles one unimodular equation whose coefficients have infinite order; the reduction here produces several equations at once, which that theorem does not cover.
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

Let `p` be a prime, `H <| G` with `Q = G/H` a finite `p`-group, `n = |Q|`, and
`w = s_1 ... s_k in G * <t>` a word with letters in `G ∪ {t, t^(-1)}` and
`m = deg_t(w)` not divisible by `p`.

1. **A root in `Q`.** There is `c in Q` with `w-(c) = 1`. Here `w-` reduces the
   coefficients mod `H` and substitutes `t = c`.
2. **Schreier basis.** Put `phi : G * <t> -> Q`, `g -> gH`, `t -> c`, and
   `M = ker phi`. Choose `g_q in G` with `g_q H = q` and `g_1 = 1`, and put
   `y_q = g_q t g_(qc)^(-1)`. Then `M` is the free product
   `H * F(y_q : q in Q)`.
3. **The square system.** `<<w>>` in `G * <t>` equals the normal closure in `M`
   of the rewritten conjugates `rho_q` of `g_q w g_q^(-1)`, `q in Q`. The
   `n x n` exponent-sum matrix of `rho_q` in the unknowns `y_q'` is

       E(q, q') = alpha(q^(-1) q'),
       alpha = sum_(s_j = t) phi(s_1...s_(j-1)) - sum_(s_j = t^(-1)) phi(s_1...s_j)  in Z[Q],

   the matrix of right multiplication by `alpha`, the image of the Fox
   derivative `dw/dt`. It is invertible mod `p`, so the system
   `{rho_q = 1}` is `p`-nonsingular.
4. **Equivalence.** `G -> (G * <t>)/<<w>>` is injective iff the square
   `p`-nonsingular system `{rho_q = 1}` in `n` unknowns over `H` is solvable
   over `H`.

## What it settles, and what it does not

This is the induction route for Kervaire--Laudenbach over torsion-free-by-finite
coefficient groups, carried out exactly when the finite quotient is a
`p`-group:
- the coefficient kernel lies in `H`;
- the obstruction is a single square system over `H` whose matrix is invertible
  mod `p`.

**The failing step.** Solving such a system over a torsion-free `H` is an
instance of Howie's conjecture, "neither proved nor disproved"
(arXiv:2309.09096 l.228--232, pinned in the artifact).
- Klyachko's theorem handles one equation at a time, and his 2006 multivariable
  corollary is still one equation.
- The theorems that do solve systems need local indicability (Howie) or local
  `p`-indicability (Krstic).
- Under local `p`-indicability of `H` the conclusion is not new: `G` is then
  itself locally `p`-indicable, see
  `krstic-p-nonsingular-equations-inject-locally-p-indicable-groups`.

So the route turns KL for "torsion-free by finite `p`-group" into Howie's
conjecture for torsion-free groups with invertible-mod-`p` exponent matrices,
and stops there.

**When the quotient is not a `p`-group.** A root may not exist in `Q`.
- After enlarging `Q` to a finite overgroup containing a root, the vertex count
  of the cover grows.
- The system acquires more relators than unknowns, with extra copies of `H` as
  coefficients.
- `alpha` need not be a unit in any `F_p[Q]`.

**ESTABLISHED** through `kl-p-power-index-p-nonsingular-proof`, an elementary
proof with no imports. Not independently reviewed; no novelty claimed.
