---
rg: 2
id: fpbs-kazhdan-twisted-lift-independence
kind: claim
title: Twisted Lackenby lifting produces weight-free equivariant classes, controlled by a bilinear commutator form
distinct_from:
  fpbs-kazhdan-twisted-certificates-vanishing-weight: that transfers a crown count to d_p of the kernel K_M and loses the Plancherel weight; this lifts twisted classes over the small complex of Gamma_n and proves the missing independence lemma with a loss x0*v0 that does not see the weight, leaving only the descent step open.
  fpbs-kazhdan-positive-rank-gradient: that asks for linear d(Gamma_n); this is one lifting step toward showing that abelian-crown certificates of every weight contradict (T) on Frattini closed families, and it isolates the single step (descent compatibility) still missing.
artifacts:
  - experiments/twisted-lackenby-lift-2026-09-17/twisted_lift.py
  - experiments/twisted-lackenby-lift-2026-09-17/independence_bound.py
  - experiments/twisted-lackenby-lift-2026-09-17/independence_results.txt
---

**ESTABLISHED (written deduction; one lifting step). The iteration built on it
is OPEN at one named step.** The deduction is checked numerically on free
groups and the genus-2 surface group. The bound is attained exactly in every
free-group case.

## Setting

- `Gamma_n` is a finitely presented group `<X|R>` with presentation complex of
  `r` 2-cells. In the application `Gamma_n` has index `N` in a Kazhdan group,
  and `r = |R|N`.
- `M` is an absolutely irreducible `F_p[Gamma_n]`-module of dimension `d`,
  with kernel `K` and `Q = Gamma_n/K`. For `e > 1`, extend scalars to
  `k = End M`.
- `C = (c_1..c_u)` are homomorphisms `Gamma_n -> F_p`.
- `Xi = (xi_1..xi_h)` are derivations `Gamma_n -> M`. On `K` the map `Xi` is a
  homomorphism into `M^h`.
- `A' = K cap ker Xi`, the kernel of `Gamma_n -> M^h x| Q`.
- For `a in F_p^(u x h)`, put `beta_a(x,y) = sum a_ij x_i y_j`, which maps
  `F_p^u x M^h -> M`. Let `Phi_a` be the path function of the cochain
  `Y_a(g,s) = sum a_ij c_i(s) xi_j(g)` on the cover of the presentation complex
  for `A'`. It satisfies
  - `Phi_a(uv) = Phi_a(u) + beta_a(Cv, Xi u) + u.Phi_a(v)`;
  - `Phi_a(g z g^-1) = g.Phi_a(z)` for `z` in `A'`.
- `Z` is the set of `a` for which `Y_a` is a cocycle. On `Z`, `Phi_a|A'` is a
  `Q`-equivariant homomorphism `A' -> M`.
- Two invariants:
  - `x0 = dim C(K cap ker Xi)`, the rank of the scalar classes on `A'`;
  - `v0 = dim V0`, where `Xi(K cap ker C) = M (x) V0` with `V0 <= F_p^h`.
    `Xi(K cap ker C)` is a `Q`-submodule of `M^h`, so it has this form.

## Statement

**Lemma (twisted independence).** The lifted cocycles span at least

`t >= x0*v0 - r*d`

independent `Q`-equivariant classes `A' -> M`. Equivalently, the crown count of
`M` on `A'` is at least `x0*v0/d - r`. Their `F_p`-coordinates span at least
`t*d` classes in `H^1(A';F_p)`.

**Consequence (weight-free lift).**
- Take `u` scalar classes that stay independent on `A'`, so `x0 = u`.
- Take `h` derivations whose restrictions to `K` are independent in
  `Hom_Q(K,M)`, so `Xi(K) = M^h` (step 2 of the weight-transfer proof). By the
  five-term sequence
  `0 -> H^1(Q;M) -> H^1(Gamma_n;M) -> Hom_Q(K,M) -> H^2(Q;M)`, the largest
  such `h` is at least `mu(Gamma_n;M) d - h^2(Q;M)` (here `e = 1`).
- `K cap ker C` has index at most `p^u` in `K`, so `Xi(K cap ker C)` has
  codimension at most `u` in `M^h`, and `v0 >= h - u/d >= h - u`.
- Then `mu(A';M) >= u(h-u)/d - r`. For a certificate with `mu(Gamma_n;M) >= cN`
  and `r = |R|N`, this gives
  `mu(A';M) >= N(cu - |R|) - u h^2(Q;M)/d - u^2/d`. The middle term is
  not controlled here; it is `O(u)` whenever `h^2(Q;M) = O(dim M)`, a bound
  this claim does not import.
- So `u = 2|R|/c` scalar classes suffice, whatever the Plancherel weight `w(M)`
  is. The scalar iteration on `K_M` instead needs `u >~ 2|R|/(c w)`
  (`fpbs-kazhdan-twisted-certificates-vanishing-weight`).
- This replaces the conditional "loss `O(t h)`" paragraph of that claim with a
  proved loss.

## Proof

1. **Codimension (twisted Lemma 5.7).** For each 2-cell of `K_(Gamma_n)`, its
   deck translates in the cover evaluate `Y_a` to `Q`-translates of one
   `M`-valued linear form in `a`. So `codim Z <= r d` and
   `dim Z >= uh - r d`.
2. **Quadratic identity on `K`.** For `x, y` in `K`, which act trivially on `M`,
   `Phi_a(xy) = Phi_a(x) + Phi_a(y) + beta_a(Cy, Xi x)`.
   - Hence `Phi_a(g^-1) = -Phi_a(g) + beta_a(Cg, Xi g)`.
   - If `z, w` in `K` have equal `C` and `Xi`, then
     `Phi_a(z w^-1) = Phi_a(z) - Phi_a(w)`.
   - With `z = xy` and `w = yx`:
     `Phi_a([x,y]) = beta_a(Cy, Xi x) - beta_a(Cx, Xi y)`.
   - `[x,y]` lies in `A'`, because `Xi` is a homomorphism on `K` into an abelian
     group.
3. **The kernel is small.** Suppose `a` is in `Z` and `Phi_a|A' = 0`.
   - Take `x` in `K cap ker Xi` and `y` in `K cap ker C`. Step 2 gives
     `beta_a(Cx, Xi y) = 0`.
   - So `x^T a v = 0` for all `x` in `X0 = C(K cap ker Xi)` and `v` in `V0`,
     since `beta_a(x, m (x) v) = (x^T a v) m` and `m` is arbitrary.
   - These are `x0*v0` independent linear conditions on `a`.
   - So the kernel of `a -> Phi_a|A'` on `Z` has dimension at most
     `uh - x0 v0`, and its image has dimension at least
     `(uh - r d) - (uh - x0 v0)`.
4. **Coordinates.** The image consists of equivariant homomorphisms into the
   irreducible `M`.
   - As in step 2 of the weight-transfer proof, `t` independent ones give a
     surjection `A'^ab (x) F_p -> M^t`.
   - So their coordinates span `t d` classes.

## Numerical check

Files: `experiments/twisted-lackenby-lift-2026-09-17/independence_bound.py` and
`independence_results.txt`. The module is `S_3` acting on `F_2^2`, `p = 2`,
`d = 2`. `x0` and `v0` are computed from Schreier generators; `t` is measured.

| case | r | x0 | v0 | bound `x0 v0 - r d` | measured `t` |
|---|---|---|---|---|---|
| `F_2`, both `U` | 0 | 1 | 2 | 2 | 2 |
| `F_2`, `U` = sign (inflated from `Q`) | 0 | 0 | 2 | 0 | 0 |
| `F_2`, `U = y` | 0 | 1 | 2 | 2 | 2 |
| `F_3` | 0 | 2 | 4 | 8 | 8 |
| genus 2, `h = 2` | 1 | 3 | 2 | 4 | 6 |
| genus 2, `U` = sign, `h = 2` | 1 | 0 | 2 | -2 | 1 |
| genus 2, `h = 3` | 1 | 3 | 3 | 7 | 8 |

The bound is exact for free groups. The sign character is inflated from `Q`,
so it dies on `A'` (`x0 = 0`); this explains the earlier zero.

## Where the iteration stops: descent compatibility

Lackenby's scheme iterates the lift. The next stage needs a member `N` of the
family inside `A'`, reached through the Sylow step of Theorem B, Step 2.4 in
`research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md`. By
pigeonhole over the composition factors of `Ind_N^(A'') M_N`, some irreducible
`M''` of the next good subgroup `A''` again carries a certificate.

The scalar classes of the next stage are the shrunk classes `W`. They must
satisfy `x0'' = rank(W on K'' cap ker Xi'') >= u - O(1)`.
- The kernel of the restriction is the inflation of `H^1(Q''; F_p)`, where
  `Q''` is the image of `A''` acting on `M''` and its derivations.
- That space has dimension at most `d_p(Q'')`, and nothing bounds it below the
  lifted count `~ |R|[Gamma:A'']`.
- For profinitely cofinal families, deep members lie inside `ker W`, so every
  class of `W` is inflated and `x0'' = 0`.

**Reduction (one direction).** Suppose that at every stage the member and the
module can be chosen with `x0'' >= u - O(1)`. Call this *descent
compatibility*. Then the twisted lift iterates with a weight-free loss, and
Corollary 3 of `fpbs-kazhdan-twisted-certificates-vanishing-weight` extends to
all Plancherel weights on `p`-Frattini closed kernel families. That kills every
abelian-crown certificate of that shape. The converse is not claimed.

The invariant to control is the gap `d_p(Q'') - x0''`, i.e. how much of the
`p`-abelianization of the finite quotient that carries the module is visible to
the scalar classes. The weight of `M''` plays no role.
