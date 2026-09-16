---
rg: 2
id: rordam-line-bundle-sums-are-k-theoretically-rigid-proof
kind: route
title: Expand line-bundle classes in the Bott basis and invert on the Boolean lattice
target: rordam-line-bundle-sums-are-k-theoretically-rigid
requires: []
---

Standard inputs, used only in their textbook form: (a) `K^0(S^2)` is free
with basis `1, b`, where `b=[H]-1` and `b^2=0`; (b) the fundamental product
theorem (Bott periodicity): for compact Hausdorff `X` the external product
`K^0(X) tensor K^0(S^2) -> K^0(X x S^2)` is a ring isomorphism; (c) Swan's
correspondence `K_0(C(X))=K^0(X)` and stability `K_0(C(X) tensor K)=K_0(C(X))`,
under which tensor products of bundles multiply classes; (d) projections
at distance less than one half are unitarily equivalent.

**Step 1 (finite `F`, basis).**  Induction on `|F|` with (a) and (b) gives

```text
K^0(Z_F) = Z[b_i : i in F]/(b_i^2),
```

a free abelian group with basis the monomials `b_S`, `S subset F`.

**Step 2 (expansion).**  Since `[zeta_i]=1+b_i` and tensor products
multiply classes,

```text
[zeta_J] = prod_(i in J)(1+b_i) = sum_(S subset J) b_S,
[zeta(m)] = sum_J m(J) sum_(S subset J) b_S = sum_S N_m(S) b_S.
```

`N_m(S)` is zero unless `S` is contained in a member of the finite support
of `m`, so all sums are finite.

**Step 3 (Boolean Mobius inversion).**  For every finite `T`,

```text
sum_(S contains T) (-1)^|S\T| N_m(S)
  = sum_(J contains T) m(J) sum_(T subset S subset J) (-1)^|S\T|
  = sum_(J contains T) m(J) (1-1)^|J\T|  = m(T).
```

So `m` is an integer linear combination of the coefficients `N_m`.

**Step 4 (rigidity and divisibility, finite `F`).**  If
`[zeta(m)]=[zeta(m')]`, independence of the `b_S` gives `N_m=N_(m')` and
Step 3 gives `m=m'`.  If `d y=[zeta(m)]`, write `y=sum_S c_S b_S` using the
basis; then `d c_S=N_m(S)` for all `S`, so `d` divides every `N_m(S)` and,
by Step 3, every `m(T)`.  Then `d(y-[zeta(m/d)])=0`, and torsion-freeness
gives `y=[zeta(m/d)]`.  The converse directions are immediate.

**Step 5 (countable `F`).**  Enumerate `F` and let `F_n` be its first `n`
elements, with coordinate projection `pi_n : Z_F -> Z_(F_n)`.  Inserting a
fixed base point in the remaining coordinates gives a section `s_n` with
`pi_n s_n = id`, so `s_n^* pi_n^* = id` and `pi_n^*` is injective on `K^0`.
It carries `zeta_i` to `zeta_i`, hence `b_S` to `b_S`.  The pulled-back
algebras `pi_n^* C(Z_(F_n))` increase and their union is dense in `C(Z_F)`
(Stone-Weierstrass).  Consequently every projection in a matrix algebra over
`C(Z_F)` is within one half of a projection pulled back from some stage (by
functional calculus on a nearby self-adjoint element), so by (d) every
`y in K^0(Z_F)` equals `pi_n^* y_n` for some `n` and `y_n`.  Given finitely
many classes and a relation among them in `K^0(Z_F)`, choose `n` so large
that all of them, and the supports of `m`, `m'`, come from stage `n`;
injectivity of `pi_n^*` transports the relation to `K^0(Z_(F_n))`, where
Step 4 applies.  Linear independence and spanning of the `b_S` pass to the
union in the same way.

**Step 6 (the displayed consequences).**  Murray-von Neumann equivalence
and stable equivalence both imply equality of `K_0` classes, and equal
multisets give isomorphic range bundles, hence Murray-von Neumann equivalent
projections, which proves item 2.  If the direct sum of `2^n` copies of `e`
is equivalent to `p(m)` then `2^n[e]=[p(m)]`; if `2^n[e]=[p(m)]` then item 3 with
`d=2^n` gives `2^n | m(J)` for all `J` and `[e]=[p(m/2^n)]`.  A nonzero
multiplicity-free `m` has an odd multiplicity, so `[p(m)]` is not in
`2K_0`.  This proves the claim.
