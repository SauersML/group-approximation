# STW LXXXVII: minimal boundary dimension-collapse audit (2026-08-30)

## Result

Let `G` be any infinite finitely generated virtually nilpotent group.  Every
free minimal action of `G` on a nonempty compact zero-dimensional Hausdorff
space `K`, without a metrizability assumption, satisfies

```text
dim_nuc(C(K) crossed_product_r G)<=1.
```

If `G` has infinite abelianization, the value is exactly one.

The new ingredient is the nonmetrizable reduction.  Every finite crossed-
product packet is placed, up to arbitrary error, in a metrizable factor which
remains zero-dimensional, free and minimal.  Freeness is retained by adjoining
a countable family of clopen displacement witnesses.  The virtually
nilpotent extension in Szabo--Wu--Zacharias, Theorem 8.8, gives finite nuclear
dimension to each separable factor crossed product; simplicity collapses each
such bound to at most one.  Injectivity of finite-dimensional operator systems
extends the incoming c.p.c. maps to the original algebra, giving the same one-
colour bound there.  When the finitely generated abelianization is infinite,
it has a quotient onto `Z`, and the resulting Pimsner--Voiculescu index of a
canonical implementing unitary is the nonzero unit class, excluding zero.

The inclusion is strict: `G=Z direct_product S_3` has cyclic subgroup
`Z direct_product {e}` of finite index, and its abelianization is infinite, but
`G` is not nilpotent because its quotient `S_3` is not nilpotent.  This is not
merely a group-theoretic enlargement.  If `T` is a free minimal Cantor
`Z`-system, the action

```text
(n,s)(y,t)=(T^n(y),st)
```

on `Y direct_product S_3` is free and minimal, so the exact dimension-one
conclusion supplies concrete crossed products absent from the nilpotent
theorem.

## Application to the uniform Roe frontier

Every minimal closed invariant subset `M` of `beta G` is contained in the
boundary, is zero-dimensional, and carries a free action.  Therefore

```text
C*_u(G) ->> C(M) crossed_product_r G
```

is a canonical quotient of nuclear dimension at most one, and exactly one
when `G_ab` is infinite.  It annihilates
`c_0(G) crossed_product_r G=K(ell^2(G))`, hence is already a quotient of the
uniform Roe corona.  Consequently, whenever `asdim(G)>=2`, the minimal
quotient has forgotten the higher dimension that LXXXVII asks ordinary
nuclear dimension to detect, whether or not the lower-bound hypothesis is
available.  This is an exact firewall for the tempting strategy "pass to a
minimal boundary quotient and read off dimension there."  It does not compute
`dim_nuc(C*_u(G))`, and it does not exclude a different, nonminimal quotient
having larger nuclear dimension.

## Imported established inputs

1. Szabo--Wu--Zacharias, [*Rokhlin dimension for actions of residually finite
   groups*, Theorem 8.8](https://arxiv.org/abs/1408.6096), record Bartels'
   virtually nilpotent extension: free minimal actions of infinite finitely
   generated virtually nilpotent groups on finite-dimensional compact
   metrizable spaces have simple ASH crossed products of topological dimension
   at most two.
2. Winter, [*Nuclear dimension and Z-stability of pure C*-algebras*](https://arxiv.org/abs/1006.2731),
   proves finite nuclear dimension implies `Z`-stability for simple separable
   nonelementary unital algebras.
3. Castillejos--Evington--Tikuisis--White--Winter, [*Nuclear dimension of
   simple C*-algebras*](https://arxiv.org/abs/1901.05853), prove nuclear
   dimension at most one for the simple separable unital nuclear `Z`-stable
   class.  This is applied only to the metrizable factor crossed products.

Everything else in the route—the clopen freeness witnesses, preservation of
minimality, extension of the incoming c.p.c. maps, the epimorphism furnished by
infinite finitely generated abelianization, the PV `K_1` obstruction, and the
Stone--Cech quotient application—is written out directly.

## Scope discipline

This is a theorem about canonical quotients of the uniform Roe algebra, not a
new equality case for `C*_u(Z^d)` itself.  Quotient monotonicity yields only the
already-known positive lower bound one when the PV hypothesis applies, and no
positive lower bound in the remaining virtually nilpotent cases.  In
particular, no claim is made that Problem LXXXVII is solved for any finite
asymptotic dimension at least two.
