# STW LXXXVII: minimal boundary dimension-collapse audit (2026-08-30)

## Result

For every infinite finitely generated nilpotent group `G`, a free minimal
action of `G` on a nonempty compact zero-dimensional Hausdorff space `K`,
without a metrizability assumption, satisfies

```text
dim_nuc(C(K) crossed_product_r G)=1.
```

The new ingredient is the nonmetrizable reduction.  Every finite crossed-
product packet is placed, up to arbitrary error, in a metrizable factor which
remains zero-dimensional, free and minimal.  Freeness is retained by adjoining
a countable family of clopen displacement witnesses.  Szabo--Wu--Zacharias
give finite nuclear dimension to each separable factor crossed product;
simplicity collapses each such bound to at most one.  Injectivity of finite-
dimensional operator systems extends the incoming c.p.c. maps to the original
algebra, giving the same one-colour bound there.  Every infinite finitely
generated nilpotent group maps onto `Z`, and the resulting Pimsner--Voiculescu
index of a canonical implementing unitary is the nonzero unit class, excluding
zero.

## Application to the uniform Roe frontier

Every minimal closed invariant subset `M` of `beta G` is contained in the
boundary, is zero-dimensional, and carries a free action.  Therefore

```text
C*_u(G) ->> C(M) crossed_product_r G
```

is a canonical quotient of nuclear dimension exactly one.  It annihilates
`c_0(G) crossed_product_r G=K(ell^2(G))`, hence is already a quotient of the
uniform Roe corona.  For `G=Z^d`, `d>=2`, the minimal quotient has forgotten
the higher rank that LXXXVII asks ordinary nuclear dimension to detect.  This
is an exact firewall for the tempting strategy "pass to a minimal boundary
quotient and read off dimension there."  It does not compute
`dim_nuc(C*_u(G))`, and it does not exclude a different, nonminimal quotient
having larger nuclear dimension.

## Imported established inputs

1. Szabo--Wu--Zacharias, [*Rokhlin dimension for actions of residually finite
   groups*](https://arxiv.org/abs/1408.6096), give finite nuclear dimension for
   crossed products of free actions of infinite finitely generated nilpotent
   groups on finite-dimensional compact metrizable spaces.
2. Winter, [*Nuclear dimension and Z-stability of pure C*-algebras*](https://arxiv.org/abs/1006.2731),
   proves finite nuclear dimension implies `Z`-stability for simple separable
   nonelementary unital algebras.
3. Castillejos--Evington--Tikuisis--White--Winter, [*Nuclear dimension of
   simple C*-algebras*](https://arxiv.org/abs/1901.05853), prove nuclear
   dimension at most one for the simple separable unital nuclear `Z`-stable
   class.  This is applied only to the metrizable factor crossed products.

Everything else in the route—the clopen freeness witnesses, preservation of
minimality, extension of the incoming c.p.c. maps, the nilpotent epimorphism to
`Z`, the PV `K_1` obstruction, and the Stone--Cech quotient application—is
written out directly.

## Scope discipline

This is a theorem about canonical quotients of the uniform Roe algebra, not a
new equality case for `C*_u(Z^d)` itself.  Quotient monotonicity yields only the
already-known positive lower bound one.  In particular, no claim is made that
Problem LXXXVII is solved for any finite asymptotic dimension at least two.
