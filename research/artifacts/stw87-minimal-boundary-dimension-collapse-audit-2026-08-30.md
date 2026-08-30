# STW LXXXVII: minimal boundary dimension-collapse audit (2026-08-30)

## Result

Let `G` be any infinite finitely generated virtually nilpotent group.  Every
free minimal action of `G` on a nonempty compact zero-dimensional Hausdorff
space `K`, without a metrizability assumption, satisfies

```text
dim_nuc(C(K) crossed_product_r G)<=1.
```

If `G` has infinite abelianization, the value is exactly one.
The value is also exactly one for `G=D_infinity`, whose abelianization is
finite.  In fact every free zero-dimensional `D_infinity` crossed product is
non-AF: its `K_1` is nonzero or its `K_0` has nonzero two-torsion.

The new ingredient is the nonmetrizable reduction.  Every finite crossed-
product packet is placed, up to arbitrary error, in a metrizable factor which
remains zero-dimensional, free and minimal.  Freeness is retained by adjoining
a countable family of clopen displacement witnesses.  The virtually
nilpotent extension in Szabo--Wu--Zacharias, Theorem 8.8, gives finite nuclear
dimension to each separable factor crossed product; simplicity collapses each
such bound to at most one.  Injectivity of finite-dimensional operator systems
extends the incoming c.p.c. maps to the original algebra, giving the same
dimension-one (two-colour) bound there.  When the finitely generated
abelianization is infinite,
it has a quotient onto `Z`, and the resulting Pimsner--Voiculescu index of a
canonical implementing unitary is the nonzero unit class, excluding zero.

The finite-abelianization advance uses a different mechanism.  Write
`D_infinity=C_2 free_product C_2=<r,s>`.  Freeness provides clopen fundamental
domains for both involutions.  Natsume's free-product six-term exact sequence
then reduces the relevant K-groups to the kernel and cokernel of

```text
Phi:C(K,Z)->C(K/<r>,Z) direct_sum C(K/<s>,Z),
Phi(f)=(f+f after r,-f-f after s).
```

The cokernel class of `(1,-1)` is killed by two.  If it is nonzero, it is a
two-torsion obstruction to AF.  If it vanishes, choose `f` with both orbit
sums equal to one; then the nonzero odd-valued function `2f-1` lies in
`ker(Phi)=K_1`.  This parity dichotomy excludes nuclear dimension zero for
every free action, without a cyclic quotient or a transfer argument.

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
when `G_ab` is infinite or `G=D_infinity`.  It annihilates
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
4. Natsume, [*On K_*(C*(SL_2(Z)))*, Theorem
   A1](https://jot.theta.ro/jot/archive/1985-013-001/1985-013-001-007.pdf),
   supplies the six-term exact sequence for crossed products by amalgamated
   free products, used here only for `C_2 free_product C_2`.

Everything else in the route—the clopen freeness witnesses, preservation of
minimality, extension of the incoming c.p.c. maps, the epimorphism furnished by
infinite finitely generated abelianization, the PV `K_1` obstruction, and the
Stone--Cech quotient application—is written out directly.

## Scope discipline

This is a theorem about canonical quotients of the uniform Roe algebra, not a
new equality case for `C*_u(Z^d)` itself.  Quotient monotonicity yields only the
already-known positive lower bound one when the PV hypothesis applies, and no
positive lower bound in the remaining virtually nilpotent cases.  In
particular, the dihedral argument does not pass automatically to arbitrary
finite extensions or products: AF-ness is not monotone to arbitrary
subalgebras, so restricting to a finite-index cyclic or dihedral subgroup is
not a valid proof.

Dimension zero can genuinely occur just beyond the finite-generation
hypothesis.  Kopsacheilis--Winter, [*Paper-folding models for the CAR
algebra*](https://arxiv.org/abs/2508.04837), construct a free minimal Cantor
action of
`D_infinity direct_product (direct_sum_N C_2)` whose crossed product is the
CAR algebra.  This acting group is virtually abelian but not finitely
generated.  Thus the new parity theorem is not evidence for the false blanket
principle that every free minimal zero-dimensional action of every infinite
virtually nilpotent group has dimension one.

No claim is made that Problem LXXXVII is solved for any finite
asymptotic dimension at least two.
