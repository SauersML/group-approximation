# Exact invariants for the literal non-MF scaling family

Date: 2026-08-30.

The literal family replaces the three relations
`t v_i t^(-1)=v_i^2` by `t v_i t^(-1)=v_i^m`, leaving the other
thirty-eight relators unchanged.  Two natural invariant computations are
now exact.

## The cheap invariant fails completely

Direct abelianization of the displayed presentation gives

```text
E_m^ab ~= Z direct_sum C_2
```

for every `m>=2`.  All affine-base generators die before the scaling
relations are used.  Thus the abelianization-rank suggestion left in the
earlier multiplicity audit cannot distinguish even one pair `E_m,E_n`.

## The affine quotient remembers the full integer

Killing the lamp generator `c` gives the canonical affine ascending HNN
quotient

```text
H_m ~= Z[1/m]^3 semidirect (SL_3(Z) direct_product Z).
```

The module `Z[1/m]^3` is the unique largest normal abelian subgroup and is
therefore characteristic.  The center of the quotient by that module is the
stable-letter `Z`, whose generator acts by multiplication by `m`.  An
abstract isomorphism must send that generator to its inverse or itself;
intertwining on the torsion-free module excludes inversion and forces the
integers to agree.  Hence the `H_m` are pairwise non-isomorphic.

This is stronger than comparing the additive groups `Z[1/m]^3`: those see
only the set of prime divisors of `m`, whereas the quotient action recovers
prime exponents as well.

## Passing the invariant through the lamp without a characteristic kernel

The kernel of `E_m -> H_m` need not be characterized.  Quotienting only by
the central mark gives a right-angled-Coxeter lamp semidirect product.  Its
finite-dimensional Davis cubing forces every commensurated property-`(T)`
copy of the affine base to have a finite-index subgroup in the affine part.
The cubical input is Niblo--Reeves,
[*Groups acting on CAT(0) cube complexes*](https://arxiv.org/abs/math/9702231):
property-`(T)` actions on finite-dimensional CAT(0) cube complexes have
bounded orbits; completeness of the locally finite Davis cubing then gives
a fixed point and a stabilized cube.

At that point the July 2026 theorem of Shalom--Venkataramana--Willis,
[*The Margulis--Zimmer Conjecture for Nonuniform Arithmetic
Groups*](https://arxiv.org/abs/2607.17078), identifies its projection to
`SL_3(Z)` as finite index.  Bounded denominators and irreducibility of the
standard rational module then make the subgroup commensurable with the
displayed base `B`.

The Hecke-pair relative modular homomorphism of this intrinsic
commensurability class has image `<m^3>`, because the stable letter carries
`B` onto the index-`m^3` subgroup `mZ^3 semidirect SL_3(Z)`.  Relative
modulus is invariant under abstract isomorphism and replacement by a
commensurable subgroup.  Therefore `E_m~=E_n` gives `<m^3>=<n^3>`, hence
`m=n`.  The full scaling family is pairwise non-isomorphic.

## Source boundary

The presentation and affine identification are in `non_mf_group_notes.tex`,
Definition `E` and the scaling-family corollary.  The affine-retract
computation uses only the classical normal-subgroup theorem for `SL_3(Z)`,
in the weak consequence that it has no nontrivial abelian normal subgroup.
Passing from the retract to `E_m` uses three auditable inputs: the
Niblo--Reeves cubical fixed-point theorem for property `(T)`, the Margulis
normal subgroup theorem, and the 2026 Shalom--Venkataramana--Willis
commensurated-subgroup theorem quoted above.  No matrix-approximation or
non-MF argument is reused in the isomorphism separation, beyond the already
established literal presentation and affine embedding.
