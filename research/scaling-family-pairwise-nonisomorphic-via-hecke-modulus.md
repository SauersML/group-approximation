---
rg: 2
id: scaling-family-pairwise-nonisomorphic-via-hecke-modulus
kind: route
title: Recover the scaling integer from the commensurated Kazhdan base
target: scaling-family-pairwise-nonisomorphic
requires:
  - scaling-family-non-mf
  - affine-scaling-hnn-groups-pairwise-nonisomorphic
artifacts:
  - non_mf_group_notes.tex
  - research/artifacts/scaling-family-invariants-audit-2026-08-30.md
---

# The full groups remember the Hecke modulus

Write

```text
B=Z^3 semidirect SL_3(Z),
H_m=<B,t | tbt^(-1)=alpha_m(b)>,
E_m=<H_m,c | c^2=1, [c,B]=1, the marked commutator w_m is central>.
```

The affine witness in `non_mf_group_notes.tex` shows that `H_m` embeds in
`E_m` and that the central involution `w_m` is nontrivial.  The subgroup `B`
is commensurated by all of `E_m`: `B` normalizes itself, `c` centralizes it,
and

```text
tBt^(-1)=alpha_m(B)<=B,       [B:alpha_m(B)]=m^3.       (1)
```

We prove two facts:

1. in `E_m`, every commensurated subgroup isomorphic to `B` is commensurable
   with the displayed copy of `B`;
2. the relative modular homomorphism of this commensurability class has image
   `<m^3>` in `Q_(>0)`.

They make `m` an abstract-group invariant.

## 1. The right-angled-Coxeter lamp quotient

Put `Z_m=<w_m>` and `bar E_m=E_m/Z_m`.  In `bar E_m` the marked
commutator is trivial.  Let `X_m=H_m/B`, and for `hB in X_m` write

```text
c_(hB)=h c h^(-1).
```

This is well-defined because `c` centralizes `B`.  Before imposing `w_m=1`,
the normal closure of `c` is the free product of the copies
`<c_x>~=C_2`, `x in X_m`: this is the standard presentation identity

```text
H_m *_B (B direct_product C_2)
   ~= ((*_(x in X_m) C_2) semidirect H_m).
```

The single relation `w_m=1` and all its `H_m`-conjugates say exactly that
two vertex involutions commute on every edge in the `H_m`-orbit of

```text
{tB, v_1tB}.
```

Consequently

```text
bar E_m ~= W_(Gamma_m) semidirect H_m,                 (2)
```

where `W_(Gamma_m)` is the right-angled Coxeter group on the resulting
`H_m`-invariant graph `Gamma_m` on `X_m`.

The graph is locally finite.  Indeed `B` is commensurated in `H_m`, so the
stabilizer in `B` of either endpoint of an edge has finite index; transitivity
then gives finite constant degree.  Hence the clique number is finite and the
Davis cubing of `W_(Gamma_m)` is finite-dimensional.  (The cubing itself is
not locally finite: `X_m` is infinite.)  The action of `H_m` on the
defining graph extends to the cubing, so (2) acts cubically on it.

## 2. Property (T) pushes every copy of the base back into the affine part

Let `K<=E_m` be commensurated by `E_m` and isomorphic to `B`.  The group
`B` has property `(T)`.  It also has no nontrivial finite normal subgroup:
a finite normal subgroup projects to a finite normal subgroup of
`SL_3(Z)`, hence trivially, and then lies in the torsion-free translation
group.  Therefore `K intersect Z_m=1`, and the image `bar K` of `K` in
`bar E_m` is again isomorphic to `B` and has property `(T)`.

Niblo--Reeves, *Groups acting on CAT(0) cube complexes*,
[arXiv:math/9702231](https://arxiv.org/abs/math/9702231), prove the
finite-dimensional cubical fixed-point consequence of property `(T)`
(property `FW`).  Applying it here, `bar K` fixes a point and hence
stabilizes the unique open cube containing that point.  Equivalently, one may
combine their bounded-orbit theorem with the standard completeness of the
finite-dimensional unit-cube Davis realization.  Every cube is a
`W_(Gamma_m)`-translate of a standard clique cube.  After conjugating by
such a Coxeter element, its stabilizer has the form

```text
W_T semidirect (H_m)_T,                                 (3)
```

where `T` is a finite clique, `W_T~=C_2^|T|` is finite, and `(H_m)_T`
is its setwise stabilizer in `H_m`.

Pass first to the finite-index subgroup of `bar K` whose `(H_m)_T`-part
acts trivially on the finite group `W_T`.  On this subgroup the `W_T`
coordinate in (3) is a homomorphism to a finite group; its kernel is a
further finite-index subgroup contained in `(H_m)_T<=H_m`.  Lifting across
the central group `Z_m` and, if necessary, taking one more index-two kernel
shows:

```text
some finite-index subgroup K_0<=K is conjugate into H_m. (4)
```

Finite-index subgroups of commensurated subgroups are commensurated.  Thus,
after conjugating, `K_0<=H_m` is commensurated by `H_m`.

## 3. The 2026 commensurated-subgroup theorem identifies the class

Use the intrinsic affine normal form from
[[affine-scaling-hnn-groups-pairwise-nonisomorphic]]:

```text
H_m=U_m semidirect (L direct_product <t>),
U_m=Z[1/m]^3,       L=SL_3(Z).                           (5)
```

The property-`(T)` group `K_0` has no nontrivial homomorphism to the
torsion-free factor `<t>`.  Let `P` be its image in `L`.  This image is
commensurated by `L`: for `ell in L`, the projection of
`K_0 intersect ell K_0 ell^(-1)` has finite index in both `P` and
`ell P ell^(-1)` and is contained in their intersection.  It is infinite: otherwise `K_0` would be virtually contained in the abelian
group `U_m`, whereas an amenable property-`(T)` group is finite.

Shalom--Venkataramana--Willis, *The Margulis--Zimmer Conjecture for
Nonuniform Arithmetic Groups*,
[arXiv:2607.17078](https://arxiv.org/abs/2607.17078), Theorems 1--2,
prove that every infinite subgroup of the higher-rank nonuniform lattice
`SL_3(Z)` which is commensurated by it has finite index.  Hence

```text
[L:P]<infinity.                                         (6)
```

Transport the canonical translation subgroup `R~=Z^3` of the abstract
copy `K~=B`, and put `A_0=K_0 intersect R`.  Since `K_0` has finite
index in `K`, the subgroup `A_0` is normal in `K_0`, free abelian of
rank three.  Its image in `P` is abelian and normal.  The Margulis normal
subgroup theorem makes that image finite.  Define `A` to be its kernel.
Then `A` is still normal and rank three, has finite index in `A_0`, and
lies inside `U_m`.

The rational span of `A` in `Q^3` is nonzero and `P`-invariant.  Since a
finite-index subgroup of `SL_3(Z)` is Zariski dense and the standard
three-dimensional rational module is irreducible, that span is all of
`Q^3`.  Thus `A` is a full lattice.

Finally `K_0` is finitely generated, so the translation coordinates of a
finite generating set have bounded `m`-power denominators.  For some `r`,

```text
K_0 <= m^(-r)Z^3 semidirect L = t^(-r) B t^r.
```

The full lattice `A<=K_0` and (6) show that this inclusion has finite index.
Therefore the conjugated `K_0`, and hence the conjugated `K`, is
commensurable with `B`.  Undoing the conjugation replaces `B` by one of
its conjugates; since `B` is commensurated by all of `E_m`, every such
conjugate is commensurable with `B`.  This proves Fact 1.

## 4. Index calculus recovers `m`

For a commensurated subgroup `C<=G`, define

```text
Delta_C(g)=
 [C:C intersect gCg^(-1)] / [gCg^(-1):C intersect gCg^(-1)].   (7)
```

Write `[A:D]_rel=[A:A intersect D]/[D:A intersect D]` for commensurable
subgroups.  Multiplicativity of relative index shows that (7) is a
homomorphism.  If `C'` is commensurable with `C`, then
```text
[ C' : gC'g^(-1) ]_rel
 = [ C' : C ]_rel [ C : gCg^(-1) ]_rel
   [ gCg^(-1) : gC'g^(-1) ]_rel.
```
The first and last factors are inverse because conjugation preserves relative
index.  Thus `Delta_(C')=Delta_C`.  The same formula also proves
functoriality under abstract group isomorphisms.

For the displayed `B<=E_m`, each of the six base generators normalizes
`B`, and the lamp generator `c` centralizes `B`; all seven therefore
have relative modulus one.  The remaining generator `t` satisfies (1), so

```text
Delta_B(t)=m^3,       Delta_B(E_m)=<m^3>.               (8)
```

Now let `Phi:E_m->E_n` be an isomorphism.  The subgroup `Phi(B)` is a
commensurated copy of `B`, so Facts 1 and (7) make its relative modular
homomorphism equal to that of the displayed `B<=E_n`.  Functoriality and
(8) give equality of subgroups of the positive rationals,

```text
<m^3>=<n^3>.                                             (9)
```

Prime valuations turn (9) into equality of the nonnegative exponent vectors
of `m^3` and `n^3` (the only other possible generator is the inverse, which
is not an integer greater than one).  Hence `m=n`.

Thus the finitely presented non-MF groups `E_m`, `m>=2`, are pairwise
non-isomorphic.
