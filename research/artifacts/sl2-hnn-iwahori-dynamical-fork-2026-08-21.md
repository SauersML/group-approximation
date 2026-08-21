# SL2 HNN, Iwahori stability, and the tree-action fork — 2026-08-21

This packet ingests the proposed four-generator HNN witness and its two
suggested forks without duplicating claims already present in Cairn.  The
mathematical content is split below into established, conditional, open, and
incorrectly inferred statements.

## 1. Explicit witness already represented in Cairn

In `PSL_2(Z[1/2])`, use the presentation from
`iwahori-square-root-presentation-is-bs14-plus-one-involution`:

```text
<x,r,s | x^2=1, (xr)^2=1, (xs^2)^3=1,
         r s r^(-1)=s^4, (xrs)^3=1>.
```

Here `C=PSL_2(Z)=<x,s^2>`.  Adjoining one stable letter gives

```text
G_2=<x,r,s,t | x^2=1, (xr)^2=1, (xs^2)^3=1,
                 r s r^(-1)=s^4, (xrs)^3=1,
                 [t,x]=1, [t,s^2]=1>,                 (SIH1)
w=[t,r].
```

This is the explicit `p=2` instance already consumed by
`non-hyperlinear-from-hnn-over-sl2-z`.  Britton normal form gives `w!=1`.
The congruence co-density and uniform conjugation gap are already established
as `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`.

The quantitative estimate proposed for an almost representation whose base
tuple is close to an exact representation is exactly the specialized theorem
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear`: property `(tau)` moves
the stable-letter unitary to `rho(C)'`, co-density identifies
`rho(C)'=rho(A)'`, and the commutator mark collapses.  At zero defect this
also proves that every finite-dimensional unitary representation, hence every
finite quotient, kills `w`.  Thus `G_2` is neither MAP nor residually finite.

The conditional conclusion is likewise already wired:

```text
iwahori-local-global-defect-question
  + sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  + hnn-over-codense-kazhdan-subgroup-not-hyperlinear
  => non-hyperlinear-group.                             (SIH2)
```

No new claim is needed for `(SIH1)--(SIH2)`.

## 2. Exact form of the remaining stability gate

The open gate is `iwahori-local-global-defect-question`.  Its two concrete
normal forms are already established:

- `iwahori-question-as-square-root-of-parabolic`: two modular
  `C_2*C_3` representations glued along opposite index-three Iwahori
  subgroups;
- `iwahori-square-root-presentation-is-bs14-plus-one-involution`: an exact
  `BS(1,4)` core plus one involution satisfying the two cubic constraints.

The latter is the cleanest repair target.  The metabelian `BS(1,4)` dynamics
can be repaired by the dense-periodic-measures theorem; the unresolved step
is simultaneous repair of the same involution against both triangular
constraints.  `sl2-half-explicit-strict-flexible-separation` already records
the deleted-line Weil sequence: it refutes strict same-dimensional stability
but is repaired by one padding dimension, so it is not a counterexample to
flexible stability.

The tensor-amplification observation is already
`projective-transfer-linear-bound-equals-no-ultraproduct-leak`, and the
warning that exact finite-dimensional co-density alone cannot control an
ambient ultraproduct commutant is already
`exact-codensity-does-not-imply-matricial-rcc`.  These are not new routes.

## 3. The Bruhat--Tits tree action: a one-sided falsification test

Let `A=PSL_2(Z[1/2])`, `C=PSL_2(Z)`, and `X=A/C`, the orbit of one color of
vertices in the 3-regular Bruhat--Tits tree.  Put

```text
W=(Z/2) wr_X A.
```

The base-coordinate lamp commutes with `C` and is moved by `r`; this is the
special case of `coset-bernoulli-ce-refutes-relative-commutant-collapse`.
Consequently:

```text
the action A on X is sofic
  => W is sofic (finite-lamp action permanence)
  => L(W) is Connes embeddable
  => relative-commutant collapse for C<A fails
  => flexible HS stability of A fails.                 (SIH3)
```

The last implication is the contrapositive of the exactification plus
property-`(tau)`/co-density argument in the HNN theorem.  The action question
is not settled by the standard easy criteria: `C` is nonamenable, co-density
collapses the finite-quotient coset actions, and tree balls have boundary of
positive density.

This is **not a two-sided dichotomy**.  A proof that the action is nonsofic
does not prove flexible stability of `A`, Connes nonembeddability of `L(W)`,
or nonhyperlinearity of `W`.  It only closes the proposed sofic-action
countermodel to stability.  Therefore the negative action statement is not
wired as a route to `non-hyperlinear-group`.

## 4. Characteristic-two direct finiteness is a separate two-open-input fork

The binary Leavitt algebra itself is not directly finite, but Cairn does
**not** establish that the modular group algebra of its unit group is not
directly finite.  The latter is the open root
`leavitt-unit-group-algebra-not-directly-finite`; direct finiteness does not
ascend from a quotient.

A hypothetical theorem

```text
hyperlinear G => F_2[G] is directly finite             (SIH4)
```

together with an actual witness to failure of direct finiteness in
`F_2[L_(F_2)(1,2)^x]` would indeed prove that the Leavitt unit group is
nonhyperlinear.  At present both the group-algebra witness and `(SIH4)` are
open.  Elek--Szabo prove the corresponding ring theorem for sofic groups,
not for hyperlinear groups.  This fork therefore shares the explicit group
with the goal but is not currently a live one-hole route to it.

## 5. Net result

The packet contributes no unconditional nonhyperlinear group.  Its strongest
correct integration is:

1. `G_2` is an explicit four-generator, seven-relator, non-MAP and
   non-residually-finite HNN group;
2. flexible Iwahori HS stability would make `G_2` nonhyperlinear;
3. soficity of the explicit tree-coset action would refute that stability;
4. nonsoficity of the action alone does not settle hyperlinearity; and
5. the characteristic-two group-algebra shortcut needs two open theorems,
   not one established Cairn fact.
