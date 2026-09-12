# Rational decomposition rank for the remaining AF-ideal extensions

This is a corollary of
[the ordered-AF index dichotomy](stw79-index-dichotomy-2026-09-04.md),
with the quotient K-zero torsion restriction removed by rational
stabilization. The general STW LXXIX problem remains open here.

Let `B,D,E,delta,Q` satisfy the claim
`stw79-rational-stabilization-removes-kzero-torsion`.

## Rationalization of the exact sequence

Write `Q` as the unital inductive limit of matrix algebras with dimensions
`n!`. Tensoring by these matrices and taking limits gives

```text
0 -> K tensor (B tensor Q) -> E tensor Q -> D tensor Q -> 0.
```

Essentiality persists: if a positive element of `E tensor Q`
annihilates `(K tensor B) tensor Q`, its image under the faithful slice
`id_E tensor tau_Q` annihilates `K tensor B` and is zero. Faithfulness
of the slice makes the original element zero. Apply this to `x*x` for
an arbitrary annihilator element.

The tensor factors of the new ideal coefficient and quotient are simple,
and tensoring with a matrix algebra followed by this injective limit
preserves simplicity. The coefficient remains unital AF. Matrix stability
and inductive-limit permanence give

```text
d_Q=dr(D tensor Q)<=dr(D)<infinity.
```

No equality between `d_Q` and `dr(D)` is assumed: rationalization can
change the latter. Nuclearity, the UCT, separability, unitality and
non-elementarity of the quotient persist.

By K-theory continuity on the same matrix-stage system,

```text
K_i(A tensor Q)=K_i(A) tensor_Z Q,
```

naturally for the algebras and maps in this sequence. Thus the new
quotient K-zero is torsion-free, and the new boundary is
`delta_Q=delta tensor id_Q`.

The order on `K_0(B tensor Q)` is the localization of the AF dimension
group order: every element can be written `g/n`, and its sign is the
sign of `g`. Totality of the original order therefore persists.
Moreover, AF dimension groups are torsion-free, so the map
`K_0(B)->K_0(B) tensor_Z Q` is injective. If `delta(x)` is nonzero,
its rationalization is nonzero as well. Consequently

```text
delta_Q=0 iff delta=0.
```

All hypotheses of the ordered-AF index dichotomy now hold. It gives

```text
dr(E tensor Q)=d_Q     if delta=0,
dr(E tensor Q)=infinity otherwise.
```

## Quasidiagonality of the original middle algebra

If `delta=0`, the finite decomposition rank just proved makes
`E tensor Q` quasidiagonal. Its canonical subalgebra `E tensor 1` is
isomorphic to `E`, so `E` is quasidiagonal and stably finite.

Conversely, suppose `E` is stably finite and `delta` is nonzero. Totality
supplies a nonzero positive `g` in `im(delta)`. A nonzero ideal projection
representing `g` has zero K-zero class in `E`, by exactness. The
Grothendieck-group argument in the prerequisite then produces an infinite
projection in a matrix algebra over `E`, a contradiction. This argument
does not involve either K-group of `D` beyond the definition of `delta`.

We have therefore proved

```text
delta=0 iff E is stably finite iff E is quasidiagonal
        iff dr(E tensor Q)<infinity.
```

The quasidiagonality equivalence itself is **prior art**, not a new
resolution: Brown and Dadarlat's
[Extensions of quasidiagonal C*-algebras and K-theory](https://www.math.purdue.edu/~mdd/Publications/Nate%2BMD.pdf),
Corollary 3.7, treats quasidiagonal ideals with totally ordered K-zero
and nuclear UCT quasidiagonal quotients. Their Proposition 4.1 attributes
the more general positive-index criterion for stable finiteness to
Spielberg. The direct projection proof here specializes that criterion;
the rational decomposition-rank formula follows from the previously
proved Cairn dichotomy.

## What remains unresolved

Finite decomposition rank passes to the rational stabilization, but
descent from `E tensor Q` to `E` is not established by these arguments.
Quasidiagonality passes to subalgebras; decomposition rank has no such
general permanence theorem. Hence the zero-index case with quotient
K-zero torsion is not being marked as finite decomposition rank for `E`.
The earlier torsion-free theorem settles that descent for its stated
class. This corollary specifies what the remaining case must overcome.

The proof uses the existing published permanence results cited in the
prerequisite and the primary Brown–Dadarlat source checked on 2026-09-05.
It is not a formalization or a computational search claim.
