# 2026-08-18 — Compiler lowering for the perfect ZPC-IRS hyperlinear route

This note isolates two exact compiler transformations that are useful after the
perfect ZPC-IRS / quantum-value separation already recorded in the research
graph. The point is not to claim the remaining groupification problem solved;
it is to move the nonlinearity into a sharply delimited interface that can be
attacked with finite-state, PCP, and compiler ideas.

## 1. Predication: lower controlled linear equations to ordinary operator equations

Let `P_1,...,P_m` be pairwise orthogonal projections with sum `1`, and let
`U_1,...,U_n` be self-adjoint involutions commuting with every `P_a`. For every
branch and variable put

```text
G_(a,i) = P_a U_i + (1-P_a),
Z_a     = 1 - 2 P_a.
```

Then `G_(a,i)` and `Z_a` are self-adjoint involutions. For fixed `a`, any
commutations among the relevant `U_i` pass to the gated variables. Moreover

```text
prod_a G_(a,i) = U_i.
```

Indeed all cross terms vanish because the `P_a` are orthogonal, and on the
`P_a` summand precisely the `a`-th gate acts as `U_i`.

Suppose branch `a` requires

```text
P_a prod_(i in I_a) U_i = (-1)^b_a P_a.
```

Because `P_a` commutes with the participating involutions,

```text
prod_(i in I_a) G_(a,i)
  = P_a prod_(i in I_a) U_i + (1-P_a)
  = Z_a^b_a.
```

So the controlled equation is lowered exactly to an unconditional parity
operator equation. The nonlinear control has not disappeared: it is now
concentrated in the requirement that the selector involutions `Z_a` really
come from one mutually exclusive, exhaustive projection partition.

This is the operator-algebra analogue of compiler predication / SSA lowering:
control flow becomes data flow plus a selector invariant.

## 2. Why a naive parity-only selector gadget cannot finish the job

On a joint eigenspace for commuting selector involutions, write a bit `s_a=1`
when `Z_a=-1`. The desired branch semantics is exactly

```text
{s in F_2^m : HammingWeight(s)=1}.
```

Any family of ordinary parity equations in the `s_a` has an affine solution
set. For `m>=3`, the one-hot set is not affine: it contains `e_1,e_2,e_3`, but
its affine closure also contains `e_1+e_2+e_3`, which has Hamming weight `3`.
Therefore no gadget that uses only commuting selector bits and affine `F_2`
equations can enforce exact one-hot semantics once there are at least three
branches.

This explains precisely where a stronger gadget must enter: a noncommutative
selector code; a binary decision-tree compiler that carries path consistency;
a verifier-specific reduction exploiting the fixed TailoredMIP dependency
structure; or a toric/BCS compiler that can express selector idempotents.

The exact task is not “linearize arbitrary Boolean control.” It is to preserve
the perfect ZPC operator solution while enforcing selector soundness strongly
enough that a perfect finite-dimensional solution decodes back to a perfect
tailored strategy.

## 3. Cairn graph consequence

There are now two one-hole compiler routes from the perfect ZPC-IRS gap to a
nonhyperlinear group:

- freezing route: prove `zpc-readable-control-freezing-to-lcs`;
- selector-sound compiler route: prove `zpc-selector-sound-lcs-compiler`.

The second bypasses the need for a globally invariant readable atom. The local
controlled equations already lower exactly by predication; the remaining issue
is the selector invariant plus sound decoding.
