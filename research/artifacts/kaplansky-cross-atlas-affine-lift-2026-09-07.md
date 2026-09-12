# 2026-09-07 — Cross-atlas affine lifting attack on Kaplansky and Gottschalk

## Outcome

This pass does **not** solve Kaplansky direct finiteness or Gottschalk
surjunctivity.  It replaces the previously selected 25-term lift by a much
shorter exact lift whose support provably generates the full nonsofic Leavitt
unit group, proves bounded minimality of that lift, and implements the stronger
joint linear system which would certify a counterexample on a hit.

All calculations use the exact reduced binary-prefix normal form.  There are
no floating-point comparisons and no quotient equality is mistaken for a
group-algebra equality.

## 1. Why the recursive quine route is closed

The elementary two-compressor core has the exact normal form

```text
C_lc({0,1}^N,GL_5(F_2)) semidirect (C_2*C_3)
```

and is LEF.  The recursive kernel packets are locally finite; every finite
packet correction therefore remains in a directly finite finite-group
algebra.  Symmetric compressor sums are square-zero packets, while a
one-packet correction is impossible and a two-packet correction must have odd
support intersection and genuine double-coset folding.  Thus self-reference
inside one recursive packet family cannot close the tail.  Any viable
compiler must use a relation crossing the two atlas charts.

## 2. Four generators instead of twelve

In either `GL_4(F_2)` chart, the adjacent-transvection words

```text
(0,1,2), (3,5,4)
```

generate a subgroup of exact order `20160`, hence the whole chart.  Applying
the same pair in both charts gives four explicit units generating
`Q=L_(F_2)(1,2)^x`, because the two charts generate `Q`.

Reproducer:

```text
python experiments/atlas_four_generator_certificate.py
```

## 3. The eleven-term full-support lift

Force those four generators into an odd group-algebra lift of `s_0`.  The
evaluation equation is linear over `F_2`, and the radius-three ball has `795`
exact group elements.  Its affine solution space has kernel dimension `703`.
Sparse decoding produces the seven correction words

```text
(1,0), (6,8), (0,2,9), (3,1,7),
(5,3,1), (5,3,4), (5,11,10).
```

Together with the four chart generators this gives the eleven terms in
`leavitt-cross-atlas-eleven-term-s0-lift`, with exact evaluation `s_0` and
support generating all of `Q`.

The exact meet-in-the-middle verifier exhausts correction weights `1,3,5` and
finds none.  Thus seven is the minimum correction weight, and eleven the
minimum total weight, after fixing the four chart generators and restricting
the correction pool to the radius-three ball.

Reproducers:

```text
python experiments/kaplansky_affine_lift_search.py \
  --lift-radius 3 --inverse-radius 3 --mandatory atlas4
python experiments/kaplansky_minimum_lift_certificate.py
```

The eleven-term lift has no left inverse supported in the radius-four ball
(`5503` candidate group elements).  This is bounded only.

## 4. Joint lifting rather than choosing A first

The sharper search chooses an odd lift `B` of `t_0` and solves simultaneously

```text
B A = 1  in F_2[Q],              evaluation(A)=s_0.       (J1)
```

For fixed `B`, both clauses are one linear system over `F_2`.  Any solution is
automatically strict:

```text
evaluation(A B)=s_0 t_0 != 1.
```

Therefore a reported hit would be a complete finite counterexample, not a
lifting heuristic.  The affine radius-three space contains mixed-chart
five-term lifts of `t_0`; one is supported on

```text
(6,2), (0,1,2), (0,2,4), (2,4,7), (6,7,6).
```

No joint solution was found in two deterministic runs containing 32 and 256
sparse affine samples with `A` in the radius-three ball.  The displayed
five-term lift also has no joint
solution with `A` in the radius-four ball.  Again these are finite fences.

Reproducer:

```text
python experiments/kaplansky_joint_lift_search.py \
  --lift-radius 3 --a-radius 3 --samples 256
```

## 5. Next exact gate

The search should now vary both affine factors while retaining a literal
cross-atlas relation.  The most promising finite formulation is a bilinear
syndrome decoder with:

1. a sparse affine lift of `t_0` whose support subgroup is certified to be
   `Q`, not merely mixed-chart;
2. an `A`-support universe grown by multiplication-collision classes rather
   than word radius;
3. exact blocking clauses learned from failed Gaussian systems;
4. final verification by canonical prefix multiplication.

The rank-three lift, locally finite recursive packets, symmetric compressor
sums, and the elementary two-compressor core should not be searched again;
their failures are structural.

## 6. Mathematical pivot: a trace-perfect nested corner

The bounded searches above are reconnaissance, not the proposed proof method.
`leavitt-trace-balanced-nested-idempotents` replaces them with a canonical
projective-module problem.

Using `R~=M_2(R)`, take the constant cubic unit

```text
G=[[0,1],[1,1]],
```

a proper scalar-diagonal idempotent `P=diag(q,q)`, and the localized cubic
unit `H=PG+(1-P)`.  Then `G+G^(-1)=1` and `H+H^(-1)=P`.  Their images `g,h`
in `Q` commute and generate `C_3 x C_3`.  In `F_2[Q]` set

```text
e=[g]+[g^(-1)],   c=[h]+[h^(-1)],   f=ec.
```

This gives a proper nesting `0!=f<e`; evaluation sends the pair to equivalent
idempotents `p<1` in `R`.  A single involution simultaneously conjugates
`g,h` to their inverses, so both `e` and `f` vanish in the full group-algebra
cocenter.  Thus augmentation and every conjugacy-class trace agree, removing
the obstruction that killed the earlier proposed corner pair.

The high-impact target is now one equation in projective-module language:

```text
e F_2[Q] ~= f F_2[Q].
```

An isomorphism supplies `xy=e`, `yx=f`; padding by `1-e` gives a literal
Kaplansky counterexample.  This equivalence remains open, but it is a
trace-compatible Hilbert-hotel mechanism and is the conceptual route to
pursue instead of larger word balls.
