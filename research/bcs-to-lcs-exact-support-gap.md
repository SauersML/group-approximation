---
rg: 2
id: bcs-to-lcs-exact-support-gap
kind: claim
title: A tracial non-RU BCS admits an exact robust LCS sub-menu with approximate soundness
distinct_from:
  robust-locally-satisfiable-relator-code: that asks for sparse group-ball preservation with no ambient tracial witness; this target uses a tracial BCS witness to certify nontriviality of the central mark and asks for an exact LCS sub-menu that rejects every marked approximate profile.
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
  - notes/FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md
---

Starting from a finite BCS `B` which is tracially satisfiable but not
`R^U`-satisfiable, construct a finite **linear-system / LCS** relator menu `S`,
a distribution `mu` on `S`, a marked central involution `J`, and a tracial
unitary assignment `rho` such that, for some

```text
0 < eps < eps_plus,
delta > 0,
```

the following strict inequality holds.

Let

```text
E = {r in S : rho(r)=1 exactly},
g = mu(E).
```

Among all finite-dimensional unitary assignments with
`d_2(J,1)>=delta`, let `q` be the supremum `mu`-mass of relators whose defect
is at most `eps_plus`. Then

```text
g > q.
```

By `exact-support-gap-nonexact-checks-no-advantage`, this condition is
qualitatively equivalent to the following simpler target: **every marked
finite-dimensional profile rejects at least one relator in the exact support
`E`**. Since `E` is finite, uniform measure on `E` then has exact tracial
completeness and a rejection margin at least `1/|E|`. Nonexact checks in
`S\E` cannot create the gap and may be discarded for existence purposes.

Thus this node should be read as an exact-robust-sub-menu compiler target, not
as a weaker route around perfect completeness. `exact-support-relator-sparsification`
remains useful downstream for finite-moment extraction once such an exact
sub-menu has been found.

## Minimal exact-support fork: the affine-support relaxation

Fix a tracial satisfying state `tau` of the source BCS.  For each context
`c`, let

```text
S_c={a:tau(P_(c,a))>0},        A_c=Aff_(F_2)(S_c),      (ESF1)
```

and let `L_tau` be the finite LCS consisting of affine equations cutting out
the `A_c`, together with the standard rows enforcing every required
contextwise commutation.  By `tracial-support-affine-linearization` and
`finite-linear-commutation-system-to-lcs`, the original tracial operators
extend to a perfect operator solution of `L_tau` with its solution-group
involution represented by `J=-I`.

> **Affine-relaxation criterion.**  If `L_tau` is not `R^U`-satisfiable, then
> `L_tau` itself supplies `bcs-to-lcs-exact-support-gap`, with the exact menu
> equal to its full finite relator list.

Indeed, non-`R^U`-satisfiability says that the marked involution cannot remain
separated in a sequence of finite-dimensional assignments whose complete
finite LCS relator defect tends to zero.  Fix any `delta>0` below
`d_2(-I,I)`.  If there were no uniform `eta>0` such that every assignment
with `d_2(J,I)>=delta` has some relator defect at least `eta`, choosing one
counterexample for each `eta=1/n` would give exactly such a forbidden
approximate sequence.  Hence some `eta>0` exists.  Put uniform measure on the
finite relator list and choose `eps_plus<eta`.  The tracial witness satisfies
every relator, so `g=1`, while each marked finite-dimensional assignment
rejects at least one relator and therefore

```text
q<=1-1/|S|<1=g.                                        (ESF2)
```

This isolates a concrete one-instance question:

```text
Does some tracial state of the fixed non-RU BCS have a
non-RU affine-support relaxation L_tau?                 (ESF3)
```

An affirmative answer finishes this compiler without a long code, mask, PCP,
or sparsification argument.

There is also a sharp limit on improving `L_tau` by a context-local exact
gadget.  Suppose a proposed local parity gadget has visible context bits `x`,
affine auxiliary bits `y`, and admits an honest auxiliary assignment for
every `a in S_c`.  Its classical solution set is affine, and its projection
to the visible coordinates is affine by
`affine-auxiliary-control-flow-barrier`.  That projection contains `S_c`, so
it contains all of `A_c=Aff(S_c)`.  Thus no assignmentwise local exact LCS
gadget—regardless of how many affine auxiliaries it uses—can exclude any of
the extra points introduced by `(ESF1)`.

Consequently a route beyond `(ESF3)` must use genuinely global
cross-context operator relations, not a stronger local linearization of the
same support.  `linear-encoding-lcs-admits-odd-subset-cheats` gives the next
obstruction: global linear encodings which remain exact on all honest support
points also retain consistent odd-subset characters.  Proving `(ESF3)`, or
globally eliminating those odd-subset profiles without losing the tracial
solution, is the remaining exact-support content.  Exact finite-dimensional
invisibility alone is insufficient by
`exact-fd-invisibility-has-no-general-hs-robustification`.

## Extreme traces are without loss, but do not remove odd subsets

There is an exact reduction answering the ``choose an extreme trace'' part
of `(ESF3)`.  For a satisfying trace `tau`, let

```text
F_tau={sigma in T(B):
       sigma(P_(c,a))=0 whenever tau(P_(c,a))=0}.       (ESF4)
```

Each condition in `(ESF4)` is the zero set of a nonnegative affine
functional on `T(B)`, hence defines a face.  Thus `F_tau` is a nonempty
compact face.  Choose an extreme point `sigma` of `F_tau`; it is also extreme
in `T(B)`, and

```text
S_c(sigma) subseteq S_c(tau),
Aff(S_c(sigma)) subseteq Aff(S_c(tau)).                 (ESF5)
```

Therefore `L_sigma` is a strengthening of `L_tau`.  Any `R^U` solution of
`L_sigma` is also an `R^U` solution of `L_tau`.  Consequently

```text
L_tau non-R^U  ==>  some extreme sigma has L_sigma non-R^U. (ESF6)
```

So extremality may be imposed without loss **after** an affine-support gap
has been found.  It is not a mechanism for producing that gap.

Indeed an extreme, even factorial, trace can have non-affine local support.
In `M_3(C)` take the normalized trace and a commuting two-bit PVM with three
rank-one atoms labelled

```text
00, 01, 10
```

and zero atom at `11`.  The normalized trace is the unique tracial state of
the factor, but its context support has three points and affine hull all of
`F_2^2`; the added point is

```text
11=00+01+10.
```

Thus factoriality or extremality of the global BCS trace does not force its
context restrictions to have affine support.

More generally, for every nonempty `S subseteq F_2^m`,

```text
Aff_F2(S)={s_1+...+s_(2k+1): s_i in S}.                (ESF7)
```

After cancelling repetitions, `(ESF7)` is exactly the odd-subset
relaxation.  Hence the affine-support fork and the odd-subset fork are not
two different losses: they are the same local relaxation.

There is one immediate positive criterion.  If a satisfying trace `tau`
has every `S_c(tau)` already affine, then `A_c=S_c` in every context.  An
`R^U` solution of `L_tau` would then have each joint context PVM supported
inside the original satisfying predicate and would give an `R^U` solution of
the source BCS, impossible.  Therefore

```text
all S_c(tau) affine  ==>  L_tau non-R^U,                (ESF8)
```

which proves this claim through the affine-relaxation criterion.  By
`(ESF6)`, one may then choose an extreme witness as well.

The unresolved source-specific theorem is now sharp: find a satisfying trace
whose support-minimal extreme face has affine context supports, or prove that
the globally consistent odd-subset profiles introduced by `(ESF7)` still
cannot live in `R^U`.  The mere availability of an extreme non-CE trace gives
neither statement.

## Attempts

- **Published Taller--Vidick test, unmodified.** Their completeness loss comes
  from the noisy mask. The relevant question is now whether the subfamily of
  checks that are operator-exact for the tracial strategy is itself sound
  against every marked finite-dimensional approximate assignment. The
  published unconditioned soundness theorem does not imply this conditioned
  statement.
- **Mask reweighting alone cannot help.** The no-advantage lemma shows that
  putting weight on checks outside `E` cannot improve the qualitative target.
  Any successful reweighting must ultimately expose a robust exact subset of
  `E`; the finite zero-sum formulation in `exact-menu-gap-is-zero-sum-game`
  can optimize its quantitative margin.
- **Quantum-sound gadget compiler.** Seek a source-specific reduction from the
  known tracial/non-`R^U` BCS to LCS checks whose exact-support subfamily
  preserves approximate-model soundness. This is compatible with the
  predicated-control route: `controlled-linear-predication-normal-form` removes
  controlled equations exactly, leaving selector soundness as a finite
  compiler invariant.
- **Oracularizability is not an affine-support certificate.**
  `three-label-affine-lowering-no-go` preserves a perfect pairwise-oracularizable
  strategy and a finite-dimensional gap under a three-label answer split, but
  makes the standard BCS trace-support affine relaxation classically
  satisfiable.  Therefore `(ESF3)` must use special global structure of the
  chosen source and trace; it cannot follow from the oracularizable source
  interface alone.
- **Modern repetition/PCP amplification.**
  [[dinur-constraint-gap-amplification]] is now the named classical baseline:
  it amplifies ordinary finite-alphabet `UNSAT` with perfect completeness and
  linear size growth.  This target needs more.  Amplification is useful here
  only if it also preserves or exposes an operator-exact support family whose
  conditioned value is below one. Driving the unconditioned value down while
  the exact subfamily remains perfectly satisfiable by a bad profile does not
  move this target.
