---
rg: 2
id: oracular-affine-support-replacement-has-no-intermediate-regime
kind: claim
title: Affine-safe replacement of oracular 2-CSP models has no intermediate regime
distinct_from:
  affine-ghosts-survive-recoverable-tracial-dilations: that preserves one forbidden affine ghost under an affine recoverable decoder; this gives an explicit same-instance oracular 2-CSP counterexample and treats arbitrary instance-changing compilers without assuming a decoder.
  contextual-fano-cap-compiler-is-equivalent-to-perfect-lcs: that is the R-star/Fano-cap specialization; this works for arbitrary finite Boolean answer blocks and arbitrary affine-safe positive edge supports.
  finite-affine-profile-or-removes-pcpp-section-gate: that narrows one verifier before a particular linear-PCPP and R-star pipeline; this classifies replacement principles themselves and separately refutes every same-instance model-selection theorem.
  matrix-conj-forces-unsafe-support: that constructs the unique-trace BCS block; this passes it through the actual constraint-variable incidence construction and locates a forbidden affine ghost on one sampled oracular edge.
  three-label-affine-lowering-no-go: that makes the affine relaxation of one chosen source trace classically satisfiable; this first proves that every perfect trace of one finite oracular 2-CSP is locally unsafe, then identifies the exact strength of changing the instance.
---

ESTABLISHED.

**Replacement dichotomy.**  There is a finite Boolean oracular
`2`-CSP `U` with a perfect finite-dimensional tracial model such that every
perfect tracial model has an affine-unsafe positive support on one sampled
edge.  Consequently no operation which merely replaces a perfect model of a
fixed instance by another perfect model of the same instance can guarantee
locally affine-safe support.  This includes central decomposition,
support-minimal factor selection, matrix amplification, and every other
operation whose output is still a perfect tracial representation of the same
universal CSP algebra.

There is also no weaker **instance-changing** compiler endpoint.  Fix any
effective machine-indexed family `(B_m)` of finite Boolean oracular `2`-CSPs
with orientation

```text
m halts      => B_m has a perfect CE tracial model,
m nonhalts   => B_m has no perfect CE tracial model.             (OAR1)
```

Suppose a total effective transformation outputs finite Boolean oracular
`2`-CSPs `C_m` such that

```text
m halts      => C_m has a perfect CE model tau_m for which
                Aff(supp((tau_m)_e)) subseteq R_e for every edge e,
m nonhalts   => C_m has no perfect CE tracial model.              (OAR2)
```

The transformation need not supply `tau_m`, its supports, a decoder, or a
canonical affine profile.  Nevertheless `(OAR2)` effectively compiles to a
finite binary LCS family with the same orientation.  Conversely an LCS
family with `(OAR1)` is already a family satisfying `(OAR2)`.  Thus an
arbitrary soundness-preserving affine-support replacement compiler is
equivalent to the missing perfect-completeness LCS compiler; it is not a
strictly weaker preprocessing lemma.

## The unique-trace oracular counterexample

Use the magic-square BCS with involutions

```text
A B C
D E F
G H I
```

and the usual five positive and one negative parity equations.  Adjoin an
involution `Y` and the context `(A,B,Y)` whose allowed assignments are the
graph of Boolean AND,

```text
R_AND={000,010,100,111}.                                  (OAR3)
```

As proved in `matrix-conj-forces-unsafe-support`, the resulting universal BCS
algebra is `M_4(C)`.  Its only tracial state is normalized matrix trace.  The
four joint atoms of `(A,B)` are rank-one, `Y` is their AND function, and hence
all four atoms in `(OAR3)` have trace `1/4`.

Apply the standard symmetrized constraint-variable incidence conversion.  A
constraint question returns one allowed assignment and a variable question
returns one bit; an incidence edge checks that the two reported bits agree.
Add the harmless synchronous self-edge at each question if the chosen
`2`-CSP syntax does not already contain it.  This is an oracular `2`-CSP:
in a perfect tracial model, the variable PVM on an incidence edge is exactly
the corresponding marginal of the constraint PVM, so the two algebras
commute on every sampled pair.

The self-edges also make the game synchronous.  Thus a perfect commuting
strategy has the standard tracial realization on its synchronous game
algebra, and the argument below covers perfect commuting strategies as well
as CE/tracial ones; it is not restricted to a trace chosen in advance.

Conversely, faithful zero-loss semantics on an incidence edge gives

```text
q_x^b = sum_(a:a_x=b) p_c^a.                              (OAR4)
```

Indeed all mismatching products vanish, and summing the matching products
first over `a` and then over `b` proves both inequalities and hence equality.
The context atoms are therefore the joint spectral products of their
marginals.  Applying `(OAR4)` on every incidence reconstructs an exact
representation of the original BCS algebra.  Every perfect tracial model of
the incidence `2`-CSP thus restricts to the unique trace of `M_4(C)`.

Consider the sampled edge from the AND context `c` to the variable `A`.  Its
positive support is

```text
T={(000,0),(010,0),(100,1),(111,1)}.                     (OAR5)
```

The odd xor of the first three points in `(OAR5)` is

```text
(000,0)+(010,0)+(100,1)=(110,1).                         (OAR6)
```

The right side lies in `Aff(T)` but is rejected, because `110` is not an
allowed AND-context answer.  Hence `(OAR5)` is affine-unsafe in every perfect
tracial model.  This proves the same-instance assertion with a
finite-dimensional, factor, support-minimal, already-oracular example.

For a machine-indexed version, replace `B_m` in `(OAR1)` by the disjoint
conjunction

```text
D_m=B_m disjoint-union U.                                  (OAR7)
```

Perfect CE completeness is preserved by tensoring models, and any perfect CE
model of `D_m` restricts to one of `B_m`, so NONHALT soundness is preserved.
But every perfect model of every satisfiable `D_m` contains the fixed unsafe
edge `(OAR5)`.  Thus the obstruction is compatible with the exact
HALT/NONHALT orientation, rather than being an isolated satisfiable toy.

## Finite affine-profile enumeration

It remains to prove the instance-changing assertion.  For one output `C_m`,
write the answer at question `x` as a tuple in `F_2^(k_x)`.  For every sampled
edge `e=xy`, enumerate all affine subsets

```text
A_e subseteq R_e subseteq F_2^(k_x+k_y).                 (OAR8)
```

There are finitely many choices.  For a complete profile
`alpha=(A_e)_e`, form a finite system `L_alpha` as follows:

1. use one involutive bit variable for every answer coordinate at every
   question;
2. impose all affine equations cutting out `A_e` on edge `e`;
3. impose all within-question and sampled cross-question commutators needed
   by the joint edge measurements.

`finite-linear-commutation-system-to-lcs` converts these equations and
prescribed commutators exactly into ordinary binary LCS syntax.

If `m` halts, choose the model in `(OAR2)` and put

```text
A_e=Aff(supp((tau_m)_e)).                                  (OAR9)
```

Its joint functional calculus is a perfect model of `L_alpha`, so at least
one enumerated branch is complete.  If `m` does not halt and some
`L_alpha` had a perfect CE model, its joint edge spectra would lie in
`A_e subseteq R_e` for every edge.  Forgetting the affine equations would
give a perfect CE model of `C_m`, contradicting `(OAR2)`.  Thus every branch
is CE-unsatisfiable in the NONHALT case.

Finally apply `finite-lcs-product-sign-is-exact-or` to the finite list of
branches.  Its output is one ordinary LCS, has a perfect marked CE model iff
some branch does, and inherits absence of marked matrix-ultraproduct models
when every branch lacks one.  This proves the forward compiler implication.
For the converse, regard an LCS as an oracular Boolean CSP: every allowed
context/edge relation is affine, so the affine hull of every positive support
is automatically contained in that relation.

The dichotomy is therefore exact.  A same-instance model-selection theorem
is false already in `M_4(C)`.  Once the instance may change while NONHALT
soundness is retained, finite profile enumeration removes every
model-dependent choice and lands directly at perfect LCS completeness.  A
positive attack must consequently use the source-specific HALT construction
to prove one of those equivalent endpoints; tensoring, central selection, or
an unspecified affine-safe replacement principle cannot be an earlier
lemma.
