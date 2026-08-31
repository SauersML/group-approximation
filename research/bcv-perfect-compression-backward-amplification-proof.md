---
rg: 2
id: bcv-perfect-compression-backward-amplification-proof
kind: route
title: Invert every BCV compression wrapper and retain the exact Pauli block algebra
target: bcv-every-perfect-compression-amplifies-readable-closure
requires:
  - bcv-perfect-answer-reduction-decodes-double-cover
  - bcv-every-perfect-question-reduction-amplifies-readable-closure
---

Use the notation in the proof of BCV Theorem 7.1. At index `n` it defines

```text
V^(1)=QuestionReduction_h(V,lambda),
V^(2)=AnswerReduction_(3,h)(V^(1),lambda),
V^(3)=ParRep_3(V^(2),K)=Compress_h(V,lambda).            (UCP1)
```

Theorem 6.8 gives the exact combinatorial identity

```text
V^(3)_n
 = (DeType(Anchor(V^(2)_n)))^(tensor K(n)).              (UCP2)
```

We invert these transformations in reverse order.

## 1. An arbitrary perfect tensor strategy has an exact first-coordinate restriction

Put `H=DeType(Anchor(V^(2)_n))`. There is a distinguished zero-answer
vertex `o` of `H` with a positive self-loop. Indeed, in Definition 4.40
the all-zero seed satisfies

```text
s_A(0)=s_B(0)=0=o
```

by the explicit zero-out clauses in the two detyping maps. This is an
A-player and B-player anchor vertex, its readable and unreadable lengths
are both zero, and every incident test autoaccepts. Uniform finite seeds
give the loop `oo` positive weight.

Let `R` be a perfect strategy for `H^(tensor r)`, where `r=K(n)>=1`.
For each supported question `x` of `H`, take the PVM of `R` at

```text
(x,o,...,o)
```

and marginalize its answer to the first coordinate. For every supported
edge `xy` of `H`, the tensor edge

```text
((x,o,...,o),(y,o,...,o))
```

has positive weight: its first coordinate has the weight of `xy` and every
other coordinate has the positive weight of `oo`. Definition 3.43 and
Section 6.2 say that the tensor predicate is the product of the coordinate
predicates. Perfectness of `R` therefore makes the first coordinate pass
the predicate of `H` exactly. The same restriction preserves synchrony and
edge commutation.

Definition 6.2 and the tensor answer split in Section 6.2 place the first
coordinate's readable variables in the target readable answer and its
linear variables in the target unreadable answer. Hence the restricted
strategy is ZPC. Every restricted generator is a target generator, so
induction on unreadable words gives

```text
D_infinity(R|H) subseteq D_infinity(R).                  (UCP3)
```

No product-form assumption on `R` is used.

## 2. Detyping and anchoring invert by restriction at zero loss

The type graph of the Answer Reduced game `V^(2)_n` has every self-loop:
Definition 5.79 takes the tensor product of the Player and Space type
graphs and explicitly includes all their loops. Definition 6.2 preserves
those loops and adds every edge incident to the new Anchor type, including
the Anchor loop. Thus `Anchor(V^(2)_n)` satisfies the hypothesis of
Corollary 4.43.

More concretely, Remark 4.41 restricts a perfect strategy for

```text
DeType(Anchor(V^(2)_n))
```

to the A- and B-copy vertices and obtains a perfect strategy for the double
cover. Every supported typed vertex has a positive synchronization loop,
as computed in the proof of Corollary 4.43. Claim 3.54 at error zero
identifies its two sheet PVMs. Selecting one sheet therefore gives a
perfect ZPC strategy for `Anchor(V^(2)_n)` in the same dimension. Definition
6.2 then discards the zero-answer Anchor vertex and gives a perfect ZPC
strategy for `V^(2)_n`; equation `(214)` also states this value-one
equivalence strategy by strategy. All these operations select existing
measurements, so

```text
D_infinity(V^(2)_n strategy)
  subseteq D_infinity(V^(3)_n strategy).                 (UCP4)
```

## 3. Exact Answer Reduction reaches the typed Question Reduced game

Apply `bcv-perfect-answer-reduction-decodes-double-cover` to the strategy
for `V^(2)_n`. The field chosen in the algorithmic construction satisfies
the required `q>63m` condition. The joint polynomial-table decoder first
gives the exact source double cover in the same matrix algebra.

The actual input `V^(1)_n` has the special form supplied by Theorem 4.36:

```text
V^(1)_n
 = DeType(Q_n),

Q_n
 = QueRed(Padding(V_(2^n),2^(lambda n)),
          2^(lambda n),B(lambda n)).                     (UCP5)
```

Definition 4.40 makes the non-anchor part of `DeType(Q_n)` bipartite, so
opposite sheet selection recovers it from its double cover. Restricting to
the A- and B-copy vertices gives `DoubleCover(Q_n)`, and Figure 14 gives
every type of `Q_n` a self-loop. Corollary 4.43 and Claim 3.54 therefore
return a perfect ZPC strategy for `Q_n` exactly. The detailed polynomial
and wrapper proof is
`bcv-exact-answer-reduction-decoder-proof`. It also proves throughout that

```text
D_infinity(Q_n strategy)
  subseteq D_infinity(V^(2)_n strategy).                 (UCP6)
```

## 4. The exact Question Reduction normal form forces the tensor factor

The Pauli parameter in `(UCP5)` is

```text
k(n)=2^(lambda n).
```

Apply
`bcv-every-perfect-question-reduction-amplifies-readable-closure`
to the decoded perfect strategy for `Q_n`. It gives a perfect ZPC strategy
`T_pad` for `Padding(V_(2^n),2^(lambda n))` and a monomial identification
under which

```text
ell^infinity(F_2^k(n)) tensor D_infinity(T_pad)
  subseteq D_infinity(Q_n strategy).                     (UCP7)
```

Fact 4.48 unpads by discarding dummy coordinates. It returns a perfect ZPC
strategy `T` for the supported part of `V_(2^n)` and

```text
D_infinity(T) subseteq D_infinity(T_pad).                (UCP8)
```

Combining `(UCP3)--(UCP8)` proves `(UCA1)`. The SamZ algebra has exactly
`2^k(n)` atoms, and every nonzero finite Boolean algebra has dimension at
least one. This proves `(UCA2)`.

The assumptions used here are exact and explicit: `V` is
`lambda`-bounded so that `(UCP5)` is the actual game identity,
`n>=C(h)` and `K(n)>=1` so every construction is defined, and only
vertices or edges in the sampler support are decoded. Trivial extension
off support makes the output a strategy on the full formal question set
without changing its value or the inclusion.
