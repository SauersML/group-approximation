# Lin--Ji--Mastel--Slofstra: the exact BCS/LCS boundary

Date: 2026-08-23

## Sources audited

This audit uses the three primary files supplied by the user:

- Junqiao Lin, *MIPco = coRE*, arXiv:2510.07162v1;
- Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry
  Yuen, *Quantum soundness of the classical low individual degree test*,
  arXiv:2009.12982v1;
- Kieran Mastel and William Slofstra, *Two Prover Perfect Zero Knowledge for
  MIPstar*, STOC 2024.

The conclusion distinguishes two BCS conversions and one later gate.
Mastel--Slofstra's generic finite synchronous-game-to-BCS construction is
unconditional but exponentially enlarges answers.  Their oracularization is
the efficient protocol-level conversion and needs an **oracularizable**
perfect strategy.  After either conversion, the strictly stronger passage
from a general weighted BCS to parity/LCS syntax remains absent.

## 1. What the low-individual-degree theorem actually supplies

Ji--Natarajan--Vidick--Wright--Yuen Theorem 1.3 is the informal main theorem.
Its formal version is Theorem 3.10.  If a projective two-prover tensor-product
strategy passes the `(m,q,d)` low individual degree test with probability at
least `1-epsilon`, then for every integer `k>=md` there are projective global
polynomial measurements `G^A,G^B`, with consistency and self-consistency
error

```text
nu = 100000 k^2 m^4
     (epsilon^(1/40000) + (d/q)^(1/40000)
      + exp(-k/(2560000m^2))).                         (LJM1)
```

This is a measurement-extraction/rounding theorem.  It does not output a
Boolean constraint system, linear equations, a weighted star-algebra
homomorphism, or a solution group.  Lin uses the low-individual-degree test
inside answer reduction and explicitly treats the commuting/tracially
embeddable soundness extension separately.  Thus the 2009 source is an
analytic soundness input to Lin's verifier construction, not an algebraic
BCS-to-LCS compiler.

## 2. Lin's exact output and where oracularity matters

Lin's Theorem 6.5 is the gap-compression theorem.  It produces synchronous
seventh-level conditionally-linear verifiers and preserves a perfect
**oracularizable** strategy in either the tensor-product or commuting model;
its soundness implication is

```text
omega^t(G)<=1/2  =>  omega^t(G_comp)<=1/2,
                         t in {*,co}.                    (LJM2)
```

Theorem 6.15 is the `1/2` Bell-separation RE-completeness theorem.  Its proof
paragraph identifies the separated promise class as synchronous twelfth-level
conditionally-linear games satisfying

```text
omega_co(G)=1,             omega_*(G)<=1/2.              (LJM3)
```

The statement of Theorem 6.15 itself records values and synchrony, not the
existence of a perfect oracularizable commuting strategy.  Theorem 6.5 only
preserves such a strategy **if the input already has one**.  Therefore a
black-box citation of Theorem 6.15 does not by itself discharge the
hypothesis of the **efficient oracularization** below.  This does not block
the unconditional fixed finite BCS construction in the next section.

This distinction is real.  In the tracial realization of a synchronous
commuting correlation, the projections for two different questions need not
commute in the same one-player algebra.  Commuting left/right actions do not
automatically give the joint one-player PVM needed for an edge context.

## 3. Unconditional fixed BCS versus conditional efficient BCS

Immediately before Lemma 3.1, Mastel--Slofstra recall the generic conversion
of every synchronous game `G` to a BCS.  It introduces a Boolean variable
`x_(i,a)` for every question/answer pair, a one-answer constraint for each
question, and a constraint

```text
x_(i,a) and x_(j,b)=false
```

for every losing answer pair.  They state that the resulting game `G_raw`
has a perfect quantum, quantum-approximable, or commuting strategy if and
only if `G` does.  They also state an answer-size-dependent quantitative
loss, exponential at the protocol level.  Since Lin's `G_loop` is one fixed
finite effective game with `omega_q<=1/2`, the loss remains a strict,
effectively determined constant:

```text
omega_co(G_raw)=1,
omega_q (G_raw)<=1-delta_loop,       delta_loop>0.        (LJM4)
```

No oracularity assumption is used in `(LJM4)`.  The price is exponential
answer blowup, irrelevant for this fixed object but unsuitable for a
polynomial-size protocol-family conversion.

For the efficient route, Mastel--Slofstra Lemma 3.1 takes a synchronous game
`G` to its oracularization `G_orac`.  It proves:

1. a perfect oracularizable synchronous strategy for `G` gives a perfect
   synchronous strategy for `G_orac`; and
2. if `omega_q(G_orac)=1-epsilon`, then
   `omega_q(G)>=1-poly(epsilon)`.

Immediately after the lemma, the paper constructs a Boolean constraint system
`B_orac(G)` with

```text
G(B_orac(G),pi_orac) = G_orac.                           (LJM5)
```

Consequently, if the separated Lin game in `(LJM3)` is accompanied by a
perfect oracularizable commuting strategy, then `(LJM5)` is a finite weighted
BCS with perfect commuting value and a dimension-independent quantum gap.
Indeed Lemma 3.1 contraposed at `omega_q(G)<=1/2` supplies some absolute
`delta>0` for which

```text
omega_co(G(B_orac(G),pi_orac))=1,
omega_q (G(B_orac(G),pi_orac))<=1-delta.                  (LJM6)
```

The paper writes the efficient loss only as `poly(epsilon)`, so these sources
do not identify a numerical value of `delta`.

The weighted algebraic structure is genuine.  Definitions 4.1--4.2 define
weighted star-algebras and the weighted BCS algebra; Lemma 4.3 identifies
strategy loss with tracial defect.  Definition 5.1 and Lemma 5.2 give
weighted homomorphisms and the defect pullback inequality.  Proposition 5.3,
Lemma 5.6, and Corollary 5.7 control changes of weights and private context
extensions.  Proposition 6.3 preserves exact perfect quantum and commuting
strategies under subdivision, while Theorem 6.4 pulls a near-perfect
subdivision strategy back with loss

```text
poly(m,2^C,M,K) epsilon.                                  (LJM7)
```

Remark 5.8 applies Cook--Levin contextwise, and Propositions 8.4--8.5 preserve
perfect quantum/commuting completeness and pull synchronous soundness back
through the 3SAT/tableau construction.  Theorem 8.8 says

```text
PZK-BCS-MIPco(2,1,1,1-1/poly(n))
  = BCS-MIPco(2,1,1,1-1/poly(n)).                         (LJM8)
```

It is an equivalence **inside the class of already existing BCS-MIPco
protocols**.  It does not assert `MIPco=BCS-MIPco` and does not remove the
oracularity gate for the efficient route `(LJM5)--(LJM6)`.  That gate is not
needed for the fixed raw conversion `(LJM4)`.

## 4. Why the chain stops before LCS and a solution group

The output of either `(LJM4)` or `(LJM5)--(LJM8)` has arbitrary Boolean
predicates; after
Cook--Levin it has 3SAT predicates.  None of the three sources replaces those
predicates by affine parity constraints while preserving the tracial defect
gap.  The Mastel--Slofstra weighted homomorphisms apply only to the explicitly
constructed context extensions, subdivisions, Cook--Levin encodings, and
tableaux.  No weighted homomorphism to an LCS algebra is stated.

This is exactly the missing structure needed for a solution group.  LCS
relations are products of commuting involutions equal to a central sign, so
their joint classical support is affine over `F_2`; projections of affine
supports along commuting auxiliary variables remain affine.  A general BCS
or 3SAT satisfying set is nonaffine.  Thus the phrase "compile the BCS to its
solution group" is not defined without a new nonabelian gadget and a
dimension-independent defect decoder.

The strongest rigorous fixed-game conclusion from the three sources is
therefore:

```text
Lin separated synchronous game
 + unconditional generic finite BCS conversion
 => effectively named perfect-commuting / quantum-gap weighted BCS
    (and a 3SAT/tableau form),

but not an LCS and not a solution group.                  (LJM9)
```

For a polynomial-size protocol-family conversion, the generic construction
has exponential answer blowup; the efficient oracularized construction still
requires the separately certified perfect oracularizable strategy.  This
efficiency distinction does not weaken the fixed-object conclusion `(LJM9)`.
