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

The conclusion has two separate gates.  The first is whether Lin's separated
synchronous game is supplied with the **oracularizable** perfect commuting
strategy required by the Mastel--Slofstra BCS conversion.  The second is the
strictly stronger passage from a general weighted BCS to parity/LCS syntax.

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

## 2. Lin's exact output and the oracularity hypothesis

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
oracularity hypothesis below.  One may use the BCS conclusion whenever one
has separately followed Lin's particular compression construction to a
preserved oracularizable perfect strategy, but that extra fact must be named;
it cannot be inferred merely from `omega_co(G)=1` for a synchronous game.

This distinction is real.  In the tracial realization of a synchronous
commuting correlation, the projections for two different questions need not
commute in the same one-player algebra.  Commuting left/right actions do not
automatically give the joint one-player PVM needed for an edge context.

## 3. The exact conditional BCS conversion

Mastel--Slofstra Lemma 3.1 takes a synchronous game `G` to its
oracularization `G_orac`.  It proves:

1. a perfect oracularizable synchronous strategy for `G` gives a perfect
   synchronous strategy for `G_orac`; and
2. if `omega_q(G_orac)=1-epsilon`, then
   `omega_q(G)>=1-poly(epsilon)`.

Immediately after the lemma, the paper constructs a Boolean constraint system
`B(G)` with

```text
G(B(G),pi_orac) = G_orac.                                (LJM4)
```

Consequently, if the separated Lin game in `(LJM3)` is accompanied by a
perfect oracularizable commuting strategy, then `(LJM4)` is a finite weighted
BCS with perfect commuting value and a dimension-independent quantum gap.
Indeed Lemma 3.1 contraposed at `omega_q(G)<=1/2` supplies some absolute
`delta>0` for which

```text
omega_co(G(B(G),pi_orac))=1,
omega_q (G(B(G),pi_orac))<=1-delta.                       (LJM5)
```

The paper writes the loss only as `poly(epsilon)`, so these sources do not
identify a numerical value of `delta`.

The weighted algebraic structure is genuine.  Definitions 4.1--4.2 define
weighted star-algebras and the weighted BCS algebra; Lemma 4.3 identifies
strategy loss with tracial defect.  Definition 5.1 and Lemma 5.2 give
weighted homomorphisms and the defect pullback inequality.  Proposition 5.3,
Lemma 5.6, and Corollary 5.7 control changes of weights and private context
extensions.  Proposition 6.3 preserves exact perfect quantum and commuting
strategies under subdivision, while Theorem 6.4 pulls a near-perfect
subdivision strategy back with loss

```text
poly(m,2^C,M,K) epsilon.                                  (LJM6)
```

Remark 5.8 applies Cook--Levin contextwise, and Propositions 8.4--8.5 preserve
perfect quantum/commuting completeness and pull synchronous soundness back
through the 3SAT/tableau construction.  Theorem 8.8 says

```text
PZK-BCS-MIPco(2,1,1,1-1/poly(n))
  = BCS-MIPco(2,1,1,1-1/poly(n)).                         (LJM7)
```

It is an equivalence **inside the class of already existing BCS-MIPco
protocols**.  It does not assert `MIPco=BCS-MIPco` and does not remove the
oracularity gate in `(LJM5)`.

## 4. Why the chain stops before LCS and a solution group

The output of `(LJM4)--(LJM7)` has arbitrary Boolean predicates; after
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

The strongest rigorous conclusion from the three sources is therefore:

```text
Lin separated synchronous game
 + separately certified perfect oracularizable commuting strategy
 + Mastel--Slofstra Lemma 3.1
 => perfect-commuting / quantum-gap weighted BCS (and a 3SAT/tableau form),

but not an LCS and not a solution group.                  (LJM8)
```

At the theorem-statement level, without the separately certified
oracularizable strategy, the chain stops one step earlier, at Lin's
synchronous value separation `(LJM3)`.
