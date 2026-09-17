---
rg: 2
id: z3-heawood-incidence-system-has-a-finite-dimensional-solution
kind: claim
title: The Heawood incidence system over Z_3 has a finite-dimensional operator solution and no classical solution, answering the p=3 case of Slofstra-Zhang Problem 2.9
artifacts:
  - experiments/odd-p-incidence-pquotient-2026-09-17/verify_monomial.py
  - experiments/odd-p-incidence-pquotient-2026-09-17/heawood_p3_monomial.json.gz
  - experiments/odd-p-incidence-pquotient-2026-09-17/pq.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/reduce.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/monomial.g
  - experiments/odd-p-incidence-pquotient-2026-09-17/RESULTS.md
distinct_from:
  high-girth-incidence-gives-uniform-quantum-classical-separation: that gives, for odd p, only possibly infinite-dimensional operator solutions; this gives an explicit finite-dimensional one (dimension 3^8) for the Heawood graph at p=3 and finite p-group certificates for four more cubic girth-six graphs.
  lcs-occurrence-two-qc-equals-q: that is Arkhipov's binary theorem, where Pauli operators suffice; at p=3 no generalized Pauli (or any nilpotent class-two) model exists, and the certificate here lives in a 3-group of nilpotency class exactly three.
  slofstra-zhang-high-girth-phase-survival: that proves order(J)=p through planar pictures; this proves the stronger statement that J survives in a finite quotient, for these specific graphs.
  lcs-phase-dies-in-every-nilpotent-quotient-of-class-below-p: that shows class p is the least nilpotency class that can carry such a certificate; this shows class p=3 is attained.
---

Let `H` be the Heawood graph (vertices `0..13`, edges `{i,i+1}` and
`{i,i+5}` for even `i`, indices mod 14), orient every edge `(tail,head)` as
listed, and let `I(H)x=b` be the oriented incidence system over `Z_3` with
`b=delta_0`.  Write `Gamma_3(H,b)` for its solution group: generators `x_e`
(21 edges) and `J`, with `x_e^3=J^3=1`, `J` central, `x_e x_f=x_f x_e` when
`e,f` share a vertex, and `prod_{e at v} x_e^{sigma(v,e)} = J^{b_v}`.

**Claim.**

1. `sum_v b_v = 1 != 0 mod 3`, so `I(H)x=b` has no classical solution.
2. There are `3^8 x 3^8` unitary matrices `X_e`, each a monomial matrix with
   cube-root-of-unity entries, such that `X_e^3=I`, `X_e X_f = X_f X_e`
   whenever `e,f` meet, and `prod_{e at v} X_e^{sigma(v,e)} = omega^{b_v} I`
   with `omega=exp(4 pi i/3)`.  Hence the linear-system game of `I(H)x=b`
   over `Z_3` has a perfect finite-dimensional quantum strategy but no perfect
   classical strategy.
3. Equivalently `J` survives in a finite quotient of `Gamma_3(H,b)`; one such
   quotient is a 3-group of order `3^17`, nilpotency class `3`, exponent `9`,
   with cyclic centre `<J>`.
4. (Computational, GAP `EpimorphismPGroup`.)  For `p=3`, `J` survives in the
   class-3 3-quotient of `Gamma_3(G,delta_0)` for each of the cubic girth-six
   graphs Heawood, Moebius-Kantor, Pappus and Desargues and for the Tutte
   8-cage, and dies in the class-`<=2` quotient in every case.  `J` does not
   survive in the class-`<=4` 3-quotient for `K_{4,4}` or the Petersen graph.

Slofstra and Zhang (arXiv:2412.10305, Problems 2.9-2.10) ask whether an
incidence system over `Z_p` with `p` odd can have a finite-dimensional operator
solution without a classical solution; Qassim-Wallman ruled out generalized
Pauli solutions.  Item 2 answers the question for `p=3` with an explicit
certificate.  Ciardo (arXiv:2609.14632) proves existence of unsatisfiable
linear systems mod `n` with finite-dimensional perfect strategies for a
homomorphism-game model via group-valued measures; that result neither
concerns graph incidence systems nor produces the commuting-observable
solution group representation here.

**Consequence for the flagship.**  The odd-modulus high-girth incidence groups
were natural candidates for nonhyperlinear solution groups because no Pauli
model exists and their quotient `Gamma/<J>` acts on a CAT(0) triangle
complex.  For the five graphs in item 4 the candidate is dead: `J` survives
in a finite quotient, so there is no R^U gap.  The graph-minor monotonicity
recorded in the proof route shows every graph containing one of them as a
minor is dead too.

**ESTABLISHED** by `z3-heawood-exact-monomial-certificate`.  Item 2 is checked
by an exact integer script independent of GAP.  Item 4 rests on GAP's
p-quotient algorithm and is recorded as computation.
