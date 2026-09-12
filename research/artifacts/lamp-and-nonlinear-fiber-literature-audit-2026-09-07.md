# Lamp permanence and nonlinear certificate fibers: literature audit

Date: 2026-09-07. Scope: bounded primary-source search and theorem comparison.
Failure to locate an exact statement does not establish novelty. This audit
does not certify either universal headline conjecture.

## Restricted wreath products

The current untwisted result says that, for a field k, a LEF lamp group A,
and any G-set X, k[A wr_X G] is stably finite exactly when k[G] is.
The accompanying monomial-action route uses finite lamps, or separating
finite lamp quotients invariant under the internal automorphisms; finitely
generated RF lamps have characteristic finite quotients supplying this
condition. These statements retain a stably finite base algebra as a
hypothesis, and concern restricted lamp support.

The following sources supply related ingredients, with materially different
scopes:

- [Federico Berlai, *Groups satisfying Kaplansky's stable finiteness
  conjecture*](https://arxiv.org/abs/1501.02893), Main Theorem, treats
  finitely generated RF kernels and **sofic quotients**, with noetherian
  coefficient rings. Lemma 2.4 supplies characteristic finite-index cores;
  Proposition 3.1 transfers direct/stable finiteness through marked-group
  limits using finite multiplication patterns. This does not subsume an
  arbitrary base whose group algebra is merely assumed stably finite, or
  remove the kernel hypotheses for a general extension.
- [Gabor Elek, *On algebras that almost have finite dimensional
  representations*](https://arxiv.org/abs/math/0311376), Proposition 1.1,
  proves LEF algebras stably finite by transferring a finite inverse witness
  into matrices. The coefficient-ring lemma R stably finite and A LEF
  implies R[A] stably finite uses the same exact finite-pattern mechanism,
  together with the regular embedding R[L] into matrices over R for finite L.
- [Benjamin Steinberg, *Stable finiteness of ample groupoid algebras,
  traces and applications*](https://arxiv.org/abs/2207.11194), Theorem 4.1,
  uses a dense union of **closed discrete orbits** with stably finite
  isotropy algebras. Its orbit-matrix method is relevant, but the theorem
  does not directly apply to the whole marked-site space: translating a
  nonempty finite support can converge to the vacuum. Theorem 4.6 also
  requires finiteness of relevant idempotent classes below each fixed
  idempotent, which an infinite orbit of marked-site idempotents below 1
  need not satisfy.
- [Henry Bradford and Francesco Fournier-Facio, *Hopfian wreath products
  and the stable finiteness conjecture*](https://arxiv.org/abs/2211.01510),
  relates Hopficity of wreath products to inverse identities over the
  **base** group algebra. It does not state the present stable-finiteness
  permanence for the wreath product's own group algebra.

No source inspected in this search states the full diagonal-induction
permanence theorem with these exact hypotheses. The finite-pattern and
characteristic-core steps should nonetheless be identified as established
methods, rather than presented as newly invented ingredients.

## Nonlinear finite-output perturbations

There is a direct antecedent for the counting argument in [Xuan Kien
Phung, *On reversible asynchronous non-uniform cellular
automata*](https://arxiv.org/abs/2201.13283), proof of Theorem 9.1, printed
pages 15-16 of the inspected arXiv PDF. The published article is [*On
invertible and stably reversible non-uniform cellular
automata*](https://doi.org/10.1016/j.tcs.2022.09.011). The cited theorem
assumes an amenable universe and an injective finite perturbation of a
constant rule configuration. Amenability first supplies surjectivity of
the background CA. The subsequent finite-cylinder argument is precisely
the following elementary lemma, with no remaining group assumption:

Let A be finite and nonempty, E a finite subset of an arbitrary index set
I, and S,T:A^I -> A^I agree outside E on every input. If S is injective
and T is surjective, both maps are bijective. Indeed, for every fixed
outside-E output, its cylinder V has |A|^|E| elements. Surjectivity gives
|T^(-1)(V)| >= |V|, whereas S injects T^(-1)(V) into V. Equality follows;
both restrictions are bijections. These cylinders partition the target.
In particular, assuming T bijective is sufficient but stronger than needed.

For an injective CA (x,c) -> (T_c(x),c) on independent finite-alphabet
full shifts, finite changes of c alter only finitely many output cells.
If one fiber is bijective, the lemma makes its entire finite-change class
bijective. That class is dense; compactness and continuity make the set
of surjective fibers closed. Therefore all fibers are bijective, or all
are injective and nonsurjective. This last full-certificate consequence
was not located as an explicit statement in the sources inspected; its
counting ingredient has the antecedent above. Arbitrary constrained
certificate spaces need not have a dense finite-change class.

[Phung's *Stable finiteness of twisted group rings and noisy linear
cellular automata*](https://doi.org/10.4153/S0008414X23000329), Theorems A-C,
is a related linear precursor concerning finite perturbations and the ring
D^1(k[G]). Its term "twisted group ring" refers to that operator-ring
construction, not to internal automorphism twists of wreath lamps.
