# Coset hyperlinearity equivalence: primary-source audit

Date: 2026-09-07. This is a bounded literature audit, not a novelty certificate
or an independently verified proof of the proposed equivalence.

The proposed statement concerns every countable pair `C <= A`, with

```text
W = (direct_sum_(A/C) C2) rtimes A,
F = (free_product_(A/C) C2) rtimes A,
D = A *_C A,
H = A *_C (C x Z).
```

It identifies hyperlinearity of these four groups with relative
embeddability over scalars of `L(C) subset L(A)`. Searches of the sources
below did not locate that full statement or an explicit contradictory
result. Failure to locate a precedent does not establish originality.

## Exact Gaussian limit precedent

Greg Kuperberg, *A tracial quantum central limit theorem*, Transactions of
the AMS 357 (2005), 459–471,
[arXiv:math-ph/0202035](https://arxiv.org/pdf/math-ph/0202035), **Theorem 2**
and its proof, PDF pages 3–4, are directly relevant. Given centered bounded
selfadjoints `a_1,...,a_k` in a tracial algebra, set

```text
S_(i,n) = n^(-1/2) sum_(r=1)^n a_i^(r).
```

Ordered products of bounded continuous functions of these tensor sums
converge to the corresponding classical Gaussian expectations, with
covariance `tau(a_i a_j)`. Repeating variables accommodates arbitrary
ordered words. This supplies the needed joint conclusion, rather than
only scalar central-limit convergence. Theorem 1 concerns the spectral
distribution of noncommutative polynomials and is a less direct citation.
Neither theorem states a group crossed-product hyperlinearity result.

For the proposed application, orthogonal involution lamps have covariance
`delta_(x,y)`. The additional proof obligations are the passage to signs
and the trace of words involving the actor. Signs require continuous
smoothing at zero and control of the spectral mass near zero; the Gaussian
limit gives that control. Diagonal actor unitaries require a separate
mixed-trace calculation. Neither obligation should be silently attributed
to the cited central-limit theorem.

## Exact relative embeddability precedent

Weichen Gao, *Relative Embeddability of von Neumann Algebras and
Amalgamated Free Products*,
[arXiv:2012.07940, Appendix Theorem 7.1](https://arxiv.org/html/2012.07940#S7),
proves, for a finite-factor reference algebra `N_1`, that `RE/N_1` is
equivalent to embeddability of the enlarged double
`(M tensor L^infinity(S^1)) *_N M` into `(R tensor N_1)^omega`. The plain
double is stated to be included under the additional hypothesis of a unitary
`u in M` with `E_N(u^n)=0` for every nonzero integer `n`.

Thus `N_1 = C` satisfies the factor requirement, but citing this theorem
alone does not prove the proposed plain-double equivalence for every
subgroup. The finite-involution centralizer/tensor argument and the group
bridge between `D` and `F` are additional arguments. There is also a
proof issue beyond the stated hypothesis: on printed page 35 the bottom
arrow of the proposed square requires the chosen unitary to commute with
the amalgamating algebra. The arithmetic diagonal does not. The
independent [HNN/source audit](centralizer-hnn-relative-embedding-audit-2026-09-07.md)
checks this explicitly. The new tensor proof establishes the group result
independently; this audit makes no claim that the general algebraic
theorem's statement is false.

## Sofic-action results and their precise scope

David Gao, Srivatsav Kunnawalkam Elayavalli, and Gregory Patchell,
*Soficity for group actions on sets and applications*, Research in the
Mathematical Sciences 12 (2025), 48,
[Theorems 3.8–3.9 and Corollary 3.10](https://link.springer.com/article/10.1007/s40687-025-00526-6),
prove hyperlinear/Connes-embeddable permanence for ordinary and free
generalized wreath products assuming a hyperlinear actor and a **sofic
action on the index set**. They do not state the proposed equivalence
without the action hypothesis. Their Question 4.4 asks whether ordinary
wreath-product soficity forces soficity of the index action.

Definition 2.1 uses injective charts of a finite subset of the index set
into another finite set, with charts depending on points in a large subset
of the approximation space. It does not require one global positive-trace
orthogonal coset partition, exact finite representations of the actor, or
subgroup separability. Replacing these moving charts by one of those
stronger objects changes the hypothesis.

In particular, a prospective hyperlinear matrix/centralizer condition
must not simply be called a sofic action. The cited permanence theorem
gives a sufficient route to that matrix condition if the proposed
equivalence is proved; strictness or a converse would need separate work.

Vadim Alekseev and Henry Bradford,
*Sofic actions, halo products, and metric approximations of groups*,
[arXiv:2601.18742v1](https://arxiv.org/html/2601.18742v1), Theorem 1.1,
Proposition 1.2, and Example 1.3, extend and unify semidirect-product
permanence through their sofic class-actions. Their applications to
ordinary, free, and other halo products retain the sofic index-action
hypothesis. The inspected paper does not state a relative-embeddability
criterion or a Gaussian proof of ordinary/free equivalence.

## Repository overlap and remaining distinction

The closest local work already present is:

- `research/fd-fell-gaussian-wreath-proof.md`: Gaussian signs convert
  approximate coset coefficients from finite-image actor representations
  into Bernoulli moments. Connes embeddability there uses finite image and
  a finite-extension crossed-product argument.
- `research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md`:
  the earlier arithmetic application, now corrected to use the tensor
  proof because the printed commutant inclusion was not justified.
- `research/centralizer-hnn-free-wreath-proof.md`: the algebraic
  identification of the centralizer HNN group with a free wreath having
  infinite cyclic lamps.
- `research/sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary.md`:
  the moving-chart action model is distinguished from stronger global
  coset models.

The proposed tensor CLT argument starts instead from a trace-preserving
embedding of the free binary wreath algebra and takes tensor powers of
its complete actor-and-lamp model. This avoids the finite-image actor
hypothesis in the existing Gaussian-sign route. The substantive new work
to verify is therefore the unrestricted implication `F hyperlinear => W
hyperlinear`, the finite-lamp expectation construction of relative
embeddability, and their combination with the group embeddings. The cited
sources support ingredients; they do not by themselves certify that
combined theorem or produce a nonhyperlinear example.
