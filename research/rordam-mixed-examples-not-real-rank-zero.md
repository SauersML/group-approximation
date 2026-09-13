---
rg: 2
id: rordam-mixed-examples-not-real-rank-zero
kind: claim
title: Rordam's simple algebras with a finite and an infinite projection have nonzero real rank but property (SP)
---

**Theorem (Rordam, *The real rank of certain simple C\*-algebras*, 2005,
Corollaries 4.2 and 4.6, Propositions 5.3 and 5.5).**  Let `B` be the simple
non-separable algebra and `D rtimes_alpha Z` the simple separable nuclear UCT
algebra from Rordam's Acta 2003 paper (Theorem 6.10 there), each containing an
infinite projection and a nonzero finite projection.  Then neither `B` nor
`D rtimes_alpha Z` has real rank zero, and both have property (SP): every
nonzero hereditary subalgebra contains a nonzero projection.

**Mechanism.**  Take `Z = product of countably many S^2` and the Bott line
projection `p_1` on the first sphere.  With `lambda: S^2 -> [-1,1]` extending a
diffeomorphism of an embedded arc and `lambda_2` its composition with the
second coordinate, the self-adjoint element `a = lambda_2 p_1` pushed to the
limit has distance `1` from the self-adjoint invertibles of the corner
`Q B Q`, where `Q` is the image of `p_1` (Proposition 4.1).  If an invertible
`b` were closer, then

1. at some finite stage the coordinate `s_n` carrying the sign change is not
   used by any index set in the tensor-product decomposition
   `Q_n ~ direct_sum_I p_I` (Lemma 3.1);
2. Villadsen's transversality (Proposition 2.2) perturbs the function in `b`
   to one whose zero set `N` is a finite CW complex with `H^*` of the other
   coordinates injecting into `H^*(N)`;
3. on `N` the corner of `b` along a subprojection `q_n ~ p_(r_n)` vanishes, so
   Villadsen's Lemma 2.1 (`pap = 0` with `a` invertible gives
   `p <~ 1 - p`) yields `q_n direct_sum q_n <~ Q_n` over the preimage of `N`,
   hence a trivial line `g <~ Q_n` there;
4. that contradicts nonvanishing of the Euler class of
   `direct_sum_(I in J_0) p_I`, which survives on `N` by injectivity and the
   Kunneth formula (Lemma 3.2).

So in these examples the finiteness certificate is a cohomological invariant
of the base.  Generic spectral cuts keep it alive, and real rank zero fails
exactly because spectral cutting would have to kill it.  The same paper
records, page 2: "This has relevance for the still open problem if all simple
infinite C\*-algebras of real rank zero must be purely infinite."
