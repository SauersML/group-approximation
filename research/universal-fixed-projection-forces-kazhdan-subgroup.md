---
rg: 2
id: universal-fixed-projection-forces-kazhdan-subgroup
kind: claim
title: If an element of the maximal group algebra of any overgroup acts as the fixed-vector projection of a subgroup N, or as a uniform gap element for N, in the induced and quasi-regular representations, then N has property (T)
distinct_from:
  z-direct-factor-kills-intrinsic-t-substitutes: that kills subgroup-intrinsic replacements of (T) for the compressed subgroup L by an MF countermodel; this kills overgroup-relative but model-independent replacements, such as relative (T) of a pair (Gamma,N) or a uniform relative Kesten gap, by showing that the certificate they would have to supply already forces absolute (T) of N. No countermodel is involved.
  root-column-fixed-projection-is-not-in-root-pair-cstar: that is a per-model statement for one root pair, and says P_N is not in C*(sigma~(K)) in delta_e-profile coronas; this is a universal statement for every pair N <= Gamma, and says no element of C*_max(Gamma) is P_N in the induced and quasi-regular representations unless N is Kazhdan. It does not decide per-model membership.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates a per-model spectral gap (MSG) as the only Kazhdan input of transport; this shows that a uniform, model-independent version of that gap for a subgroup N is equivalent to (T) of N.
  relatively-kazhdan-amenable-pairs-allow-sofic-defects: that refutes the relative-(T) compression criterion for sofic approximations by a countermodel, and kills the route left-orderable-non-sofic-via-relative-kazhdan-defect-criterion; this names the operator-algebraic reason in the MF setting. The relative (T) pair gives no projection in the maximal algebra.
  k-amenable-compressors-need-infinite-projections: that constrains the defect projection of a K-amenable compressor; this constrains the transport projection of any compressor.
artifacts:
  - research/universal-fixed-projection-forces-kazhdan-subgroup-proof.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED CLASS KILL (written proof; elementary, no imported results; not Lean-verified).**

**Setting.**
- `Gamma` is a countable discrete group and `N <= Gamma` is any subgroup. `N`
  need not be normal or finitely generated.
- `C*(Gamma)` is the maximal group C*-algebra.
- For a unitary representation `rho` of `Gamma`, `F_rho` is the orthogonal
  projection onto `Fix rho(N)`.
- `lambda_(Gamma/N)` is the quasi-regular representation on `l^2(Gamma/N)`.
- `Ind sigma = Ind_N^Gamma sigma` is the induced representation, for `sigma` a
  unitary representation of `N`.

**Theorem.** Let `x in C*(Gamma)` be self-adjoint. Assume that for every
`rho` in the family `{lambda_(Gamma/N)} union {Ind sigma : sigma a unitary rep of N}`:
- (G1) `rho(x)` fixes `Fix rho(N)` pointwise;
- (G2) `||rho(x) restricted to (Fix rho(N))^perp|| <= 1 - epsilon`, for one
  `epsilon > 0` that does not depend on `rho`.

Then `N` has property (T).

The main case is `x = p` with `rho(p) = F_rho` for every `rho`, a "universal
N-fixed projection", which satisfies both conditions with `epsilon = 1`. The
converse holds by the classical theory: if `N` has (T), its Kazhdan projection
`p_N in C*(N) subset C*(Gamma)` works. So:

> **A universal N-fixed projection exists in C*(Gamma), for any overgroup
> Gamma, if and only if N is Kazhdan.**

**Refinement (class-restricted form).** Let `D` be a class of unitary
representations of `N`. Require (G1) and (G2) only for `lambda_(Gamma/N)` and for
`Ind sigma`, `sigma in D`. Then every `sigma in D` that has almost invariant
vectors has a nonzero invariant vector. The same proof applies.

**What this kills (the class).** It kills every attempt to run Step 1 (transport)
of the one-sided compression criterion (`non_mf_groups_exist.tex`,
Theorem `thm:transport`) with a **model-independent** substitute for the
Kazhdan projection of a non-Kazhdan subgroup `N`. Such a substitute is any
element of `C*(Gamma)` for some overgroup `N <= Gamma <= G`, pushed into the
adjoint corona of each model. Members of the class:
- relative property (T) of a pair `(Gamma,N)` for any overgroup `Gamma`. Examples:
  - `Z^2 <= Z^2 x| SL_2(Z)`;
  - the root column `J^2 <= EL_2(J) x| J^2`;
  - the Clifford-lamp pair over `V_2 = Z[1/2]^2 x| (SL_2(Z) x <t>)`;
- strong or "Kazhdan-projection" forms of relative (T);
- a uniform relative Kesten gap: one Markov or Laplacian element of `C[Gamma]`
  with a gap uniform over all representations on the complement of `Fix(N)`;
- norm limits and functional calculus of such elements;
- the case `Gamma = G` itself, for example `Gamma = Delta = St_20(L_(F_2)(1,2))`.
  No element of `C*(Delta)` is a universal fixed projection for a non-Kazhdan
  subgroup of `Delta`.

**Invariant and step.**
- The step is the demand that the transport projection lie in the image of
  `C*(Gamma)` and be correct in every representation.
- The invariant is the vector state of the coset vector `delta_(eN)`. It is
  approximated pointwise on `Gamma` by vector states of `Ind sigma` supported on the
  coset `N`, where `N` has no fixed vectors. So the substitute has value `1` in the
  limit and at most `1 - epsilon` along the approximating states.

**Consequence for the goal `property-t-free-leavitt-full-mf-radical`.**
- A certificate that is uniform over representations is (T) of the subgroup
  it certifies, so it is Kazhdan input under certificate typing.
- Together with the intrinsic fence (`z-direct-factor-kills-intrinsic-t-substitutes`),
  this leaves a single admissible shape for a (T)-free compression proof. Its
  transport projection must be **model-dependent**, that is, correct only on the
  class of corona representations of MF models.
- By the refinement, such a class must exclude every limit of induced vector
  states `Ind sigma -> lambda_(Gamma/N)`, with `sigma` almost invariant and without
  fixed vectors. Equivalently, the corona representations must not realize
  `delta_(eN)` as a limit of N-non-fixed coset vectors.
- This is the gap that `root-column-fixed-projection-is-not-in-root-pair-cstar`
  probes per model, and fences for one root pair.
