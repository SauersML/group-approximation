---
rg: 2
id: literal-fp-via-folner-rf-core
kind: route
title: Compress quasi-regular finite-quotient windows of the telescope core
target: literal-group-factorization-property
requires:
  - literal-telescope-core-lef
  - literal-telescope-split-normal-form
artifacts:
  - GroupApproximation/Sofic/ResidualFinitePacket.lean
  - GroupApproximation/Analysis/QuasiRegularCompression.lean
  - GroupApproximation/Analysis/AmenableTraceGeneratorDense.lean
  - GroupApproximation/Analysis/LocallyRFByIntAmenableTrace.lean
  - GroupApproximation/Analysis/LocallyRFByIntAction.lean
  - GroupApproximation/Analysis/LocallyRFByIntFactorization.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
---

**ESTABLISHED AND FORMALIZED IN LEAN.**  Put
`K = E_T = ker(E -> Z)`.  The split normal form is the group isomorphism

```text
E = K rtimes_alpha Z,
```

and `literal-telescope-core-lef` says every finitely generated subgroup of
`K` is residually finite.  The formal proof uses these group facts directly;
it does not pass through a maximal crossed-product model, a maximal subgroup
C-star embedding, or Arveson's extension theorem.

At stage `n`, take the first `n + 1` elements of a countable exhaustion of
`E` and the integer representatives `0,...,n` of `ZMod (n+1)`.  Collect all
normal coordinates of the tested elements at those levels in one finitely
generated subgroup `H <= K`.  Remove the identity coordinates.  Local
residual finiteness and `ResidualFinitePacket.exists_packet` give one normal
finite-index subgroup `J normal H` avoiding every remaining coordinate, and
hence one finite quotient `Q = H/J` that separates all of them at once.

Embed `J` in `E` and use the honest quasi-regular representation of `E` on
`l2(E/J)`.  The finite set

```text
ZMod (n+1) x Q -> E/J
```

sends a level and quotient label to the corresponding ambient coset.
`LocallyRFByIntAmenableTrace.windowCompression` compresses the quasi-regular
representation to this set.  Since it is a compression of a genuine
representation, the resulting map from `C*_(max)(E)` to a matrix algebra is
unital, completely positive, and contractive.

The exact action formula in `LocallyRFByIntAction.smul_windowCoset` says that
translation adds the integer height and multiplies the quotient label by the
visible normal coordinate.  Away from cyclic wrap-around, a translated
coordinate stays in the selected window.  Consequently the generator-pair
defect is supported on boundary levels and satisfies

```text
||Phi_n(uv)-Phi_n(u)Phi_n(v)||_(2,tr)
  <= sqrt(card(boundary(height(v),n))/(n+1))
  <= sqrt(2*|height(v)|/(n+1)) -> 0.
```

The trace is exact on every eventually tested group generator.  A nonzero
height cannot fix an ambient coset.  At height zero, a fixed window coset
would force its visible normal coordinate into `J`, contradicting the packet
separation unless the tested group element is the identity.  Thus every
tested nonidentity generator has normalized trace zero, exactly its canonical
trace value; the identity has trace one.

Finally,
`AmenableTraceGeneratorDense.amenableTraceModel_of_dense_generators` upgrades
generator-pair Hilbert--Schmidt convergence and generator trace convergence,
using uniform contractivity and density of the complex span of the canonical
group generators, to a full amenable-trace model.  The generic axiom-clean
endpoint is

```text
LocallyRFByIntFactorization.
  canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt.
```

Specializing it to `StableLetterLEFRoute.shiftAction`,
`markedGroupEquivKernelByInt`, and
`telescopeKernel_locallyResiduallyFinite` gives
`NinetyNineProblems.literalFactorizationProperty`.  The estimate is only in
normalized Hilbert--Schmidt norm, so it does not conflict with the proved
failure of quasidiagonality/operator MF.
