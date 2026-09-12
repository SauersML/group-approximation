---
rg: 2
id: agent-mf-hyperlinear-shadow-refutes-corner-route
kind: claim
title: The integer compression lamp refutes operator-trace selection but not MF implies hyperlinear
distinct_from:
  sparse-lamplighter-corona-has-no-visible-corner: That theorem fixes one hostile realization of a hyperlinear group; this theorem gives one nontrivial word which is trace-blind in every operator-norm almost representation of the same MF group.
  mf-vs-tracial-radical-strict-gap: That theorem supplies the strict shadow-radical witness; this claim records its previously unpropagated consequences for the MF-to-hyperlinear cluster and closes the invariant-corner route.
  mf-implies-hyperlinear: The root allows genuinely Hilbert--Schmidt almost representations which need not arise from operator-norm models, so the shadow witness does not decide the root.
artifacts:
  - GroupApproximation/Sofic/IntrinsicCompressionMFRadical.lean
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
  - research/infinite-cyclic-compression-lamp-mf-proof.md
  - research/agent-mf-hyperlinear-shadow-refutes-corner-route-proof.md
---

Let `H` be a countable residually finite group, let `L <= H` be finitely
generated and Kazhdan, and suppose

```text
L_1 = t L t^(-1) < L.
```

Put `X=H/L_1` and

```text
W_Z = (directSum_(x in X) Z) semidirect H.
```

Let `c` be the root lamp at `L_1`, choose `g in L\L_1`, and put

```text
w=[g,c].
```

Then the following all hold.

1. `W_Z` is MF in the weak Carrión--Dadarlat--Eckhardt norm-corona sense.
2. `w != 1`.
3. In every operator-norm almost representation `phi_n` of `W_Z`,

   ```text
   ||phi_n(w)-I||_(2,norm) -> 0.                         (SH1)
   ```

4. Consequently `w` has no dimension-free normalized-trace gap in any
   operator-norm model.  In particular the corner-free condition `(I')` in
   `mf-invariant-corner-visibility` is false for `(W_Z,w)`, and hence the
   universal claim `mf-invariant-corner-visibility` is false.
5. `W_Z` is not MF in the stronger trace-controlled sense of Schafhauser.
   Thus the weak and trace-controlled group-MF conventions are separated by
   this explicit group.

This does **not** refute `mf-implies-hyperlinear`.  A hyperlinear model is
only required to be multiplicative in normalized Hilbert--Schmidt norm, and
need not be obtained from an operator-norm almost representation.  The exact
remaining question on this example is whether `w` can be seen by such a
genuinely Hilbert--Schmidt-only model.

## Proof

The slow-bump construction in `infinite-cyclic-compression-lamp-mf-proof`
gives a faithful homomorphism

```text
W_Z -> U(product_n M_(d_n)/directSum_n M_(d_n)),
```

proving item 1.  The two lamps occurring in the commutator have distinct
sites:

```text
w = delta_(gL_1) - delta_(L_1)
```

inside the free abelian lamp subgroup.  Since `g notin L_1`, this is nonzero,
proving item 2.

The root lamp `c` centralizes `L_1`.  Equivalently,
`z=t^(-1)ct` centralizes `L` and `tzt^(-1)=c`.  Therefore `[c,g]`, and hence
also `[g,c]`, is an intrinsic compression--centralizer defect generator.
Kazhdan asymptotic-commutant transport puts every such generator in

```text
R_(infinity->2)(W_Z)=opToHSShadowResidual(W_Z).
```

By definition of that subgroup, and concretely by
`compressionCentralizerDefect_generator_eq_one_in_hyperlinearHom` in
`IntrinsicCompressionMFRadical.lean`, this is precisely `(SH1)` for every
operator-norm almost representation.  This proves item 3.  This is the
strict inclusion already established in `mf-vs-tracial-radical-strict-gap`:

```text
Rad_MF(W_Z)=1 < R_(infinity->2)(W_Z),
```

with strictness witnessed by `w`.

For any finite-dimensional unitary `U`,

```text
1-Re tr(U) = (1/2)||U-I||_(2,norm)^2.                    (SH2)
```

Thus `(SH1)` makes every coordinate trace gap for `w` tend to zero.  If the
corner-free condition `(I')` held, exhausting operator-norm local models
could be diagonalized to an operator-norm almost representation with

```text
1-Re tr(phi_n(w)) >= c_w > 0,
```

contradicting `(SH1)`--`(SH2)`.  The claimed invariant corner cannot exist
either: compressing to it and using its intrinsic normalized trace produces
exactly such operator-norm local models, as proved in
`mf-implies-hyperlinear-via-invariant-corner`.  This proves item 4.

Finally, a trace-controlled MF model would satisfy
`tr(phi_n(w))->0` for the nonidentity word `w`, hence by `(SH2)` its squared
distance from the identity would tend to `2`, again contradicting `(SH1)`.
This proves item 5.

## Exact effect on `mf-implies-hyperlinear`

The MF-to-hyperlinear root is correctly stated only for the weak
norm-corona convention and remains open on the present dependencies.  What
was mis-stated in the cluster is that it had two live operator-norm routes.
The invariant-corner route is false, not open.  Only the vanishing-gap rate
route remains compatible with this example.

Indeed, for `w` every operator-norm model has

```text
kappa_n=1-Re tr(phi_n(w)) -> 0.
```

The intrinsic profile `mf-hs-defect-gap-profile` could still hold if its
actual normalized-HS multiplicative defects satisfy

```text
eta_n^2/kappa_n -> 0
```

along this vanishing-gap sequence.  Its phase-cancelled tensor amplifier
then produces an HS-almost representation, not another operator-norm almost
representation, so it does not contradict `(SH1)`.  Therefore `W_Z` is the
sharp current stress test:

```text
W_Z nonhyperlinear  =>  weak MF does not imply hyperlinear;
W_Z hyperlinear     =>  the required models are genuinely HS-only.
```

## Dependencies

The argument uses exactly:

1. `infinite-cyclic-compression-lamp-mf` and
   `infinite-cyclic-compression-lamp-mf-proof` for weak MF and faithfulness;
2. `kazhdan-asymptotic-commutant-transport`, in the instantiated form
   `mf-vs-tracial-radical-strict-gap-proof`, for `(SH1)`;
3. `op-to-hs-shadow-residual-functoriality` / the definition in
   `GroupApproximation/Sofic/OpToHSShadowResidual.lean` for the universal
   quantifier over operator-norm almost representations;
4. the elementary unitary identity `(SH2)`;
5. the corner-to-local-model implication recorded in
   `mf-implies-hyperlinear-via-invariant-corner`.
