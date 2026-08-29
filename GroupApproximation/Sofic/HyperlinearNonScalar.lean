import GroupApproximation.Sofic.HyperlinearAmplification

/-!
# The unitary separation constant, and why it is not elementary

`Sofic.HyperlinearAmplification` shows that the tensor-power argument which
makes the sofic separation constant a convention does not transport to unitary
models: scalars are raised to the `k`-th power, so `1` and `i\cdot1` are
maximally separated with equal fourth tensor powers.  What survives is the
conjugate double `A \otimes \bar A`, whose normalized trace is `|\tau(A)|^2`,
and it amplifies exactly when the trace is bounded off the unit circle.

That bound is a property a model may or may not have.  Call a unitary model
**non-scalar** when

  `|\tau(u_g u_h^*)|^2 \le 1 - \delta`   for distinct `g, h` in the test set,

with `\delta` depending on the test set alone.  This is strictly more than the
separation `2 - \eps` of `HyperlinearModel`, which controls only the *real
part* of the trace and so tolerates `u_g u_h^* \approx \pm i`.  Two theorems
place the resulting condition:

* `isHyperlinearNonScalar_of_isSofic` -- soficity gives non-scalar models,
  because the trace of a permutation matrix is the proportion of its fixed
  points, a *real* number in `[0,1]`, and separation makes it small.
* `isHyperlinear_of_isHyperlinearNonScalar` -- non-scalar models amplify, by
  `hsDistSq_conjDoubleTensorPow`, to models of every accuracy and separation
  `2 - \eps`.

Thus the declarations below establish

  sofic  ==>  non-scalar hyperlinear  ==>  hyperlinear.

The endpoint reading `not_isSofic_of_not_isHyperlinearNonScalar` is recorded in
the same form as the one in `Sofic.Hyperlinear`.
-/

/-! ## The trace of a permutation matrix is its proportion of fixed points -/

/-! ## Non-scalar models -/

/-! ## Soficity gives non-scalar models -/

/-! ## Non-scalar models amplify -/
