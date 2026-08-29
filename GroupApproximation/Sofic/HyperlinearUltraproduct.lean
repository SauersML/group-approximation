import GroupApproximation.Sofic.PhasePropagation
import GroupApproximation.Sofic.SoficUltraproduct

/-!
# The unitary metric ultraproduct

`Sofic.SoficUltraproduct` builds `∏_𝒰 Sym(X i)`, the universal sofic group, and
proves the bridge in both directions: an injective homomorphism into such a
quotient makes a group sofic, and a sofic approximation is such an embedding.
The forward direction is amplification -- injectivity separates a pair by *some*
positive amount, never by the `1 - ε` the definition asks, and tensor powers
close that gap.

This file builds the unitary counterpart `∏_𝒰 U(X i)`.  The construction goes
through verbatim, and it goes through *without square roots*: the null
sequences are those whose squared Hilbert--Schmidt length vanishes, and the
three closure properties come from

* `hsNormSq_add_le`, the crude `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`, which is enough
  because a factor `2` cannot obstruct a limit;
* `hsNormSq_mul_left` and `hsNormSq_mul_right`, unitary invariance on both
  sides, which give inverse- and conjugation-invariance of the length.

The reverse bridge is proved separately in `HyperlinearUltraproductBridge`.
Plain tensor powers cannot supply it because scalar phases can collapse.
Instead, equal-size identity padding sends a relative trace `z` to
`(z + 1) / 2`, pushing every positively separated pair off the unit circle;
the conjugate-double amplification then applies.
-/

/-! ## The squared Hilbert--Schmidt length -/

/-! ## The null subgroup -/

/-! ## What injectivity of the induced map would need -/

/-! ## From an approximation to an embedding -/

/-! ## The centre, where the root asymmetry lives

`UntwistSeparation` records the asymmetry that drives every phase phenomenon in
this development: `U(Y)` has a central element at maximal distance from the
identity while `Sym(Y)` has none.  Stated at the level of the ultraproduct --
which is where Question 3.4 actually lives, soficity and hyperlinearity being
embeddability into `∏_𝒰 Sym` and `∏_𝒰 U` -- it says that the universal
hyperlinear group has a **nontrivial central element**.

The constant sequence `-1` is unitary, central in each factor and so in the
product, and not null: `hsLengthSq(-1) = 4` at every index, so it stays a
positive distance from the identity along any ultrafilter.  Its class is
therefore a nontrivial central element of `UniversalHyperlinear`.

The corresponding statement for `∏_𝒰 Sym` fails, by `eq_one_of_central_perm`.
That is the asymmetry in the form the question sees it.  It is not an
obstruction -- `eq_one_of_fixed_of_commutes_transitive` explains why -- but it is
the reason the two ultraproducts are not obviously the same object.
-/
