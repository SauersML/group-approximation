import GroupApproximation.Sofic.HyperlinearUltraproduct
import GroupApproximation.Sofic.HyperlinearWeakBridge

/-!
# The tracial-ultraproduct characterization, elementary direction

An injective homomorphism into a metric ultraproduct of finite unitary groups
produces hyperlinear models.  Representatives of finitely many group elements
are simultaneously approximately multiplicative on an ultrafilter-large set.
Injectivity says that each of the finitely many distinct pairs has some
positive Hilbert--Schmidt separation on an ultrafilter-large set; taking the
minimum gives a common positive separation.  Equal-size identity padding and
conjugate-double amplification then turn that finite-set-dependent separation
into the convention used by `IsHyperlinear`.
-/
