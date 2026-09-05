import GroupApproximation.AlgTop.ChernEvenTopClass
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# A worked instantiation of the Chern-class layer

`GroupApproximation.AlgTop.TotalChern` is stated over an abstract `CommRing A`,
which is where the cohomology ring will go once `found-cohomology-ring` has one.
This file instantiates the whole layer at a concrete `A` — the polynomial ring
`MvPolynomial ι ℤ`, with `X j` playing `h_j = c₁(L_j)` — and checks that the two
statements the STW Problem LIX manuscript actually uses come out right:

* (2.1)  `c_m(⨁_j L_j^{⊕ d_j}) = ∏_j h_j^{d_j}` with `m = ∑_j d_j`;
* the vanishing `c_k = 0` for `k > m`, which is what makes `c_r(1³ ⊕ H) = 0`.

It proves nothing new.  Its purpose is to be a compiled witness that the API
instantiates without friction at a real ring, so that the cohomology lane does
not discover an interface problem only at the moment it has a ring to offer.
Nothing downstream should import it.
-/

namespace GroupApproximation
namespace AlgTop
namespace ChernPolynomialModel

open TotalChern

noncomputable section

variable {ι : Type*} (s : Finset ι) (d : ι → ℕ)

/-- `H = ⨁_j L_j^{⊕ d_j}` with `c₁(L_j) = X j`, as a total Chern class over
`MvPolynomial ι ℤ`. -/
def bundleH : TotalChern (MvPolynomial ι ℤ) :=
  ∏ j ∈ s, (line (MvPolynomial.X j)) ^ (d j)

/-- **(2.1) at a concrete ring.** -/
theorem chernClass_bundleH_top :
    (bundleH s d).chernClass (∑ j ∈ s, d j) = ∏ j ∈ s, (MvPolynomial.X j : MvPolynomial ι ℤ) ^ d j :=
  chernClass_prod_line_pow_top s (fun j => MvPolynomial.X j) d

/-- Above the rank of `H` every Chern class vanishes; with `V = 1³ ⊕ H` this is
the manuscript's `c_r(V) = 0`, with no dimension count. -/
theorem chernClass_bundleH_eq_zero {k : ℕ} (hk : (∑ j ∈ s, d j) < k) :
    (bundleH s d).chernClass k = 0 :=
  chernClass_prod_line_pow_eq_zero_of_lt s (fun j => MvPolynomial.X j) d hk

/-- Adjoining trivial summands changes nothing: the total Chern class of
`1ⁿ ⊕ H` is that of `H`, because a trivial bundle's total class is the identity
of the group. -/
theorem trivial_mul_bundleH : (1 : TotalChern (MvPolynomial ι ℤ)) * bundleH s d = bundleH s d :=
  one_mul _

end

end ChernPolynomialModel
end AlgTop
end GroupApproximation
