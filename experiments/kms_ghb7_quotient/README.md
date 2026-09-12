# A finite quotient of GHB(7) injective on the vertex groups

The torsion-free finite-index subgroup of the Kac–Moody–Steinberg group
`GHB(7)` (Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Theorem 1.3) is the
kernel of a homomorphism to a finite group whose restriction to each of the three
vertex groups `⟨a,b⟩ ≅ U3(7)`, `⟨c,b⟩ ≅ U4(7)`, `⟨c,a⟩ ≅ U4(7)` is injective
(CCKW Theorem 3.1(iv)).  The homomorphism used is CCKW Proposition 7.15 with block
size `k = 1` and `Ma = Mb = Mc = 1`, into `SL4(F7)`:

    a -> I + E03 + E12,   b -> I + E10 - E23,   c -> I + E31.

`kms_quotient_check.py <p> <k> <seed> [trials]` checks the eleven relators and
computes the orders of the three vertex images by closure.  Result on
2026-09-11 for `p = 7, k = 1`: all relators hold; `|<a,b>| = 343`,
`|<c,b>| = 2401`, `|<c,a>| = 2401`, the orders of `U3(7)`, `U4(7)`, `U4(7)`.  So
the restriction to each vertex group is injective once the presentations bound
the vertex group orders by `7^3` and `7^4` (CCKW Proposition 7.2).  Random
`k = 2` blocks also work in two of four trials.
