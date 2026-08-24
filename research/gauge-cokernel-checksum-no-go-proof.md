---
rg: 2
id: gauge-cokernel-checksum-no-go-proof
kind: route
title: Split the checksum into torsion and free parts and apply amplification and profile density
target: gauge-cokernel-checksums-cannot-produce-a-normalized-hs-gap
requires:
  - atlas-fixed-packet-arithmetic-has-no-hs-gap
  - finite-rational-rank-flows-are-fd-dense
---

The cokernel `Q=Z^N/im(D)` of a finite integral matrix is a finitely generated
abelian group, hence `Z^k directSum F` with `F` finite.  Any `gamma` on `Q`
therefore decomposes into a free `Z`-valued part and a part valued in a finite
group of exponent `e`.

**Torsion part.**  `atlas-fixed-packet-arithmetic-has-no-hs-gap` proves
`(APA1)`: multiplying an integral profile by `e` leaves the normalized profile
`x/dimension(x)` fixed while landing the profile in the kernel of every
homomorphism to a group of exponent `e`.  Any normalized-HS cost is a function
of the normalized profile alone, so it is constant along this operation while
the checksum is annihilated.  No inequality between them can hold with a
positive constant.

**Free part.**  The same claim proves `(APA2)`: the closure of the realizable
normalized profiles is the full convex hull of the atomic normalized type
vectors, and the conclusion persists for a rational polyhedral multiplicity
cone by a finite Hilbert basis.  `finite-rational-rank-flows-are-fd-dense`
proves `(RFD2)`: a tracial flow in the polyhedron is approximated in the sup
norm by a rational flow in the same minimal face, which after clearing one
denominator is an integral flow realized by finite-dimensional packet
representations.  Together these say that whenever the local data admit an
exact tracial model, integral matrix profiles accumulate on that model's
normalized profile.  A `Z`-valued linear functional normalized by the
dimension is continuous and degree zero, so its infimum over those profiles is
zero, which is `(GCC4)`.

The explicit witness needs no density argument: `gamma(m_wit + k m_src)` is
independent of `k` by linearity and `gamma(m_src)=0`, while the dimension
grows linearly in `k`.

**Mixed.**  Adding the two parts adds the two failures, so no component of
`gamma` survives both operations.

Both operations — amplification by the exponent, and direct sum with the
distinguished source — are available in every architecture in which the source
model is itself exactly realizable, which is the standing hypothesis of every
route that would use such a checksum.
