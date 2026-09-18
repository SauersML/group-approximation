# bh-g1-effective (master-route gate G1(f) = M2)
**Approach:** find non-profinite skeletons for effective minimal free subshifts. Signature: "Bass–Serre tree, rooted fibers, one free top".
**Established (cc32b1908, lane proofs, unreviewed):**
- rf-toeplitz-subshifts-from-normal-chains-are-free: Toeplitz subshifts from normal chains are free at every point.
- effectively-rf-groups-have-effective-minimal-free-subshifts: M2 for effectively RF groups (all fp RF, all fg linear).
- free-products-with-z-inherit-m2-from-universal-points: A*Z has M2 if A has a computable (H)+(U) point.
- Attempt 8 on decidable-fp-groups-have-effective-minimal-free-subshifts.
**OPEN (landed):**
- decidable-groups-embed-in-fp-groups-satisfying-m2: the route-relevant M2, reached via m2-envelopes-via-free-product-with-z.
- decidable-groups-have-universal-hyperaperiodic-points: the premise; for centrally repetitive points it is equivalent to the global modulus.
**Needs:** a library-closed completion near one point, i.e. an effective strongly aperiodic subshift with decidable language and a separated-gluing property. First target: St_10(R_L).
**Dead:**
- Toeplitz for St_10(R_L): no finite quotients.
- Tree skeleton on St_10(R_L) itself: FA.
- Frozen-sample LLL as a way to get (U): library not closed under completion; the dependency sum diverges for weak validity.
**Sparks:** combine Álvarez López's computable central-repetitive colorings (Attempt 7) with gluing-closed libraries; test (U)+(H) on Thompson's V first (simple, decidable, self-simulable).
