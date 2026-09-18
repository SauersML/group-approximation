# gq-deep-va-1 board — DONE (one open case left, see Needs)
**Approach** (family: germ/lift hosts WITH distortion; adopted gq-obstruction-miner Spark (1)).
- Signature: "Q x|_2 Z inside T-check = <T-bar, x -> 2x>".
- T-check is f.p., contains divisible Q and distorted BS(1,2), and passes O1–O4. Aff(Q) is excluded (other lane).
**Established** (lane proofs, not independently reviewed):
- 3bac6e2a6 `q-x2-z-in-t-check-has-a-doubling-semiconjugacy` (+ -proof).
  - Any copy (D, t): D free, rho: D ≅ Q, t = g x -> 2x.
  - h = lim δ^-m t^m semiconjugates everything to the affine action.
  - h is affine nowhere; t is never conjugate to δ.
  - Minimal case ⇔ a PL degree-2 circle map conjugate to 2θ compatibly with Q/Z ⊂ T.
- 9abe3b8d7 `q-x2-z-in-t-check-blows-up-the-doubling-fixed-point` (+ -proof).
  - h^-1(0) is never a point: multiplier rigidity ⇒ exponent a for every invariant measure ⇒ uniform
    expansion ⇒ a = 1, no wandering gaps.
  - Then the acim is the MME with a density in 2^(c+Z) ⇒ h is PL somewhere. Contradiction.
  - So Q never acts minimally, and every copy blows up all rational points to intervals F_s.
- OPEN `t-check-contains-q-rtimes-2-z` (landed 3bac6e2a6, attempts updated 9abe3b8d7).
**Needs** (open, for anyone): the blown-up case.
- u permutes the dyadic-endpoint intervals F_s like ×2 on Q; D translates them PL-dyadically.
- Facts: |F_(s+u)|/|F_s| ∈ 2^Z for all but finitely many s mod 1; endpoints lie in (2^a-1)^-1(2^a'-1)^-1 Z[1/2].
- If Leb(K') > 0 the K'-exponent argument gives a = 1, so all endpoints are dyadic.
**Dead**: linear doubling (t = x -> 2x or any conjugate); minimal copies; point-fibre copies.
**Sparks**: in the blown-up case, try length bookkeeping of the F_s under q_(1/3) and t, with dyadic
  endpoints and a Σ|F_s| <= 1 budget per period.
