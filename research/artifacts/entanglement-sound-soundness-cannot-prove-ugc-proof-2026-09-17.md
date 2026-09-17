# Threshold the Kempe--Regev--Toner estimate of the entangled deficit

*Attempt artifact (2026-09-17), formerly route `entanglement-sound-soundness-cannot-prove-ugc-proof` into `entanglement-sound-soundness-cannot-prove-ugc`, requires [unique-games-entangled-value-approximable-by-sdp]. Demoted from the graph together with the other two routes of this result because referee lenses 1 and 2 of three returned *refuted* on `entanglement-sound-soundness-cannot-prove-ugc` (missing outer completeness hypothesis in B3; overclaimed class kill for 2-to-1 soundness); lens 3 returned *survives*. See `## Attempts` in the claim. Restore it as a route once the statements are corrected and a full referee pass survives.*

All inputs come from `unique-games-entangled-value-approximable-by-sdp`.

- Item 1 (relaxation) gives `val* <= val_qc <= omega_sdp1`.
- Item 3 (KRT Theorem 1.3) gives an efficient algorithm computing `eps'` with
  `eps*/6 <= eps' <= eps*`, where `val*(G) = 1 - eps*`.
- Classical strategies are tensor strategies of dimension 1, so `val <= val*`.
- Tensor strategies are commuting strategies, so `val* <= val_qc`.

**B1.** On input `x`, compute `G = R(x)`, run the KRT algorithm on `G` and accept
iff `eps' <= eps`.

- If `x in L`: `val*(G) >= val(G) >= 1 - eps`, so `eps* <= eps` and `eps' <= eps`.
  The algorithm accepts.
- If `x notin L`: `val*(G) <= val_S(G) <= delta`, so `eps* >= 1 - delta` and
  `eps' >= (1 - delta)/6 > eps`, because `6 eps + delta < 1`. The algorithm
  rejects.

The run time is polynomial because `R` and the algorithm are. So `L in P`.

**B2.** Run the same algorithm. YES instances are accepted, as in B1.

Suppose only finitely many NO instances `x` had `val*(R(x)) >= 1 - 6 eps`. Every
other NO instance has `eps* > 6 eps`, so `eps' >= eps*/6 > eps` and it is rejected.
Hard-coding the finitely many exceptions gives a polynomial-time algorithm for
the NP-complete `L`, contradicting `P != NP`.

Hence infinitely many NO instances have `val*(R(x)) >= 1 - 6 eps`, and by
item 1 also `omega_sdp1(R(x)) >= 1 - 6 eps`.

For a NO instance, classical soundness gives `val(R(x)) <= delta < 1 - 6 eps`.
So on these instances any valid soundness argument proves a bound that the
entangled value violates. Such an argument cannot consist of inferences that
remain valid when classical labelings are replaced by entangled strategies.

**B3.**

1. Since `val(Psi) <= val*(Psi)`, the conclusion of `D_cl` implies that of `D_q`.
2. Take the composed reduction `R o O`. Completeness gives
   `x in L => val(O(x)) >= 1 - eta => val(R(O(x))) >= 1 - eps`. For soundness,
   let `x notin L`, so `val(O(x)) <= eta'`. The contrapositive of `D_cl` gives
   `val*(R(O(x))) <= delta`. Apply B1 with `S = *`.
3. Let `x notin L`, so `val*(O(x)) <= eta'`. The contrapositive of `D_q` gives
   `val*(R(O(x))) <= delta`. Completeness is as in part 2. Apply B1.

Replacing `val*` by `val_qc` changes nothing, because B1 holds for `val_qc` and
`val <= val_qc`.
