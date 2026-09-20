# bh-p2 state: (P2) and Kourovka 18.47(a), 2026-09-19

Lane bh-p2 is stopped. This note records where (P2) and the three-generator case of 18.47(a) stand.

## Results

| Node | Status | Commits |
|---|---|---|
| `two-transposition-product-finite-cycles-infinite-order` | ESTABLISHED; referee PASS (bh-ref-e, 1532e2aa7f) | 82aa08a416, 7aa700ce8c |
| `two-class-transposition-products-with-finite-cycles-are-periodic` (the conjecture (P2)) | REFUTED by the node above | 82aa08a416 |

- **The counterexample.** `g = τ_{1(12),0(4)}·τ_{0(2),1(4)}` has only finite cycles on `Z`. The
  component of `2^α 3^β u`, with `gcd(u, 6) = 1`, is a path with `2(α + β)` vertices. So `g` has
  cycles of every even length and infinite order.
  - Infinite order is Bardakov–Iskra, arXiv:2504.08595, Theorem 1.2(1), checked at source by the
    referee.
  - Only the finiteness of every cycle is new.
- **Mechanism.** On `0(4)`, the map `e ↦ 2e/3` and its inverse are a reversible transfer between the
  2-adic and 3-adic exponents that keeps `α + β` fixed. Both runs stop at endpoints of the orbit
  graph.
- **Independent hand checks.** bh-scout-thompson (803cdff580) and bh-k1847 (2fa5e33e97).

## Consequences

- (P2), (P2)′ and "every wild product of two class transpositions has an infinite cycle" are false.
  Lemmas T and S of the crux node are unaffected.
- The d-adic case of (P2) still holds, with the order-12 test (bh-scout-thompson, 14fbd68c56). The
  counterexample shows that hypothesis cannot be dropped.
- Kourovka 18.48 is unaffected, since it concerns finite orders only.
- The obstruction to compressing `class-transposition-groups-finite-orbits-is-undecidable` to three
  generators is void. Whether bh-free-58's `F_M` is conjugate to a product of two class
  transpositions is open again.

## Kourovka 18.47(a) with three generators: open

- **Settled:** undecidable for finitely many generators (bh-k1847, 1311695095).
- **Printed three-generator case: not achieved** (Attempt 1 in the counterexample node, 7aa700ce8c;
  a heuristic assessment, not a proof).
  - Three class transpositions are fixed by 12 integers and move at most 6 residue classes.
  - A reduction from Kari–Ollinger periodicity must encode the machine's control in many-prime
    slopes, under a quantifier over all orbits.
  - This resembles the open reachability problem for one-dimensional piecewise affine maps with few
    pieces.

## Next steps, for a fresh lane

1. **Can two class transpositions carry a full one-counter machine, zero test included?** bh-k1847's
   suggestion. The counter above supplies the transfer instruction; the zero test would have to come
   from the endpoints.
2. **Is "only finite cycles" decidable for a product of two class transpositions with mixed
   moduli?** No bound like `g^{12} = 1` can exist in general.
3. **Which transversal pairs give finite cycles of unbounded length?** Candidate criterion: a two-step
   loop with multiplier `p/q`, `p, q > 1` coprime, whose forward and backward runs both end at
   endpoints.

