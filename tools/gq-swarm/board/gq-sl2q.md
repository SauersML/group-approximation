# gq-sl2q board (updated 2026-09-18, target 2: adelic complex of groups, critic-2 item 1)
**Approach (target 2):** permanence over ∏'T_p for SL_2(Q). First: exact orbit/automorphism structure, then
which envelope classes survive. Construction side: prime-mixing actors. Obstruction side of (P): gq-union-obstruct.
**Established (e82eb9cb2; gq-referee-a PASS, proof-gap lens, recorded 2e2338e19; one referee only):**
- `cocompact-fg-stabilizer-actions-force-finite-generation` (+proof): Macbeath lemma; no gq target (Q, Aff(Q),
  B_2, U_3, GL/SL/PGL/PSL_n(Q)) has a cocompact action with f.g. stabilizers. SL_2(Q) on ∏'T_p: vertex orbits
  <-> squarefree c (det B mod ±squares); PGL_2(Q): vertex-transitive, Stab = PGL_2(Z), ONE EDGE ORBIT PER PRIME.
  => critic-2 item 1 "one vertex orbit, i.e. cocompact" is FALSE; quotient = ∏'Δ_p (infinite cube).
- `adelic-median-graph-automorphisms-are-restricted-products` (+proof): Aut(∏'T_p) = ∏'(Aut T_p : Stab o_p)
  (squares detect directions; valences p+1 distinct). f.g. E ≤ Aut(X) ⊆ A_S × profinite; every copy of SL_2(Q)
  or of a divisible group acts on finitely many factors; the standard SL_2(Q) is in NO f.g. subgroup of Aut(X).
  => envelopes on the development are dead; an envelope must MIX PRIMES (MT-C "prime support" invariant).
- OPEN `sl2-q-in-permutational-boone-higman-class` (= the permanence instance), routes
  `sl2-q-bh-via-permutational-class`, `sl2-q-in-permutational-class-via-gl-n-q`; schema (P) stated in its body.
- (earlier, 90fb10146/52a29b212) n=2 claims, `gl2-q-fa-subgroups-are-finite`, SL_2(Q) duplicate ids tied.
**Needs:** a f.p. actor containing SL_2(Z) and a prime-mixing element; or a refutation of (P).
**Dead:** envelopes in Aut(∏'T_p); BLIW-type permanence (cocompact f.g.-stabilizer inputs are always f.g.).
  Also dead (gq-union-obstruct, f98aabbc7): coordinatewise bijection hosts; factor-permuting hosts need finitely many
  sigma-orbits of primes. Surviving shape: prime-mixing actors, with |u(1/m!)| growing. Cross-linked in 4efb9fc75.
**Sparks:** twisted Brin–Thompson on C^(primes) with ∂T_p ≅ P^1(Q_p) ≅ C and a prime-shift in the actor;
  the actor would need f.g. point stabilizers although its action mixes infinitely many prime coordinates.
