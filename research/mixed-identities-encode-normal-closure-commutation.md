---
rg: 2
id: mixed-identities-encode-normal-closure-commutation
kind: claim
title: The mixed identity [x c x^-1, d] holds in G exactly when the normal closures of c and d commute, so a finitely presented group with solvable word problem and undecidable normal-closure commutation would answer MathOverflow 412219 negatively
requires:
  - e-of-finitely-presented-group-is-recursively-presented
distinct_from:
  e-of-finitely-presented-group-is-recursively-presented: that is the open MO 412219 question and its reformulation E(G) = (G*Z)/J_1(G); this identifies an explicit two-parameter family inside J_1(G) and reduces a negative answer to one decision problem.
  bffhz-q33-is-normal-finite-generation-of-mixed-identities: that concerns finite normal generation of J_k(G); this concerns decidability of J_1(G).
---

**ESTABLISHED** (lane proof, elementary; not reviewed; no priority claimed).

For a group `G` and `c, d ∈ G`, write `N_c` and `N_d` for their normal closures, and put
`w_{c,d}(x) = [x c x^{-1}, d] ∈ G * ⟨x⟩`.

1. **Encoding.** `w_{c,d} ∈ J_1(G)` if and only if `[N_c, N_d] = 1`.
   - By definition, `w_{c,d} ∈ J_1(G)` means `[a c a^{-1}, d] = 1` for every `a ∈ G`.
   - Conjugating by `b`, this gives `[b a c a^{-1} b^{-1}, b d b^{-1}] = 1` for all `a, b`. So every conjugate
     of `c` commutes with every conjugate of `d`, and hence `N_c` and `N_d` commute elementwise.
   - The converse is immediate. ∎
2. **Reduction for MO 412219.** Let `G` be finitely presented with solvable word problem. By item 2 of
   `e-of-finitely-presented-group-is-recursively-presented`, `E(G)` is recursively presented if and only if
   `J_1(G)` is decidable. Item 1 is a computable many-one reduction from normal-closure commutation to `J_1(G)`.
   So if the problem "given words `c, d`, decide whether `[N_c, N_d] = 1`" is undecidable in `G`, then `E(G)` is
   not recursively presented. That would answer MO 412219 negatively.
3. **Complexity.** For such `G`, normal-closure commutation is always co-r.e.: search for `a` with
   `[a c a^{-1}, d] ≠ 1`. So the target is an f.p. group with solvable word problem in which this co-r.e.
   problem is not decidable.

**Calibration.** In each of the following classes the problem is decidable, so they cannot be used:
- **Nonabelian simple groups:** `N_c = G` for every `c ≠ 1`, so the normal closures commute only when `c = 1`
  or `d = 1`.
- **f.p. metabelian groups:** by the Noetherian module theory underlying Baumslag–Cannonito–Robinson, recalled
  and not read at source here.
- **Groups in which normal closures of nontrivial elements contain the finitary alternating group:** for
  example Houghton groups `H_n` with `n ≥ 3`.

**Where to look.** Undecidability of a co-r.e. commutation problem naturally comes from non-reachability. The
natural candidates are groups of homeomorphisms or permutations in which `[N_c, N_d] = 1` holds exactly when no
group element carries `supp(c)` onto a set that meets `supp(d)`, and in which that reachability simulates a
universal machine while the word problem stays solvable. No such group is constructed here.

**Status note (2026-09-18).** MathOverflow 412219 in the finitely presented case is now answered negatively outright by `fp-decidable-group-whose-e-is-not-recursively-presented` (bh-free-08, 1c6cfe928). That construction is consistent with this node: in its group, normal-closure commutation is undecidable. This node remains a separate reduction and is no longer needed for the answer.
