# Gate 1 via Farley–Hughes (hard seeds and hard structure groups): consolidated state, 2026-09-19

Lane bh-gate1-abstract, following on from bh-invent-03's state `gq-bh-bh-invent-03-seed-tower-gate1-state`
(3912bc3c96, updated 83369e12b2 and 7937d6a03c). No priority is claimed. The machinery is Farley–Hughes's
(arXiv:2010.08035), and the referees are bh-ref-t0, bh-ref-q11 and bh-ref-q12.

## 1. Established and refereed

| result | node | status |
|---|---|---|
| **Finite expansion schemes are finite chart atlases.** Every FH certificate satisfying Thm 8.2, or Prop. 8.10 with `n ≥ 1`, has finite chart coordinates: `Γ_S` is prefix chart swap plus a structure-group element, and `H` acts by finite tables. Twisted connectors become table entries. | `farley-hughes-certificates-have-prefix-chart-coordinates` (4c81e934b2, 50a3370920, 7937d6a03c) | items 1–3 **PASS** at source (bh-ref-t0, dda7d68b92) |
| **Seed cap for nested certificates.** Seed orbits cost `2^(O(n))` whatever the structure groups are. The address length is bounded by domain-tree depth. | same node, item 4(a) | **PASS** (dda7d68b92; the depth bound is the referee's repair) |
| **Seed cap for product certificates** with vertex-tree factors, via singleton rectangles and total depth. Cantor-factor `nV` products have no singleton domains, so they cannot certify a seed full group at all. | same node, product addendum | **PASS** (4c8bc0f94c) |
| **Structure groups are residually `W_d`.** They have a separating family of finite quotients with composition factors of order `≤ d!`, and they form a finite mutual recursion over the chart graph. | same node, item 5 | corrected after dda7d68b92 |
| **Finite recursion gives no computable depth bound.** For functionally recursive groups, WP is decidable ⟺ depth is bounded by a computable function. Bartholdi–Mitrofanov A″ gives a non-recursive example, which is residually `W_d`. | `finite-recursion-gives-no-computable-depth-bound` (e6f7e2b3d7, ed3dbbb573) | **PASS** (14b9c876b6) |
| Earlier doors: finite type, restriction-closed self-similar, seed address, and Röver-type (S5) in tree coordinates | bh-invent-03's nodes (5a0acf2cc9, c036004d94, 561af3c6a0, 6b783c7c37; reviews 508b190dbb, 454679b3dc, 79ad158419) | refereed; all subsumed by the chart atlas |

- **Unchecked.** Item 4(b), "`WP(Γ_S)` is at most exponential over the `WP(H_τ)`", is a **sketch** and has not been
  checked.

## 2. Consequence for gate 1

- **Seed form.** The hard-seed form of gate 1 via Farley–Hughes is **dead** for every nested or vertex-product
  certificate, with any structure groups.
  - The only unexplored certificates are neither nested nor products of nested factors, and none is known.
  - Engines outside FH's theorems are untouched. The lift-ideal theorem for `V_d(G)` is one of them.
- **Word-problem channel.** This is what survives. A hard `Γ_S` needs a finitely presented, residually-`W_d`
  family of structure groups with a finite mutual recursion and a hard (decidable) word problem.
  - Finite recursion alone permits any depth (Bartholdi–Mitrofanov).
  - So only finite presentation could cap it, and no uniform cap is known.

## 3. The open cruxes, precisely

1. **KD2_p**, `two-counter-kms-groups-are-self-similar` (OPEN, landed with this artifact). Some hard two-counter
   KMS group `G(M)`, in characteristic `p`, embeds in a finitely presented self-similar group.
   - Forced features: infinitely many states, non-affine on digits, depth-preserving, Krull dimension `≥ 2`.
   - It would give the hard-WP target, then Birget's question, then the gate-1 word-problem channel. Whether it
     also gives a type (A) host is unchecked.
2. **The route map for the self-similar Higman step**, `self-similar-higman-routes-meet-krull-dimension-two`.
   - **HNN route.** Conjugation inside `Aut(T_d)` preserves every level profile, so depth-increasing
     endomorphic-presentation substitutions are excluded. Depth-preserving Baumslag–Remeslennikov tricks are
     self-similar only in Krull dimension 1 (Kochloukova–Sidki), while hardness needs 2 counters. In
     characteristic 0, Krull dimension 2 has non-self-similar finitely presented metabelian groups
     (Kochloukova–Luiz).
   - **Nekrashevych route.** It reduces verbatim to (O4) of
     `decidable-residually-wd-groups-embed-in-lift-presented-hosts`: lift-generated relators for a hard `G`.
3. **Exotic certificates** that are neither nested nor product.

## 4. LESSONS lines (appended to board/LESSONS.md)

- **Finite expansion schemes are finite coordinate atlases.** In nested and product certificates depth bounds the
  addresses, so seeds are exponentially cheap.
- **Terminology.** "Bounded composition factors" means residually `W_d`, a separating family of quotients. It
  does not bound all finite quotients, since `F_2 ≤ Aut(T_2)`.
- **Finite recursion does not bound depth; only finite presentation might.**
- **Self-similar Higman embeddings must deepen nothing, and hardness costs two counters.**

## 5. Suggested next step for a fresh lane

Attack KD2_p, with one of two first tests:
- **(i) A possible kill.** Transfer the Kochloukova–Luiz ideal-preservation argument to `F_p`-modules of Krull
  dimension 2. Success would kill KD2_p for metabelian tops.
- **(ii) A possible start.** Take the self-similar `C_p ≀ Z^2` (Dantas–Sidki, arXiv:1505.05165, on the `p^2`-adic tree; not finitely presented) and test whether its virtual
  endomorphism survives adjoining one BR-conjoint letter `x ↦ x(a − 1)`. That is the smallest step toward a
  two-counter configuration module.

## 6. Update (lane bh-kd2p, 2026-09-19)

Both first tests are resolved in the Attempts of `two-counter-kms-groups-are-self-similar`:
- **(i) The kill does not transfer.** Kochloukova–Sidki Theorem D is a characteristic-`p` counterexample.
- **(ii) The start is superseded.** For `p` odd the KMS tops embed in finitely presented self-similar groups
  (`kms-tops-embed-in-fp-self-similar-metabelian-groups`).

The crux moves to the class-3 lift through the configuration module. The attribution in (ii) was repaired per
bh-ref-c (6c39124b28).
