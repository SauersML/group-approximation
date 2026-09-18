# Kojima–Sheng's Q ≤ 2V: mechanism, extensions, and where they die (lane gq-bt-kojima, 2026-09-17)

Target: `gl-n-q-embeds-in-fp-simple-group`. Assignment: extract the mechanism of the embedding of `(Q,+)` in Brin's
`2V` and extend it to `Aff(Q)`, `U_3(Q)` or `GL_2(Q)` inside some `nV` or a twisted Brin–Thompson group.

## 1. Source

S. Kojima, X. Sheng, *On subgroups of Brin–Thompson groups nV*, arXiv:2603.18410. Versions: v1 2026-03-19, v2
2026-04-20, v3 2026-05-23. Unrefereed. The statements below were read from the v3 HTML through a summarizing fetch;
quotes are as returned.
- Abstract: "We prove that the Brin-Thompson group nV is torsion locally finite for n ≥ 1 which is known only when
  n = 1, and nV contains continuum many copies of the additive group of the rationals ℚ for n ≥ 2 which is known to
  be false for the n = 1 case."
- Thm 1.1 / 3.11: "nV is torsion locally finite for n≥1".
- Prop 4.1: "nV contains a subgroup isomorphic to ℚ for n≥2".
- Thm 1.2 / 4.2: "For n≥2, the Brin-Thompson group nV contains continuum many copies of the additive group of the
  rationals ℚ sharing the subgroup isomorphic to ℤ".
- Cor 4.3: "nV does not act on CAT(0) cube complexes properly by isometries for n≥2".
- Problem 1.1 (Kourovka): "Find an explicit and natural finitely presented group Γ and an embedding of the additive
  group of the rationals ℚ in Γ." They offer nV as an example.
- **Their construction.** Horizontal slides with vertical shifting of dyadic blocks. The sequence of blocks `L_k`
  (repeatedly halving the left half) or `R_k` (the right half) carries the roots. A free choice of `L_k` or `R_k` at
  each `k` gives continuum many copies of `Q`.
- **Beyond Q.** The paper says nothing about `Q^n`, `Z[1/2]`, Baumslag–Solitar, Heisenberg or linear groups. The
  lane gq-lit-arxiv reports that the earlier Baumslag–Solitar exclusions for `nV` (X. Sheng, arXiv:2209.11982) were
  withdrawn.
- The repository has a self-contained explicit version, verified PASS:
  `rationals-embed-in-brin-thompson-group-2v(-proof)`.

## 2. The mechanism: a fractional-part register with overflow

The explicit version (repo route):
- Coordinate 2 of `C × C` holds a **register**: `y = c(d_1) c(d_2) ⋯` in mixed radix `2, 3, 4, …`, with the most
  significant digit first.
- Coordinate 1 carries an infinite-order `t ∈ V`.
- `s_n` = "add 1 to the first `n` digits; apply `t` in coordinate 1 on overflow".
- Then `s_n^(n+1) = s_(n−1)`, `s_0 = t × id`, and `∪ <s_n> ≅ Q`.

Reading the register as a fractional part `Σ d_i/(i+1)! ∈ [0,1)`, with the integer part carried by the orbit of `t`,
`Q` acts on a Cantor model of `R = Z × [0,1)` by translations. This is the same geometry as Belk–Hyde–Matucci's
`Q ≤ T̄` (lifts to `R`). Three points explain why it works:
- **Bounded depth for coarse roots.** Adding `1/(n+1)!` changes only the first `n` digit codes, because carries
  run toward the most significant digit. Every `s_n` is a bounded prefix rewrite.
- **One element absorbs every overflow.** Carries out of the register go into a single fixed element `t`, never into
  an odometer. An odometer is excluded from `nV`, since it has unbounded carries.
- **Why 2 coordinates.** In `V` the register and the integer part would share one coordinate. The register would
  then have to sit at unbounded depth, and Higman's theorem forbids that: no infinite-order element of `V` has
  roots of unbounded order.

The abstract requirement: an infinite-order element that ignores one coordinate (acts as the identity on it and
does not read it). Nothing else about `t` is used.

## 3. What extends (landed claims)

- `countable-virtually-abelian-groups-embed-in-2v`: every countable virtually abelian group, in particular every
  countable abelian group, `GL_1(Q)`, `Q^n`, `(Q^x)^n` and `Q^n ⋊ F` with `F` finite. Proof: disjoint rectangles
  carry independent copies of `2V`; fill them with `Q` and with `⊕ Q/Z ≤ V` (Higman); then Krasner–Kaloujnine.
  So `2V` is a second finitely presented simple group containing all countable abelian groups, after BHM's `VA`.
- `twisted-bt-point-fixing-actor-elements-are-divisible`: in every twisted Brin–Thompson group `SV_G`, any
  infinite-order element ignoring a coordinate lies in a copy of `Q`. This covers every `g ∈ G` fixing a point.
  Commuting families with distinct fixed points extend to `Q^k`. Adding fixed points preserves type (A). So every
  actor `G` of a type (A) action sits in a finitely presented simple group in which any fixed finite commuting
  family of `G` extends to its rational hull.
- `rational-stepping-stones-in-nv-need-bs12-or-heisenberg`: the gate for plain `nV` (Section 4.1).

**Carry conjugation (one level; recorded, not landed).** Let `u` satisfy `u s u^-1 = s^a`, and let `r` be a
radix-`m` register root of `s` (`r^m = s`) with `gcd(a,m) = 1`. Put
`φ_a(d, z) = (a d mod m, s^(⌊a d/m⌋) z)` on the register digit `d`, and `u' = φ_a ∘ u`. Then `u' s u'^-1 = s^a`
and `u' r u'^-1 = r^a`. Checked by hand for all `d`; the case `d = m−1` uses `⌊a m/m⌋ = a`. So one level of
`Z[1/m]`-divisibility can be made compatible with one dilation. Section 4.2 explains why the full tower cannot.

## 4. Where the extension to Aff(Q), U_3(Q), GL_2(Q) dies

### 4.1 Plain nV: two open gates (established reduction)
- `Aff(Q)`, `B_2(Q)` and `GL_n(Q)` (n ≥ 2) contain `BS(1,2)`: `z ↦ z+1` and `z ↦ 2z`.
- `SL_2(Q)` contains `BS(1,4)`: `[[1,1],[0,1]]` and `diag(2,1/2)`. `BS(1,4)` has index 2 in `BS(1,2)`, and virtual
  embeddings into `nV` upgrade to embeddings.
- `U_3(Q)` and `GL_n(Q)` (n ≥ 3) contain `H_3(Z)`. `GL_n(Q)` (n ≥ 3) contains `SL_3(Z)`.
- `BS(1,2) ≤ nV` (`bs12-embeds-in-brin-thompson-2v`) and `H_3(Z) ≤ nV`
  (`heisenberg-group-embeds-in-some-brin-thompson-group`) are both OPEN in the repo.
- Unlike `VA` (root obstruction O4), `nV` has distorted cyclic subgroups (Callard–Salo, `|f^N| = O(log^4 N)`). But
  `BS(1,2)` needs `|g^N| = O(log N)`, and `bs12-images-in-nv-have-logarithmic-table-length` records what a witness
  must satisfy.
- So for plain `nV`, the question "is `BS(1,2) ≤ nV`?" is the first gate for every non-abelian stepping stone.
- **Side check.** Callard–Salo's Lemma 6.4 puts `RTM(n,k)` in `mV`. So `BS(1,2) ≤ RTM` would open the gate. The
  RTM papers (Barbieri–Kari–Salo, arXiv:1603.08715, 2303.17270; abstracts read) do not state that it is. Callard–Salo
  themselves ask the subshift analogue (their Question 7.2) and "believe the SMART machine does not have this
  property".

### 4.2 Registers versus dilations (heuristic obstruction, not proved)
A dilation `×a` must conjugate the register tower `(r_n)` to `(r_n^a)`.
- **`a` coprime to the radices.** The conjugator must act on the register space by `×a` on the fractional digits.
  With the most significant digit first, the new top digit depends on carries from arbitrarily deep digits. This is a
  finite-state transducer, not a bounded prefix rewrite, so it lies in no `SV_G`.
  - Heuristic reason the conjugator is forced: the register dynamics of the tower is minimal and equicontinuous, so
    any conjugator is `×a` composed with a register rotation.
  - Carry conjugation (Section 3) is exactly the one-level truncation of this map.
- **`a` dividing the radices.** `×a` becomes a shift of the register, which is bounded. But the overflow must then
  absorb `k ↦ a k + d` on the integer part. That is a `BS(1,a)` structure on the overflow element, which is circular
  in `nV`.
  - In a twisted group the actor can supply it. `G = BS(1,a)` acting on `S = Z[1/a] ⊔ {*}` gives
    `⟨s, u, a-power roots⟩` inside `SV_G`.
  - That actor action is not of type (A): it has infinitely many pair orbits.
- `Aff(Q)` needs both kinds, for every prime at once. This is the precise tension. Whether a cleverer coordinatization
  of the register escapes it is open. A proof would need to show that every conjugator normalizing a register copy of
  `Q` is forced to be `×a` on the register.

### 4.3 Non-abelian relations: localized commutators
- Let `r` be a register root of `g`, and let `h` not commute with `g`. Then `[r, h]` is supported on the overflow
  slab of the register, where it equals `[g, h]`. It is not a root of `[g, h]`.
- **Example.** In `SL_3`, `[r(e_12(1)), e_23(1)]` is `e_13(1)` restricted to the top register cylinder, while
  `SL_3(Q)` needs `e_13(1/m)`.
- So Kojima–Sheng-type devices give rational hulls of abelian subgroups only. `U_3(Q)` needs a bilinear register:
  the central fractional part must receive the product of two fractional parts. In a Cantor model of `H_3(R)`
  acting on `R^3`, the term `x b` involves the unbounded integer part `x`. That is not a bounded rewrite, and
  `H_3(Z) ≤ nV` is already open.

## 5. Verdict and sparks

- **Verdict.** For `G`, the Brin–Thompson family is live only through two routes:
  - the open gates `BS(1,2) ≤ nV` and `H_3(Z) ≤ nV`, for a plain `nV` host;
  - type (A) actors that already contain the non-abelian rational structure, where the registers supply divisibility
    of abelian pieces only.
  Divisibility itself (O1) is no longer an obstacle in these hosts. The obstacle is dilations (Section 4.2) and
  bilinearity (Section 4.3).
- **Spark 1.** Settle the gate `BS(1,2) ≤ nV` with reversible Turing machines. A candidate witness is a Turing
  machine `g` conjugate to `g^2` inside `RTM(n,k)` or the `mV` image of Callard–Salo Lemma 6.4. Conjugating `g`
  to `g^2` means the conjugator doubles the head speed, e.g., a machine that on each step reads a "parity"
  register. Not pursued here.
- **Spark 2.** A type (A) actor containing `BS(1,a)`, or `Aff(Z[1/m])`, in which the extra `Z[1/m']` roots come from
  registers, stopped at finitely many levels by carry conjugation. This gives `Aff(Z[1/(m m')])`-type groups, which
  are already f.g. and covered by Zaremsky. So it offers no progress toward the full union.
- **Spark 3.** Look for a register whose conjugation by `×a` is bounded: a coordinatization of `Ẑ_odd`, the
  odd-denominator part of the register, in which multiplication by 2 is a coordinate permutation. With finite cycles,
  `×2` is a profinite rotation. The question is whether "add `1/M_n`" can simultaneously stay a bounded rewrite. This
  is the only escape from 4.2 that I see. Not pursued.
