# bh-kourovka-2174a
Direction: Kourovka 21.74(a) (Kohl): is it decidable whether g ∈ CT(Z) permutes a nontrivial partition of Z into residue classes?
Source: arXiv:1401.0300v46, verbatim per referee fac0259d6b. Literature: none on (a).

**Established (lane proof, not reviewed).** d61d20b6b `ct-z-residue-partition-question-finite-vs-infinite-reading`:
- every F_M, H_M, A_M, B_M is YES via {0(7),…,6(7)}, so the (b)/(c)/21.73 reductions are blind to (a);
- g_0 = τ_{1(2),0(4)}τ_{0(2),1(2)} is NO for finite and for infinite partitions (fixed point 0, slope 2);
  two transpositions is the minimum;
- ψ permutes an infinite partition, so (a) depends on reading "partition" as finite (Kohl's usage);
- dissipative elements (conditions (A1)–(A3)) are always YES∞.

**Open.** 21.74(a) itself, under the finite reading. Missing both ways:
- undecidability needs digit coding over ≥2 primes, plus a lemma "non-periodic machine ⇒ NO";
- decidability needs Σ₁ NO-certificates for multi-prime (non-autonomous) dynamics.

**Needs.** Referee for d61d20b6b. The owner of `ct-z-north-south-element-has-no-finite-cycles` should
restrict its item 2 to finite partitions (Theorem 3 of d61d20b6b shows it fails for infinite ones).

**09-18 (pass 2) — 4267a301f `ct-z-residue-partition-certificates-live-on-s-adic-coordinates` (lane proof):**
- ĝ is a skew product over the S-adic dynamics g_S, with S-unit affine fibre maps.
- A partition can split at a prime ℓ ∉ S only where the K-blocks are trivial mod ℓ.
- An orbit-hull NO-certificate needs only the primes in S, plus unit defect of the blocks.
- "Non-periodic ⇒ NO" is false as stated (every F_M is YES).
- Conditional reduction, with three remaining gaps:
  - (G1) an undecidable torsion problem for a family in CT(Z);
  - (G2) a reversible universal model realized directly as g_S (no independent digit tapes exist);
  - (G3) the design of (N).
- Next: (G1). Is the torsion problem in CT(Z) decidable? Read Belk–Bleak (2V) at source first.

**09-18 (pass 3) — 5dee66c22 `ct-z-torsion-problem-and-the-brin-thompson-transplant` (lane proof):**
- Belk–Bleak read at source (arXiv:1405.0982). Their input is Kari–Ollinger: uniform periodicity
  of complete reversible TMs is undecidable. The coding uses independent prefix replacements on C².
- CT(Z) cannot do independent prefix replacements, since one slope acts on every p-adic coordinate.
  The rational transfers x ↦ (ax−u)/b move symbols between alphabets of coprime sizes a ≠ b, and
  writes carry into both tapes.
- tame = finite order (L1 from bh-free-58), so the torsion problem = decidability of tameness.
- Reaching a residue class is undecidable in CT_{3,5,7,11,13}(Z) (analog of Belk–Bleak Thm 6.6).
- **Open:** the torsion problem of CT(Z). A clean test: does 2V embed in CT(Z)?
- **Dichotomy:** thin questions are undecidable, thick questions (torsion, 21.74(a)) are open.

**09-18 (pass 4) — 324752e8a `ct-z-monomial-elements-have-decidable-torsion` (lane proof):**
- Monomial elements (n ↦ λn on each piece) are counter machines, so their torsion is uniform
  periodicity: decidable (KO Thm 4).
- All moduli powers of 2 ⇒ torsion reduces to V ⇒ decidable.
- So the coordinator's route (the group of a universal reversible machine's step maps) has solvable
  torsion problem. Dead.
- Any f.g. H ≤ CT(Z) with unsolvable torsion problem needs a non-monomial element with a modulus
  that is not a power of 2.
- Live routes: 2V ↪ CT(Z) (bh-free-57), or rational-base TMs with block cells plus a
  junk-reflection gadget. The missing piece is the gadget.

**09-18 (pass 5) — 768c12ce6 `ct-z-rational-base-machines-carry-a-potential` (lane proof):**
- Junk reflection works (KO direction switching at the junk digit): finite order ⟺ T uniformly
  periodic.
- But an exact realization ⟺ a rational potential Ψ on the states (moves ×(2/3)^{±1}, writes +Δ).
- The base-3/2 uniqueness law (digits −1,0,1) makes net tape change a function of
  (s_0, s_t, D_t), so the machine stores nothing. The route is dead for exact codings.
- Caveat: membership in CT(Z) also needs canonical pieces.
- Lean now: torsion in CT(Z) is DECIDABLE, since conserved quantities are the engine. That would
  imply 2V ↛ CT(Z). A proof needs a revealing-pair-type structure theorem on Ẑ_S.
- bh-free-57: a138a1757 (any 2V in CT_P(Z) needs germ-degree rank ≥ 2) agrees.

**09-18 (pass 6) — f08cecd33 `ct-z-torsion-reduces-to-hyperbolic-primes` (lane proof):**
- Isometric primes (every slope a unit) collapse to a finite set without changing the order.
- H = ∅ ⇒ finite order.
- H = {2} ⇒ f.g. subgroups embed in V ⇒ torsion decidable. So any 2V needs an odd hyperbolic prime.
- Two Σ₁ certificates of infinite order: (a) compression, (b) a hyperbolic periodic germ in the
  quotient. Neither is complete alone:
  - ψ_{0(3)}τ_{1(3),2(9)} has no (b);
  - a non-uniformly periodic F_M has no (a).
- Conway's amusical permutation acts on Z_2×Z_3 as the full 3-shift.
- **Conjecture 7:** (a) ∨ (b) is complete ⇒ torsion decidable ⇒ 2V ⊄ CT(Z).
- **NOT proved.** Next: prove Conjecture 7 on the class with no expanding piece, using
  bh-free-57's fragmentation bound (15698b400).
- Note from bh-typeA-universal (09-18, 252979610): host-side confirmation of your thin/thick dichotomy. Any operad/full-group host built from residue-class-affine identifications has WP in 2^O(n), and residue-class operads have unary squares (CRT), hence automatic Ore. Undecidable orbit questions in CT(Z) never reach host word problems.
