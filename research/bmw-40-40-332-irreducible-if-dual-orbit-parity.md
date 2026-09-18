---
rg: 2
id: bmw-40-40-332-irreducible-if-dual-orbit-parity
kind: claim
title: If every orbit of the 3-state dual transducer of K(332V) on {a_0,a_1,a_2}^n contains a sequence with an odd number of a_0 (in particular if the dual is level-transitive), then K(332V) is V_4 * C_2 and 40_40#332 is irreducible; the condition holds for n ≤ 8, so K(332V) and V_4 * C_2 agree through length 17
distinct_from:
  bmw-332-193-self-similar-certificates-need-new-relation: that shows the self-similar certificates for K are blocked unless K has a relation outside the amalgam A; this reduces the opposite alternative, K = A, to an orbit property of the dual
  bmw-40-40-281-is-irreducible: that is #281, whose K is linear over F_3((s)); for #332 no linear model is known and the route here is combinatorial
  bmw-44-sat-survivor-parity-kernels-not-left-orderable: that is the OPEN dichotomy for three classes; this is a sufficient condition for the first alternative for #332 only
artifacts:
  - experiments/bmw-332-193-amalgam-2026-09-17/README.md
  - experiments/bmw-332-193-amalgam-2026-09-17/aut.py
  - experiments/bmw-332-193-amalgam-2026-09-17/checkaut.log
  - experiments/bmw-332-193-amalgam-2026-09-17/dual.py
  - experiments/bmw-332-193-amalgam-2026-09-17/dual332V.log
  - experiments/bmw-332-193-amalgam-2026-09-17/bH.py
  - experiments/bmw-332-193-amalgam-2026-09-17/bH.log
  - experiments/bmw-332-193-amalgam-2026-09-17/bobs.py
  - experiments/bmw-332-193-amalgam-2026-09-17/bobs_8_2.g
  - experiments/bmw-332-193-amalgam-2026-09-17/bobs_8_2.log
  - experiments/bmw-332-193-amalgam-2026-09-17/bc1.py
  - experiments/bmw-332-193-amalgam-2026-09-17/parreg2.py
  - experiments/bmw-332-193-amalgam-2026-09-17/parreg2.log
---

**ESTABLISHED (an implication, by hand proof).** Proof: `bmw-40-40-332-dual-orbit-parity-proof`.

**Setting.**
- `K = K(332V)` is the invariant-subtree quotient of the V-side vertex stabilizer of `40_40#332`
  (`aut.py`, `checkaut.log`). On `X = {0,1,2}`:
  - `a_0 = (a_1,a_1,a_1)`
  - `a_1 = (12)(a_2,a_0,a_0)`
  - `a_2 = (12)(a_0,a_2,a_2)`
  - `τ = (01)(τ,τ,τ)`

  This is the `#281` automaton with the sections of `a_1` and `a_2` exchanged. `K` is a quotient
  of `A = V_4 * C_2`, where `V_4 = {1, a_0, a_1, a_2}`.
- The **dual transducer** `B` has states `b_x` for `x ∈ X` and alphabet `D* = {a_0,a_1,a_2}`. In state
  `b_x`, reading `d` outputs `d|_x` and moves to `b_{τ(d(x))}`. Explicitly, with `a_i` written `i`:
  - `b_0 = (012)(b_1,b_1,b_1)`
  - `b_1 = (01)(b_0,b_2,b_2)`
  - `b_2 = (01)(b_2,b_0,b_0)`

  `B` is invertible.

**Theorem.**
1. **Duality.** Write a word `w = τd_1τd_2⋯τd_n` with `d_i ∈ D*` as the sequence
   `δ(w) = (d_n,…,d_1)`. Then `w = 1` in `K` iff the level-1 permutation of `w_u` is trivial for
   every `u` in the `⟨B⟩`-orbit of `δ(w)`.

   That permutation is odd iff `u` contains an odd number of `a_0`.
2. **Reduction.** Suppose every `⟨B⟩`-orbit on `(D*)^n`, `n ≥ 1`, contains a sequence with an odd
   number of `a_0`. This holds in particular if `⟨B⟩` is level-transitive. Then:
   - `π : V_4 * C_2 → K(332V)` is an isomorphism;
   - `K` is infinite;
   - `40_40#332` is an irreducible lattice (Burger–Mozes, Prop. 1.2);
   - for `#332`, the dichotomy of `bmw-44-sat-survivor-parity-kernels-not-left-orderable` becomes
     the single question whether `Γ^+` is left-orderable.
3. **Verified range.** `⟨B⟩` is transitive on `(D*)^n` for `n ≤ 8` (`dual332V.log`). Hence every
   nontrivial element of `ker π` is conjugate to `τd_1⋯τd_n` with `n ≥ 9`. In particular, a word of
   length `≤ 17` is trivial in `K(332V)` iff it is trivial in `V_4 * C_2`. This extends the
   agreement to length 12 of `bmw-332-193-self-similar-certificates-need-new-relation`.

**What is known about B (context for the open condition; not used above).**
- `c_1 = b_1b_0^{-1}` and `c_2 = b_2b_0^{-1}` generate a self-similar `V_4`:
  - `c_1 = (02)(c_3,c_1,c_3)`
  - `c_2 = (02)(c_1,c_3,c_1)`
  - `c_3 = c_1c_2 = (c_2,c_2,c_2)`

  After relabelling the letters, this is exactly the `V_4` of the `#281` automaton.
- `B = ⟨c_1, c_2, b_0⟩`. Its relations of length `≤ 8` are consequences of the relations of `V_4 * Z`
  (`bobs_8_2.log`).
- `φ_v(St_B(v)) = B` modulo levels 1–5, for each `v` (`bH.log`).
- Exactly, however, `H = φ_2(St_B(2))` lies in an index-3 subgroup of
  `⟨b | relations of length ≤ 8⟩` that does not contain `c_1` (`bobs_8_2.log`). So the same
  non-congruence obstruction blocks an exact self-replication proof for `B`, unless `B` has a longer
  relation.
- A search over words of length `≤ 13` finds no exact `g ∈ St_B(2)` with `g|_2 = c_1` (`bc1.py`).
- The largest `B`-invariant set of even-`a_0` sequences, computed as a regular language, blows up
  (automata with 2, 12, 648 states, then more than 2 GB; `parreg2.log`).

**Open step.** Prove the orbit-parity condition, or level-transitivity of `⟨B⟩`, without
self-replication. Possible routes:
- a spherically transitive element;
- a transitivity invariant that is compatible with the index-3 non-congruence quotient;
- a fiber argument: an orbit inside the even set is the graph of a function over level `n−1`.
