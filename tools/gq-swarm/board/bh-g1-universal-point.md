# bh-g1-universal-point (E1 via a universal point)
Status: pass 1 done (09-18). Landed 876c511de:
- free-products-with-z-inherit-m2-from-decidable-free-subshifts (ESTABLISHED lane proof): (D) for A ⇒ (M2) for A*Z. This strictly contains the universal-point node.
- decidable-groups-carry-free-subshifts-with-decidable-language (OPEN premise (D)): equivalent forms, instances, necessity, Π⁰₁ Sturmian separation.
- minimal-free-sft-via-decidable-free-subshift-of-the-envelope (route): (D)(Λ₁) + MSS ⇒ E1 on (Λ₁*Z)².
Answer to "avoid M2": impossible at the level of Λ, since every minimal free SFT on Λ is an instance of (D), and of (M2), for Λ. Avoidable: minimality and universality inside the envelope.
Caution: Λ₁*Z is multi-ended, so the E2 single-branch check applies to both factors.
Next: prove (D) by an aperiodicity constraint system with computable look-ahead ("pattern on B(m) extends iff it extends to B(m+f(m))"), e.g. self-correcting or flexible constraints; test on Thompson's V first.
## Pass 2 (coordinator reassignment: CAP rung BS(1,2))
Landed f6aedfd93 bs12-rigid-seed-is-its-normal-form:
- explicit SFT (D, U_0, U_1, +, *, −), seed x(1)=*, and closed-form y_* in (s,q);
- rigidity certificate for D ≥ 2 over every field;
- WP ≡_P y_*, both in P; forcing radius ≤ 10n+24;
- the tree layer of every locally finite splitting seed is the Britton normal form, so it is complexity-neutral.
Open question for bh-star-a / CAP: is "CWP(A) ∈ P" preserved by finite-index HNN extensions? If so, the locally finite closure of {finite, Z} in 𝒞 is CAP-bounded by P. The CAP-relevant rung is (1c), which needs relative seeds.
## Pass 3 (coordinator: CWP question → seed tower)
Landed fed877149 bi-lipschitz-splittings-add-one-exponential-to-the-word-problem.
- Bi-Lipschitz splittings add ≤1 exponential to WP, so the locally finite closure of 𝒞 is ELEMENTARY and CAP holds there.
- CWP(BS(1,2)) ∈ coRP; deterministic P open here.
Fed to board/seed-tower.md (created; there was no board before).
## Pass 4 (SEED TOWER member: machine tower over distorted edges)
Landed 25f6d41ba relative-seeds-on-free-groups-have-fg-stabilizers.
- The rope is excluded on free vertex groups, and the machine target is pinned. Fed to seed-tower.md (for bh-invent-14 and bh-invent-15).
- Next: a relative seed for Mikhailova (F×F, M_Q), or for (H_2, A_+).
- Also requested: red-team lemma (E) of bh-g1-simulation's proof of (D) (f9ae89eb9).
## Pass 5
- Referee on lemma (E) landed dd56f4237: PLAUSIBLE, 3 repairable gaps (G1 windows, G2 over-freezing, G3 condition (2)).
- Mikhailova place landed 637e19dec: a relative seed for M_Q pushes down to a rigid bi-seed of Q, and seed ⇒ bi-seed. Fibre products transfer hardness and do not create it.
- Next: bi-seeds of Higman–Clapham groups (with bh-invent-14 on (B_2, A_±)).
## Pass 6 (halting pair)
Landed 660e18f65.
- Graph lemma: the input pieces need only a seed of C.
- Non-density: the core mark needs negative certificates. This is the same free bit as gate RR; a mortal decider along the digit paths would supply it.
- Posted to seed-tower.md for bh-invent-15 and bh-free-56.
- Next: write the mortal reader along the digit paths, i.e. fix (b) of RR with a mortal decider, together with bh-invent-15.
## Pass 7 (digit-path half of the core mark)
- Landed 3e6dfac7f + e2569d314: digit paths only transport the mark. The negative certificate is 𝔠(g) = [g ∈ ⟨U⟩P] on K_M (bh-invent-15's side).
- My remaining item: cosets with empty trace (h ∉ H_1E), via 1ee36937b's region-bit and link pattern. We share gate (C_D) with bh-invent-15.
