# gq-referee-c — third referee (independent re-derivation + calibration)

**Approach.** Referee only. Re-derive without the author's text, then calibrate against O1–O3, distortion, FW,
and "what does it use that Q has and Z[1/m] lacks". Verdict artifacts: research/artifacts/gq-referee-c-<id>.md.

**Verdicts landed (09-17):**
- 4529c10a3 leavitt-pairs-embed-sl-n-q-in-steinberg-groups: PASS (self-contained swindle; +1 rank = room lemma;
  S^N ≅ S^2N only in the square swap).
- f7c7c3e04 leavitt-resolvent-ring-is-fp-simple-of-char-zero: PASS by an independent proof (compression along an
  aperiodic word to f(k) ∈ Q^x); all four non-Leavitt relations needed (char-p quotients / Toeplitz ideal).
- b16f34bc0 gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups: PASS.
- b16f34bc0 sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially: PASS (H_m step removed by the author,
  ea82341f9).
- b16f34bc0 bffhz-closures-cannot-create-gl-n-q + gl-n-q-fixes-a-vertex-in-free-splittings: PASS, 4 wording
  fixes (applied by the author, 1300752a6).
- a9cc1c9a7 finitely-presented-divisible-ring-engine: PASS.
- a9cc1c9a7 one-steinberg-group-contains-every-gl-n-q: PASS conditional on classical inputs; C1 (centrality of
  K_2(4, M_k(Q)), van der Kallen sr+2) is load-bearing and needs a source check.

- 5d6390c47 steinberg-finite-presentation-and-kazhdan-theorem:
  - PASS for n >= 5 by a direct elementary proof (explicit presentation, any finitely presented ring);
  - n = 4 is still a Krstić–McCool import (primary text unread);
  - the companion quotient node also PASSES;
  - St_5(D) variant suggested to team-lead.

- 894d10d19 renormalizable-thompson-elements-give-baumslag-solitar: PASS; the infinite-order hypothesis is
  redundant.
- 894d10d19 smart-induced-map-has-brick-local-height-3-renormalization and bs13-in-3v-via-smart-renormalization:
  PASS, so BS(1,3) ≤ 3V once referees a and b agree. Priority is not yet checked.

- 7dad6752e matricial-divisibility-kills-rational-k2-symbols: PASS. Fact (D) re-derived from Milnor Theorems
  5.1, 5.10 and 11.6.

- ce6547e91 clopen-crossed-product-subrings-have-local-annihilation, sl3-toeplitz-harmonic-pe-groups-are-simple
  and q-algebra-host-via-sl3-toeplitz-harmonic-ring: PASS (second pass). Conditional on R_T ring parts 1–3,
  which I have not reviewed.

- 282b018d4 PASS on four trust surfaces:
  - smart-induced-on-genuine-moves-has-exact-tripling;
  - brin-thompson-first-return-maps-lie-in-kv;
  - the SMART prefix-code encoding into 2V (table reversibility checked);
  - leavitt-nekrashevych-completion-simplicity-criterion, with its embedding input and the application to R_k.

- dc754467b q-embeds-in-a-corner-of-a-fp-toeplitz-ring and gl-n-q-embeds-in-e-n-plus-1-of-a-fp-ring: PASS. This
  covers the model, the Limits remark, Ψ, finite generation, and the word problem in the model.

- 418581fee resolvent-presentation-ring-is-residually-finite and resolvent-ring-has-path-normal-form: PASS for
  every prime l, with a wording nit on the copy index.

**Needs (for the Problem 2.7 routes).** C1, the centrality of K_2(r, M_k(Q)), which gq-referee-b is checking.
**Dead.** —
**Status.** Idle; waiting for review requests.
