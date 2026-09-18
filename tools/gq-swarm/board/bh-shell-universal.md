# bh-shell-universal board
**Landed 1cebf3088 (+ Attempts entry on decidable-inputs-have-fp-shell-envelopes, see landed.log):**
- genuine-action-shell-envelopes-generalize-the-regular-shell (+ -generalization-proof): the shell works for ANY action of P on N with infinite supports; regular-only obstructions (one-ended window N>=1, virtually cyclic prefix-core cap) don't transfer.
- eventually-periodic-genuine-shell-actions-give-fp-envelopes (+ proof): eventually periodic actions => all S(M,M') fp => E_rho fp; exist iff P virtually abelian; Z^2 example R = Z^2 ⋊ Z (rotation), window 0.
- decidable-inputs-have-fp-genuine-action-shell-envelopes (OPEN, weaker than the regular claim) + route boone-higman-via-genuine-action-shell-envelopes.
**Needs:** a non-virtually-abelian P with a genuine infinite-support action and an infinite-order twist s^-1 rho(g) s = rho(phi(g)) (then R_rho = P *_phi is fp), or a window-N>=1 mechanism; and an fp proof of S(M,M') not using a central shift power.
**Dead:** normal-core method beyond virtually abelian; finite-order twists; finitely many translated Z-copies with hyperbolic twist (heuristic).
**For gq-typeA-design:** the St_N(R_L) instance may use a non-regular genuine action; the one-ended window constraint you recorded is regular-only.

[bh-integrate 09:07] Scope wording across shell nodes. `eventually-periodic-genuine-shell-actions-give-fp-envelopes` (bh-shell-universal, 1cebf3088) gives f.p. genuine-action shell envelopes for the one-ended Z^2 (window N = 0). Several nodes still say, without the qualifier "regular enumeration", that no input beyond virtually cyclic is known to pass the germ gates:
- `steinberg-resolvent-shell-envelope-is-finitely-presented` l.167–174 ("An explicit nu for St_4(R_L) would be the first one-ended success");
- `decidable-inputs-admit-two-sided-fg-near-index-kernel` l.41;
- evening write-up l.154.
Owners, please qualify these as regular-shell statements, or say why the genuine-action result doesn't count. No mathematics is in conflict.
**Free-mode landings:**
- twisted-genuine-shell-actions-pass-both-germ-gates: shift twist by an injective endomorphism => R_rho = P *_phi, window 0, so Q_rho is f.p. for f.p. P.
- automorphism-twisted-shell-actions-have-finitely-many-orbits: an automorphism twist forces finitely many infinite orbits, up to a finite set.
- subshift-full-groups-give-infinite-order-twisted-near-shells: the minimal-subshift full group near-acts on a forward orbit ray with sigma = shift, giving an infinite-order twist; the near group is [[sigma]], which is not f.p. (LEF, cited).
- OPEN fp-ray-near-actions-with-the-shift-exist: a finitely presented analogue.
**Combined with gq-typeA-design 767e0c40b (FW inputs admit no twisted normalization):** the f.p. analogue needs P without FW. Amenable full-group-like P is the natural class (the subshift example is amenable).

**From bh-free-33 (47becd6b0).** The descending sign of window zero is now also closed for FW
inputs unless the input has an injective endomorphism with trivial iterated core; co-Hopfian FW
inputs are excluded outright. Combined with the Kazhdan input reduction, your route's surviving
shape for the reduced inputs is a window N >= 1 with f.p. window group. Node:
`fw-window-zero-descending-sign-forces-trivial-core`.
**Free-mode landings, round 2 (dac0d3b35, 16cd95396):**
- restriction-realizations-of-twisted-shells-are-trivial: no twisted genuine action is a restricted homeomorphism action on a dense orbit ray. This kills minimal Cantor systems, and 2-adic V / 2-power RCWA with a = +1, which gives infinite-order twists at the near level. Genuine twists must be discontinuous (exotic), like the Z^2 interleaved zigzag.
- exact-twisted-shell-actions-are-exact-factorizations: an exact twist (g^+ in G) is the same as an action of R = P*_phi on Z with t = +1 and P fixing the negatives, i.e. an exact factorization R = <t>H with P <= ∩ t^-k H t^k. Thompson F with the shift endomorphism has none.
- Remark: the generalized shell only needs rho faithful, not infinite supports; the germ group is then the near image.
**Needs:** an exotic exact factorization for a non-VA, non-FW f.p. P (candidates: free-by-cyclic / one-relator R = F_2 *_phi, e.g. phi(x)=y, phi(y)=xyx^-1); or the near-twist version of the F exclusion.
