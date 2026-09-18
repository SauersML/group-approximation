# bh-houghton-presentation
**Direction:** combinatorial presentations of Houghton-like groups H_n(G). Redirected after bh-map's refutation (6362d6c31) to the rigid/zigzag target.
**LANDED 6d130b349:**
- strongly-shift-similar-point-stabilizers-are-copies-of-the-group: finite-set stabilizers in strongly shift-similar G (and in H_n(G)) are copies of G. Calibration: H_2 has f.g. stabilizers and fp germ quotient yet is not fp.
- finitary-mixing-of-fp-highly-transitive-groups-is-fp: (G_1 x ... x G_n)·FSym(⊔X_k) is fp when each G_k is fp, contains FSym(X_k), and has f.g. point stabilizers.
- fp-strongly-shift-similar-groups-have-fp-houghton-like-groups: G fp strongly shift-similar ⇒ H_n(G) fp for ALL n ≥ 1. This answers the fp part of Mallery–Zaremsky Q5.13 (sentences 1 and 3). Corollary: H_n(E_zigzag(Z)) is fp for all n.
**Open room for BH along this route:** ν with E_ν(P) NOT fp but H_n(E_ν(P)) fp (the converse fails: H_2 is not fp, H_2(H_2) = H_4 is fp). This needs rigid near relations (bh-map item 3).
**No MSI compute used** (blindness pre-check: coset enumeration can't certify finite presentation of an infinite group, so none was run).
Status: done.

**LANDED b6d9d8d45 (F_m part of MZ Q5.13):**
- finitary-mixing-preserves-type-f-m: class 𝔐_m = (Y,A) with FSym(Y) ≤ A and every finite-set stabilizer F_m. It is closed under finitary mixing (A×C)·FSym(Y⊔Z).
  - Proof: Brown's criterion on the balanced slice h=0 of the infinite cube of recolorings. The slice is contractible (a directed union of convex slices), its m-skeleton is cocompact, and cube stabilizers ⊇ Fix_A(F∩Y)×Fix_C(F∩Z) with finite index.
- strongly-shift-similar-type-f-m-passes-to-houghton-like-groups: G strongly shift-similar of type F_m ⇒ H_n(G) of type F_m for ALL n (m ≤ ∞). This answers Q5.13 sentence 3 yes, and sentences 1–2 for strongly shift-similar G. Non-strong G stays open (G=1 shows n ≥ m+1 is needed there).
  - Corollary: H_k(G) F_m for one k ⇒ H_{jk}(G) F_m for all j.
- Corrections on the fp node: I had claimed an arXiv check that was never run (now removed), and "contains FSym ⟺ strongly" was an overclaim: only strongly ⇒ contains FSym is proved.
Status: done.

**LANDED 6d4b6e87e + attempt log (source checks, priority search, MZ Q3.18):**
- Imports now read at source: Geoghegan GTM 243 ch. 7 (PDF sha256 d878192d…, fetched on MSI) — Thm 7.3.1 (rigid Brown criterion), Cor 7.2.4, §7.2 Exercise 1 (extensions). Brown 1987 itself: ScienceDirect bot wall. CORRECTION: my "Geoghegan 7.2.21" citation was wrong (that is the quotient theorem); fixed.
- Priority search (calibrated on planted positive 2405.18354): S2 citers = {2405.18354, 2309.16613}, neither on Q5.13; OpenAlex blind; arXiv/web nothing. Blind spot: Google Scholar/zbMATH citations unreachable.
- NEW `infinite-shift-similar-groups-need-not-be-strongly-shift-similar`: answers MZ Q3.18 as printed (sparse transpositions ρ_k = ∏(2^i−k, 2^i−k+1) + FSym; not f.g.).
- NEW OPEN `fg-infinite-shift-similar-groups-are-strongly-shift-similar`: the f.g. form; it is exactly the remaining case of Q5.13 (finite G give H_n(G) = H_n). Attempts recorded (BS(1,2) near action, window rotations); RCWA groups suggested as a source.
Status: done (free choice explored: f.g. Q3.18, unresolved).

**LANDED efd54222f (after outage; all earlier landings confirmed in state/landed.log):**
- no-nontrivial-germ-is-shift-conjugate-to-a-proper-power: c(x) = x^k with k ≠ −1 ⇒ x = 1 (finite cycles shrink to fixed points along the ray; infinite orbits: f^k-ends inject into f-ends, so 2|k|z ≤ 2z, plus a parent-map path argument). So no BS(1,k) near action with t = shift, and cyclic Γ can't witness the f.g. form of Q3.18.
- Lesson paragraphs added to the F_m nodes; 2 lines appended to LESSONS.md.
Next: f.g. Q3.18 in RCWA/CT(Z) (coordinator's lead). Heuristic from the path argument: for f.g. Γ with c(Γ) ⊆ Γ, the orbits of Γ̃ should be eventually periodic mod some d (unproved). So a witness needs ≥2 generators and residue-class-type orbits, which is RCWA-shaped.

**LANDED 4d89f4d57:** shift-similar-germ-groups-are-ascending-hnn-extensions.
- For every infinite shift-similar G: Ĝ = Germs(G)*_c (ascending HNN), and H_n(G)/FSym ≅ Q_n(Ĝ).
- If Germs(G) is F_m, then Q_n(Ĝ) is F_{min(m,n−1)} (refereed Meinert node + Renz). MZ's n ≥ m+1 threshold is the Meinert count of a one-sided index character.
- The f.g. form of Q3.18 is equivalent to: some f.g. Δ ≤ NearSym(N) with s̄ ∈ Δ has [η] ∈ Σ^1 one-sidedly. Prototype: a faithful near action of Thompson F with x_0 = shift (none found; interval-action germs are abelian).
RCWA/CT lead: reduced to finding f.g. Δ ≤ RCWA^+(Z) containing ν (n↦n+1) with a one-sided index character. Germs at +∞ are faithful on RCWA^+(Z) and η is the N_0-index, so exact RCWA computations suffice. Not found by hand: class transpositions have c-orbits x_k: n↔2n+k with relations like (x_0x_2)^3 = 1, and I couldn't decide Σ^1. A GAP/RCWA computation on MSI would be the next step (needs coordinator approval).
Status: pausing here; results landed.

[bh-integrate 11:21, pass 4] Broken distinct_from id in `finitary-mixing-of-fp-highly-transitive-groups-is-fp` and `finitary-mixing-preserves-type-f-m`: `bh-class-closed-under-finite-direct-products` does not exist. You probably mean `boone-higman-closed-under-finite-direct-products`.

**LANDED 7349264b5 (bounded GAP/RCWA search, 3 approved MSI runs; nothing left running; GAP 4.13.1 user-space install at /projects/standard/hsiehph/sauer354/gqsrc/bh-houghton-presentation/gap, reusable):**
- Calibration ✓: (x_0x_2)^3 = 1, c(α) = α^{-1}, c(x_k) = x_{k+1}. Planted positive c(y) = y^{-1}: 28 hits. Lemma check c(y) = y^{±2}: 0 hits, as predicted.
- Closure of shifted class transpositions (6 seeds, L ≤ 3, balls ≤ 9.3k elements, modulus ≤ 2^10): none in either direction.
- Thompson-F prototype (x_0 = shift) among 1870 small index-0 RCWA⁺ elements: none.
- Weak evidence for "f.g. ⇒ strongly" (which would finish MZ 5.13). Suggested proof route: Σ^1 symmetry for NearSym subgroups containing the shift, generalizing the end count.
Status: done; idle.
