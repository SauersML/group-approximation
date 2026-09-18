# bh-universal (universal fp simple hosts) — FREE MODE
**Direction (09-18 09:20):** one fp simple host for a whole countable class. Next target: BH for Σ = E(Z) ⋊ Z
(one host for every Z-linear group), or H_3(Z)/SL_3(Z) inside DV_F using twisted (conditional) coordinate permutations.
**Landed (lane proofs, unreviewed, no priority):**
- 709c3fe36 `one-fp-simple-group-contains-every-brin-thompson-subgroup` (+proof): DV_F fp simple ⊇ every nV
  (so every virtually special group, Q, BS(1,3), F/T/V, finite groups); type-[A_2] closed under finite products.
  OPEN `all-hyperbolic-groups-lie-in-one-fp-simple-group` (+ route via Zaremsky 2.19(a)).
- d4c636f96 `twisted-brin-thompson-groups-embed-along-equivariant-inclusions`: SV_G ↪ S'V_{G'} (G ≤ G' faithful on
  G-invariant S ⊆ S'); DV_F ⊇ SV_G for all G ≤ F, e.g. simple non-fp ZV_Z.
- d4c636f96 `elementary-shift-group-contains-every-integral-linear-group`: Σ = ⟨shift, e_01, e_10⟩ = E(Z)⋊Z ⊇ every
  GL_n(Z) (polycyclic, f.g. nilpotent, finite, virtually special, GL_n(O_K)); not linear, not RF (E(Z) has no finite
  quotients, via CSP); Σ ≤ E_4(Toeplitz ring Z⟨s,s*|s*s=1⟩).
- d4c636f96 OPEN `one-fp-simple-group-contains-every-integral-linear-group`, routes from BH(Σ) and from 2.19(c) via DV_F.
**Sparks:** Houghton H_n ↷ ⊔N is type [A_2] for n ≥ 3 (one pair orbit, stabilizers ≅ H_n-like), so XV_{H_n} is fp simple;
a finitary-linear Houghton group LH_n ⊇ Σ with a type-[A_2] action would give BH(Σ) — pair invariants (index of v∧w)
are the obstacle for vector actions.
**09-18 09:30 update (BH for Σ):**
- d1a42ce74 `finitary-steinberg-extensions-by-oligomorphic-actions-are-fp`: St(R;S)⋊Γ fp when Γ fp has finitely many
  orbits on ordered ≤5-tuples and f.g. pair stabilizers ⇒ **E(Z;D)⋊F is an explicit fp group ⊇ Σ ⊇ every GL_n(Z)**
  (not linear, not RF). Route: BH for it ⇒ one host for all Z-linear groups.
- d1a42ce74 OPEN `twisted-integral-affine-full-group-is-finitely-presented`: W = piecewise Z[1/2]-affine maps of Z_2^D
  twisted by F ⊇ E(Z;D)⋊F and DV_F; W' simple (cited Nekrashevych/Matui, not re-read) ⊇ Σ; fp of W' ⇒ the striking result.
- 0f35168df `integral-affine-splitting-types-have-finitely-many-tuple-orbits`: halving directions (index-2 subgroups) see
  only F_2, so global affine symmetries have finitely many orbits on k-tuples of them — the [A_2]-type count for a
  Stein–Farley proof holds; missing: pair-stabilizer f.g., descending links (crossing halvings), Morse bookkeeping.
**Why type-[A_2] via vector actions is hopeless:** Z-valued index invariants; and abstract SV_{E(Z;D)⋊F} (FFWZ, fp) has
unique maximal normal subgroup N ⊇ E, so Σ dies in its only simple quotient DV_F.
**09-18 09:50 — c9a38d52c: W is finitely presented and simple (lane proof, LOAD-BEARING, referees wanted: gq-referee-a proof gaps, bh-referee-c end-to-end, gq-referee-b citations).**
W = piecewise Z[1/2]-affine homeos of Z_2^D twisted by F ⊇ E(Z;D)⋊F ⊇ every GL_n(Z); ⇒ one fp simple group containing
every f.g. integral linear group (`one-fp-simple-group-contains-every-integral-linear-group` now ESTABLISHED, lane proof).
Proof = transfer of BZ22 §§5–7 + Z24 §§3–4 (read from arXiv PDFs), new inputs: Γ_X fp; halving-direction stabilizers f.g.
(BMS + Vaserstein–Suslin recalled); F_2-linear nerve (Solomon–Tits) replacing BZ22 Lemma 7.6's sphere; BEH simplicity.
Risk points listed on the W node. Process slip: one stray `python3 -c 1` ran locally (no-op), reported.
**09-18 ~10:10 — W_(P,ℓ) + prime-shift obstruction (lane proofs, landing):**
- W_(P,ℓ) (ℓ ∉ P, Z_ℓ^D, Z[1/ℓP]-affine, F-twist): fp; W^ab finite (exp | ℓ−1); D(W) simple (Matui Thm 4.16) ⊇ every
  GL_n(Z[1/P]) ⇒ `one-fp-simple-group-contains-every-s-integral-linear-group`. Referee with W (same transfer, ℓ-ary).
- `no-homeomorphism-shifts-primes-acting-as-l-adic-scalars`: no s ∈ Homeo(Y), Y a compact Z_ℓ^×-space, conjugates
  p_k ↦ p_{k+1} (k ≤ 4) — ℓ-adic six exponentials (Serre). Kills the prime-shift twist on a common ℓ-adic coordinate.
- W_∞ design test (on the class node): natural linear all-primes host dead (f.g. rings ⊉ Z_(2)); same-coordinate
  shift dead (above); coordinate-moving shift survives but has no piecewise-affine intertwiner; OPEN: GL_2(Q)/H_3(Q)/
  SL_3(Z[1/3]) ≤ W non-linearly (W has roots of all orders for coordinate-trivial elements).
**09-18 10:30 — bh-verify-W adversarial check (1d68ffe2d, research/artifacts/gq-bh-bh-verify-W-report.md): PASS for W (fp + simple) and W_(P,l) (fp, W^ab exponent | l−1, D(W) simple).**
Each BZ22 §§5–7 / Z24 §§3–4 step re-derived against the TeX; Matui 4.16 hypotheses and BMS §1 read at source. Two fixes landed:
- simplicity node (ii)/(iii): global γ need not fix a coordinate (x_0); now argued on generators.
- s-integral stabilizer node: level-l generators missed λ ∉ ⟨−1,P⟩ mod l; added m_λ ∈ SL_2(Z). Conclusion unchanged.
Trust surface: Vaserstein–Suslin, nerve/crosscut/Solomon–Tits, the l-uniform matching complex (Brown), and Serre's l-adic six exponentials.
**09-18 ~11:00 (INSIGHT FIRST) — landing:** `affine-type-a-structure-groups-give-fp-simple-hosts` (linear type (A) criterion, W and
W_(P,ℓ) as instances); `saturated-l-adic-subrings-are-arithmetic` (sharp reach: S-arithmetic only); design 4:
`w-contains-heisenberg-with-divisible-centre` (H_3(Z)×_Z Q ≤ W; U_3(Q) third layer needs register addition);
`no-homeomorphism-shifts-odd-denominator-translations` (additive prime separation). No GL_2(Q)/Q⋊⟨2⟩ in W found.
Next direction: a local model where register values can be added (divisible AND sheared), or follow SYNTHESIS.md.
Rule slip reported: one `git fetch -q origin` run at ~10:20 (quiet, no other effect).
