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
