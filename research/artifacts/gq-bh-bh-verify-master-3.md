# bh-verify-master, item 3: `zero-set-confinement-unifies-host-obstructions`

Adversarial check by lane bh-verify-master, 2026-09-18, read on origin/main at 6481dbd30 (node landed in
5f923fc28). Lane check, not an external review.

**Verdict: PASS for the Theorem. CORRECTION for the "Instances" and "Lesson" framing.**

## The Theorem, items 1–4: correct

- **Lengths.** (L1)–(L4) are lengths.
  - (L2) is symmetric because `‖b(g⁻¹)‖ = ‖−π(g⁻¹)b(g)‖ = ‖b(g)‖` for an orthogonal representation `π`.
  - (L3) is symmetric because `|g⁻¹M △ M| = |M △ gM|`.
- **Existence of ν.** Fekete gives the limit `ν = inf ℓ(g^m)/m`.
- **Item 1.** Homogeneity uses a subsequence plus symmetry. Conjugation invariance comes from
  `|ℓ(hg^mh⁻¹) − ℓ(g^m)| ≤ 2ℓ(h)`.
- **Item 2.** `ν(u) = |n| ν(u)` with `ν(u) < ∞`, so `ν(u) = 0`.
  - `R(s,u)` is an ascending union, because `u = s⁻¹u^n s ∈ s⁻¹⟨u⟩s`. So it is a group.
  - Its elements `s^{-k}u^j s^k` have `ν = 0` by item 1.
- **Item 3.**
  - (FH) makes `b|_K` a coboundary, so `ℓ` is bounded on `K`.
  - FW transfixes `M` by some `K`-invariant `M'` with `|M △ M'| = c`, so `|gM △ M| ≤ 2c` on `K`.
  - (T) ⇒ (FH) ⇒ FW.
- **Item 4.** It is immediate from items 2 and 3.

## Correction: the Kazhdan half is bounded-set confinement, not zero-set confinement

Item 3 proves that `ℓ` is **bounded** on `K`, which is strictly stronger than `K ⊆ Z(ν)`. The exclusions
listed for the Kazhdan half use that boundedness, together with properness or finiteness of bounded sets.
Zero-set confinement alone would not give them.

- **Counterexample to the zero-set reading.** On `Z` take `ψ(n) = |n|`, which is conditionally negative
  definite. Then `ℓ = √ψ` is proper and `ν ≡ 0`, so `Z(ν) = Z`. The zero set is not confining, but bounded
  sets of `ℓ` are finite.
  - So "Z(ν) small" is the wrong criterion for Haagerup-type exclusions.
  - The right one is "ℓ-bounded subsets are small", i.e. properness.
- **Affected instance lines.**
  - "V is Haagerup (Farley)". The line reads "Z(ν) ∩ K bounded". It should read: `ℓ` is bounded on `K`
    by item 3, and `ℓ` is proper, so `K` is finite.
  - "Germ localization". This is bounded (L3)-length on FW subgroups.
  - "FW shell windows". The near index is a character that vanishes on FW groups; that is again a
    boundedness or homomorphism statement.
- **Unaffected instance lines.** These are genuine zero-set confinement:
  - proper cocompact CAT(0): the zero set is the torsion;
  - movement and entropy in nV;
  - slopes at periodic points;
  - central elements of Kazhdan subgroups of 2V.

**Corrected unifying statement.** A host excludes rigid (FH/FW) subgroups when its natural lengths are
*proper*, i.e. bounded sets are confining. It excludes Baumslag–Solitar root groups when its natural
stable lengths have *confining zero sets*. These are two related but distinct mechanisms. For
proper-length hosts in the second case, zero sets need not be small.

## Effect on the design specification (D1–D6 of the obstructions synthesis)

The design conclusion survives in this form:
- a host for the reduced input class must have natural lengths that are **not proper** on some infinite
  Kazhdan subgroup;
- for Baumslag–Solitar-type inputs, it must have **non-confining zero sets**.

The node's phrase "non-confined zero sets" should be read with this split in mind.

A short Attempts note recording the correction was added to the node in this landing.

## Lesson for general BH

The two walls are distinct:
- **Kazhdan wall:** properness of cocycle and wall lengths.
- **Distortion wall:** zero sets of stable lengths.

A host can break one without the other. Proper cocompact CAT(0) groups kill Baumslag–Solitar roots through
the zero set but say nothing about Kazhdan subgroups. Haagerup groups kill Kazhdan subgroups through
properness, while their zero sets can be everything.
