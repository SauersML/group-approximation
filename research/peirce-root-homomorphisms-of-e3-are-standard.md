---
rg: 2
id: peirce-root-homomorphisms-of-e3-are-standard
kind: claim
title: A homomorphism E_3(R) → M^× that maps the six root subgroups onto the Peirce root groups of three full orthogonal idempotents is the restriction of a ring isomorphism M_3(R) ≅ M
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part1.md
distinct_from:
  root-preserving-el3-isomorphisms-give-ring-isomorphisms: that assumes the standard root subgroups of E_3(S), needs S directly finite, and gives R ≅ S; this allows any decomposition into full orthogonal idempotents, needs no direct finiteness, and gives the whole isomorphism M_3(R) ≅ M implementing the homomorphism
  subshift-el3-isomorphisms-are-standard-over-f2: that open claim asks whether every isomorphism of the note's groups is standard; this shows that standardness is equivalent to carrying root subgroups onto Peirce root groups
---

Let `R` and `M` be unital associative rings. Let `1 = E_1 + E_2 + E_3` in `M`, with the `E_k` orthogonal idempotents
and `M E_k M = M` for each `k`. For `i ≠ j` put `P_ij = 1 + E_i M E_j`, an abelian subgroup of `M^×`, and
`A_ij(R) = {e_ij(r) : r ∈ R} ≤ E_3(R)`.

Let `α: E_3(R) → M^×` be a group homomorphism that maps `A_ij(R)` bijectively onto `P_ij` for all `i ≠ j`. Write
`α(e_ij(r)) = 1 + φ_ij(r)` and `a_ij = φ_ij(1)`, `a_ii = E_i`. Then:
1. `(a_ij)` is a full system of `3 × 3` matrix units in `M`: `a_ij a_kl = δ_jk a_il` and `Σ_i a_ii = 1`.
2. `θ(r) = φ_12(r) a_21` is a unital ring isomorphism `R → E_1 M E_1`.
3. `Θ(Σ r_ij E_ij) = Σ a_i1 θ(r_ij) a_1j` is a ring isomorphism `M_3(R) → M`, and `α = Θ|_{E_3(R)}`.

Consequences:
- A homomorphism `E_3(R) → GL_3(S)` is standard (the restriction of a ring isomorphism `M_3(R) → M_3(S)`) iff it maps
  the root subgroups onto the Peirce root groups of some decomposition of `I` into three orthogonal idempotents.
  Nonzero idempotents of a simple ring are full, so for simple `S` any nonzero decomposition qualifies.
- For `M = M_3(S)` and `E_k = E_kk` (always full), `R ≅ E_11 M_3(S) E_11 = S` with no hypothesis on `S`. So the
  direct-finiteness hypothesis of `root-preserving-el3-isomorphisms-give-ring-isomorphisms` can be dropped.
- Only the Steinberg relations `[e_ik(r), e_kj(s)] = e_ij(rs)` are used, so the same holds for `St_3(R)`.

Status: proved in `peirce-root-homomorphisms-of-e3-are-standard-proof`, unreviewed.

**Review (sk-verify-15, 2026-09-13): PASS.** Peirce commutator identity, Step 1 (fullness gives a_ik a_ki = E_i), matrix units, multiplicativity of θ via a_23a_31 = a_21, Θ, and all six index pairs of Step 5 re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §3.
