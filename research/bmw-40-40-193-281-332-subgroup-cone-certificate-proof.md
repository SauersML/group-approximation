---
rg: 2
id: bmw-40-40-193-281-332-subgroup-cone-certificate-proof
kind: route
title: An unsatisfiable positive-cone certificate on the radius-4 ball of the subgroup <x, y, f x^-1 f, g y^-1 g> of the parity kernel, checked by an independent verifier with three solvers and a DRUP proof
target: bmw-40-40-193-281-332-parity-kernels-not-left-orderable
requires: []
artifacts:
  - experiments/bmw-44-survivor-left-orders-2026-09-17/README.md
  - experiments/bmw-44-survivor-left-orders-2026-09-17/verify_cert.py
  - experiments/bmw-44-survivor-left-orders-2026-09-17/verify.log
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_193.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_281.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/cert_332.json
  - experiments/bmw-44-survivor-left-orders-2026-09-17/certgen.py
  - experiments/bmw-44-survivor-left-orders-2026-09-17/certgen.log
  - experiments/bmw-44-survivor-left-orders-2026-09-17/gen_search.py
  - experiments/bmw-44-survivor-left-orders-2026-09-17/gs193.log
  - experiments/bmw-44-survivor-left-orders-2026-09-17/gs332.log
  - experiments/bmw-44-survivor-left-orders-2026-09-17/gs0.log
  - experiments/bmw-census-left-orders-2026-09-17/census_40_40.json
---

This is a finite computation. The certificate is found by `certgen.py`, but the proof does not depend on how it
was found. It rests only on the census data, the three certificate files and `verify_cert.py`, which shares no
code with the search.

## 1. The group and normal forms

`census_40_40.json` gives, for each class `c`, the 16 squares as a map `SQ_c : (h, v) ↦ (v', h')` on
`{0..3} × {0..3}`. Each square means the relation `h v = v' h'`. The group is
`Γ = ⟨v_0..v_3, h_0..h_3 | v_i^2, h_j^2, h v = v' h' for all squares⟩`.

Since the letters are involutions, `h v = v' h'` is equivalent to `v h = h' v'`, so the reading of a square does
not matter.

Consider the rewriting system `R = {x x → 1 for each letter x} ∪ {h v → v' h' : SQ(h, v) = (v', h')}`.
- **It terminates.** Every rule either shortens the word, or keeps its length and lowers the number of pairs
  (horizontal letter before vertical letter).
- **It is locally confluent.** The critical pairs come from the overlaps `h h v` and `h v v`. `verify_cert.py`
  checks all 32 of them: `h · v' h' ⇝ v` and `v' h' · v ⇝ h`, in its lines 31-36.
- **Unique normal forms.** By Newman's lemma, each element of `Γ` has a unique irreducible word. That word is a
  freely reduced vertical word followed by a freely reduced horizontal word, and `verify_cert.py` asserts this
  shape. So `g = 1` in `Γ` if and only if its normal form is empty.
- **The squares are a VH-datum.** `SQ` is a bijection `H × V → V × H`. `verify_cert.py` asserts this, which is
  the vertex-transitive BMW condition.

The parity map `Γ → (Z/2)^2` counts vertical and horizontal letters mod 2. The relations preserve these counts,
so the map is well defined. Its kernel `Γ^+` is the parity kernel. An element lies in `Γ^+` if and only if its
normal form has even vertical and even horizontal length.

## 2. The positive-cone lemma

**Lemma.** Let `G` be a left-ordered group and `P = {g > 1}` its positive cone. Then:
- `P ∩ P^{-1} = ∅`;
- `P ∪ P^{-1} = G \ {1}`;
- `P P ⊆ P`.

So take any finite set `E ⊂ G \ {1}` closed under inversion, and relations `e_p e_q = e_c` among its elements.
Setting `p_e := [e ∈ P]` satisfies these clauses:
- `(p_e ∨ p_{e^{-1}})` and `(¬p_e ∨ ¬p_{e^{-1}})`, for each `e ≠ e^{-1}`;
- `(¬p_{e_p} ∨ ¬p_{e_q} ∨ p_{e_c})` for each relation, and `(¬p_{e_p} ∨ ¬p_{e_q})` if the product is 1.

Two remarks on soundness:
- If two variables happened to denote the same group element, the real cone still satisfies the clauses. Unique
  normal forms rule this out anyway.
- The inversion clauses need `e ≠ 1` and `e ≠ e^{-1}`. The verifier asserts both.

So an unsatisfiable CNF of this form shows that `G` has no left order. Left orders restrict to subgroups, so the
same holds for every group containing the elements of `E`.

## 3. The certificates

`cert_c.json` (c = 193, 281, 332) lists 333 elements, as normal-form strings `V-word|H-word`, and 420 relations
`[p, q, c]`. For each class, `verify_cert.py census_40_40.json cert_c.json` checks the following
(`verify.log`):

1. `SQ_c` is a bijection, and `R` is locally confluent.
2. Every listed element is a nonempty normal form of even vertical and horizontal length, so it is a nontrivial
   element of `Γ^+`. Its square is nontrivial.
3. Every relation `e_p e_q = e_c` holds: the concatenated word rewrites to the normal form of `e_c`.
4. The CNF of §2 has 490 variables (the elements and their inverses) and 910 clauses. Glucose 4, MiniSat 2.2 and
   CaDiCaL 1.5.3 all report UNSAT.
5. Glucose's DRUP refutation is replayed by the reverse-unit-propagation checker `rup_check` in `verify_cert.py`.
   Every lemma must be RUP with respect to the input clauses and the earlier lemmas, and the empty clause must be
   derived. Deletions are ignored, which is sound. The replay returns `True`, with 151 lemmas for #281 and #332,
   and 291 for #193.

By §2 and §3, `Γ^+` has no left order, for each of the three classes. ∎

The elements are products of the four generators of `M = ⟨x, y, f x^{-1} f, g y^{-1} g⟩`:

| class | x | y | f | g | `certgen.py` arguments `i j f k l g` |
|---|---|---|---|---|---|
| #281 | `v0v1` | `h0h1` | `v3` | `h3` | `0 1 3 0 1 3` |
| #332 | `v0v1` | `h0h1` | `v3` | `h3` | `0 1 3 0 1 3` |
| #193 | `v1v3` | `h1h2` | `v2` | `h3` | `1 3 2 1 2 3` |

So `M` itself is not left-orderable. The proof does not use this. The elements all lie in the ball of radius 4 in
`M`'s generators, and the certificate was cut out of that ball's positive-cone instance, which has 3169 elements.
In each relation, one factor has generator length at most 2.

## 4. Controls

- **Calibration.** `gen_search.py 0 4 2` (`gs0.log`) runs the same instance for all 144 subgroups of this shape in
  the product class `#0`, where `SQ(h, v) = (v, h)`. There `Γ^+ = W_4^+ × W_4^+ ≅ F_3 × F_3`, which is left-orderable. All 144 instances are SAT, as they must be.
- **Search.** In `#193` and `#332`, exactly one of the 144 subgroups gives UNSAT at radius 4 with short factor 2
  (`gs193.log`, `gs332.log`). In `#281` the UNSAT subgroup was found first by other means, from the Z²-kernel
  `N = A ⋈ B` of `Γ^+`.
- **Earlier letter balls.** The letter-ball instances of the census stayed SAT up to radius 10, because the
  certificate's elements have up to 14 letters and many of its relations have both factors 6 or 8 letters long.
