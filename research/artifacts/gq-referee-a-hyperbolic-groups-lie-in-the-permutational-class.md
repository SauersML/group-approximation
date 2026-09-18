# Referee report (gq-referee-a, proof-gap lens): hyperbolic groups lie in the permutational class

**Reviewed** (lane bh-typeA-universal), read on origin/main:
- `hyperbolic-groups-lie-in-the-permutational-class` and its route `hyperbolic-groups-in-b-a-proof` (fa1747017,
  fixed in 6932547c3);
- at lower priority, `bbmz-oligomorphic-and-twisted-questions-are-pbh-forms` and its proof (6932547c3).

**Verdict: PASS for both.** Given the four quoted BBMZ inputs and the landed closure nodes, the logic is complete.
There are two nits.
- The BBMZ quotes are for the citation lens, as are Hermiller–Meier, FFWZ Theorem C and the twisted Brin–Thompson
  criterion.
- I did not reread the BBMZ TeX on MSI (l.1752–1834).

## 1. `hyperbolic-groups-in-b-a-proof`
- **Step 2: the four type (A) conditions.**
  - *Faithful.* `S` is dense in `E`, and two homeomorphisms agreeing on a dense set are equal, so (d) gives
    faithfulness.
  - *Finitely presented.* This is (a).
  - *Finitely generated stabilizers.* The type (A) definition asks for `Stab_G(s)` finitely generated for **every**
    `s ∈ S`. (c) gives it for rational points. Every `s = gω` has `Stab(s) = g Stab(ω) g^(−1)`, so one rational
    point suffices (N1).
  - *Pairs.* High transitivity (b) on the orbit `S` gives one orbit of ordered pairs of distinct points, hence one
    orbit of two-element subsets. `S` is infinite, being dense in `E`. ✓
- **Step 3.**
  - Hyperbolic groups embed in full contracting RSGs, by the cited theorem.
  - A contracting self-similar group is finite-state. For each `g`, the sections at words longer than some `n_g` lie
    in the finite nucleus, and there are only finitely many sections at shorter words.
  - So `G ≤ V_n(G)`, which is a full contracting RSG by BBMZ Example `ex:rn` and the remark after it. ✓
  - Subgroup-closure holds by definition of `B_A`.
- **Step 4.** Direct products, finite-index overgroups, free products and graph products are the cited closure
  nodes. The mixed examples use landed `B_A` members. ✓
- **Step 5.** The automatic and CAT(0) bearings rest on unpinned inputs, and items 1–3 do not use them, as stated. ✓

## 2. `bbmz-oligomorphic-twisted-questions-proof`
- **Step 1: oligomorphic, with finitely presented finite-set stabilizers.**
  - *The pointwise stabilizer.* The pointwise stabilizer `P` has finite index in `Stab_D(F)`.
    - `g ∈ P` exactly when `g` preserves each nonempty Boolean atom of `F`: each `U ∈ F` is a union of atoms, and each
      atom is an intersection of the `U`s and their complements.
    - `D` is full, so `g` is the product of its restrictions extended by the identity. So `P = ∏ D(A_i)`, with commuting
      disjoint supports.
  - *Each factor is a copy of `D`.* Take a `D`-local `f : C^S → A_i`. Conjugation by `f`, extended by the identity, is
    `D`-local, so fullness gives `D(A_i) ≅ D`.
  - *Conclusion.* So `P ≅ D^m` is finitely presented, and so is its finite-index overgroup. ✓
- **Step 2.**
  - Question 1.5 ⇒ PBH, via Clapham: an oligomorphic permutation group has finitely many orbits on `S^2`, and its
    one-point stabilizers are finitely generated, so it is of type (A).
  - The converse is Step 1. ✓
- **Step 3.** Both directions use the twisted Brin–Thompson criterion as an equivalence, as cited. The faithful
  reading is then "every finitely presented simple group lies in `B_A`". ✓
- **Step 4.** If `K ≠ 1`, then `λ(K) ≠ 1` lies in the proper normal subgroup `SK_G`, so `SV_G` is not simple, and the
  parenthetical "(simple)" fails. ✓

## Nits
- **N1 (hyperbolic, Step 2).** Add the conjugation line `Stab(gω) = g Stab(ω) g^(−1)`, or note that orbits of rational
  points consist of rational points. The type (A) definition needs finitely generated stabilizers at every point of
  `S`.
- **N2 (bbmz, Step 1).** Say explicitly that `P` equals `Stab_D` of every atom. Clopen transitivity then applies to each
  atom, because the atoms are nonempty clopen sets.
