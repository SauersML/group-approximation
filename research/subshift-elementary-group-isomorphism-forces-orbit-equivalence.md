---
rg: 2
id: subshift-elementary-group-isomorphism-forces-orbit-equivalence
kind: claim
title: If EL_3(LC(X,F_q)⋊Z)/Z ≅ EL_3(LC(Y,F_q)⋊Z)/Z for infinite minimal subshifts X, Y, then X and Y are strongly orbit equivalent
---

**OPEN.** Let `X, Y` be infinite minimal subshifts and `q` a prime power, and suppose `S_X ≅ S_Y`
(notation of `marked-subshift-elementary-group-determines-language`). Are `(X,T)` and `(Y,T)` strongly orbit
equivalent, i.e. do they have isomorphic unital ordered dimension groups `K^0(X,T)`? Stronger variants: flip
conjugacy, or conjugacy.

The easy direction holds. Conjugacy, or flip conjugacy (`u ↦ u^(-1)`), gives `R_X ≅ R_Y` and hence `S_X ≅ S_Y`.
Countable fibres (`continuum-many-simple-kazhdan-lef-groups`) show that `S_X` remembers `X` up to countable
ambiguity, but not which `X`.

## Attempts

- **Route through ring isomorphism theorems (unverified, lane un-open-5).**
  1. An isomorphism `PE_3(R_X) ≅ PE_3(R_Y)` should be standard: induced by a ring isomorphism or anti-isomorphism
     `M_3(R_X) ≅ M_3(R_Y)`, composed with conjugation. Candidate sources: Golubchik–Mikhalev and Zelmanov, 1983–85,
     on isomorphisms of `GL_n`/`E_n` over associative rings for `n ≥ 3`. Their hypotheses on `2` may exclude
     `q` even; this has not been read from the PDFs.
  2. Morita invariance keeps `(K_0, [R^3])`. For the regular ring `LC(X,F_q)`, the algebraic Pimsner–Voiculescu
     (Farrell–Hsiang) sequence should give `K_0(R_X) ≅ C(X,Z)/(1−T)C(X,Z) = K^0(X,T)`, since `K_(−1)` of a regular
     ring vanishes. The positive cone and anti-isomorphisms must be checked.
  3. Giordano–Putnam–Skau: the unital ordered `K^0` classifies strong orbit equivalence. The unit becomes `3[1]`,
     so the conclusion may only be "strongly orbit equivalent after scaling the unit". Record the exact form.
  Where it could die: step 1 for `q` even, or with non-standard isomorphisms; the order on `K_0` in step 2.
- **Firewall.** The approximation type of `S_X` (LEF, MF, (T), simple) is the same for every `X`, so no
  approximation invariant distinguishes these groups. Any separation must come from isomorphism-theoretic or
  computability invariants (see `subshift-elementary-group-word-problem-equals-language`, lane un-open-5, in
  progress).
