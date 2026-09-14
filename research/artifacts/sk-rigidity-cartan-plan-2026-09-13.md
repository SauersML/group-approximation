# sk-rigidity-cartan plan (2026-09-13)

## Target (brief, sk/ROSTER-D.md)
Cartan uniqueness for `R_X = LC(X,F_2) ⋊_T Z`, where `X` is an infinite minimal subshift. Is every maximal
commutative, idempotent-spanned subalgebra whose normalisers span `R_X` the image of the diagonal `D_X = LC(X,F_2)`
under a ring automorphism?

This is step (ii) of Firewall F2 in `research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md`.
- Together with Theorem A (`subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`, PASS) and a recognition
  step (i), it would give "`G_X ≅ G_Y` iff flip conjugate".
- It is also the ring rigidity question "`R_X ≅ R_Y` as rings ⇒ flip conjugate".
- Its C*-analogue is false: Giordano–Putnam–Skau (1995) show that `C(X)⋊Z` sees only strong orbit equivalence.

## Not duplicated
- sk-rigidity-f2 owns step (i): standardness of `EL_3` isomorphisms, and recognition of root subgroups.
- sk-rigidity-ring landed Theorem R: a matrix ring isomorphism forces strong orbit equivalence.
- sk-rigidity-intrinsic landed Theorem A: diagonal-preserving rigidity.

## Plan
1. **Precise formulation** through algebraic Cartan pairs (Armstrong–de Castro–Clark–Courtney–Lin–McCormick–Ramagge–
   Sims–Steinberg, IMRN 2021, arXiv:2101.08556).
   - Over `F_2` the unit group is trivial, so discrete twists are trivial.
   - Algebraic Cartan subalgebras of `R_X` then correspond exactly to effective ample Hausdorff groupoid models of `R_X`.
   - Import the definitions and theorems verbatim from the arXiv source.
2. **Theorem C (reduction):**
   - Cartan uniqueness for `R_X` ⟺ every effective ample Hausdorff `G` with `A_{F_2}(G) ≅ R_X` is ≅ the
     transformation groupoid of `X`.
   - Every such model is minimal with Cantor unit space.
   - Uniqueness for `X` gives ring rigidity at `X`.
   - It also gives group rigidity at `X`, given step (i).
   - Diagonal-preserving reconstruction: Steinberg, arXiv:1711.01903, Cor `c:effective.case.gpd.rec`.
3. **Theorem G (ring invariants):** `R_X ≅ R_Y` ⇒ strong orbit equivalence (Theorem R), plus equivalent growth
   `n·p_X(n) ≈ n·p_Y(n)`, via Nekrashevych, IJAC 26 (2016), Prop `pr:shiftgrowth`.
   - So entropy zero and the upper polynomial complexity exponent are ring invariants.
   - Ring isomorphism is then strictly finer than strong orbit equivalence whenever one class contains subshifts of zero
     and of positive entropy. The realization theorem (Boyle–Handelman; Sugisaki) must be checked at source,
     expansivity included.
4. **Attack uniqueness itself:**
   - an intrinsic recognition of `D_X` among Cartans; or
   - a non-conjugate Cartan, i.e. a ring isomorphism `R_X ≅ R_Y` with `X, Y` not flip conjugate.
   Record the dead routes as Attempts.
5. **Proposal:** expected no change to the note. Q3 of the questions paragraph stays open.

## Landings
- The open claim `subshift-crossed-product-algebraic-cartans-are-conjugate`, with Attempts.
- Citation imports, and Theorems C and G with proof routes.
- Artifact part 1 (proofs), then the proposal.
- Review requests go to `sk/queue/sk-verify-5.txt`.
