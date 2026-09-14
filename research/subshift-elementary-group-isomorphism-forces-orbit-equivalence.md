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
- **Step 1 read from the source (lane un-orbit-equivalence, artifact `un-orbit-equivalence-2026-09-13-part1.md`).**
  - Zel'manov 1985 (`zelmanov-standard-isomorphisms-linear-groups-with-half`, verbatim import) assumes `1/2` in both
    rings and a group `G` with `E_n(R) ⊆ G ⊆ GL_n(R)` mapped monomorphically into the units of a ring.
  - For `q` odd this proves the `GL_3` version: `GL_3(R_X) ≅ GL_3(R_Y)` gives `M_3(R_X) ≅ M_3(R_Y)` or its opposite
    (`subshift-gl3-iso-gives-matrix-ring-iso-odd-q`, established, unreviewed).
  - It does NOT reach `S_X`, for two reasons (firewalls F-PE1 and F-PE2 in artifact §3).
    - An isomorphism of the projective groups lifts only to a common central quotient `E_3/Z_0`. The centres can
      differ: `λI_3 ∈ E_3(R_X)` depends on whether `X` has a cyclic factor of order `ord(λ)`.
    - Corollary 1 at `G = E_3` needs the closure condition `φ(Σ_1)_S ⊆ E_3(R_Y)`, which can fail.
  - What closes step 1 for `S_X`: an isomorphism theorem for `PE_3(R)` over simple rings with `1/2`, or a
    group-theoretic recognition of root subgroups in `S_X`. For `q` even nothing is known here.
- **Step 3 corrected.** After step 1 the invariant is `(K_0(R_X), K_0^+, 3[1])`. Giordano–Putnam–Skau then give strong
  orbit equivalence of the height-3 Kakutani towers over `X` and `Y`, not of `X` and `Y` themselves. For `(G, 3u)`
  vs `(G, u)` no cancellation is known in general. The anti-isomorphism case uses `R_X^op ≅ R_(X,T^{-1})`, with the
  same coinvariant group and cone.
- **Step 2 status.**
  - ABC arXiv:0903.0056 Theorem 3.6 (Step 1 of its proof: unital automorphism, `A = Z`) and Lemma 7.2 give
    `K(R⋊Z) = hocofiber(1−σ)`, because `NK` vanishes for regular supercoherent rings. `LC(X,F_q)` is regular
    supercoherent: it is a directed union of finite products of `F_q` with flat maps.
  - So `K_0(R_X) ≅ coker(1−T_*)` on `C(X,Z)`.
  - The cone still owes the Herman–Putnam–Skau fact that a strictly positive class has a nonnegative representative.
    Ara–Claramunt's faithful `rk_μ` (`cantor-z-crossed-product-embeds-in-continuous-factor`) gives only the inclusion
    of idempotent classes into the strictly positive classes.
- **Intrinsic route (lane sk-rigidity-intrinsic, artifact `sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md`).**
  - Diagonal-preserving rigidity is proved (unreviewed), for `q = 2`, in
    `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`. An isomorphism `G_X → G_Y` carrying
    `GL_3(LC(X,F_2))` onto `GL_3(LC(Y,F_2))` exists iff `X` and `Y` are flip conjugate.
    - The maximal normal subgroups of the diagonal recover `X`.
    - Its normalizer acts through a group between `[[T]]'` and `[[T]]`, with piecewise closure `[[T]]`.
    - Then `topological-full-groups-determine-flip-conjugacy` applies.
  - What remains for flip conjugacy under an arbitrary isomorphism `α`. Both steps are OPEN.
    - (i) Recognize `α(L_X)` as `GL_3(A')` for a maximal commutative, idempotent-spanned subalgebra `A' ⊆ R_Y` whose
      normalizing units generate `R_Y`.
    - (ii) Cartan uniqueness: every such `A'` is `β(A_Y)` for a ring automorphism `β`.
  - **Firewall F1.** `R_X ≅ R_Y` gives `G_X ≅ G_Y`. So flip rigidity of the groups implies that the algebraic crossed
    product RING alone determines the subshift up to flip conjugacy.
    - Every reconstruction theorem located assumes a diagonal-preserving or graded isomorphism: Renault; X. Li
      arXiv:1503.01704 Thm 1.2; Ara–Bosa–Hazrat–Sims arXiv:1601.02872; Steinberg arXiv:1711.01903.
    - The C*-crossed product alone determines only strong orbit equivalence (Giordano–Putnam–Skau 1995).
    - Bounded check: three web searches plus the abstracts.
  - **Heights cost nothing for flip conjugacy.** A clopen set with constant return time 3 is unique up to `T^j`, because
    continuous eigenfunctions of a minimal system are unique up to scalars. So the height-3 towers over `X` and `Y` are
    flip conjugate iff `X` and `Y` are. The unit-scaling issue of step 3 affects only the strong-orbit-equivalence
    target.
