---
rg: 2
id: amenable-purely-infinite-groupoid-full-group-hosts-kazhdan
kind: claim
title: Some amenable, minimal, effective, purely infinite ample groupoid has a topological full group containing an infinite Kazhdan group
distinct_from:
  brin-thompson-groups-nv-are-a-t-menable: that asks for the Haagerup property of the specific full groups nV = [[G_2^n]]; this shows that the groupoid-level properties G_2^n shares with many other groupoids do not imply the Haagerup property, or even finiteness of Kazhdan subgroups.
  sft-topological-full-groups-have-the-haagerup-property: that is Matui's positive theorem for one-sided irreducible shifts of finite type, which uses the zipper structure of those groupoids; this is a negative calibration for the general class that contains them.
  input-encoded-sft-groupoid-hosts-are-not-universal: that shows shift-of-finite-type groupoids contain no infinite Kazhdan group; this builds a different purely infinite amenable groupoid whose full group does contain one.
  irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups: that is a measured transfer theorem for orbit full groups of free actions of Haagerup groups; this is a topological example where the acting group has property (T) and the groupoid is still amenable.
---

**OPEN.** A complete drafted proof is recorded as an attempt (see Attempts). It is not
established because referee lens 1 refuted it on citation grounds: two imports (exact
implies an amenable compact model; (T) plus Haagerup implies finite) lack verbatim
sources. The route now requires the OPEN gap claim
`kazhdan-host-route-imports-have-verbatim-sources`.

**Theorem.** Let `Γ = Z^3 ⋊ SL_3(Z)`. There is a second countable, Hausdorff, ample
groupoid `𝒢` on a Cantor set with all of the following properties:

1. `𝒢` is topologically amenable (approximately invariant continuous systems of
   probability measures, uniformly on compacts; Step 0 of the route);
2. `𝒢` is minimal;
3. `𝒢` is essentially principal (effective);
4. `𝒢` is purely infinite in Matui's sense;
5. its topological full group `[[𝒢]]` contains a copy of `Γ`.

`Γ` is infinite and has property (T). So `[[𝒢]]` does not have the Haagerup property,
and it has an infinite Kazhdan subgroup.

**Construction.** `𝒢 = (M ⋊ Γ) × G_2`. Here `M` is a Cantor set with a free, minimal,
topologically amenable `Γ`-action, and `G_2` is the Deaconu–Renault groupoid of the
one-sided full shift on two letters, with `[[G_2]] = V`. The drafted proof is the route
`amenable-purely-infinite-groupoid-kazhdan-host-proof` (demoted; see Attempts).

## Why it matters for nV

Brick maps are products of prefix replacements, so `nV ≤ [[G_2^n]]`, and the same
product arguments show `G_2^n` has properties 1–4 (section "Application to nV" of the
route). So any argument of the form

> `𝒢` is ample, amenable, minimal, effective and purely infinite, hence `[[𝒢]]` is
> a-T-menable (or: has only finite Kazhdan subgroups)

is false. A Haagerup proof for `nV` must use structure that `(M ⋊ Γ) × G_2` lacks,
for instance the local similarity or product-of-trees structure of `G_2^n`, or
expansivity or compact generation of the groupoid. This is a class-kill in the sense
of the playbook:

- **Invariant:** property (T) of `Γ = Z^3 ⋊ SL_3(Z)`.
- **Step where every member dies:** the passage from groupoid-level hypotheses to a
  proper conditionally negative definite function on `[[𝒢]]`. Its restriction to
  `Γ ≤ [[𝒢]]` would be proper on an infinite Kazhdan group, which is impossible.

The example is not in `nV`, so it says nothing about the truth of
`brin-thompson-groups-nv-are-a-t-menable`.

## Attempts

1. **Product of a free minimal amenable Cantor model of `Z^3 ⋊ SL_3(Z)` with the full
   two-shift groupoid (2026-09-17).** Route
   `amenable-purely-infinite-groupoid-kazhdan-host-proof`, kept in place as an attempt and
   demoted by requiring the OPEN gap claim
   `kazhdan-host-route-imports-have-verbatim-sources`.
   Audit 2026-09-17: referee lens 2 returned refuted=false (no gap found; it also noted
   that the "compact generation of the groupoid" clause in "Why it matters for nV" is
   false, since `(M ⋊ Γ) × G_2` is compactly generated). Referee lens 1 returned
   refuted=true. Its reason, verbatim:

   > I checked every step of amenable-purely-infinite-groupoid-kazhdan-host-proof and the math holds, but one imported result has no source. The claim is probably true, and the fix is to add a verbatim citation.
   >
   > What checks out:
   > - Step 0 (the transformation groupoid is amenable, and amenability pulls back along equivariant maps) is correct.
   > - Step 2 (the model built from closed covers, X' inside T^Γ) is correct. The line 'T closed by compactness' is misworded: T is closed because each condition involves only finitely many coordinates.
   > - Step 3 (the diagonal action on X'×Z, a minimal subset M, and the isolated-points argument) is correct.
   > - Step 4 (G_2 is essentially principal via U_{α,β} with α=βρ; the averages m_N give the 2(a+b)/N bound) is correct. The map x ↦ (x,j,σ^j x) is the inverse of r|U_{μ,∅}, not s as written.
   > - Step 5, items 1-5, are correct. Continuity of the product system is not argued, but it is easy to fill.
   > - Imports that say exactly what is used: Matui's quotes, Elek Theorem 1 (verbatim), GTY (verbatim, R=Z inside GL_4(Z)), and Osajda l.119-120 (verbatim).
   >
   > First step that fails the verbatim-citation test: Step 1, last bullet, 'Γ is exact and nonamenable, so stw40 (1)⇒(2) gives a compact metrizable Y with a topologically amenable action'.
   > - The route behind that prerequisite (stw40-compact-amenable-model-and-reiter-obstruction-proof) supports (1)⇒(2) with one sentence: 'Exactness of a countable discrete group is equivalent to the existence of a topologically amenable action on a compact metrizable space', plus 'the usual Stone--Cech proof'.
   > - Nothing is quoted or cited for 'exact ⇒ amenable action on βG'. That is Ozawa 2000 / Higson–Roe; Brown–Ozawa Thm 5.1.7 is a likely reference, not verified. This is the load-bearing input for the whole construction.
   > - The stw40 claim never defines 'exact'. So there is no check that its hypothesis matches what the host route supplies: C*_r(Γ) exact / property A, via Osajda.
   > - The Conclusion uses '(T) + Haagerup ⇒ finite'. That comes from thompson-v-has-haagerup-property-citation, which says the source was not re-read and gives no verbatim text. Its proof sketch relies on the uncited Delorme–Guichardet result.
   >
   > These steps are unfilled by the lens's standard, so refuted=true. Verdict posted on the bus (e01b968e).
