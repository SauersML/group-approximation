---
rg: 2
id: lea-permanence-closure-fp-kazhdan-groups-are-residually-finite
kind: claim
title: Every finitely presented Kazhdan group built from LEA groups by subgroups, directed unions, amenable-quotient extensions, graphs of groups and finite products is residually finite
distinct_from:
  sofic-permanence-closure-omits-simple-fa-nonsofic-groups: that shows a finitely presented simple nonsofic FA group never enters the closure of the sofic groups, even under arbitrary extensions and marked limits; this concerns non-simple finitely presented Kazhdan groups, which only enter when amenable-kernel extensions are allowed, and concludes residual finiteness.
  fp-simple-groups-escape-soft-hyperlinear-permanence: that shows marked limits and residual amenability never certify a non-amenable finitely presented infinite simple group; this covers the full operation closure of the LEA groups and needs no simplicity.
  fp-sofic-kazhdan-group-not-residually-finite: that is the open existence question of Alekseev--Thom Open problem 6.1; this shows its witnesses lie outside every permanence closure of this shape.
artifacts:
  - research/artifacts/sk-fp-sofic-host-status-2026-09-13.md
  - research/artifacts/sk-verify-14-2026-09-13-part6.md
---

**ESTABLISHED (unreviewed).** Let `𝒫` be the smallest class of groups that contains every group
locally embeddable into amenable groups (LEA, "initially subamenable") and is closed under:

- (P1) subgroups;
- (P2) directed unions;
- (P3) extensions with amenable quotient: `N ⊴ G`, `N ∈ 𝒫`, `G/N` amenable ⇒ `G ∈ 𝒫`;
- (P4) fundamental groups of graphs of groups with vertex groups in `𝒫`, for any edge groups;
- (P5) finite direct products.

Then every finitely presented group in `𝒫` with Kazhdan's property (T) is residually finite.

**Consequence for Alekseev--Thom Open problem 6.1.** The problem asks for finitely presented sofic
Kazhdan groups that are not residually finite. By the claim, no witness lies in `𝒫`. `𝒫` contains
every group that the standard soficity theorems produce from LEA groups:
- amenable groups and LEF groups;
- sofic-by-amenable extensions (Elek--Szabó);
- amalgams and HNN extensions over amenable subgroups;
- graph products;
- wreath products with amenable top group;
- direct products.

The same holds for hyperlinearity certificates of these shapes. So a witness needs an approximation
that is not assembled from local amenable models by these operations.

**Sharpness.** The claim fails for the closure under extensions with a FINITE central kernel.
- Deligne's triple cover `E_3` of `Sp_4(Z)` is a central extension of the residually finite group
  `Sp_4(Z)` by `C_3`. It is finitely presented and Kazhdan: the kernel is finite and the quotient
  has (T).
- It is not residually finite: `deligne-covers-of-sp2g-z-have-finite-residual-2z` gives
  `Res_fin(E_3) = ⟨z^2⟩ = C_3`.
- Glebsky (Rev. Mat. Iberoam. 39 (2023), Theorem 1.1) shows that weakly sofic-by-residually-finite
  groups are weakly sofic, so `E_3` is weakly sofic. Its soficity is open
  (`deligne-triple-cover-is-sofic`). Glebsky's introduction records the hope that "a non-sofic group
  may be constructed as an extension of a residually finite group by a finite one".
- So the single missing permanence property, finite-central-by-residually-finite ⇒ sofic, would
  answer 6.1 at once.

**Model tests.**
- Kar--Nikolov (arXiv:1405.1620, Theorem 1): `SL_n(Z[1/p]) *_Z SL_n(Z[1/p])`, `n ≥ 3`, is finitely
  presented, sofic and not LEA.
  - It lies in `𝒫` by (P4), since the vertex groups are linear, hence residually finite, hence LEA.
  - It is a nontrivial amalgam, so it fails FA and has no (T). The claim does not apply, as it must
    not.
- Thom's LEF Kazhdan non-residually-finite group lies in `𝒫_0` and is not finitely presented.
- `SL_3(Z)` is finitely presented, Kazhdan, residually finite and in `𝒫`.
- The Caprace--Rémy lattices and the finitely presented Kazhdan nonsofic group are finitely presented,
  Kazhdan and not residually finite, so they are outside `𝒫`. That is consistent.
- Dropping (T) breaks the claim: the Kar--Nikolov amalgam above is finitely presented, lies in `𝒫`
  and is not residually finite, since it is not LEA.

**Credit.** The base case is standard and in print. Thom (arXiv:0810.2180, section on initially subamenable groups, e-print l.263–300; GGD 2010) writes:
"any finitely presented initially subamenable group is residually amenable. Being a Kazhdan group,
a homomorphic image in an amenable group follows to be finite. Hence, each finitely presented
initially subamenable Kazhdan group is necessarily residually finite."
- The inductive closure argument is routine: (T) kills infinite amenable quotients and gives FA
  (Watatani 1982).
- No novelty beyond assembling it is claimed. The bounded literature check is in the artifact.

Proof: `lea-permanence-closure-fp-kazhdan-rf-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived:
- the base case: a finite presentation turns an LEA local embedding into an amenable quotient, which (T) makes finite;
- the lexicographic induction on `(α, k)` over finite product families, through (P1)–(P5);
- the Sharpness example: Deligne's triple cover in the finite-central closure.

See `research/artifacts/sk-verify-14-2026-09-13-part6.md` §1.
