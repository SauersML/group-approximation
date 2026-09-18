---
rg: 2
id: spherical-artin-groups-satisfy-boone-higman
kind: claim
root: true
title: Every spherical-type Artin group embeds in a finitely presented simple group
distinct_from:
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is the established conditional statement reducing the permutational form to E_6, E_7, E_8; this is the unconditional Boone--Higman statement for all spherical types, which that reduction feeds as one route.
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups with solvable word problem; this is its spherical part.
  spherical-artin-groups-are-linear-over-q-x-y: that is the established linearity of these groups over Q(x,y); this asks for a finitely presented simple envelope, which linearity gives through the characteristic-zero root.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`spherical-artin-bh-via-char-zero-linear-groups`, now that
`char-zero-linear-groups-satisfy-boone-higman` is established. That root rests on
`polynomial-linear-groups-satisfy-boone-higman`~~, whose independent review is still
pending (lane `bh-poly-linear-review`)~~.
*Reviewed (lane `bh-poly-linear-review`, 2026-09-12).* The status stands.
- The review corrected one step of the polynomial theorem.
- No step here uses Digne (attempt 4).
- See `research/artifacts/review-bh-polynomial-linear-2026-09-12.md`.

**Statement.** Every Artin group of spherical type embeds in a finitely presented
simple group.

*Marked `root` because it is a named class.* BFFHZ (arXiv:2503.21882v2, after
Corollary B) and survey Remark 5.4 both list the exceptional spherical types as
open.

**Status.**
- **Permutational form:**
  - *settled* for A_n, B_n = C_n, D_n and I_2(m)
    (`aut-free-groups-satisfy-permutational-boone-higman`);
  - *still open* for E_6, E_7, E_8, F_4, H_3 and H_4
    (`e-type-artin-groups-satisfy-permutational-boone-higman`). G_2 = I_2(6) is
    dihedral.
- **Plain form, every type** (2026-09-12): route 1, which includes the exceptional
  types that BFFHZ and survey Remark 5.4 list as open.

**Routes.**
1. `spherical-artin-bh-via-char-zero-linear-groups`: these groups are linear
   over `Q(x,y)` (`spherical-artin-groups-are-linear-over-q-x-y`), so the claim
   follows from `char-zero-linear-groups-satisfy-boone-higman` at transcendence
   degree 2. *Complete* (2026-09-12).
2. `spherical-artin-bh-via-e-type-reduction`: by
   `spherical-artin-boone-higman-reduces-to-e6-e7-e8`, it suffices that
   E_6, E_7, E_8 satisfy the permutational property
   (`e-type-artin-groups-satisfy-permutational-boone-higman`).

## Attempts

1. **Mapping class groups with boundary.** *Dies for the E types.* Paris
   (arXiv:0711.2372, §7.1): "the representation ρPV is faithful if and only if
   either Γ = An for some n≥ 1, or Γ = Dn for some n≥ 4". So the geometric
   monodromy does not put E_6, E_7, E_8 inside a mapping class group of a surface
   with boundary, where BFFHZ would apply.
2. **Zaremsky's rational theorem.** *Does not reach.* The faithful LKB
   representation lives over `Q(x,y)`. No faithful specialization to a number
   field is recorded in the sources read. `algebraic-linear-groups-satisfy-boone-higman`
   covers only transcendence degree zero.
3. **Locally finite trees.** *Dies.* Irreducible spherical Artin groups have
   infinite centre. Jankiewicz (arXiv:2103.01343) notes that none of them splits
   as a graph of finite-rank free groups except the dihedral ones, so the BLIW
   generalized Baumslag--Solitar route does not apply.
4. **Linearity plus the characteristic-zero root** (lane
   `bh-char0-linear-reduction`, 2026-09-12). *Succeeds, in the plain form.*
   - **Linearity, from the primary source.** Cohen--Wales, arXiv:math/0010204v2
     (Israel J. Math. 131 (2002)), Theorem 1.1: "Every Artin group of finite type
     is linear."
     - They reduce to types A, D and E through the embeddings of their
       reference [4].
     - Theorem 1.2 gives a representation of the type-A, D, E group on the free
       `Z[r^(+-1), t^(+-1)]`-module with basis indexed by the positive roots. It is
       faithful after specializing `r` to a real `r_0` in `(0,1)`.
     - Specializing only enlarges the kernel, so the representation over
       `Z[r^(+-1), t^(+-1)]` is already faithful.
     - Digne, J. Algebra 268 (2003), was not reachable: it has no open-access copy
       and no arXiv version.
     - *Review (lane `bh-poly-linear-review`, 2026-09-12):* no step uses Digne.
       - The bibliography of math/0010204v2 has no Digne entry.
       - Its proof of Theorem 1.1 reaches the types with multiple bonds (B_n,
         F_4, H_3, H_4, I_2(m)) only through Crisp's embeddings into types
         without multiple bonds (source lines 109–116 and 1656–1661).
       - Crisp's theorem itself is read through Cohen–Wales and Paris.
   - **Coordinates.**
     - `A(E_8) <= GL_120(Z[r^(+-1), t^(+-1)])`.
     - `Z[r^(+-1), t^(+-1)]` is free over `Z[s_1, s_2]`, where
       `s_1 = r + r^-1` and `s_2 = t + t^-1`, with basis `1, r, t, rt`.
     - So `A(E_8) <= GL_480(Z[s_1, s_2])`.
   - **Host.** The polynomial theorem with `k = 2` and `N = 480` gives the host
     `Z[s_1,s_2]^960 x| E_960(Z[s_1,s_2])`.

**Verification (bh-verify-artin, 2026-09-18; lane check, not an external review).** PASS conditional. The linearity import checks. The claim is carried entirely by `polynomial-linear-groups-satisfy-boone-higman` with m = 1 and k = 2, since A(E_8) <= GL_480(Z[s_1,s_2]); the full characteristic-zero reduction is not needed. That theorem rests on `elementary-groups-over-polynomial-s-integers-are-fp` and Zaremsky's Theorem 1.1. Both are internal lane proofs with internal review only. BFFHZ and survey Remark 5.4 list the exceptional types as open. So this status is exactly as strong as the polynomial theorem, which is the external-verification target. See `research/artifacts/gq-bh-bh-verify-artin-report.md`.

## Named question (bh-free-21, 2026-09-18)

Belk--Bleak--Chatterji--Matucci--Perego, *Rational embeddings of continuous automatic groups*
(preliminary version 2026, p. 7, read at source), pose Question 1.12: "Does every Artin group of
finite type admit an embedding into a finitely presented simple group?"

They add that "it is an open problem whether exceptional Artin groups of finite type (E_6, E_7,
E_8, F_4, and H_4) admit embeddings into finitely presented simple groups."

This node answers Q1.12 yes, through the chain recorded above. That chain was re-verified
end to end by `research/artifacts/gq-bh-bh-verify-linear-report.md` and
`research/artifacts/gq-bh-bh-verify-artin-report.md`. All reviews are internal, and a
MathSciNet/zbMATH priority search is still outstanding.
