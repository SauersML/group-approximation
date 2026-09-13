---
rg: 2
id: zd-derived-full-group-fp-forces-finite-type
kind: claim
title: A free minimal Z^d-subshift whose derived full group is finitely presented is of finite type
distinct_from:
  fp-subshift-full-group-subgroups-extend-to-sft: That builds some SFT neighbourhood on which the extended generators satisfy the relators; this shows that for the derived full group the neighbourhood of configurations with legal bounded windows is the subshift itself, because nested commutators of 3-cycles detect every illegal pattern there.
  periodic-approximable-subshifts-host-no-fp-simple-group: That kills finitely presented simple subgroups through periodic approximations, which Z^2-subshifts may lack; this uses no periodic points, only failure of finite type.
  fp-subshift-crossed-products-are-sfts: That is the algebra analogue for crossed products, proved through cylinder idempotents; this is the group statement for derived full groups, proved through nested commutators of 3-cycles.
---

**ESTABLISHED (unreviewed).**

**Statement.** Let `d >= 1` and `X ⊆ A^(Z^d)` a free minimal subshift. If `D([[Z^d ~ X]])` is
finitely presented, then `X` is a subshift of finite type.

**Quantitative form (`d >= 2`).**
- Take the generating set `𝒯_R` of Chornyi–Juschenko–Nekrashevych, with `R >= R_1 + 2`.
- Suppose `D([[X]]) = <𝒯_R | ℛ>` with every relator of length at most `L`.
- Then `X` is exactly the set of configurations all of whose patterns on translates of
  `B(max(2L + R + 1, R_1 + 3))` occur in `X`.

**Cases.**
- `d = 1`. Infinite minimal `Z`-subshifts are never of finite type, so the statement is Matui's
  theorem that `D([[phi]])` is never finitely presented (arXiv:math/0404117). The proof below
  needs a perpendicular direction and is written for `d >= 2`.
- `d >= 2`. The proof is new in the sources read: math/0404117, 1105.0719, 1508.04454,
  1602.04255 and 1210.5800.

**Mechanism.**
- The relators hold for the rule action on every configuration whose bounded windows are legal.
- ChJN's commutator identity is pure permutation combinatorics. Its hypotheses read only windows
  of radius `R_1 + 3`.
- So on such a configuration the nested commutator word of any pattern `q`, legal or not, acts as
  the 3-cycle on the occurrences of `q`.
- In `D([[X]])` the word of an illegal pattern is trivial. A configuration with legal bounded
  windows but an illegal pattern would therefore violate a relation of the group.

**Why it matters.**
- It answers sub-question 4 of `research/artifacts/fp-simple-sofic-orbit-certificate-crux-2026-09-12.md`
  for `Z^d`: finite presentation does force finite type. Section 4 of that dossier recorded
  why the direct commutator attack seemed to stall; the stall is resolved here.
- Among free minimal `Z^d`-subshifts, only SFTs can carry finitely presented derived full groups.
  Labbé's shift is one (`minimal-aperiodic-wang-shift-exists`).
- The converse for Labbé's shift is the open `labbe-shift-derived-full-group-is-finitely-presented`.
- Every spatial approximant built from windows of the subshift is dead for SFTs. What remains are
  colourings with illegal small windows, or non-spatial groups.

**Proof:** `zd-derived-full-group-fp-forces-finite-type-proof`.
