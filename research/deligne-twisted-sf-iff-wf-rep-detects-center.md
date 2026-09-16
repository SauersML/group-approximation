---
rg: 2
id: deligne-twisted-sf-iff-wf-rep-detects-center
kind: claim
title: Deligne's twisted algebras over F_p(w) are stably finite iff some weakly finite characteristic-p representation of E_3 moves z
distinct_from:
  deligne-twisted-group-algebra-is-not-stably-finite: that is the open counterexample claim; this is an equivalence, proved unconditionally, that turns it into a representation-theoretic statement about E_3 and a rank-condition statement about one algebra, and decides neither side.
  deligne-triple-cover-group-algebras-are-stably-finite: that is the positive claim over all fields of positive characteristic, characteristic three and infinite fields included; this concerns only the twisted factors over finite fields of characteristic other than three.
  deligne-cover-linear-soficity-is-rank-projective-approximation: that characterizes linear soficity of E_3 by approximate projective representations; this needs no metric, and a single exact representation moving z into any weakly finite ring decides the matter.
  rank-condition-rings-have-weakly-finite-images: that is the general ring theorem used for item 3; this is its specialization to E_3, combined with absorption into LEF group rings, Malcev and the finite residual.
  binary-corner-weakly-finite-images-are-unit-representations: that ties weakly finite images of a Leavitt-unit corner to representations of a simple non-LEF group and does not reach stable finiteness; this uses that Sp4(Z) is LEF to get stable finiteness itself.
artifacts:
  - research/artifacts/deligne-twisted-sf-rank-condition-dichotomy-2026-09-16.md
---

Let `1 -> <z> = C_3 -> E_3 -> Sp_4(Z) -> 1` be Deligne's triple cover with section cocycle `a`. Fix a prime
`p != 3` and put `F_0 = F_p(w)`, and `A_j(F) = F^(w^(ja))[Sp_4(Z)] = F[E_3]/(z - w^j)`. Let `N_p` be the
intersection of the kernels of all homomorphisms `E_3 -> R^x` with `R` a nonzero weakly finite ring and
`p·1_R = 0`. The following are equivalent:
1. `deligne-twisted-group-algebra-is-not-stably-finite` holds at `p`: some `A_j(F)`, with `F` finite of
   characteristic `p` containing `w` (so `F ⊇ F_0`), is not stably finite;
2. every `A_j(F)`, for both `j` and every finite `F ⊇ F_0`, is not stably finite;
3. `A_1(F_0)` fails the rank condition. Equivalently, it has no nonzero weakly finite image, and
   `(K_0(A_1(F_0)), [1])` has no state;
4. some matrix ring `M_n(A_1(F_0))` is properly infinite;
5. `z in N_p`: every homomorphism from `E_3` into the unit group of a weakly finite ring of characteristic
   `p` kills `z`.

Moreover `N_p` is `1` or `<z>`.

**So** the target holds iff, for some prime `p != 3`, every weakly finite characteristic-`p` representation
of `E_3` factors through `Sp_4(Z)`. One homomorphism `E_3 -> GL_n(R)` with `R` weakly finite of
characteristic `p` and `rho(z) != 1` refutes the target at `p`. Examples of such `R` are Ore domains,
division rings, rank ultraproducts and stably finite group algebras.

**Remarks recorded in the artifact (Sections 4–5).** These are not part of the certified statement above,
and the route below does not cover them. The PI and matricial-limit items also lean on classical results
not re-fetched here (Posner with Formanek–Rowen, Behr's finite presentation of `Sp_4(Z)`).
- Under the target, every Sylvester matrix rank function on `F[E_3]` is pulled back from
  `F[Sp_4(Z)]`, and a witness can be normalized to a compression.
- Unconditionally, `A_j` has no nonzero PI image and no exact matricial-limit image.
- Finite subgroups of `E_3` carry no obstruction, since each has a character sending `z` to `w`.

Proof: route `deligne-twisted-sf-iff-wf-rep-detects-center-proof`.
