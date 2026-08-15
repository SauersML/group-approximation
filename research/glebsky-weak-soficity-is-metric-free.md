---
rg: 2
id: glebsky-weak-soficity-is-metric-free
kind: claim
title: Glebsky's weak-soficity permanence produces no metric — the witness is algebraic
distinct_from:
  weakly-sofic-not-sofic: that is the separation obtained by composing Glebsky's theorem with Kun--Thom; this records what his proof does and does not supply, namely no bi-invariant metric at all
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks for a Hilbert embeddable witnessing length for the wreath; this is the source-level finding that no such length is handed to us by the permanence theorem, so the question must be posed as a choice
---

Extraction requested by `cairn-survivor` and performed 2026-08-14 from the
published PDF of Glebsky, *Extensions of a residually finite group by a
weakly sofic group are weakly sofic*, Rev. Mat. Iberoam. 39 (2023), no. 3,
1097--1104, doi:10.4171/RMI/1368.

**Finding: the proof of Theorem 1.1 never constructs a metric.** There is no
sequence of finite groups carrying bi-invariant metrics anywhere in it.  The
argument runs entirely on the algebraic side of

> **Lemma 1.2.** Let `K` be a group.  The following are equivalent:
> 1) `K` is weakly sofic;
> 2) every system of equations solvable in all finite groups is solvable
>    over `K`;
> 3) `K` is a subgroup of a quotient of a direct product of finite groups.
>    (The direct product may be uncountable.)

Theorem 1.1 is proved by: Krasner--Kaloujnine to embed the extension in the
unrestricted wreath product `H wr G`; Lemma 1.2 to write `H < H~/M` with
`H~` a direct product of finite groups; Theorem 1.3 to solve
`w(a~,y~)=1` in `H~ wr G^` (`G^` the profinite completion); then push the
solution forward.  This shows every `w in Sys(Fin)` is solvable over
`H wr G`, and weak soficity follows by Lemma 1.2 **(2) implies (1)**.

**The metric-bearing step is quarantined and imported.**  Direction
(2) implies (1) is the only place a metric can enter, and it is black-boxed:
"by [6], every finitely generated subgroup of `K` is weakly sofic", where
[6] is Glebsky, *Approximations of groups, characterizations of sofic
groups, and equations over groups*, J. Algebra 477 (2017), 147--162
(Corollary 19 there, specialized to the class of finite groups).  Anyone
wanting an explicit metric must read that paper, not this one.

**The definition prescribes nothing either.**  Definition 2.3: `G` is weakly
sofic if for every finite `Phi` containing 1 and every `eps>0` there is a
`(Phi,1/2,eps)`-homomorphism into *a finite group with a bi-invariant
metric* — an arbitrary such metric, with separation constant `1/2`.  So even
at the level of the definition there is no canonical length to expand in
characters.

**Glebsky states the sofic-versus-weakly-sofic crux in metric-distortion
terms himself**, immediately after Definition 2.3:

> "The other inclusion is an open question: although all finite groups are
> embeddable into finite symmetric groups, not all bi-invariant metric on a
> finite group is a restriction of a corresponding Hamming metric."

That is the exact shape of the hyperlinear question one class over: the
obstruction is not the finite groups but which lengths on them are induced
from the target geometry.

## Consequences for the Kun--Thom wreath

1. **The general witness simplifies.**  For `W=(directSum_(G/Gamma) Z/2) semidirect G`
   the kernel `H=directSum_(G/Gamma) Z/2` is already a subgroup of the direct
   product `prod_(G/Gamma) Z/2` of finite groups, so `M=1` and
   `H~=prod_(G/Gamma) Z/2`.  The witness is `W <= H wr G ,-> (prod_(G/Gamma) Z/2) wr G`,
   with the work being solvability of `Sys(Fin)` over it.
2. **The quotient in Lemma 1.2(3) is essential, and the source confirms it.**
   A *subgroup* of a direct product of finite groups is residually finite,
   hence sofic; since `W` is not sofic, its witness must genuinely use the
   quotient.  This independently confirms the "no finite-quotient witness"
   constraint already recorded on
   `hilbert-embeddable-witness-for-kun-thom-wreath`.
3. **Only the "some length" form of the question is well posed.**  Because no
   length is produced, one cannot ask whether *Glebsky's* length has
   nonpositive character coefficients.  The answerable question is whether
   the lengths on the finite factors can be *chosen* Hilbert embeddable so
   that the induced length on the quotient still separates the mark, with
   defect tending to zero and separation bounded below uniformly along the
   sequence.  That freedom is favourable, not an obstruction.
