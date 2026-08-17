# A candidate answer to Question 2: torsion-free, finitely presented, non-MF

**Status: candidate, not a theorem. Not printed in the manuscript.**
Steps 1–4 and 9 are checked below. Steps 5–8 rest on results of Hull and
Osin that are not verified here and not formalized anywhere in the
corpus. Do not promote this to a numbered environment until a geometric
group theorist has confirmed Steps 5–8.

**PROHIBITION, not a caution (2026-08-17).** Steps 5–8 quote Hull and Osin.
Under the standing zero-literature order — `Audit.literatureInputNames` is empty
and its docstring states that literature-transcription premises are not
permitted in the corpus — this route **cannot** be used to close anything, at
any quality. There are exactly two legal moves: retire the dependence, or prove
the antecedent in-repo. The second is not a lemma but a library: the pinned
Mathlib has no acylindrical hyperbolicity, no hyperbolically embedded subgroups,
no small cancellation and no Greendlinger's lemma. So this document is a record
of a research route, not a plan of work, and promoting any part of it to a
numbered environment or to a `\leanverified` badge would require deliberately
overriding a written prohibition. What is worth preserving here is the
mathematics, not the schedule.

## The claim

There is a nontrivial, two-generated, finitely presented, torsion-free
group `Q` with property (T) such that every homomorphism
`Q → U(𝒬)` is trivial. Hence `Res_MF(Q) = Q`, `Q` is not MF, and every
nontrivial quotient of `Q` is not MF.

This would close Question 2 and, in Lean, would exhibit the first
inhabitant of `DefectRoutingData`, discharging the hypothesis of
`FullMFRadicalEndpoint.exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical`.

## The idea

The printed obstruction was: to apply Hull's small-cancellation theorem
one needs a *suitable* two-generated subgroup of the conjugation defect,
and the Bass–Serre action of an ascending HNN extension fixes an end, so
it certifies no such subgroup.

The route below sidesteps that. Rather than exhibiting a hyperbolically
embedded element by hand, it makes the ambient group acylindrically
hyperbolic first; then *normality does the work*, because an infinite
normal subgroup of an AH group is automatically non-elementary. Hull is
applied twice: once to reach an AH property-(T) source with one defect
element surviving, once to force a two-generated subgroup of the defect
onto the whole quotient.

## Step 1 — an infinite-order source (checked)

Fournier-Facio's group `P` is finitely presented, torsion-free, has (T),
and contains `P₁ × P₂ ≤ P` with `P₁ ≅ P₂ ≅ P`. Take `α : P ≅ P₁ ≤ P`,
a proper injective endomorphism, and `1 ≠ a ∈ P₂`, so `a ∉ α(P)`.

**Do not impose `c² = 1`.** Set

    E∞ = ⟨ P, t, c | t γ t⁻¹ = α(γ), [c,γ] = 1  (γ ∈ P) ⟩
    d = t c t⁻¹,   u = [d,a]

`(P, ι, t, c)` is a Kazhdan conjugation datum: `def:pattern` imposes only
(M1) one-sided conjugation and (M2) centralization, and **no torsion
condition on `c`**. Verified against the printed definition.

## Step 2 — `E∞` is torsion-free (checked)

`E∞` is the HNN extension of `B = P × ⟨c⟩ ≅ P × ℤ` with associated
subgroups `P` and `α(P)` and stable letter `t`. `P` torsion-free ⇒ `B`
torsion-free; every finite-order element of an HNN extension is conjugate
into the base; so `E∞` is torsion-free. Finitely presented because `P`
is.

This is exactly where the Clifford source failed: there `c² = 1` was
imposed deliberately, so the source had torsion by construction.

## Step 3 — `u` has infinite order (checked, and this is the repair)

Let `G = ⟨P,t | tγt⁻¹ = α(γ)⟩`, `X = G/P`, and `L = (⨁_X ℤ) ⋊ G`.
Map `P, t` naturally and `c ↦ e_P`. This respects `[c,P] = 1` because `P`
fixes the base coset. Then in `L`,

    Φ(u) = Φ([d,a]) = e_{tP} − e_{atP}

computed as `(e_{tP},1)(0,a)(−e_{tP},1)(0,a⁻¹) = (e_{tP} − e_{a·tP}, 1)`.
The cosets differ: `atP = tP` forces `t⁻¹at ∈ P`, i.e. `a ∈ tPt⁻¹ = α(P)`,
contradicting `a ∉ α(P)`. So `Φ(u)` is a nonzero vector in a free abelian
group and `u` has infinite order.

Replacing the ℤ/2 Clifford lamp by a ℤ lamp is what converts the old
torsion witness into an infinite-order one.

## Step 4 — an AH source (checked)

`H = E∞ * ⟨r⟩` is finitely presented and torsion-free, and acts on its
Bass–Serre tree with trivial edge stabilizers, non-elementarily; so `H`
is acylindrically hyperbolic. The free factor exists only to enter Hull's
category without analyzing the ascending HNN action.

## Steps 5–8 — the two Hull applications (NOT checked)

5. Common quotient of `H` and a torsion-free non-elementary hyperbolic
   property-(T) group `K`, protecting `u`: gives `π : H ↠ G₀` and
   `K ↠ G₀` with `G₀` finitely presented, torsion-free, AH, with (T)
   (as a quotient of `K`), and `π(u) ≠ 1`. Put `N₀ = π(N_H) ≠ 1`.
6. `G₀` is torsion-free, so it has no nontrivial finite subgroup, and an
   infinite normal subgroup of an AH group acts non-elementarily; hence
   `N₀` is suitable.
7. A suitable subgroup contains independent loxodromics `h₁,h₂` with
   `S = ⟨h₁,h₂⟩` suitable, and `S ≤ N₀`.
8. Hull again on `(G₀, S)` with the generators of `G₀` prescribed gives
   `σ : G₀ ↠ Q` with `Q = σ(S) = ⟨σh₁,σh₂⟩`, hence `σ(N₀) = Q`, `Q`
   torsion-free (finite-order elements lift), with (T), and finitely
   presented (finitely many relators).

**These are the steps to have checked.** Specifically:

- **(a) Finite presentability of the common quotient in Step 5.** This is
  the load-bearing claim. Hull's Theorem 7.1 adds finitely many relators
  for finitely many prescribed elements, so it preserves finite
  presentability; whether the *common quotient* corollary does is the
  question, since a common quotient is naturally built by an iteration.
  If it does not, `Q` is finitely generated but perhaps not finitely
  presented, and the answer to Question 2 as printed does not follow.
- **(b) Suitability of `N₀` in Step 6** — that an infinite normal subgroup
  is non-elementary for the *ambient* acylindrical action.
- **(c) That `S ≤ N₀` may be chosen suitable in Step 7**, and that
  Step 8's quotient keeps `π(u) ≠ 1` (or that `Q` is infinite because it
  is AH, which suffices for `Q ≠ 1`).

## Step 9 — the obstruction fires (checked)

Push the datum to `Q`. Normal closure commutes with surjections, so
`N_conj(Q) = q(N_H) = Q`. Apply `thm:normal-kazhdan` with `K = Q`: `Q` is
normal in itself, has (T), and is contained in `N_conj(Q)`. So every
`Θ : Q → U(𝒬)` is trivial, `Res_MF(Q) = Q`, and — since a homomorphism
from a quotient composed with the projection is again a homomorphism
from `Q` — every nontrivial quotient of `Q` is non-MF too.

Checked against the printed hypotheses: `thm:normal-kazhdan` requires
only `K ⊴ H` with (T) and `K ⊆ N_conj`, and `K = H` is permitted.

## Why this is not in the manuscript

Two reasons, and the first is the important one.

1. **The external inputs are unverified here.** Steps 5–8 use Hull's
   Theorem 7.1 and Corollary 7.4 and Osin's normal-subgroup result. The
   manuscript's selling point is that Theorem A is unconditional; a
   theorem resting on three unverified citations belongs in print only
   after someone who knows that literature has confirmed them, which is
   what the author of the argument also asked for.
2. **Nothing here is formalized.** `FournierFacioDefectData` is still
   unbuilt anywhere in the corpus, and formalizing Hull's
   small-cancellation theory is not a near-term project. Printing the
   theorem would mean printing a numbered environment with no
   `CLAIM_TARGETS` declaration, or one carrying a literature interface.

The precedent from 2026-08-16 is directly relevant: the five printed
conditions of Question 2 were satisfied by the trivial group for months,
in a passage that read as though it were nearly a theorem. The cost of
being early here is higher than the cost of being slow.

## If it survives review

The manuscript change is small, because the machinery is already there:
Question 2 becomes a corollary of `thm:normal-kazhdan` plus the
construction above, and the six conditions in the printed question become
its proof outline. In Lean, the honest shape is a
`HullSmallCancellationData` interface next to `FournierFacioDefectData`,
from which `DefectRoutingData` is built — leaving the conditionality
visible and exactly localized to the two Hull applications.
