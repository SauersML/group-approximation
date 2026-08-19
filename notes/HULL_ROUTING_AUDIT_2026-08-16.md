# Auditing Hull's small-cancellation theorem against baseline rows 3–4

**Date:** 2026-08-16.
**Question audited:** do the published acylindrical small-cancellation results
supply `DefectRoutingData`, the undischarged package behind rows 3 and 4 of
`notes/NON_MF_UNCONDITIONAL_BASELINE.txt`?

**Sources read in full, not from memory.**

* M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
  Geom. Dyn. **10** (2016) 1077–1119, DOI 10.4171/GGD/377 (published version;
  arXiv:1308.4345v2).  Statements below are quoted from the published
  pagination.
* D. Osin, *Groups acting acylindrically on hyperbolic spaces* (survey,
  arXiv:1712.00814), for the classification of acylindrical actions; the
  classification itself is proved in Osin, *Acylindrically hyperbolic groups*,
  Trans. AMS **368** (2016).

## 0. Verdict

The routing does **not** need the strengthening of Hull that the manuscript's
Question 2 describes.  Six of the seven fields of `DefectRoutingData` come out
of Hull's Theorem 7.1 as published, including finite presentation, which is the
field one would expect to be lost.  What is missing is a single hypothesis of a
different kind, and it is missing for a reason that a published theorem
explains rather than for want of effort:

> the routing needs a **suitable subgroup inside the compression defect**, and
> by Hull's Lemma 5.8 that reduces to **one infinite-order element `h` of the
> defect whose cyclic subgroup `⟨h⟩` is hyperbolically embedded in the ambient
> group** (with `⟨h⟩` a proper subgroup of the defect).

Nothing else is open.  Rows 3–4 should therefore be described as blocked on that
one certificate, not on a common-quotient technique that does not yet exist.

## 1. What the target package requires

`DefectRoutingData` (`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`)
carries, for a `FournierFacioDefectData D` over a skeleton `E`:

| # | Field | Requirement |
|---|---|---|
| 1 | `quotient`, `quotient_surjective` | an epimorphism `E ↠ Q` |
| 2 | `finitelyPresented` | `Q` finitely presented |
| 3 | `kazhdan` | `Q` has property (T) |
| 4 | `defect_surjective` | `q(N_comp) = Q` |
| 5 | `protected_ne_one` | `q(s) ≠ 1` |
| 6 | `generatorOne/Two`, `generates` | `Q` two-generated |
| 7 | `torsionFree` | `Q` torsion-free (power form) |

## 2. What Hull's Theorem 7.1 gives

> **Definition 1.4.** Given `G ∈ 𝒜ℋ`, a generating set `𝒜` of `G` and a
> subgroup `S ≤ G`, we say `S` is *suitable with respect to `𝒜`* if (1)
> `Γ(G,𝒜)` is hyperbolic and the action of `G` on `Γ(G,𝒜)` is acylindrical;
> (2) the induced action of `S` on `Γ(G,𝒜)` is non-elementary; (3) `S` does
> not normalize any finite subgroup of `G`.

> **Theorem 7.1** (= Theorem 1.5).  Suppose `G ∈ 𝒜ℋ` and `S ≤ G` is suitable
> with respect to `𝒜`.  Then for any `{t₁,…,t_m} ⊂ G` and `N ∈ ℕ` there exist a
> group `Ḡ` and a surjective homomorphism `γ : G → Ḡ` with
> (a) `Ḡ ∈ 𝒜ℋ`; (b) `γ|_{B_𝒜(N)}` injective; (c) `γ(tᵢ) ∈ γ(S)`;
> (d) `γ(S)` suitable with respect to some `𝒜' ⊇ γ(𝒜)`; (e) every element of
> `Ḡ` of order `n` is the image of an element of `G` of order `n`.

Field by field:

* **1** — Theorem 7.1's `γ`.
* **4 and 6 are the same clause.**  The remark after Remark 7.2 (p. 1110):
  *"if `G` is finitely generated, we can choose `t₁,…,t_m` to be a generating
  set of `G`, and we get that `γ|_S` is surjective."*  So `γ(S) = Ḡ`.  Taking
  `S ≤ N_comp` gives field 4.  Taking `S = ⟨h₁,h₂⟩` — legitimate by Corollary
  5.7, which produces non-commensurable loxodromic `h₁,…,h_k ∈ S` with
  `E_G(hᵢ) = ⟨hᵢ⟩` — gives field 6 simultaneously, since then
  `Ḡ = γ(S) = ⟨γ(h₁),γ(h₂)⟩`.  This is exactly how Hull gets two-generated
  common quotients in the proof of Corollary 7.4.
* **5** — same remark: *"we can always choose `N` such that `B_𝒜(N)` contains
  any given finite subset of `G`"*, so choose `N` with `s ∈ B_𝒜(N)` and apply
  (b).
* **7** — clause (e): a torsion-free `G` gives a torsion-free `Ḡ`.
* **2 — available, and this is the surprise.**  The proof of Theorem 7.1 sets
  `Ḡ = G/⟨⟨ℛ⟩⟩` where `ℛ` is the set of all cyclic shifts of `W^{±1}` for a
  **single** word `W ≡ t⁻¹h₁^{m₁}h₂^{l₁}…h₁^{m_n}h₂^{l_n}` (the proof opens
  *"Clearly it suffices to prove the theorem with `m = 1`, and the general
  statement follows by induction"*).  So each application of Theorem 7.1 adds
  finitely many relators, and `m` applications add finitely many; a finitely
  presented `G` therefore has a finitely presented `Ḡ`.
* **3** — property (T) has to come from a second group.  Hull's Corollary 7.4
  (= Corollary 1.6) produces a common quotient of `G₁` and `G₂`, and property
  (T) then descends from a Kazhdan `G₁` (this is how Corollary 1.7, *"every
  countable `G ∈ 𝒜ℋ` has an infinite quotient with Property (T)"*, is proved).
  A torsion-free finitely presented Kazhdan `G₁ ∈ 𝒜ℋ` exists: a torsion-free
  uniform lattice in `Sp(n,1)`, `n ≥ 2`.

### 2.1 Finite presentation survives only on the Theorem 7.1 route

Corollary 7.3 must **not** be used.  Its proof builds
`Q = G₀/⋃_{i≥1} ker η_i` as a direct limit of infinitely many small-cancellation
quotients, which destroys finite presentation.  The general case of Corollary
7.4 routes through Corollary 7.3 and inherits that.  The escape is the last
sentence of Corollary 7.4's proof: *"Now if `G₂` is finitely generated, then we
can apply Theorem 7.1 to `F'` with a generating set of `F'` as a finite set of
elements to get `Q` such that the image of `G₁` maps onto `Q`."*  Two
applications of Theorem 7.1, no limit — so with both inputs finitely presented,
the common quotient is finitely presented.  Surjectivity of the defect is
preserved by the second application, because a surjection composed with a
quotient map is a surjection.

## 3. The one thing that is missing

Every route above is an application of Theorem 7.1, whose hypotheses are
`G ∈ 𝒜ℋ` **and** a suitable `S`.  The suitability of the defect is the
undischarged certificate.  Two published statements reduce it:

> **Lemma 5.5.**  Let `S` be a non-elementary subgroup of `G`.  Then `K_G(S)`
> is the maximal finite subgroup of `G` normalized by `S`.

So over a torsion-free ambient, condition (3) of Definition 1.4 is automatic
and suitability is exactly non-elementarity of the induced action.

> **Lemma 5.8.**  If `S` contains an infinite order element `h` such that
> `⟨h⟩` is a proper subgroup of `S` and `⟨h⟩ ↪_h (G,X)`, then `S` is suitable
> with respect to `𝒜` for some `𝒜 ⊇ X`.

That is the cheapest sufficient condition, and it is what rows 3–4 now reduce
to: **one infinite-order `h ∈ N_comp` with `⟨h⟩` hyperbolically embedded in the
skeleton and `⟨h⟩ ⊊ N_comp`.**  (Lemma 5.9 is the alternative: if the defect is
itself in `𝒜ℋ` and hyperbolically embedded in the ambient, suitability
transfers.)

### 3.1 Why the ascending HNN skeleton does not certify itself

The skeleton `E' = ⟨Γ, t | tΓt⁻¹ = α(Γ)⟩` cannot be shown acylindrically
hyperbolic by its own Bass–Serre action, and this is not a gap in the argument
but a theorem:

> **Theorem 2.10** (Osin's survey, proved in *Acylindrically hyperbolic
> groups*).  Let `G` act acylindrically on a hyperbolic space.  Then exactly one
> of: (a) elliptic; (b) lineal, in which case `G` is virtually cyclic; (c)
> general type.  *"Theorem 2.10 rules out parabolic and quasi-parabolic
> actions."*

In the Bass–Serre tree of an ascending HNN extension one of the two edge
inclusions is onto, so every vertex has exactly one edge in the `α`-direction
and the action fixes the end of the telescope.  With `[Γ : α(Γ)] = ∞` the action
is non-elementary, hence quasi-parabolic, hence not acylindrical.  So that tree
is the wrong space; whether `E'` lies in `𝒜ℋ` for some other action is not
settled by these sources.

Nor does Hull's own HNN section help directly:

> **Proposition 6.2.**  Suppose `S` is a suitable subgroup of a group
> `G ∈ 𝒜ℋ`.  Then for any isomorphic **cyclic** subgroups `A` and `B` of `G`,
> the corresponding HNN-extension `G *_{A^t = B}` belongs to `𝒜ℋ` and contains
> `S` as a suitable subgroup.

Section 6 is about HNN extensions over cyclic subgroups (Lemma 6.1, Proposition
6.2).  The compression datum needs the associated subgroups to be the whole
Kazhdan base, which is not cyclic, so Proposition 6.2 does not apply to `E'`.

## 4. Consequences for the repository

1. The manuscript's Question 2 mis-describes the intended route.  Prescribing
   the target elements inside a chosen subgroup is not a strengthening anyone
   needs to prove: Theorem 7.1(c) prescribes an arbitrary suitable `S`, and the
   remark after Remark 7.2 upgrades that to `γ(S) = Ḡ` for a finitely generated
   ambient.  The sentence is corrected in the same commit as this note.
2. Rows 3–4 of the baseline stay, with a sharper reason: the missing object is a
   hyperbolically embedded cyclic subgroup inside the compression defect (or,
   failing that, an acylindrically hyperbolic action of the skeleton), not a new
   small-cancellation theorem.
3. If that certificate is ever produced, the Lean side needs no new analytic
   input: `DefectRoutingData` is exactly the interface, and fields 1, 2, 4, 5,
   6, 7 are then discharged by one application of Theorem 7.1 to
   `B * E'` and a second to its output, with `B` a torsion-free finitely
   presented Kazhdan uniform lattice supplying field 3.

## 5. What this note does not claim

It does not claim `E' ∈ 𝒜ℋ`, and it does not claim `E' ∉ 𝒜ℋ`: only that the
Bass–Serre action cannot witness it and that Hull's HNN result covers a
different case.  It does not construct `h`.  It does not formalize any of the
quoted statements; they are literature inputs, quoted at the point of use, and
the two Lean endpoints behind rows 3–4 remain conditional on the data packages
they take as arguments.
