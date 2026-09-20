---
rg: 2
id: arithmetic-lattices-f-infinity-hosts-review
kind: claim
title: Referee review of 313d20dd29 / 45e85f5110 (F_∞ simple hosts for arithmetic lattices) — the BLIW Theorem 11.1 route is correct and n-independent for lattices in LINEAR semisimple groups, including every lattice in Sp(n,1) and F_4^(-20); the finite-center step fails for non-linear groups (Deligne's lattices); the result is already implied by Llosa Isenrich–Schesler–Wu arXiv:2510.01952 Theorem 1.4 and Remark 1.5, verified at source, so it is an independent second proof, not a first
distinct_from:
  arithmetic-lattices-embed-in-f-infinity-simple-groups: that is the claim under review; this checks its proof against BLIW at source, repairs its scope and attribution, and settles priority.
  free-group-houghton-group-f-infinity-review: that review found T0 outside BLIW's viral-expansion hypothesis; this records why the lattice route is not, namely BLIW's augmentation.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; adversarial review of the lane proof 313d20dd29, with the priority
update 45e85f5110, by bh-q12-alt-host).**

Read at source:
- **Bux–Llosa Isenrich–Wu** arXiv:2408.05673v2: Def. 1.2–1.3, §3, Lemma 3.2, Def. 4.3, Remark 4.4, Thm 8.2,
  Lemma 8.3, Cor. 8.4, Thm 9.1, Prop. 9.2, §10 (Lemmas 10.1–10.4, Thm 10.5), Thm 11.1, Thms 12.1–12.6.
- **Llosa Isenrich–Schesler–Wu** arXiv:2510.01952v1, pp. 1–4.

## Verdicts

| item | verdict |
|---|---|
| (1) BLIW Thm 11.1 hypotheses, viral expansion, local finiteness, transitivity | **PASS**: met by the Hecke member |
| (2) one envelope for all `n`, hence `F_∞` | **PASS**, and it is BLIW's own reading |
| (3) arithmeticity, (T), hyperbolicity | **PASS with an attribution repair** |
| Step 1, finite center | **FAIL for non-linear `L`**; repaired by assuming `L` linear |
| (4) priority | **already implied by LISW 2025** (verified at source); grade: independent second proof |

## (1) Theorem 11.1, verbatim, and why the viral condition is not an extra hypothesis

**The theorem.** BLIW Thm 11.1 (p. 24): "Let `G` be a group of type `F_n` for `n ≥ 2`. Assume that there is a
non-trivial group `H ∈ 𝓑𝓢_G` such that `H` acts faithfully on its Bass–Serre tree. Then every `K ∈ 𝓑𝓢_G` embeds
in a simple group of type `F_n`."
- That is the whole hypothesis list.
- The proof glues the graphs of `H` and `K` along one edge, then applies Lemma 10.1 (faithfulness) and Thm 10.5.

**Where the remaining conditions come from.** The conditions of Thm 9.1 are all manufactured inside Thm 10.5:
- *Strong faithfulness.* Lemma 10.2, after the augmentation `Ĝ_v = G_v × Z/3Z`.
- *Admissible gates.* Lemma 10.3.
- *Viral expansion* (`M_ii ≥ 3`, `L_i(T_0) ≥ 2`). Lemma 10.4, because the augmentation makes
  `[Ĝ_v : Ĝ_e] ≥ 3` at every edge end.
- *Local finiteness.* This comes from the finite-index edge inclusions required in the definition of `𝓑𝓢_G`.
- *Transitivity on half-edges of one label.* This is used in Lemma 3.2 and holds automatically in a Bass–Serre
  tree.
- *Edge stabilizers of type `F_n`.* The edge groups are commensurable with `G`.

**The contrast with T0.**
- T0 (`free-group-houghton-group-f-infinity-review`) is `RP_(F_2)` of the bare Cayley tree. There `M_ii = 1`,
  which is outside Prop. 9.2.
- Here BLIW's augmentation is applied before Prop. 9.2, so no viral issue arises.

**The witness.** `arithmetic-lie-lattices-have-faithful-bs-members` (refereed PASS by referees a and b) gives a
nontrivial faithful `H ∈ 𝓑𝓢_G`: a finite commensurator HNN with finite-index edge groups, for `L` with trivial
center. **PASS.**

## (2) One envelope for every `n`

The envelope of Thm 10.5 is `SV_(RP_Ĝ(T̂))`, the twisted Brin–Thompson group of the rigid permutation group of the
augmented tree (Thm 9.1 via Cor. 8.4 and Thm 8.2). It does not depend on `n`, for three reasons:
- *The gates.* The `n` in Lemma 10.3 is the number of vertices of the quotient graph, a notational clash, not
  the finiteness degree.
- *The base trees.* The base trees of Lemma 10.4 are chosen per finite set `𝓑`, not per `n`.
- *`n = ∞` is allowed.* Thm 8.2 and Cor. 8.4 are stated for `n ∈ ℕ ∪ {∞}`.

With edge groups of type `F_∞`, Prop. 9.2 makes every `RP_Ĝ(T̂, 𝓑)` of type `F_n` for all `n`, so Cor. 8.4 applies
with `n = ∞`. BLIW themselves conclude `F_∞` this way in Thms 12.2, 12.3 and 12.5. **PASS.**

## (3) Arithmeticity, (T), hyperbolicity

- **Arithmeticity (attribution repair).** For lattices in both `Sp(n,1)`, `n ≥ 2`, and `F_4^(-20)`, it follows
  from Corlette's archimedean superrigidity (Ann. of Math. 135 (1992)) **together with** Gromov–Schoen's
  `p`-adic superrigidity (Publ. IHÉS 76 (1992)). The node's split, "Corlette for `Sp(n,1)`, Gromov–Schoen for
  `F_4^(-20)`", should read "Corlette and Gromov–Schoen" for both.
- **Property (T) (Kostant).** It is inherited by lattices.
- **Hyperbolicity (Švarc–Milnor).** Cocompact lattices act geometrically on a negatively curved symmetric
  space. The Niblo–Reeves remark is correct.
- **Type `F_∞`.** A torsion-free finite-index subgroup is of type `F`. In the cocompact case it acts freely and
  cocompactly on the contractible symmetric space; otherwise use Borel–Serre.

## Step 1 fails for non-linear `L`

**The claim.** Step 1 says that `Γ` "is finitely generated and linear through `Ad`", so Selberg's lemma gives a
finite-index `Γ_0` with `Γ_0 ∩ Z(L) = 1`.
- Only `Ad(Γ)` is linear. `Γ` itself is a finite central extension of it.

**The counterexample.** Deligne (C. R. Acad. Sci. Paris 287 (1978)) proves: for `n ≥ 2`, every finite-index
subgroup of the preimage of `Sp_(2n)(Z)` in the universal cover of `Sp_(2n)(R)` contains `2Z ⊂ π_1 = Z`.
- In the `m`-fold cover with `m ≥ 3`, the image `Γ_m` is an irreducible arithmetic lattice in a connected simple
  group with finite center.
- Every finite-index subgroup of `Γ_m` contains the nontrivial central subgroup `2Z/mZ`.
- So `Γ_m` is not residually finite, and no finite-index subgroup meets `Z(L)` trivially.

**Consequence.**
- *No faithful member.* Every group commensurable with `Γ_m` contains a finite-index subgroup of `Γ_m`, so it is
  not residually finite. A vertex group of a faithful action on a locally finite tree embeds in a profinite vertex
  stabilizer of `Aut(T)`, so it is residually finite. Therefore `𝓑𝓢_(Γ_m)` has **no** faithful member, and
  Theorem 11.1 does not apply.
- *What fails.* The general statement, and Instance 2 ("every irreducible lattice in real rank ≥ 2"), are **not
  proved** for non-linear `L`.

**Repair.** Assume `L` linear, or more generally that `Γ` has a finite-index subgroup meeting `Z(L)` trivially.
- Then Step 1 holds: Selberg applies to `Γ` itself.
- Instances 1 and 3 (`Sp(n,1)`, `PSp(n,1)`, `F_4^(-20)`, `SO(n,1)^0`, `SU(n,1)`) and the examples
  `SL_n(Z)`, `Sp_(2n)(Z)` are all in linear groups, so they stand.

## (4) Priority: already implied by LISW 2025

**The source.** Llosa Isenrich–Schesler–Wu, *Infinitely presented simple groups separated by homological
finiteness properties*, arXiv:2510.01952v1 (2 Oct 2025).
- Theorem 1.4 (p. 2), verbatim: "Let H be a finitely generated subgroup of GL_n(ℚ) for some n ∈ ℕ. There exists a
  simple group G that has the following properties: (1) G has the same finiteness properties as H, (2) H is a
  subgroup of G, (3) G admits a quasi-retract onto H."
- Remark 1.5: "every finitely generated subgroup of GL_n(ℚ̄) … can be embedded into GL_m(ℚ) … one could replace ℚ
  with ℚ̄ in Theorem 1.4."
- The quotation in 45e85f5110 is accurate. It is now **verified at source**.

**What it covers.** An arithmetic lattice in a linear group is virtually `ℚ̄`-linear, hence `ℚ̄`-linear, by
induction of a faithful representation from a finite-index subgroup. It is also of type `F_∞`.
- So LISW Thm 1.4 already gives `F_∞` simple hosts for every lattice in `Sp(n,1)` and `F_4^(-20)`, and for every
  arithmetic lattice in a linear semisimple group, although LISW do not state lattices.
- It also reaches the non-arithmetic lattices in `SO(n,1)` and `SU(n,1)`, which are linear over number fields by
  local rigidity. The tree route cannot reach those.

**Grading.**
- The node is an **independent second proof by a different mechanism**: BLIW trees and commensurator HNNs,
  instead of Röver–Nekrashevych groups.
- It is **not** the first `F_∞` simple host for Kazhdan hyperbolic groups.
- Credit LISW for the result and BLIW for the machinery. Priority is not a risk; the node already claims none.

## Recommended status

**ESTABLISHED for linear `L`** (lane proof plus this review), with the Step 1 scope repair and the arithmeticity
attribution. Priority goes to Llosa Isenrich–Schesler–Wu; the route is an independent second proof.

## Lesson for general BH

**Two known mechanisms give `F_∞` simple hosts, and both are linear-algebraic.**
- LISW: self-similar Röver–Nekrashevych extensions of `ℚ̄`-linear groups.
- BLIW with dense commensurators: this route.

The Kazhdan hyperbolic inputs that remain open for `F_∞` are exactly the non-linear, or not-known-linear, ones,
such as `𝓗_31` and random groups. The node's own Scope section already points there.
