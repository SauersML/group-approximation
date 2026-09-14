# Bestvina--Brady dichotomy: Eilenberg--Ganea versus Whitehead (lane hl-whitehead-bestvina-brady, 2026-09-13)

## 1. Source pins

**Paper.** M. Bestvina, N. Brady, *Morse theory and finiteness properties of
groups*, Invent. Math. 129 (1997), 445--470.
- Springer PDF (doi 10.1007/s002220050168), fetched on MSI into
  `/scratch.global/sauer354/hl-whitehead-bestvina-brady/src/`.
- Converted with ghostscript `txtwrite`. Some symbols were lost; the quotes
  below restore them in obvious places only.

**Introduction, Example (3), text lines 713--726.**
- "(3) Let L be an acyclic nonsimply-connected finite flag complex, say of
  dimension 2. Then H_L is FP (over all rings) but it is not finitely
  presented."
- "Furthermore, the cohomological dimension of H_L is 2 since the level sets
  are 2-dimensional and acyclic. It is natural to ask if such groups H_L have
  2-dimensional Eilenberg-Mac Lane spaces. Thus one obtains a family of
  potential counterexamples to the Eilenberg-Ganea conjecture."
- "If L is a flag triangulation of a spine of the Poincare homology sphere,
  then in Theorem 8.7 we show that H_L is either a counterexample to the
  Eilenberg-Ganea conjecture or that there is a counterexample to the Whitehead
  conjecture."

**p. 461, text lines 728--731.** "Recall that the Eilenberg-Ganea conjecture
states that if a group H has cohomological dimension 2, then it has a
2-dimensional Eilenberg-Mac Lane space K(H,1). The Whitehead conjecture states
that every connected subcomplex of an aspherical 2-complex is aspherical."

**Theorem 8.7, p. 469, text lines 1139--1141.** "Let L be a flag
triangulation of a spine of the Poincare homology sphere. Then either H_L is a
counterexample to the Eilenberg-Ganea conjecture or there is a counterexample
to the Whitehead conjecture."

**Proof of Theorem 8.7, key sentences, pp. 469--470.**
- "If H_L does not have geometric dimension 2 we are done. Otherwise, let Y be
  a contractible 2-complex on which H_L acts freely, faithfully, properly and
  cellularly. Since Y is contractible we can define an H_L-equivariant PL map
  φ: X_t → Y."
- "Thus the shadow S_(v,L) is a homotopy retract of φ_v(S_(v,L)), and so we
  have π_2(φ_v(S_(v,L))) ⊇ π_2(S_(v,L)) = π_2(L) = H_2(L~) = H_2(S^3 − {120
  points}) ≠ 0."
- "In conclusion φ_v(S_(v,L)) ⊆ Y is a connected subcomplex of the contractible
  2-complex Y which is not aspherical, and so gives a counterexample to the
  Whitehead conjecture."

**Closing remark, p. 470.** "Fix a metric on L. We conjecture that there is
ε > 0 such that if g : L → K is a surjective PL ε-map, then K is homotopy
equivalent to L with 1- and 2-cells attached. This conjecture implies that the
geometric dimension of H_L is 3."

## 2. Generality check: what the proof of Theorem 8.7 uses about L

| Input | Where | Hypothesis on L in the source |
|---|---|---|
| Cubical complex Q_L, Morse function f, links ≅ L | Theorem 5.12 | "Let L be a finite flag complex" |
| X_J ≃ wedge of L's | Theorem 8.6 | general finite flag L (§7--8 setup: "We now fix a finite flag complex L") |
| K_x convex | Lemma 8.3 | any vertex x of X |
| St0(σ,L) contractible | Proposition 5.10 (1) | "Let L be a flag complex" |
| shadow quasi-isometry, constants independent of \|f(v)−t\| | observation after Definition 8.8 | uses Lemma 8.3 and the 1-skeleton of L |
| FP, not fp, cd 2 | Example (3) | "acyclic nonsimply-connected finite flag complex, say of dimension 2" |
| π_2(L) ≠ 0 | last display of the proof | the only Poincaré-specific step |

Hence `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`: the
dichotomy holds for every acyclic finite flag 2-complex with `π_2(L) ≠ 0`, in
particular for every acyclic one with finite nontrivial fundamental group.

## 3. Literature status (secondary, abstracts only)

- **Howie (1999).** J. Howie, *Bestvina--Brady groups and the plus
  construction*, Math. Proc. Cambridge Philos. Soc. 127 (1999), 487--493. Its
  abstract, fetched through a web tool, restates that Theorem 8.7 shows one of
  the two conjectures fails. The body was not read.
- **Gersten (arXiv:1501.06875).** S. Gersten, *Asphericity for certain groups
  of cohomological dimension 2*. Abstract via a web tool, not verified
  verbatim: "A finite connected subcomplex of an aspherical 2-complex is
  aspherical iff its fundamental group is of cohomological dimension 2."
- **Web search, 2026-09-13.** Found no source deciding which alternative holds
  for any L. This is a spot check, not a literature review.

## 4. Attempts and gap

1. **The Whitehead side gives no contradiction from the subcomplex alone.** In
   case gd(H_L) = 2, the subcomplex `K` has `π_1(L)` (binary icosahedral) as a
   retract of `π_1(K)`. So `cd π_1(K) = ∞`, and Gersten's criterion is
   consistent with `K` being non-aspherical. Homological constraints on
   subcomplexes of contractible 2-complexes don't bite either: `H_1(K) ≅
   H_2(Y,K)` is free abelian, and `H_1(L) = 0`.
2. **Any 2-dimensional K(H_L,1) is infinite.** It has infinitely many cell
   orbits, since `H_L` is not finitely presented.
3. **Presentation complexes with free π_2.** Killing `π_1(X_t)`, a free product
   of copies of `π_1(L)`, by equivariant 2-cells gives a free `Z H_L`-module
   `π_2` of countable rank. But by the Eilenberg swindle this is available for
   every countable group of cohomological dimension 2, so it carries no
   information about gd.

**Exact gap.** For one acyclic non-aspherical finite flag 2-complex `L`,
decide whether `H_L` acts freely on a contractible 2-complex.
- Yes: Whitehead's conjecture fails.
- No: Eilenberg--Ganea fails.
- Bestvina--Brady's unproved ε-map statement would give "no".
