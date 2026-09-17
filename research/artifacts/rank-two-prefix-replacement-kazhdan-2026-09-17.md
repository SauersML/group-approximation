# Rank-two prefix replacement groups host Kazhdan lattices (calibration for nV)

Lane `swarm-0917-w4-z-nv-kazhdan-subgroups`, 2026-09-17, target
`kazhdan-subgroups-of-brin-thompson-groups-are-finite`. **Unreviewed.**

## 1. Outcome

- **Established (unreviewed)**, `rank-two-prefix-replacement-groups-contain-infinite-kazhdan`:
  a lattice `Γ` in `PGL_3(K)` (`K` nonarchimedean, characteristic zero), acting freely
  and type rotatingly on vertices, is:
  - infinite and Kazhdan;
  - acts faithfully on the Robertson–Steger boundary `Ω`;
  - acts element by element through finitely many cylinder prefix replacements
    `ᾱ(p) ⇒ ᾱ(p')` of a finite rank-two word system, with `Z²` shape offsets;
  - has no invariant probability measure on `Ω`, and every orbit is infinite.
- **New imports.**
  - `pgl3-nonarchimedean-lattices-have-property-t` (BdHV 1.3.4, 1.4.15, 1.7.1,
    verbatim);
  - `robertson-steger-boundary-cylinders-and-pure-infiniteness` (RS rel1, f2, 5, 4,
    φ, c1, c2, main2 proof, Remark, examples, verbatim TeX).
- **No groupoid machinery.** The prefix replacement property is read directly off
  `φ(s_{w̄2,w̄1}) = γ1_{Ω(p1)}` and Lemma f2. Kumjian–Pask and Renault are not used.
  This removes the need for those pins in the Kazhdan application, though not for
  `a2-group-embeds-in-full-group-of-its-rs-two-graph` as stated.

## 2. What is killed

These open claims each ask for a statement that is false for rank-two word systems in
general:
- `kazhdan-subgroups-of-nv-act-with-finite-orbits`,
- `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`,
- the target itself.

**Invariant.** Product factorization of the word system: tiles `A = A_1 × A_2`, with
`M_1 = J ⊗ I` and `M_2 = I ⊗ J`, so that horizontal prefix replacement leaves vertical
letters fixed.

**Step where word-system-generic proofs die.** The passage from "Kazhdan and acting by
finitely many prefix replacements with `Z²` offsets" to finite orbits, or to an invariant
measure on a minimal set:
- `Γ ↷ Ω` satisfies all of the hypotheses and neither conclusion;
- the Robertson–Steger system satisfies (H0)–(H3), including the irreducibility
  condition (H2), and the crossed product is simple and purely infinite. So
  irreducibility, minimality-type or pure-infiniteness hypotheses do not rescue the
  argument.

**Threshold.** Rank one is exactly below: SFT full groups contain no infinite Kazhdan
group (`input-encoded-sft-groupoid-hosts-are-not-universal`, via Matui's Haagerup
theorem). So a proof must use rank at least two *together with* the commuting product.

**Relation to earlier kills.**
- `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan` (lane
  swarm-0917-w2-nv-atmenable) kills groupoid-generic proofs with a non-AF kernel. The
  RS example has the same kind of degree grading as nV, so the present kill is strictly
  finer.
- The target's last Attempts line uses `SL_3(Z[1/p]) ↷ P²(Q_p)`, which is not shown to
  act by prefix replacements. It kills only proofs that do not use nV-type structure
  at all.

## 3. Negation route (open) and where the direct attempt dies

If some such `Γ` embeds in some nV, the target is refuted. Rank one suggests trying a
coding.

**Rank one works.**
- An irreducible SFT groupoid `G_A` embeds in `G_2` as an open subgroupoid.
- Code the edges out of each vertex by a complete binary prefix code `c`.
- The prefix replacement `μx ↦ νx` becomes `c(μ)c(x) ↦ c(ν)c(x)`.
- So `[[G_A]] ≤ V`.

**Rank two, direct coding.** Look for a homeomorphism `κ: Ω -> clopen ⊂ C²` sending each
cylinder `Ω[w̄]` to a brick and each prefix replacement to a brick prefix replacement.
- Coordinate `1` of `κ(x)` must be unchanged under removing a vertical prefix (shape
  `e_2`), because brick replacements in coordinate 2 do not touch coordinate 1.
- So the horizontal coding of row 0 of `x` and of row 1 of `x` must coincide.
- In a Robertson–Steger system, row `j+1` is obtained from row `j` through the (H1)
  factorization squares. That map is a finite-state sequential transducer on horizontal
  words, and it is not the identity coding unless `M_2` is a permutation matrix on
  horizontal classes. That it fails for Robertson–Steger systems is expected from
  thickness but is not proved here.
- **The coding dies at this step** (heuristic record, unproved).

**Not excluded.**
- Codings that change shape by a nonconstant offset.
- Embeddings of `Γ` into nV that do not come from an open subgroupoid embedding,
  for example through the `C(C,Γ')⋊V ≤ (n+1)V` construction
  (`cantor-maps-by-v-embed-in-next-brin-thompson-group`). In that construction a Kazhdan
  subgroup has finite image in V and so reduces to Kazhdan subgroups of products of
  copies of `Γ'`. Iterating from V therefore never produces an infinite Kazhdan group.

**Precise open question.** Does the rank-two Robertson–Steger full group of a
`PGL_3(Q_p)` lattice embed in some nV? A yes refutes the target. A no for every rank-two
system is not implied by the target.
