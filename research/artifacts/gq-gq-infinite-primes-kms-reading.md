# Kharlampovich–Myasnikov–Sapir, read from source, for the Z_(l) bottleneck (lane gq-infinite-primes, 2026-09-18)

**Source.** O. Kharlampovich, A. Myasnikov, M. Sapir, *Algorithmically complex residually finite groups*,
arXiv:1204.6506v5 (22 Mar 2013).
- Fetched as the arXiv e-print on MSI (`/scratch.global/sauer354/gq-kms/`): a gzipped single file `KMS-322.tex`,
  1829 lines.
- Local copy: session scratchpad `gq/src/kms/KMS-322.tex`.
- Theorem numbers below are from the tex counters (`\newtheorem{theorem}{Theorem}[section]`, with lemmas, remarks
  and corollaries on the same counter). The sections are 1 Introduction, 2 Turing and Minsky machines,
  3 Semigroups, 4 Solvable groups, 5 Distortion, 6 Universal theories.

## 1. What the paper proves, and under which hypotheses

- **No embedding theorem.** Nothing in the paper embeds a given group into a finitely presented residually finite
  group. The paper constructs specific groups.
- **§1.1.7 "What next?"** poses the question, verbatim: "it would be very interesting to find out whether every
  finitely generated residually finite group with solvable word problem embeds into a finitely presented residually
  finite group. [...] we can consider this paper as a step toward the residually finite version of Higman's
  theorem." It is the unrestricted form; no effectiveness hypothesis is mentioned. Rauzy arXiv:2002.02540 refuted
  that form.
- **§4.1, the construction.** Inputs are a Minsky machine `M` with `K` glasses and `N+1` commands, and a prime `p`
  ("Also fix a prime p (say, p=2)").
  - Generators: `L_0 = {x_u : u in U}` (configurations), `L_1 = {A_0,...,A_K}`,
    `L_2 = {a_i, a_i', ã_i, ã_i' : i = 1..K}`.
  - Relations: G1 (`H_0`, `H_1` abelian of exponent `p`; `H_2` abelian), G2 (block commutation), G3–G4
    (Baumslag–Remeslennikov "BR-conjoints", Lemma 4.1), G5–G7, and G8 (one relation per command of `M`).
- **Theorem 4.3(a), verbatim:** "The group G(M) belongs to 𝒜_p^2𝒜 ∩ 𝒵𝒩_{K+1}𝒜."
- **Lemma 4.4:** `<H_1 ∪ H_2>` is metabelian, and is the semidirect product of an abelian normal subgroup of
  exponent `p` by `H_2`.
- **Lemma 4.5:** `T = <<x_u>>` is abelian of exponent `p`.
- **Theorem 4.17, verbatim:** "If a Minsky machine M is sym-universally halting then the group G(M) is residually
  finite. Its word problem is at least as hard as the halting problem for M."
  - Hypothesis: sym-universally halting, meaning the transition graph is a vertex-disjoint union of finite trees
    (§1.1.6 and §2.2).
  - The proof uses finite exponent at the key step: "the image of the set of elements (\ref{e:x}) with u in Y_D in G'(M)
    form a normal N subgroup of G'(M) of finite index (because T is an Abelian group of finite exponent p)".
- **Theorems 4.18 and 4.19.** 4.19 is referred to as "Theorem 4.20" in the introduction's cross-reference. These
  give finitely presented residually finite groups, soluble of class 3, with Dehn function, respectively depth
  function, above any recursive `f`.
- **Caution (W7, gq-referee-b):** Theorem 4.19 asserts `𝒵𝒩_3𝒜` for its 4-glass machines, but Theorem 4.3(a) and §6
  give `𝒵𝒩_5𝒜`. This lane uses only the `𝒜_p^2𝒜` conjunct.
- **Theorem 4.16 (Kh81):** a finitely presented group in `𝒜_p^2𝒜 ∩ 𝒵𝒩_3𝒜` with undecidable word problem.
- **Theorems 5.5 and 5.6:** finitely generated subgroups of `F_2 × F_2`, respectively `S_3(X) × S_3(X)` (`S_3(X)` the free soluble group of class 3), closed in the
  profinite topology, with distortion and relative depth above any recursive `f`.
- **Remark 1.2:** "although our groups are not linear they are (elementary Abelian)-by-linear since they are
  solvable of class 3 with the second derived subgroup elementary Abelian."

## 2. Decision for route (a): do G_l or Z_(l) meet these hypotheses?

**No, for the groups of the paper.** Node `kms-minsky-groups-contain-no-z-localized`.
- By Theorem 4.3(a) every `G(M)` is finitely generated and torsion-by-abelian: it has a normal subgroup of exponent
  dividing `p^2`, with abelian quotient.
- A torsion-free subgroup meets that normal subgroup trivially, so it embeds in a finitely generated abelian group
  and is free abelian of finite rank.
- So no `G(M)` contains `Z[1/q]` for any prime `q`, and none contains `Z_(l)` or `G_l`.

**The failing hypothesis, precisely.** It is the torsion base. In KMS the machine is simulated in the exponent-`p`
module `T`, and the top `<H_1 ∪ H_2>` is metabelian and finitely generated.
- `Z_(l)` is torsion-free, so it cannot meet `T`.
- It cannot map injectively to the top either (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).

## 3. What a characteristic-0 variant would need

`G_l = Z_(l)[y^(±1)] ⋊ (Z ≀ Z)` has the KMS shape (abelian ⋊ metabelian), but with a torsion-free, non-finitely
generated base. A finitely presented residually finite host of KMS type for it would need three things.
1. **A finitely presented metabelian top containing `Z ≀ Z`,** such as Baumslag's
   `<a, s, t | [s,t], [a,a^t], a^s = a a^t>`. The action of `Z ≀ Z` on `Z_(l)[y^(±1)]` would have to extend to it.
   - For the action of this lane (`β = 1 + l·y d/dy`), the element `s` must conjugate `β` to `β · β_(±1)`.
   - That changes the spectrum `{1 + lj}` to `{(1+lj)(1 + l(j±1))}`, so the base must be enlarged. Not attempted.
2. **Finite presentation of the base as a module over the top,** in the style of KMS relations G5–G8 (BR-conjoints).
3. **A new residual-finiteness proof.** KMS's proof of Theorem 4.17 needs finite exponent, so that the span of all
   but finitely many basis elements has finite index. With a `Z_(l)`-module base one would instead
   reduce modulo `l^r` and fold. That is the `M_(r,N)` argument of `z-localized-embeds-in-fg-rf-soluble-group`, but
   it has to be made compatible with the finitely many module relations.

None of 1–3 is supplied by the paper. So route (a) reduces to a new construction; the KMS paper itself cannot supply
it.

## 4. Calibration of the characteristic-0 variant (2026-09-18)

**4.1 The naive variant is inconsistent** (`kms-configuration-letters-inherit-exponent-p`, lane proof).
- Drop only the base law "`H_0` has exponent `p`" from G1.
- G1 (`A_i^p = 1`), G5 a), G5 c) and G7 still give `x_u^(A_i^n) = x_u x_(uA_i)^n`, hence `x_(uA_i)^p = 1`.
- So every configuration letter except `x_(q_0), ..., x_(q_N)` has order dividing `p`, and the machine
  relations G8 live in the `p`-torsion.
- **The relation that kills torsion-freeness:** the exponent law on `H_1` in G1, transported by G5 a).

**4.2 The fully characteristic-0 variant `G^Z(M)`.** Drop the exponent laws on both `H_0` and `H_1`. This is
analysis, NOT proved: the KMS structure lemmas were not re-derived over `Z`.
- *Where exponent `p` enters KMS.*
  - The structure of `T` is Lemma 4.14 (label `l097`): `T` is "the direct product of cyclic subgroups generated
    by the elements `x_(i,w)`". It is proved by linear independence of the images in the model `T_1` of a group
    `Ḡ`, built over `F_p` (Lemmas 4.9–4.13).
  - The finite-index step is Lemma 4.15 (`l096`): `T(V_R)` is normal and of finite index. Finite index holds
    because `T/T(V_R)` is spanned by finitely many `x_(i,w)` of order `p`.
- *If the model works over `Z`.* Then `T` is free abelian on the `x_(i,w)`, and `T(V_R)` has
  finitely generated free abelian cokernel.
  - Theorem 4.17's argument then goes through with "finite ⋊ metabelian" replaced by
    "(finitely generated abelian) ⋊ (finitely generated metabelian)". Such split extensions are residually
    finite: reduce the base modulo `m`, a characteristic subgroup of finite index.
  - So residual finiteness, ingredient (3), is plausibly NOT where a Minsky-type characteristic-0 variant breaks.
- *Where it does break, conditionally.* If `T` is free abelian, `G^Z(M)` contains no `Z_(l)`.
  - `Z_(l) ∩ T` would be free abelian of rank at most 1.
  - Then `Z_(l) / (Z_(l) ∩ T)` is either `Z_(l)` or a torsion group with elements of order `q^j` for every prime
    `q != l` and every `j`. It would have to embed in the finitely generated metabelian top.
  - The first is impossible (`fg-metabelian-groups-have-roots-at-finitely-many-primes`).
  - The second is impossible because torsion in a finitely generated metabelian group has bounded exponent. The
    torsion of `G'` is a finitely generated module over the Noetherian ring `Z[G/G']`, and `G/G'` has finite
    torsion.
  - So in characteristic 0 the obstruction moves from (3) to (2). Minsky relations (G5–G8) only identify
    configuration elements, with coefficients `±1` in `Z[top]`. Divisibility needs a relation with a non-unit
    integer coefficient.
- *The minimal such relation* is the Euler relation of `G_l`: `m^(x β x^(-1)) = m^β m^l` on the base, which makes
  `x β x^(-1) - β` act as `l`. With it, the base becomes `D/Du`, the Euler lamplighter module, and ingredient (3)
  becomes hard again. The quotient `T/T(V_R)` is then no longer finitely generated abelian: it contains `Z_(l)`.
  The only residual-finiteness mechanism known here is `l`-adic reduction and folding, as in
  `z-localized-embeds-in-fg-rf-soluble-group`.

**4.3 Classical inputs: status.**
- *Finitely generated metabelian groups are residually finite.* KMS use it without citation in the proof of
  Theorem 4.17 ("Since every finitely generated metabelian group is residually finite"). It is P. Hall's theorem,
  Proc. LMS 1959, NOT read at source.
- *Finitely generated metabelian groups embed in direct products of linear groups.* KMS §1.4 cites Wehrfritz,
  "On finitely generated soluble linear groups", Math. Z. 170 (1980), 155–167.
- *Residual finiteness of finitely generated abelian-by-polycyclic groups* (Roseblade, Jategaonkar). NOT read at
  source. It does not apply to `G_l`, whose top `Z ≀ Z` is not polycyclic.
- *Hall's centre-by-metabelian groups with centre `Q`* show that finitely generated abelian-by-metabelian groups
  need not be residually finite. From memory, NOT read at source.
- *Bieri–Strebel criterion for finitely presented metabelian groups.* NOT read at source. There is no known
  general criterion for finitely presented abelian-by-metabelian groups.
