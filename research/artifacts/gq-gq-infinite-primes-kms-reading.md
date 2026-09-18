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
  - Relations: G1 (`H_0`, `H_1` abelian of exponent `p`; `H_2` abelian), G2–G4 (Baumslag–Remeslennikov
    "BR-conjoints", Lemma 4.1), G5–G7, and G8 (one relation per command of `M`).
- **Theorem 4.3(a), verbatim:** "The group G(M) belongs to 𝒜_p^2𝒜 ∩ 𝒵𝒩_{K+1}𝒜."
- **Lemma 4.4:** `<H_1 ∪ H_2>` is metabelian, and is the semidirect product of an abelian normal subgroup of
  exponent `p` by `H_2`.
- **Lemma 4.5:** `T = <<x_u>>` is abelian of exponent `p`.
- **Theorem 4.17, verbatim:** "If a Minsky machine M is sym-universally halting then the group G(M) is residually
  finite. Its word problem is at least as hard as the halting problem for M."
  - Hypothesis: sym-universally halting, meaning the transition graph is a vertex-disjoint union of finite trees
    (§1.1.6; also §1.6).
  - The proof uses finite exponent at the key step: "the image of the set of elements (\ref{e:x}) with u in Y_D in G'(M)
    form a normal N subgroup of G'(M) of finite index (because T is an Abelian group of finite exponent p)".
- **Theorems 4.18 and 4.19.** 4.19 is referred to as "Theorem 4.20" in the introduction's cross-reference. These
  give finitely presented residually finite groups, soluble of class 3, with Dehn function, respectively depth
  function, above any recursive `f`.
- **Theorem 4.16 (Kh81):** a finitely presented group in `𝒜_p^2𝒜 ∩ 𝒵𝒩_3𝒜` with undecidable word problem.
- **Theorems 5.5 and 5.6:** finitely generated subgroups of `F_2 × F_2`, respectively `S_3 × S_3`, closed in the
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
3. **A new residual-finiteness proof.** KMS's proof of Theorem 4.17 needs finite exponent, so that "all but
   finitely many basis elements" span a subgroup of finite index. With a `Z_(l)`-module base one would instead
   reduce modulo `l^r` and fold. That is the `M_(r,N)` argument of `z-localized-embeds-in-fg-rf-soluble-group`, but
   it has to be made compatible with the finitely many module relations.

None of 1–3 is supplied by the paper. So route (a) reduces to a new construction; the KMS paper itself cannot supply
it.
