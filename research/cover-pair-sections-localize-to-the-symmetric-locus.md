---
rg: 2
id: cover-pair-sections-localize-to-the-symmetric-locus
kind: claim
title: A cover pair has a continuous section iff some continuous equivariant seed into its domain is an exact lift on the finitely many fixed-point sets Fix(e), e in E minus 1
distinct_from:
  post-surjective-sft-covers-admit-scheduled-sections: that builds a section over the proper-colouring shift from any seed; this removes the colouring base entirely, showing the only obstruction to a genuine section lies on the closed set of configurations fixed by some nontrivial e in E, and that off that set colourings are clopen for free.
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids cover pairs of constant-point domains; this does not decide it, but reduces its de-colouring question (need 36774ad3) to the existence of one seed exact on the symmetric locus.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that counts fixed points on finite quotients or sofic models; this uses no finite model and localizes the section problem to fixed-point sets of the finitely many elements of E.
artifacts:
  - research/artifacts/symmetric-locus-seeds-2026-09-18.md
---

**ESTABLISHED (unreviewed)** by [[cover-pair-sections-localize-to-the-symmetric-locus-proof]].

**Setting.** `(X, F)` is a cover pair over `A^G` as in `post-surjective-sft-covers-admit-scheduled-sections`,
with the finite symmetric set `E = NΦ^-1 ∪ ΦN^-1 ∪ {1}`. A **seed** is a continuous equivariant `ξ : A^G → X`. The
**symmetric locus** is the closed set `Sym_E = ∪_{e ∈ E \ {1}} Fix(e)`.

**Theorem S (every group).** `(X, F)` has a continuous equivariant section `s` (`F ∘ s = id`) iff some seed `ξ`
satisfies `F(ξ(z))(1) = z(1)` for every `z ∈ Sym_E`.

Proof: the exact set `V` of `ξ` is a clopen neighbourhood of `Sym_E`. Its complement `K` is compact and `E`-free,
so a finite clopen cover gives a continuous greedy colouring of `K`. Schedule Lemma-2 lifts at the non-exact sites
colour by colour, starting from `ξ(z)`.

**Consequences.**
- **S1.** `G` is non-surjunctive iff some cover pair has a seed exact at `1` on its symmetric locus. So Gottschalk
  is the statement that `F ∘ ξ` always disagrees with the identity somewhere on `∪_{e} Fix(e)`.
- **S2.** The de-colouring question (bus need 36774ad3) is equivalent to finding one seed exact on `Sym_E`.
- **S3.** The interface-buffer obstruction (Obstruction 2 of the scheduled-sections artifact) is not an
  obstruction. There is no interface: all non-exact sites are lifted, and they are locally `E`-free.
- **S4.** What remains is the `⟨e⟩`-coset lift. On `Fix(e)`, a seed must lift at all `e^j` at once by an
  `e`-invariant patch, where Lemma 2 fails because `e ∈ E`. At constant configurations this is Obstruction 1:
  exactness at `a^G` forces a constant `b^G ∈ X` with `F(b^G) = a^G`.

**Not claimed.** This does not decide CP at any nonsofic group, and it does not prove Gottschalk ⇒ CP.
