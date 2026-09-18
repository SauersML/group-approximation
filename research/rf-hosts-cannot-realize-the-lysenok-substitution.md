---
rg: 2
id: rf-hosts-cannot-realize-the-lysenok-substitution
kind: claim
title: A group containing a torsion group Γ and an element t with t g t^-1 = σ(g) for a proper injective endomorphism σ contains the whole ascending HNN extension Γ*_σ; for Grigorchuk's group and the Lysenok substitution this forbids every residually finite, in particular every self-similar, host
distinct_from:
  grigorchuk-ascending-hnn-extension-is-finitely-presented: that is the finitely presented HNN extension itself; this shows it is forced as a subgroup by any conjugator realizing the substitution, so its failure of residual finiteness excludes the substitution from every self-similar host.
  bounded-automaton-groups-embed-in-fp-automaton-groups: that is the open input this constrains; this rules out the one known mechanism that makes a finitely presented overgroup of the Grigorchuk group.
---

**ESTABLISHED** (lane proof below, elementary; the input that `Γ̃` is not residually finite is cited from Sapir–Wise,
J. Pure Appl. Algebra 166 (2002) 191–202, via secondary sources and not re-read here; no priority claimed). Referee a (proof gaps) PASS: `research/artifacts/gq-referee-a-rf-hosts-cannot-realize-the-lysenok-substitution.md`. The citation is no longer needed: `rf-hosts-cannot-realize-branch-substitutions` proves directly that every group containing `Γ` and such a `t` is not residually finite.

## Statement

1. **Rigidity.** Let `Γ` be a torsion group, `σ: Γ -> Γ` injective with `σ(Γ) ≠ Γ`, and let `P ⊇ Γ` contain `t` with
   `t g t^{-1} = σ(g)` for all `g in Γ`. Then `⟨Γ, t⟩ ≅ Γ*_σ = ⟨Γ, t | t g t^{-1} = σ(g)⟩`.
2. **Grigorchuk.** For the first Grigorchuk group `Γ` and the Lysenok substitution
   `σ: a ↦ aca, b ↦ d, c ↦ b, d ↦ c`, `Γ*_σ` is Grigorchuk's finitely presented extension `Γ̃`, which is not
   residually finite. So no residually finite group, and in particular no group acting faithfully on a locally finite rooted tree,
   contains `Γ` together with such a `t`.

## Proof

Let `K` be the kernel of the natural map `Γ*_σ -> ⟨Γ, t⟩`. It meets `Γ` trivially.
- **`K` meets `N` trivially.** Let `N = ∪_n t^{-n} Γ t^n`, the normal closure of `Γ`; the union is ascending
  because `tΓt^{-1} ⊆ Γ`. Then `K ∩ t^{-n}Γt^n = t^{-n}(K ∩ Γ)t^n = 1`, so `K ∩ N = 1` and `[K, N] = 1`.
- **Reduction to `h`.** Suppose `1 ≠ k in K`. Then `k = n t^m` with `n in N` and `m ≠ 0`, and we may take
  `m >= 1` (pass to `k^{-1}`). Commuting with `Γ` gives `σ^m(g) = n^{-1} g n` for all `g in Γ`. Write
  `n = t^{-j} h t^j` with `h in Γ` and conjugate by `t^j`: `σ^{m+j}(g) = h^{-1} σ^j(g) h`.
- **Contradiction.** So on `Λ = σ^j(Γ)`, `σ^m` is conjugation by `h`, and
  `h^{-1} Λ h = σ^{m+j}(Γ) ⊊ σ^j(Γ) = Λ`. The inclusion is strict because `σ^j` is injective and
  `σ^m(Γ) ⊆ σ(Γ) ⊊ Γ`. Iterating the conjugation gives a strictly decreasing chain `h^{-i} Λ h^i`, but `h` has
  finite order. The contradiction takes place entirely inside `Γ`.

So `K = 1`. For (2), `σ(Γ) ⊆ St_Γ(1) ≠ Γ`, and `Γ` is torsion. ∎

## Lesson for general BH

Branch groups become "finitely presented up to an endomorphism" (Lysenok's L-presentation), and the endomorphism is
realized by an ascending HNN extension. That realization is incompatible with residual finiteness. So a finitely
presented self-similar or automaton overgroup of the Grigorchuk group, the input needed by
`separated-automata-reduce-bh-to-fp-overgroups-of-the-base` and `bounded-automaton-groups-embed-in-fp-automaton-groups`,
must get its finite presentation from a different mechanism, one that never conjugates `Γ` onto `σ(Γ)`. V-type
hosts avoid this because they are not residually finite: there the prefix shift plays the role of `t`
(`grigorchuk-groups-lie-in-one-point-germ-extensions-of-v`).
