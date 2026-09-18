---
rg: 2
id: type-f-normal-closure-lemma-is-the-whole-benign-problem
kind: claim
title: "The type F normal-closure lemma is not a step toward type F benignness of N_U but equivalent to it; the join lemma for finitely generated subgroups of F x F implies it; and the classical join witness is not even finitely presented at its first instance"
distinct_from:
  every-re-normal-subgroup-of-a-free-group-is-type-f-benign: That is the open universal statement; this proves that the normal-closure lemma proposed as its missing step is equivalent to it, and isolates the strictly smaller-looking statement (finitely generated subgroups of F x F are type F benign) that implies it.
  two-occurrence-realizability-is-type-f-benignness: That proves closure under preimages, intersections and injective images and names the join as the open step; this shows the join is needed only once, for two finitely generated free subgroups of F x F, and that the classical witness for that join fails already at FP_2.
  separable-benign-witness-forces-rf-quotient: That kills separable witnesses; this is a reduction of the root to a statement about finitely generated subgroups of F x F, whose witnesses by that claim must be non-separable.
---

**ESTABLISHED (proposed, 2026-09-18; referee welcome).** Fix
`m ∈ {2, 3, ..., ∞}` or `m = F`; `F_m`-benign is as in
`two-occurrence-realizability-is-type-f-benignness`. `F` denotes a free
group of finite rank.

1. **Normal closure = the whole problem.** The following are equivalent.
   - (a) Every recursively enumerable `N ⊴ F` is `F_m`-benign in `F` (the
     root `every-re-normal-subgroup-of-a-free-group-is-type-f-benign` at
     level `F_m`).
   - (b) **Normal-closure lemma.** For every `F` and every `F_m`-benign
     `C ≤ F`, the normal closure `<<C>>` is `F_m`-benign.
   - (b') The same for finitely generated `C ≤ F` only.
   - (c) For every finitely presented `P = F/N_P`, `N_P` is `F_m`-benign;
     equivalently, `N_U` is, for Higman's universal group `U`.

   So a "type `F` normal-closure lemma" cannot be proved as a lemma on the
   way: it is the open root itself, already for finitely generated `C`.
2. **One join suffices.** Let `C ≤ F` be finitely generated with
   `N = <<C>>`, and let `ΔF = {(f, f)} ≤ F × F`. Then

       <C × 1, ΔF>  =  F ×_{F/N} F  =  {(u, v) : u v^{-1} ∈ N},
       <C × 1, ΔF> ∩ (F × 1)  =  N × 1.

   Both `C × 1` and `ΔF` are finitely generated free, hence type `F` and
   trivially `F`-benign in `F × F`. Hence (a) follows from
   - (d) every finitely generated subgroup of `F × F` is `F_m`-benign in
     `F × F`,

   and so from any join lemma "`A`, `B` `F_m`-benign in `K` implies `<A, B>`
   `F_m`-benign", applied once, to two finitely generated free subgroups of
   `K = F × F`. The same holds with `K` replaced by the free group `F * F`:
   `N = <C_1, Δ', ker(F * F -> F × F)> ∩ F_1`, where `ker` is `F`-benign
   because its quotient `F × F` is of type `F`.
3. **The classical join witness fails at FP_2.** In the instance of item 2
   the classical Higman witness for the join is
   `<Σ_A, Σ_B> = <C × 1, ΔF> ≤ K *_K K = K`, the Mikhailova fibre product
   `F ×_P F`. If `P = F/N` is infinite and `N ≠ 1`, it is a full subdirect
   product of two free groups of infinite index, so it is not finitely
   presented (Baumslag--Roseblade; or Bridson--Howie--Miller--Short). So the
   answer to "is the classical join witness of type `F_3`?" is no: it is not
   even of type `F_2` in the simplest case the root needs.
4. **Replacement witnesses must be non-separable and non-product.** By
   `separable-benign-witness-forces-rf-quotient`, a witness for
   `F ×_P F ≤ F × F` with `P` not residually finite cannot have `Σ`
   profinitely closed; in particular it cannot be of type `FP_k` inside a
   product of `k` limit groups, cannot live in a LERF host, and cannot be a
   Bestvina--Brady or character kernel of a residually finite group.
5. **Open converse.** Whether (a) implies (d) is open. By Goursat, a
   finitely generated `S ≤ F × F` is `(1 × L) ⋊ Γ_λ` with `L` an r.e.
   normal subgroup of a free group and `Γ_λ` the graph of a homomorphism of
   free groups. Given (a), `1 × L` is `F_m`-benign and `Γ_λ` is type `F`.
   So "(a) implies (d)" reduces to this one semidirect join, where the
   finitely generated factor normalizes the benign one.

Proof: route `type-f-normal-closure-lemma-is-the-whole-benign-problem-proof`.
