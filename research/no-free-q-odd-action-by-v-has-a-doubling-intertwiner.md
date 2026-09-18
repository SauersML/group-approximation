---
rg: 2
id: no-free-q-odd-action-by-v-has-a-doubling-intertwiner
kind: claim
title: No free action of an amenable group with free Z/p for infinitely many primes admits a V-intertwiner with its doubled lift, so Q semidirect <2> never embeds in 2V_tau with 1 sent to the odometer
requires:
  - q-semidirect-2-in-2v-tau-reduces-to-a-circle-coding
distinct_from:
  rational-rotations-and-doubling-have-no-common-tree-coding: that restricts which rotations can be almost-automorphic when the covering is; this needs no hypothesis on the action maps at all (any free homeomorphism action, exotic or not), and shows that on the rationally Cantorized circle the doubling covering alone is never almost-automorphic.
  q-semidirect-2-in-2v-tau-reduces-to-a-circle-coding: that reduces the embedding to a tree-coding question and leaves exotic actions open; this closes every case.
---

**ESTABLISHED** (lane proof, bh-free-30, 09-18; elementary; not reviewed; no priority claimed).

**Notation.** C = {0,1}^N with V acting. For h ∈ Homeo(C) and a locally constant f: C → {0,1}, put Ψ_f(h)(z_0 z) = (z_0 ⊕ f(z)) h(z).

## Theorem

Let L be an amenable group, α ∈ Aut(L), and ρ: L → Homeo(C) an action. Suppose that for infinitely many primes p, some subgroup of order p acts freely. Then there is **no** g ∈ V and no family of locally constant f_a with

  g ρ(a) g^{-1} = Ψ_{f_a}(ρ(α a))  for all a ∈ L.

No hypothesis is placed on the maps ρ(a) beyond being homeomorphisms.

## Proof

1. **A self-similar invariant measure.** Let 𝓜 be the set of ρ(L)-invariant Borel probability measures on C. It is nonempty, because L is amenable and C is compact, and it is compact and convex.
   - For λ′ ∈ 𝓜 put λ̂′(xE) = λ′(E)/2 for x ∈ {0,1}.
   - λ̂′ is Ψ_{f_a}(ρ(αa))-invariant: the preimage of xE splits into the two halves according to f, and the halves together have λ̂′-mass λ′(ρ(αa)^{-1}E)/2 = λ′(E)/2.
   - So S(λ′) := (g^{-1})_* λ̂′ lies in 𝓜.
   - S is affine and weak-* continuous. By Markov–Kakutani it has a fixed point λ, so g_*λ(xE) = λ(E)/2.
2. **Cone masses halve.** Refine the finite partition of g into cones so that every image cone has depth ≥ 1. For a cone W inside a piece, g(W) = x Z″ is a cone, and λ(W) = g_*λ(xZ″) = λ(Z″)/2. Here Z″ = σ(g(W)) is again a cone.
3. **Finitely many generators.** Let N_0 be the largest depth of a piece.
   - If λ(W) > 0, iterating step 2 doubles the mass at each step, so the iteration leaves the pieces after finitely many steps.
   - A cone that lies in no piece contains a piece, so it has depth ≤ N_0.
   - Hence λ(W) ∈ G := Z[1/2]·{λ(Z) : |Z| ≤ N_0} for every cone W. G is a finitely generated Z[1/2]-module.
4. **Contradiction.**
   - A free action of Z/p on C has a clopen fundamental domain D_p, which is a finite union of cones. So 1/p = λ(D_p) ∈ G for infinitely many primes p.
   - But G ∩ Q is a finitely generated Z[1/2]-submodule of Q, because Z[1/2] is noetherian. So G ∩ Q = (1/m)Z[1/2] for some m, and it contains 1/p only for p | m. ∎

The d-ary version, with V_{d} and Z[1/d], works the same way for the primes p ∤ d.

## Corollaries

- **No embedding with 1 ↦ s.** Suppose Q ⋊ ⟨2⟩ ≤ 2V_τ with 1 ↦ s = τ × id.
  - By §1 of `q-semidirect-2-in-2v-tau-reduces-to-a-circle-coding`, the roots are r_a = (x + k_a(y), ρ(a)y) for a ∈ Q_odd.
  - Each nonzero element of L = Q_odd/Z acts freely, by the orbit-sum argument.
  - The doubling element is u∘c with c = (x + j(y), gy) and g ∈ V, and it forces gρ(a)g^{-1} = Ψ_{f_a}(ρ(2a)). Here ×2 ∈ Aut(Q_odd/Z).
  - The Theorem forbids this, so no such embedding exists. This refutes the full target of `lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map`. The per-q statements of `odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators` remain true: they are one prime at a time.
- **On the rationally Cantorized circle D,** the doubling covering is never almost-automorphic, for any binary tree coding. Lebesgue measure plays the role of λ, and the clopen sets [0, 1/p) give the contradiction. This strengthens the hypothesis side of `rational-rotations-and-doubling-have-no-common-tree-coding`.

## Scope

- Only embeddings sending 1 ∈ Q to the odometer s of 2V_τ are excluded.
- A copy of Q ⋊ ⟨2⟩ in 2V_τ in which 1 goes to an element that is not conjugate to s is not addressed.
- Other hosts are not addressed either, for example ones where the centralizer of the "1" element is not fibered over a V-coordinate.

## Lesson for general BH

**The mechanism** is a *mass-module obstruction*. It has three ingredients:
- **Divisibility in the input.** Q-roots of one element s force, through the fibered centralizer, free actions of Z/p for unboundedly many primes p on a transverse coordinate.
- **Free torsion.** Every invariant mass on that coordinate must then contain 1/p for all those p in its value set on clopen sets.
- **Self-similarity of the host.** Here that is the V-intertwiner with its doubled lift. It forces the cone masses of a suitably chosen invariant measure into a *finitely generated* Z[1/d]-module, which can hold only finitely many 1/p.

**Transferable test.** For any candidate host that is a full group of an ample groupoid, the value group of invariant masses on clopen sets must be infinitely generated over Z[1/d] wherever divisible inputs are carried. Every host whose relevant maps are local similarities of one tree fails this. That includes nV, 2V_τ, SV_G on a fixed coordinate, and Röver–Nekrashevych groups.

**Link to the ring route.** This is the dynamical twin of the ring-route gate "[1] divisible by every integer in K_0 with a finitely generated K-budget". In both routes, Q-divisibility demands an infinitely generated trace or dimension range, and finite presentation or self-similarity pushes toward finite generation. A host for GL_n(Q) must resolve exactly this tension, for example with infinitely many independent scaling ratios that are *not* related by a self-similar intertwiner.
