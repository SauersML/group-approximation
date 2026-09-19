---
rg: 2
id: basilica-fp-amenable-hnn-satisfies-boone-higman
kind: claim
title: The Bartholdi–Virág finitely presented amenable HNN extension of the Basilica group embeds in a finitely presented simple group
distinct_from:
  basilica-hnn-extension-is-fp-amenable-non-ea: that records the group B~ (finitely presented, amenable, not subexponentially amenable); this embeds B~ in a finitely presented simple group.
  grigorchuk-fp-amenable-group-satisfies-boone-higman: that is a torsion-type example with finite tail group and a contracting Röver–Nekrashevych host; this is dilation-type, with tail group Z^2 and germ group Z[1/2]^2 ⋊ Z, which cannot be a germ group of a contracting RSG at a rational point (so this construction needs a non-RSG host; other embeddings of B~ are not excluded).
---

**ESTABLISHED** (lane proof below plus the general theorem; not reviewed; no priority
claimed).

## Statement

Let `B = ⟨a, b⟩ ≤ Aut(T_2)` be the Basilica group, and `σ: a ↦ b², b ↦ a`. Let
`B~ = ⟨B, t | t^{-1}gt = σ(g)⟩` be the finitely presented amenable group of
`basilica-hnn-extension-is-fp-amenable-non-ea` (Bartholdi–Virág; not in `SG`, so not
elementary amenable). Then:
- `B~` embeds in a finitely presented simple group, so it satisfies **Boone–Higman**;
- `B~ ∈ B_A`, the **permutational** class;
- so do all subgroups of `B~`, among them `B` and `BS(1,2) = ⟨a, t²⟩`.

## Proof: the general theorem applies

**Conventions.** Maps act on the left, with sections listed at `0`, then `1`:
- `a(0w) = 0w`, `a(1w) = 1b(w)`;
- `b(0w) = 1w`, `b(1w) = 0a(w)`.

So `b² = (a, a)`. These are the Bartholdi–Virág right-action maps. Changing convention
replaces the group by its opposite, and inversion `g ↦ g^{-1}` identifies the two. The
substitution `a ↦ b², b ↦ a` commutes with that identification, so `B~` is the same group
(recheck of the landed import's convention).

**Last-section form.**

```text
σ(a) = b² = (a, a),     σ(b) = a = (1, b).
```

So `σ(g) = (ψ(g), g)`. Here `ψ(g) = σ(g)|_0` is a homomorphism, because `σ` is an
endomorphism (literature import). It satisfies `ψ(a) = a` and `ψ(b) = 1`, so
`ψ(g) = a^{χ_a(g)}` with `χ_a` the `a`-exponent sum.

**Hypotheses of the theorem.**
- `B` is a bounded automata group (BHM's list includes the Basilica), and `ψ(B) = ⟨a⟩ ≤ B`.
- (H0) holds: `a|_0 = b|_0 = 1`, so the directed ray is `1^∞`, not `0^∞`.

**The tail group.** `ψσ^k(g) = a^{n_k(g)}`, where `n_k: B → Z` factors through the characters
`(χ_a, χ_b)`, and `σ` acts on them by `M = [[0,1],[2,0]]` (`ā ↦ 2b̄`, `b̄ ↦ ā`; `M² = 2I`):

```text
n_{2m} = 2^m χ_a,     n_{2m+1} = 2^m χ_b.
```

So `E(B) ≅ Z²`, spanned by the images of `a` and `b`, and it is `F_∞`.

The theorem therefore gives `B~ ↪ W`, with `W` of type `F_∞`, and `W ↪ SV_W`, a finitely
presented simple group. `W` also has a type (A) action. ∎

## What the host looks like

- `W` is a finite germ extension of the Röver–Nekrashevych group `V_2B`, with singular set the
  tail class of `0^∞`.
- The germ group there is `Z[1/2]² ⋊_M Z`, where the dilation germ acts by the expanding matrix
  `M`. It contains the germ image of `BS(1,2) = ⟨a, t²⟩`, namely `Z[1/2] ⋊ Z`.
- By BBMZ `prop:CyclicStabilizers`, germ groups at rational points of RSGs with finite nucleus
  are virtually cyclic, so this germ group cannot occur there. That rules out only this
  construction inside such a host, not every embedding of `B~`. This is why the earlier
  contracting-host criterion
  (`bounded-last-section-ascending-hnns-satisfy-boone-higman`) had to exclude Basilica.
- `det(M − I) = −1`, so the normal closure of the dilation germ is the whole germ group. The
  germ group is not a finite extension of the dilation germs, and they do not form a normal
  subgroup. So BHM `cor:MainFinitenessCorollary` does not apply as stated.

## Lesson for general BH

Dilation (Baumslag–Solitar-type) dynamics, the classical enemy of Thompson-like hosts, is
harmless in a finite germ extension. It is enough that the germ group at the new point is an
ascending HNN extension of an `F_∞` group that lifts equivariantly into a cone. Basilica shows
the two routes to BH genuinely differ:
- "contracting RSG" is too small for this construction: its germs at rational points are
  virtually cyclic;
- "one-point germ extension of a bounded Röver–Nekrashevych group" works.

For general BH this suggests a host class closed under ascending HNN extensions: iterated
one-point germ extensions of bounded Röver–Nekrashevych groups, with ascending-HNN germ groups.
