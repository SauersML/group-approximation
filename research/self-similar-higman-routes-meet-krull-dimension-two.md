---
rg: 2
id: self-similar-higman-routes-meet-krull-dimension-two
kind: claim
title: Two natural finite-presentation-preserving embeddings of hard decidable functionally recursive groups meet named obstructions. Ascending HNN extensions inside Aut(T_d) must preserve every level profile, which excludes the depth-increasing substitutions of endomorphic presentations and leaves only Baumslag–Remeslennikov-type depth-preserving tricks; those are self-similar in Krull dimension 1, but hard word problems need at least two independent counters, i.e. Krull dimension at least 2. The Nekrashevych route reduces verbatim to lift-generation of a hard group's relators
distinct_from:
  decidable-fg-self-similar-groups-embed-in-fp-self-similar: that is the open self-similar Higman theorem; this records where its two most natural constructions die and what each reduces to.
  decidable-residually-wd-groups-embed-in-lift-presented-hosts: that names the lift-presented host step; this shows the Nekrashevych route of the hard-WP target reduces exactly to it, and adds the HNN route's obstruction.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the target; this is an attempt record under its Attempts, localizing the ascending-HNN route at Krull dimension 2 in characteristic p.
  two-counter-kms-top-has-no-affine-self-similar-action: that kills affine realizations of the two-counter KMS top; this explains why two counters are unavoidable, and why Krull dimension 1 is not.
---

**ESTABLISHED as an attempt record (lane bh-gate1-abstract, 2026-09-19).**
- Lemma 1 is elementary and proved here.
- Items marked *cited* are quoted from sources; items marked *recalled* were not re-read.
- The target stays **OPEN**. Not independently reviewed.

## Route 1: Nekrashevych groups `V_d(G)`

- **Why it is tempting.** For a functionally recursive `G`, `V_d(G)` is finitely presented as soon as the relator
  kernel of `G` is a finitely generated lift ideal (`lift-ideal-criterion-sufficiency-holds-for-infinite-state`).
  `G` itself need not be finitely presented, as with Röver over Grigorchuk.
- **What it is not.** `V_d(G)` contains the Higman–Thompson group `V_d`, an infinite group with simple
  commutator subgroup. So `V_d(G)` is not residually finite, and it is never a structure group `H_τ` of
  `farley-hughes-certificates-have-prefix-chart-coordinates`.
  - Its finite presentation is certified by the lift-ideal theorem, an engine outside FH's Thm 8.2 and Prop. 8.10.
  - The lift identities `w = (w_1, …, w_d)π` are relations among prefix maps `σ_(ε,x)`, which are not tree
    automorphisms. So they do not descend to any subgroup of `Aut(T_d)`.
- **What it reduces to.** A hard `V_d(G)` needs a functionally recursive `G` with a hard, decidable word problem
  and a finitely generated lift ideal of relators. That is verbatim the lift-presented step of
  `decidable-residually-wd-groups-embed-in-lift-presented-hosts`, (O4) there: a recursion that contracts relators
  while expanding elements.
  - Finite-state `G` are capped at PSPACE (target node, item 4), so `G` must be infinite-state. There only
    sufficiency of the lift criterion is known.
- **No new obstruction; this is a reduction.** A decidable Bartholdi–Mitrofanov-type group, obtained by running
  their construction on a decidable hard machine, is a natural input, but its lift-generation is untested.

## Route 2: ascending HNN extensions that keep functional recursion

**Lemma 1 (level profiles).** Let `t ∈ Aut(T_d)` and `G ≤ Aut(T_d)` with `t^(-1) G t ⊆ G`, and put
`ψ(g) = t^(-1) g t`. Then for every `k` and `g`, the level-`k` permutation of `ψ(g)` is conjugate in
`Sym(level k)` to that of `g`. In particular `g ∈ St(k) ⟺ ψ(g) ∈ St(k)`.
- *Proof.* `St(k)` is normal in `Aut(T_d)`, and the level-`k` quotient map is a homomorphism. ∎

**Consequences.**
- **Depth-increasing substitutions are excluded.** The endomorphic-presentation substitutions that turn
  infinitely presented branch groups into finitely presented ascending HNN extensions push elements deeper, for
  example Lysenok's `σ` for Grigorchuk's group, *recalled*: `a ↦ aca`, with `a ∉ St(1)` and `aca ∈ St(1)`. So they
  are never induced by conjugation in `Aut(T_d)` extending the given action. An HNN overgroup of that kind needs a
  **new** tree action of `G`, if it has one at all.
- **What remains is depth-preserving.** These are Baumslag–Remeslennikov-type tricks: adjoin a module automorphism
  such as `x ↦ x(a − 1)`, making the configuration module finitely presented over a larger ring. The KMS groups
  are built exactly this way (KMS Lemma 4.1, the BR-conjoints). Lemma 1 allows this, since the new letter can act
  by a level-preserving automorphism.
- **Krull dimension 1 works.** *Cited:* Kochloukova–Luiz (arXiv:2509.05798) quote Kochloukova–Sidki 2020: "if the
  Krull dimension of A as ℤQ-module is 1 … and the centralizer C_Q(A) is trivial then G is transitive
  self-similar", for finitely presented `G = A ⋊ Q`. Baumslag's finitely presented overgroup of the lamplighter,
  `F_2[x^(±1), (1+x)^(-1)] ⋊ Z^2`, meets these hypotheses as quoted. So the depth-preserving trick is self-similar
  in Krull dimension 1. The full hypothesis list behind the ellipsis was not read.
- **Hardness needs Krull dimension at least 2.**
  - *Recalled:* one-counter machines have decidable, low-complexity reachability.
  - A KMS-type encoding of a hard machine therefore needs `K ≥ 2` counters.
  - The counter letters `a_1, …, a_K` act on the configuration module, which by KMS Lemma 4.14 has a basis indexed
    by all counter values. So it is supported in dimension `≥ K ≥ 2` over the counter ring. That last step is a
    heuristic reading, not a computed Krull dimension.
- **In Krull dimension 2 there are two known kills and one hope.**
  - *Characteristic 0, cited:* Kochloukova–Luiz give finitely presented metabelian `A ⋊ Q` with Krull dimension 2
    that are **not** self-similar. Their hypotheses need `A` to be `ℤ`-torsion-free, with `A/pA` an infinite
    domain for every `p`.
  - *Characteristic `p`:* on main, `two-counter-kms-top-has-no-affine-self-similar-action` kills affine
    realizations of the two-counter KMS top.
  - *The hope, recalled from the Dantas–Santos–Sidki literature:* `C_p ≀ Z^2` is self-similar, of degree `p + 1`.
    So characteristic-`p` Krull dimension 2 is not excluded as such.

## The precise obstruction

The ascending-HNN (Higman/Baumslag–Remeslennikov) route to
`fp-self-similar-groups-with-arbitrarily-hard-word-problem` is localized at one question:

> **(KD2_p)** Does some finitely presented, characteristic-`p`, BR-conjoint module group encoding a two-counter
> machine, of Krull dimension `≥ 2` over the counter ring, admit a faithful self-similar action that is not
> affine?

- The characteristic-0 analogue has counterexamples (Kochloukova–Luiz).
- The affine characteristic-`p` realizations are dead (bh-free-25).
- Nonlinear realizations are open.
- Route 1 is open exactly as (O4) of `decidable-residually-wd-groups-embed-in-lift-presented-hosts`.

## Lesson for general BH

**Self-similar Higman embeddings must deepen nothing, and hardness costs two counters.**
- Inside `Aut(T_d)`, conjugation preserves every level profile. So the branch-group trick of endomorphic
  presentations, which deepens, cannot be internalized.
- The Baumslag–Remeslennikov trick, which preserves depth, can be, but it is known to be self-similar only in
  Krull dimension 1.
- Hard word problems need two counters, i.e. Krull dimension 2. That is exactly where finitely presented
  metabelian self-similarity is known to fail in characteristic 0.
