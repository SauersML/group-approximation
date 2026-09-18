---
rg: 2
id: juschenko-zheng-liouville-actions
kind: claim
title: Juschenko–Zheng define Liouville actions, build infinitely supported Liouville measures for Thompson's F on the dyadics and for lamplighter actions, and ask whether abelian stabilizers force amenability
distinct_from:
  thompson-f-random-walks-are-not-liouville: that is Kaimanovich's theorem that finitely supported measures on F are not Liouville for the group or its dyadic action; this imports the complementary construction of infinitely supported Liouville measures for the action, and the open questions of the same paper.
  thompson-f-finite-entropy-walks-are-not-liouville: that is the open group-level finite-entropy question; this is about Liouville measures for actions, where every orbit of F is Liouville.
---

**ESTABLISHED by citation.** K. Juschenko and T. Zheng, *Infinitely supported Liouville measures of Schreier
graphs*, arXiv:1608.03554v1 (11 Aug 2016). Verbatim from the arXiv PDF, read 2026-09-17:

> For the simplicity of the notations we write µ · x = Pµ(x, ·). A function f : X → R is Pµ-harmonic if
> f (x) = ∑_{y∈X} f (y)Pµ(x, y), and (X, Pµ) is Liouville if all bounded Pµ-harmonic functions are constant.
> The action G ↷ X is µ-Liouville if (X, Pµ) is Liouville, and if this is the case we say µ is a Liouville
> measure for the action. We call an action Liouville if there is a measure µ on G which makes it µ-Liouville.

Here `Pµ(x, y) = ∑_{g∈G} 1{g·x=y}µ(g)`, and "A measure µ on G is non-degenerate if supp µ generate the group G."

> In order to show that a group is not amenable it is sufficient to find an action which does not admit any
> non-degenerate Liouville measure. Indeed, this will insure that there is no non-deneg erate Liouville measure
> on the group itself, thus, by renowned result of Kaimanovich and Vershik, [6], the group is not amenable. The
> problem of amenability of Thompson's group F can be approached with this technique.

> Lemma 2. Suppose there exists an increasing sequence of finite subsets (Kn) exhausting X and a sequence (ǫn)
> decreasing to 0 such that for each n, there exists a probability measure νn of finite support on G such that
> for any x, y ∈ Kn such that y = s · x for some s ∈ S, we have ‖νn · x − νn · y‖1 < ǫn. Then there exists a
> non-degenerate probability measure µ on G such that (X, Pµ) is Liouville.

> Theorem 3. There is a non-degenerate symmetric measure µ on Thompson group F such that the action on
> Orb(1/2) is µ-Liouville.

> Lemma 4. Consider the semi-direct product G⋉A with G discrete and A amenable. Then there exists a
> non-degenerate probability measure µ on G ⋉ A such that the action of G ⋉ A on A is µ-Liouville.

> While the following questions should have a negative answer, we currently don't have any examples to
> support it.
> Question 5. Let G act transitively on a set X and assume that this action is µ-Liouville action of G on X
> for some measure µ on G such that StabG(x) is abelian for some (equivalently for all) x in X. Is G amenable?

(The extracted text is reproduced as printed, including the typo "non-deneg erate".) Section 2 of the paper
works with a finite generating set `S` of `G`. The proofs of Lemma 2 and Theorem 3 are sketches. This graph
does not rely on them: `amenably-coupled-actions-admit-symmetric-liouville-measures` reproves the statements
it uses, for countable groups and symmetric measures.

Citation route: `juschenko-zheng-liouville-actions-citation`.
