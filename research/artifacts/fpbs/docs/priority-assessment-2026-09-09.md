# Priority assessment: Benjamini–Schramm before Fixed Price (2026-09-09)

Forwarded by the user on 2026-09-09 while the cost-percolation archive
(`research/artifacts/fpbs/`) was being wired into Cairn. It is the closing
research judgment of the session that produced that archive, and it fixes the
relative priority of the two universal goals `fpbs-benjamini-schramm-universal`
and `fpbs-fixed-price-universal`. Verbatim below.

Editorial note (integration lane, 2026-09-09): Section 3 below credits
arXiv:1804.10191 with both the hyperbolic and the nonunimodular results and the
tree-times-lattice example. The nonunimodular theorem and that example are
Hutchcroft, arXiv:1711.02590 ("Non-uniqueness and mean-field criticality for
percolation on nonunimodular transitive graphs"); arXiv:1804.10191 is the
hyperbolic paper. Both are recorded on
`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`. The text is otherwise
reproduced as forwarded.

---

**Between Fixed Price and Benjamini–Schramm, I would prioritize Benjamini–Schramm for a full affirmative solution.** That is a research judgment—not a known ordering of their difficulty. My confidence is moderate: Fixed Price could yield to a new structural idea, but percolation currently has a more concrete route from an estimate to the complete conclusion.

**Fixed Price is better aligned with our recent constructions for proving additional special cases. That is different from being closer to its universal solution.**

## 1. The fundamental difference

Benjamini–Schramm asks, for each nonamenable Cayley graph,

$$
\boxed{p_c<p_u.}
$$

There is one prescribed random model: independently retain each edge with probability $p$. We must show that the appearance of infinite clusters and their merger into a unique infinite cluster occur at different parameters. ([arXiv][1])

Fixed Price asks

$$
\boxed{C(\alpha)=C(\beta)}
$$

for **every pair of free probability-preserving actions of the same group**. Each cost is itself an infimum over measurable generating graphings. Thus we must compare optimizations performed in probability spaces with potentially very different group-correlated information. ([arXiv][2])

My assessment is:

> **Benjamini–Schramm is principally a problem of controlling a phase transition. Fixed Price is principally a problem of proving that measurable information cannot improve an optimization.**

That distinction does not prove one is harder. But it explains why I see a more identifiable analytic target for percolation.

## 2. Benjamini–Schramm has a concrete sufficient estimate

For a fixed graph $G$, define its connectivity operator by

$$
T_p(x,y)=\mathbb P_p(x\leftrightarrow y).
$$

Hutchcroft's theory establishes the implication

$$
\boxed{
\|T_{p_c}\|_{\ell^2\to\ell^2}<\infty
\quad\Longrightarrow\quad
p_c<p_u.
}
$$

The boundedness persists into a supercritical interval; uniqueness there would force connection probabilities to be uniformly positive, making the operator unbounded. ([arXiv][1])

So one possible finishing theorem has a definite form:

> Nonamenability forces the critical connectivity operator to be bounded.

This is a **stronger conjecture than Benjamini–Schramm**, not an established consequence of nonamenability. We should not mistake having a clean sufficient condition for having solved its difficult part. ([arXiv][1])

Nevertheless, it gives a useful research advantage: the desired conclusion requires only a finite bound, with a constant allowed to depend on the graph. We do not need to compute either threshold, identify critical exponents, or prove one universal numerical gap.

That leaves room for rough but structurally correct estimates.

## 3. There is substantial affirmative evidence from different geometries

The nonuniqueness conclusion has been proved for nonamenable Gromov-hyperbolic quasi-transitive graphs and for graphs admitting a nonunimodular quasi-transitive automorphism group. Those results include, for example, products of regular trees with Euclidean lattices. ([arXiv][3])

The Choi–Seo preprint extends the conclusion to **every Cayley graph of every acylindrically hyperbolic group**, including relatively hyperbolic groups and mapping class groups among its applications. ([arXiv][4])

These are not merely demonstrations on specially engineered examples. They show that the required phase separation can be derived from several substantial geometric structures.

**My inference:** a successful general proof may identify the common mechanism behind these structures and replace their stronger geometric assumptions with nonamenability itself. That is a plausible direction—not evidence that the replacement is routine.

The conceptual target is to explain why, just after infinite clusters appear, outward growth can outpace the reconnections needed to merge them all. A useful theorem would quantify that competition directly.

## 4. Fixed Price has a canonical action—but the difficult comparison remains

Fixed Price is not completely lacking a canonical object. For finitely generated groups, Abért–Weiss proves that Bernoulli actions have maximal free-action cost:

$$
C(\alpha)\le C(b_\Gamma).
$$

Thus it would suffice to prove the reverse inequality for every free action. ([arXiv][5])

But that reverse inequality must preserve the savings in an arbitrary nearly optimal graphing.

An edge may serve many requests while being paid for only once. A low-cost graphing can exploit long-range correlations in deciding where those shared edges should be. Replacing the correlations by independent randomness can change which savings are available. Merely preserving connectivity does not establish preservation of optimal cost.

Our recent reuse-localization argument clarifies this issue, but does not resolve it. Reducing the extra information to the orbit names of a few binary observables does **not** remove the information: one binary observable indexed by every group element can still encode a complicated invariant process.

The gap between "some low-cost action exists" and "every free action has that cost" is visible in established results. Hutchcroft–Pete proves that infinite property-$(T)$ groups have infimal cost one, while explicitly distinguishing that conclusion from fixed price one. ([arXiv][6])

**This is why I would not infer that Fixed Price is close merely because we have better sparsification, routing, or information-localization lemmas.** The missing comparison is structural, not necessarily a residual error estimate that another iteration will shrink.

## 5. Their connection does not make one a shortcut to the other

Lyons proves:

$$
\boxed{
\Gamma\text{ does not have fixed price one}
\quad\Longrightarrow\quad
p_c(G)<p_u(G)
\text{ for every Cayley graph }G\text{ of }\Gamma.
}
$$

Notice **"fixed price one,"** not just "fixed price." ([arXiv][2])

Consequently, a counterexample to Benjamini–Schramm would have to be a nonamenable group of fixed price one. It would therefore **satisfy**, rather than contradict, the Fixed Price assertion for that group.

This explains two things.

First, the cost argument has already disposed of a substantial part of the percolation problem. The remaining case for that approach is precisely the nonamenable fixed-price-one class.

Second, proving fixed price one for another nonamenable group does not automatically advance its percolation problem. It places the group in the class where the cost obstruction supplies no strict threshold separation.

That logical distinction should guide our allocation of effort.

## 6. What could reverse my assessment?

The main reason to be cautious about favoring Benjamini–Schramm is that its full statement concerns **every finite generating set**, not merely one convenient Cayley graph. Every finitely generated nonamenable group is already known to admit a Cayley graph with a nonuniqueness phase; extending this to arbitrary Cayley graphs is a real part of the difficulty. ([arXiv][2])

Nonamenability alone may leave geometry much less controlled than in the successful special cases.

Conversely, Fixed Price could become the easier problem if we found a genuine invariance principle—for example, a theorem that removes correlated reuse information from a graphing without increasing its completed cost. Such a theorem could resolve many cases simultaneously rather than estimate them one by one.

But **we do not currently possess that principle**. Writing an equivalent vanishing-defect condition does not supply it.

## My recommendation

For the goal you have emphasized—**a full affirmative solution rather than a growing collection of examples**—I would make **Benjamini–Schramm the primary target**.

The reason is not that it has fewer symbols or that inequalities are inherently easier than equalities. It is that its randomness is prescribed, its conclusion is a positive separation rather than an exact optimization identity, and established results provide concrete analytic mechanisms capable of delivering that separation.

For Fixed Price, I would continue only along a line that genuinely compares different actions. Another cleverly constructed cost-one group would be worthwhile mathematics, but it would not address the universal obstacle.

**My ranking is therefore: Benjamini–Schramm looks more tractable for a complete positive proof; Fixed Price looks more accessible for further structural and class-level progress with our current methods. Neither assessment justifies treating either missing theorem as a minor lemma.**

[1]: https://arxiv.org/html/1904.05804v2 "The L^2 boundedness condition in nonamenable percolation"
[2]: https://arxiv.org/html/1109.5418v1 "Fixed price of groups and percolation"
[3]: https://arxiv.org/abs/1804.10191 "[1804.10191] Percolation on hyperbolic graphs"
[4]: https://arxiv.org/abs/2508.08932 "[2508.08932] Percolation in acylindrically hyperbolic groups"
[5]: https://arxiv.org/html/1103.1063v2 "Bernoulli actions are weakly contained in any free action"
[6]: https://arxiv.org/abs/1810.11015 "[1810.11015] Kazhdan groups have cost 1"
