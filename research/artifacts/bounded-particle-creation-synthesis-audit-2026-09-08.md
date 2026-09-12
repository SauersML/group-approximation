# Bounded particle creation in strict binary encoders

## Result and scope

The current positive-charge proof can be stopped at any finite particle
level N: if a quiescent binary CA is injective on finite configurations
and is noncreating on inputs with at most N particles, then it preserves
and attains every sector through N. Its Hall argument only truncates
inputs, so no hypothesis about larger particle counts is needed.

For a full-shift encoder tau with a supplied local decoder sigma,
memories M,S and sigma tau=id, choose N=|MS|. The existing local decoder
bound confines some missing output to at most N particles if tau is
strict. Therefore a strict encoder must already create particles on
an input with at most N particles. Component additivity extracts such
an input from the finite list of rooted M^(-1)M-connected subsets of
(M^(-1)M)^(N-1) of size at most N.

This closes the unbounded-quantifier issue for this particular synthesis
filter. It does not close Gottschalk's conjecture. The finite list may
be large, and the necessity is far from sufficient: reversible rules
can create particles.

## Exact checks for a proposed rule

1. Verify quiescence and the literal local identity sigma tau=id.
2. Form the finite sets MS and E=M^(-1)M in the actual group.
3. Enumerate nonempty rooted E-connected supports in E^(|MS|-1) of
   size at most |MS|, respecting actual group equalities.
4. If none expands under tau, the truncated induction proves tau
   surjective. If some expands, this filter passes and supplies no
   evidence of nonsurjectivity by itself.

There were no computation jobs or executable validation runs in this
audit. The proof is `truncated-charge-induction-forces-a-bounded-creation-witness`.

## Current external status check

Xuan Kien Phung, *Around Gromov's injectivity lemma and applications to
post-injunctive groups*, arXiv:2603.18183v1, 18 March 2026,
[primary full text](https://arxiv.org/html/2603.18183v1), introduction,
still states unrestricted Gottschalk surjunctivity as open. Its main
results concern post-injunctivity permanence and analogues of Gromov's
lemma; they do not supply an unrestricted counterexample or proof.
This limited check is not a novelty claim for the bounded criterion.
