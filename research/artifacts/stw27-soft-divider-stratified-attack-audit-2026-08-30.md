# STW XXVII(2): stratified attack on soft dividers — outcome audit (2026-08-30)

## What was attempted

The recorded hinge (`stw27-soft-divider-hinge-audit`) asked whether a
soft `(ell,ell+1)`-divider for the Villadsen seed class can evade the
mod-prime Chern obstruction on its constant-rank strata.  This session
ran that attack to completion.  Outcome: two theorems and one verified
dead end.

## Theorem 1 (pinching)

If `ell[b]<=[E]<=(ell+1)[b]` with `[E]` compact of rank `M`, then some
`epsilon_0>0` has: for all `epsilon<=epsilon_0`, the pointwise ranks of
`(b-epsilon)_+` lie in `[M/(ell+1), M/ell]`.  Upper bound from
`ell(b-epsilon)_+ <= ell b <~ E`; lower bound because compactness of
`[E]` pushes the upper sandwich down to a fixed cutdown.

## Theorem 2 (constant-rank rounding at every rank)

A positive element over compact `X` with constant pointwise rank `r` is
Cuntz-equivalent to a projection: `lambda_r` is continuous and positive,
hence uniformly bounded below, so `0` is uniformly isolated in the
spectrum and the support projection is continuous.  Therefore a divider
with a constant-rank small cutdown is a compact divider, and the
coordinate Euler no-go `(ell+1)N_ell<=M` applies REGARDLESS of rank.
This strictly extends `stw27-low-rank-soft-divider-rounding` (which
needed `M<ell(ell+1)` to force constancy through the narrow window).
Corollary: over coordinate-heavy blocks every divider cutdown has
non-constant rank; the window must contain two integers.

## Dead end (verified): the Frobenius wall does not localize

The stratified geometry is all present:

- the minimal-rank stratum `C` of a cutdown is closed, the support over
  it is a genuine bundle `F_C` (same eigenvalue-gap argument);
- the sandwich restricts to honest subbundle relations
  `ell F_C <= E|_C <= (ell+1)F_C` via the Rordam element `t` with
  `t^*t` a cutdown and `tt^*` under `E`, polar-corrected by the
  continuous local inverse of `|t|` on the constant-rank locus.

The obstruction step is the sole failure point.  Over `X=(S^2)^N` the
identity `c(F)^ell=1` mod `ell` uses Frobenius PLUS the square-free
relations `e_i^2=0`.  Over a stratum `C`, `c(F_C)` need not extend to
`X`, and `H^*(C;F_ell)` need not be square-free: closed subsets of the
`2N`-manifold can contain an embedded `CP^ell` (dimension `2ell`, so it
embeds for `N>2ell` by general position), whose ring is polynomial
truncated at height `ell+1`.  A class with `alpha^ell != 0` makes
`c(F_C)^ell` invisible to the argument.  So no stratified vanishing
theorem is available from this mechanism, for any prime.

A counting patch was also checked and fails: granting (counterfactually)
that each stratum kills all coordinate monomials `e_S` with
`|S|>M/(ell+1)`, the relative-cohomology cup-product trick over a cover
by the strata closures would need disjoint sets `S_1,...,S_m` (`m` = the
stratum count, at most `M/ell(ell+1)+1`) of size `M/(ell+1)+1` inside
`{1,...,N}`; the total is of order `M^2/ell(ell+1)^2 > N` once
`M>ell(ell+1)^2`.  So even the strongest imaginable stratified vanishing
cannot globalize on coordinate-heavy blocks of realistic size.

## Where this leaves Problem XXVII(2)

For the Villadsen test class, cohomology now provably fences exactly the
compact and constant-rank witnesses, and nothing else.  A soft divider
with two rank values on a coordinate-heavy block of rank
`M>=ell(ell+1)` faces only rank arithmetic.  The kill-shot experiment
is therefore a CONSTRUCTION: build `b` with rank function taking the
two admissible values on a designed closed/open partition of `(S^2)^N`
and verify both Cuntz comparisons directly (the upper one is the tight
side: it has essentially zero rank slack, so it must be established by
an explicit embedding, not by comparison-with-slack).  If it exists for
every seed class simultaneously, XXVII(2) answers positively on
Villadsen algebras; the present audit removes the last known
obstruction-side hope.

## Sources checked

- Schafhauser--Tikuisis--White, arXiv:2506.10902v2, Problem XXVII.
- Rordam, *On the structure of simple C*-algebras tensor K*, the
  `(a-epsilon)_+ = r^*br` characterization of Cuntz subequivalence.
- Toms--Winter, arXiv:math/0611059v1, Section 4 (the ambient
  square-free Chern calculus; their arguments are always on `X` itself,
  never on strata, consistent with the non-localization found here).
- Robert--Rordam, arXiv:1106.5523v2, Section 7 (divisibility numbers;
  no stratified obstruction there either).
