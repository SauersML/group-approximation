# STW XXVII(2): Villadsen compact-divider no-go audit (2026-08-30)

## Result

For a prime `ell`, let a homogeneous Villadsen block contain coordinate
Hopf summands `L_i` with multiplicities `t_i`, together with point-evaluation
trivial summands.  Write `M` for the total rank and `N_ell` for the number
of coordinate multiplicities not divisible by `ell`.  A projection bundle
`F` satisfying

```text
ell F <= E <= (ell+1)F
```

can exist only if `(ell+1)N_ell<=M`.

Thus the `+1` in almost divisibility does not by itself cross the Euler
barrier.  When coordinate maps are multiplicity-free, a divider requires
the coordinate fraction to be at most `1/(ell+1)`.  This remains false for
coordinate-heavy blocks even if `M` is divisible by arbitrarily large
factorials: divisibility of the matrix rank is not divisibility of the
coordinate bundles.

## Chern calculation

If `E=ell F direct_sum G`, then in mod-`ell` cohomology of a product of
two-spheres,

```text
c(E)=c(F)^ell c(G)=c(G).
```

The Frobenius identity kills every positive-degree term of `c(F)^ell`
because the coordinate generators square to zero.  But

```text
c(E)=product_i (1+(t_i mod ell)e_i)
```

has a nonzero degree-`2N_ell` component.  Hence `rank(G)>=N_ell`.
The upper sandwich `E<=(ell+1)F` gives
`rank(G)=M-ell rank(F)<=M/(ell+1)`, proving the threshold.

The calculation is the mod-prime analogue of the Euler obstruction used in
Toms--Winter, Section 4, and applies to an arbitrary proposed divider bundle,
not only to a chosen sum of Hopf lines.

## Inductive-limit consequence

For a simple injective Villadsen type-I system with seed `S^2`, projection
classes and their comparison lift through the inductive system. Therefore,
if the coordinate threshold is violated eventually, the limit class of the
seed Hopf projection has no compact almost divider.  Simple Villadsen
type-I limits are stably finite; Brown--Ciuperca therefore identifies their
compact Cuntz classes with projection classes. Stable rank one is not needed
for this step.

This does not refute almost divisibility of the full Cuntz semigroup.  It
proves that any positive answer for a perforated coordinate-heavy Villadsen
algebra must use a noncompact, soft divider with variable spectral rank.
The remaining question is whether such a soft element can satisfy both
comparisons while evading the same Chern obstruction on its constant-rank
strata.

Robert--Rordam's bad-divisibility AH systems do not close this hinge.  Their
Section 7 constructs simple AH algebras with `Div_* > 1` (and even
`Div_* = infinity`), hence examples that are not almost divisible.  Problem
XXVII(2) instead asks for the opposite conjunction: almost divisibility
together with failure of strict comparison.  The result above is therefore
a local no-go theorem for compact witnesses in the proposed Villadsen test
case, not a new construction of a globally non-almost-divisible algebra.

## Sources checked

- Schafhauser--Tikuisis--White, *Nuclear C*-algebras: 99 problems*,
  arXiv:2506.10902v2, Problem XXVII and the paragraph immediately before it.
- Toms--Winter, *The Elliott conjecture for Villadsen algebras of the first
  type*, arXiv:math/0611059v1, Definition 3.1, Theorem 3.4, and Section 4.
- Robert--Rordam, *Divisibility properties for C*-algebras*,
  arXiv:1106.5523v2, Section 7 (especially Theorem 7.9, Corollary 7.12, and
  the construction with `Div_* = infinity`).
- Brown--Ciuperca, *Isomorphism of Hilbert modules over stably finite
  C*-algebras*, arXiv:0811.0958, compact elements theorem.

## Independent audit

An independent adversarial audit verified the mod-prime Frobenius
calculation, the top Chern monomial, both rank inequalities, and the common
finite-stage lift of the two projection comparisons. It confirmed that the
conclusion concerns compact dividers only. The audit requested explicit
provenance for compact Cuntz classes and inductive-limit comparison; those
inputs are now separate required nodes, with the latter proved directly.
