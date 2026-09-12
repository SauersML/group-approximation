# Solution: matricial stability of the Fournier-Facio group

## Result

Let `G` be the torsion-free finitely presented Fournier-Facio group used by
`fournier-facio-torsion-free-skeleton`. Every operator-norm asymptotic
homomorphism

`phi_n : G -> U(k_n)`

is pointwise asymptotic to the trivial representation:

`||phi_n(g) - 1|| -> 0` for every fixed `g in G`.

Consequently `G` is matricially stable. This is stronger than the existing
Cairn target `fournier-facio-group-matricially-stable`.

## Cairn ingredients already established

1. `normal-kazhdan-defect-non-mf`: if a nontrivial normal Kazhdan subgroup
   `K` lies in the compression defect, every homomorphism from the ambient
   group to a norm matrix corona kills `K` elementwise.
2. `defect-normally-generates-torsion-free-quotient`: for this concrete
   Fournier-Facio construction, the relevant normal closure is the whole
   group, `K = G` (indeed the established note explicitly records that every
   norm-matrix-corona homomorphism is then trivial).
3. `fournier-facio-torsion-free-skeleton`: fixes the group and the
   compression core to which the preceding facts apply.

## Proof

Take an arbitrary operator-norm asymptotic homomorphism
`phi_n : G -> U(k_n)`. Put

`Q = (prod_n M_{k_n}(C)) / c0(M_{k_n}(C))`,

where `c0` denotes sequences converging to zero in operator norm. Define

`Theta(g) = [(phi_n(g))] in U(Q)`.

For fixed `g,h in G`, the asymptotic-homomorphism condition says

`||phi_n(gh) - phi_n(g) phi_n(h)|| -> 0`.

Hence the two sequences represent the same corona element, so
`Theta(gh) = Theta(g)Theta(h)`. Thus `Theta : G -> U(Q)` is an exact group
homomorphism.

By the established normal-Kazhdan killing theorem, `Theta` kills the normal
Kazhdan subgroup `K` in the compression defect. By the established
normal-generation result, `K = G`. Therefore `Theta` is trivial.

Fix `g in G`. Since `Theta(g)=1`, the sequence `(phi_n(g)-1)_n` lies in the
norm-null ideal. Equivalently,

`||phi_n(g)-1|| -> 0`.

This holds for every fixed `g`. Taking the genuine representations
`rho_n(g)=1_{k_n}` therefore gives

`||phi_n(g)-rho_n(g)|| -> 0`,

which is exactly operator-norm matricial stability.

## Why this was previously easy to miss

The old Cairn page for `fournier-facio-group-matricially-stable` predates the
later closure of `defect-normally-generates-torsion-free-quotient`. Once the
latter was strengthened all the way to `K=G`, the corona obstruction stopped
being merely a non-embedding argument: it made *every* corona representation
trivial. Matricial stability then follows immediately by passing an
asymptotic representation to the corona.

## Formalization status

The two hard ingredients are already Cairn-established; the normal-Kazhdan
corona-killing ingredient points to machine-checked Lean artifacts in
`GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean` and
related files. The short bridge from an asymptotic representation to a
corona homomorphism is supplied here at the Cairn proof level.

This bridge was authored without a Lean toolchain in reach, so no new Lean
file is claimed to have been compiled; formalizing the asymptotic-rep-to-
corona bridge is the natural follow-up.
