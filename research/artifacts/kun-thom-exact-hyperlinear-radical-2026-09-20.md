# Exact hyperlinear radical of the Kun--Thom binary wreath family

2026-09-20. Checked downstream deduction. No Lean verification or new
analytic import. The PDF skill was used for source inspection; the
Theorem E parameters and its residual-finiteness argument were checked
against the full relevant source page, not inferred from an abstract.

## Source and scope

Gabor Kun and Andreas Thom,
[*Nonsofic wreath products of residually finite groups*](https://arxiv.org/pdf/2608.06222v3)
(v3, 2026-08-20), Theorem E on printed page 3 and its proof in Section
5.2 on printed page 15, supply every prime-power q and all r,d>=3.
The groups are `Gamma=EL_r(F_q[x_1,...,x_d])` and
`G=EL_r(F_q[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z)`.
Both are residually finite Kazhdan groups; Gamma is infranormal and not
normal in G.

The universal tracial normalization input is the named claim
`kazhdan-compression-pairs-normalize-all-tracial-models`. Its analytic
source is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2/6.7, via Andreas Thom's
[conditional normalization Theorem 1.2](https://andreasthom.github.io/pdf/nonhyperlinear.pdf).
Liu's Theorem 1.3/7.4 also supplies normalization and credits Thom.
Liu's fixed q=2, r=d=3 group is one instance, not the full scope of his
printed Theorem 8.3. The family-wide exact radical computation below is
a deduction, not a quotation of that theorem.

The already established repository theorem
`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel` supplies the exact
sofic radical and its residually finite quotient. Its entire proof was
read for this check, particularly the normal closure and quotient steps.
The elementary residual-finiteness proof below also removes any need
to rely solely on its Gruenberg citation.

## 1. Normal closure and quotient map

Write `E=EL_r(R)` for the Laurent factor and `N=<<Gamma>>_G`.
Since E is normal in G and contains Gamma, `N<=E`. For distinct i,k,
choose j different from both, possible because r>=3. For every b in R,

```
[e_ij(1),e_jk(b)]=e_ik(b).
```

The first factor lies in Gamma and the second in G, so normality of N
puts every elementary root element in N. Thus `N=E` and
`G/N=SL_d(Z)`.

Let `X=G/Gamma`, `Y=G/N`, and let `p:X->Y` be the coset map. Define
`p_*:direct_sum_X C_2 -> direct_sum_Y C_2` by fibre sums. Finite support
makes each sum finite, and p is G-equivariant. The kernel K is precisely
the finite configurations with even parity in each fibre. Hence

```
W/K = W_N := (direct_sum_Y C_2) rtimes G.
```

K is nontrivial: the cosets Gamma and `e_12(x_1^-1)Gamma` are distinct
but lie in the same N-fibre. Their two lamps give a nonidentity element
of K. The Laurent matrix is not in Gamma because it has a nonpolynomial
entry. No claim that the entire lamp subgroup dies is made: the quotient
retains one binary lamp per N-fibre.

## 2. Every tracial model kills exactly the required pairs

Infranormality and finite generation allow a finite compressor list
generating G together with Gamma, so the normalization premise applies.
Fix an arbitrary homomorphism `sigma:W->U(M)`. Set
`D=sigma(Gamma)' cap M`. The root lamp belongs to D and sigma(G)
normalizes D, so every lamp image belongs to D. Thus

```
sigma(e_(gamma g Gamma))=sigma(e_(g Gamma))
    for every gamma in Gamma and g in G.
```

Conjugate by h and put `y=hg`, `c=g^-1 gamma g`. This kills the pair
`e_(y Gamma)e_(y c Gamma)` for every y and every such conjugate c.
For `n=c_1...c_k in N`, multiply the pairs at
`y, y c_1, ..., y c_1...c_(k-1)`; intermediate lamps cancel because
binary lamps commute and square to one. The remaining pair is
`e_(y Gamma)e_(y n Gamma)`.

Two cosets lie in one fibre exactly when representatives can be chosen
in this form. An even finite subset of a fibre can be partitioned into
pairs. Therefore every element of K dies under every sigma. For a map
from W into any hyperlinear group, compose with its tracial-ultraproduct
embedding to reach the same conclusion. This gives `K<=Rad_hyp(W)`.
It is important that normalization holds for all homomorphisms, not
only canonical models of W: a single nonhyperlinearity statement would
not yield this radical inclusion.

## 3. Residual finiteness: all parameters checked

First, the actor G is residually finite by explicit finite quotients.
For m>=2 reduce exponent vectors modulo m in the finite group algebra
`F_q[(Z/mZ)^d]`, and reduce the acting integer matrix modulo m.
The two reductions are equivariant, giving a homomorphism

```
G -> EL_r(F_q[(Z/mZ)^d]) rtimes SL_d(Z/mZ).
```

The target is finite. A nonidentity integer matrix coordinate survives
for some m. If that coordinate is identity and a Laurent elementary
matrix is nonidentity, choose a nonzero entry of its difference from I.
Its finite exponent support remains pairwise distinct modulo a
sufficiently large m, so that entry survives. This verifies the source's
residual-finiteness assertion in the exact family, for every q,r,d in
scope; no arbitrary extension-closure assertion for residual finiteness
is used.

Next put `B=SL_d(Z)`. The regular binary wreath `C_2 wr B` is residually
finite by an elementary finite-support argument. A nonidentity actor
is detected in a finite quotient of B. A nonzero lamp configuration
has finite support S. Residual finiteness gives a single finite quotient
`beta:B->F` injective on S, by taking a product of quotients separating
all pairwise differences. Summing lamps over beta-fibres is equivariant
and extends to a homomorphism

```
C_2 wr B -> C_2 wr F.
```

It retains the chosen nonzero configuration, since its support points
remain distinct. The target is finite. This proves precisely the
abelian-lamp wreath fact needed here, without invoking a theorem for
nonabelian lamps or for arbitrary permutational wreaths.

Finally, with `rho:G->B`, the map

```
W_N -> (C_2 wr B) x G,
(f,g) |-> ((f,rho(g)),g)
```

is a homomorphism because the action on Y=B factors through rho, and
it is injective because f and g are both recovered from its image.
Products and subgroups of residually finite groups are residually
finite, so W_N is residually finite. Equivalently, project an element
with nontrivial g to a finite quotient of G; if g=1, use the finite
support-separating lamp quotient just constructed.

Every w outside K is consequently separated by a finite quotient of W.
Thus `Res_fin(W)<=K`. Since finite groups are sofic and sofic groups
are hyperlinear, and since the existing fibre theorem gives the same
sofic radical, all inclusions close:

```
K <= Rad_hyp(W) <= Rad_sof(W) <= Res_fin(W) <= K.
```

This also proves unique factorization of every hyperlinear-target
homomorphism through W_N. It does not identify an operator-norm/MF
radical without a separate argument.

## 4. Two compressors: explanatory connection only

For d=3, `kt-two-positive-compressors-generate-full-obstruction` gives
the explicit pair `B=I+E_12`, `A=CB` with C the cyclic permutation
matrix, and proves `<Gamma,A,B>=G`. Thus these two compressors suffice
for the finite-list normalization hypothesis in the radical proof.
Their individual one-compressor flexibility does not alter the
conclusion for the joint actor.

That existing claim only proves a permutation/coset-model obstruction;
it is not itself a unitary normalization theorem. The new argument uses
the established all-trace normalization input explicitly. This note
does not change surjunctivity claims or infer a general unitary result
from the two-compressor permutation obstruction.
