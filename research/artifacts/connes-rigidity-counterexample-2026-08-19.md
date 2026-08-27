# Connes' rigidity conjecture falls — ingestion note, 2026-08-19

Three papers were handed to this session on 2026-08-19 with the instruction
"wire into Cairn if useful".  One of them carries content this program can
use; the other two do not, and this file records why, so the next session does
not re-ingest them.

## 1. Zhou, *ICC Property (T) Groups without W\*-Superrigidity* — WIRED

Source: LaTeX manuscript supplied in-session (Shuoxing Zhou, ENS; no arXiv
number in the source).  Two nodes were authored from it:
`icc-property-t-not-w-star-superrigid` and
`hyperlinearity-cannot-see-the-lamp-module`.

### The statement

There are countable discrete groups `Gamma_1`, `Gamma_2`, both ICC and both
Kazhdan, with `Gamma_1` not isomorphic to `Gamma_2` but
`L(Gamma_1) = L(Gamma_2)` as von Neumann algebras.  Connes' 1982 rigidity
conjecture for ICC property (T) groups is therefore false.  The paper states
that the result was obtained with assistance from GPT-5.6 Sol, independently of
and concurrently with the OpenAI Astra construction announced 2026-08-01
(cited there as chapter 4 of the same release whose nonsoficity chapter this
graph imports at `openai-leavitt-unit-nonsofic`); the OpenAI family is
countably infinite, pairwise nonisomorphic and mutually commensurable.

### The data

```text
k = F_2,  R = k[t],  A = R^3,  C = (A tensor A)^Flip,  V = k^4 symplectic
Q = Sp_4(k)  (finite),  H = SL_3(R) x Q,  D = (A tensor V^*) + C
theta_1(l,q)(u,c) = ((l,q).u,                          l.c)
theta_2(l,q)(u,c) = ((l,q).u + l delta(c) tensor ell_q, l.c)
Gamma_i = D rtimes_(theta_i) H
```

`delta: C -> A` is the `SL_3(R)`-equivariant retraction of `a |-> a tensor a`
(kill the off-diagonal basis vectors), and `ell_q = q.r_0 - r_0` for the
quadratic refinement `r_0(a_1,b_1,a_2,b_2) = a_1 b_1 + a_2 b_2`.

### Steps re-derived by hand here (agree with the source)

- `ell_q` is **linear**, not merely a function: its polarization is
  `B_(q.r_0) - B_(r_0) = omega - omega = 0` because `q` is symplectic, and a
  function vanishing at `0` with zero polarization is additive.  `q |-> ell_q`
  is then a `1`-cocycle by the standard telescoping.
- The dual defect equals a difference of the shear: with
  `calR(z) = x_1 tensor x_2 + x_3 tensor x_4` one has
  `calR(z)(Delta(a)) = r_0(z(a))` and `ell_(q^(-1))(v) = r_0(qv) - r_0(v)`, so
  `J_q(z) = calR(qz) - calR(z)` holds on square tensors and hence on all of `C`,
  since `Delta(b+b') = Delta(b) + Delta(b') + (b tensor b' + b' tensor b)` in
  characteristic two makes the squares span `C`.
- Therefore `F(z,y) = (z, y + calR(z))` conjugates `alpha_1` to `alpha_2`, is
  its own inverse, and preserves Haar measure because it translates inside each
  `hat C`-fibre.  It is **not** a group automorphism of `hat D` — `calR` is
  quadratic — which is the whole mechanism.
- Nonsplitness of `E_ell = V^* + k`: if `ell_q = q.lambda - lambda` then
  `r_0 - lambda` is `Q`-invariant and vanishes at `0`; `Sp_4(k)` is transitive
  on `V \ {0}`, so `r_0 - lambda` is `0` or the indicator of `V \ {0}`, and
  both have the wrong polarization (`omega` versus `0` resp. a nonzero value at
  an `omega`-orthogonal pair).  So `D_2` is not `Q`-semisimple while `D_1` is,
  and that is the isomorphism invariant.
- The characteristic-subgroup extraction is what makes the invariant usable:
  `D_i` is the unique largest normal elementary abelian exponent-two subgroup
  of `Gamma_i` (using that `SL_3(R)` has no nontrivial abelian normal subgroup
  and `Sp_4(F_2)` no nontrivial normal elementary abelian one), and `Q` is the
  unique largest finite normal subgroup of the quotient.

### Taken on the source's word, not checked here

- Property (T): the reduction to Ershov--Jaikin-Zapirain--Kassabov via
  `SL_3(F_2[t]) = EL_3(F_2[t])` is routine (Euclidean ring, and in
  characteristic two the transposition matrix is a product of elementary ones),
  but the relative-(T) argument — the Boolean weight bound
  `wt(P) >= 2^(n-2)` for nonzero Boolean polynomials of degree at most two, run
  through the five detectors `d_1,...,d_5` and the spectral measure — was read,
  not audited line by line.
- ICC of both groups.
- The independence/concurrency claim with respect to the OpenAI construction.

### Deliberately NOT claimed anywhere in the graph

**Soficity or hyperlinearity of `Gamma_1`, `Gamma_2`.**  Truncating `R = k[t]`
at `t^N` makes every constituent finite and looks like it exhibits both groups
as residually finite, hence sofic, hence hyperlinear — but the compatibility of
`delta` and of `theta_2` with the truncation was not verified, so no node says
it.  Nothing in the wired claims depends on the answer: the point of
`hyperlinearity-cannot-see-the-lamp-module` is that the two groups stand or
fall **together**, whichever way they fall.

Also not claimed: any transfer to MF-ness or to soficity.  `L(Gamma_1) =
L(Gamma_2)` is an isomorphism of *von Neumann* algebras and carries no
information about `C*_r(Gamma_i)`, so the graph's MF layer is untouched by it.

## 2. Davies--Hatzel--Yepremyan, *Minimal Cayley graphs with large chromatic number* — NOT WIRED

Resolves Babai's minimal Cayley graph problem: for every `k` there is a finite
group with a minimal generating set of involutions whose Cayley graph has
chromatic number at least `k`, by a Hales--Jewett-augmented Tutte/Descartes
induction (`Gamma_(k+1)` is generated by the left translations `L_(b_0(s))`
and the involutions `t_J` on `B x V`).

No hook.  The corpus has no chromatic-number, independence-number or
minimal-generating-set content (the only `chromatic` hit in `research/` is
Koenig edge colouring inside
`spherical-tight-single-colour-near-perfect-matching-proof`, and the `Ramsey`
hits are the surname in Ji--Ogle--Ramsey).  The groups produced are finite,
hence sofic and hyperlinear, so they are not candidates; and the graph-theoretic
input that the nonsoficity machinery actually consumes is *expansion*
(`kun-expander-decomposition-formalized-proof`), not chromatic number, which is
neither implied by nor implies it.  The paper's own Conjecture 1 (large girth
**and** large chromatic number) would be the interesting shape for graphical
small cancellation, and it is open.

## 3. van Doorn--Judin--Monticone--Morrison, *On Some Problems from the Kourovka Notebook* — NOT WIRED

Eight Kourovka solutions found and formalised in Lean by Harmonic's Aristotle:
3.46 (a group with exactly two maximal locally soluble normal subgroups), 18.50,
19.25, 20.125, 21.8 (`CT_((k)) = S_(lcm(2..k))`), 21.24, 21.147, 21.150.

Checked one candidate hook and it does not hold.  Problem 3.46 is a
non-uniqueness theorem for a **join-type** radical: the maximal locally soluble
normal subgroup is non-unique because the product of two locally soluble normal
subgroups need not be locally soluble (Baumslag--Kovacs--Neumann 1965), and
local solubility is subgroup-closed and closed under directed unions exactly as
soficity is.  That would be a live caution if this graph's radicals were joins
of normal subgroups — but they are not: `sofic-radical-soficization` defines
`Rad_sof(H)` as the **intersection of the kernels** of all homomorphisms to
sofic groups, which is well defined with no product-closure input, and the MF
radicals in the corpus are of the same residual shape.  So the analogy has
nothing to bite on.

The rest is disjoint from the program: no node touches ordered groups, power
graphs, Rota--Baxter operators, totient sums or class transpositions, and
`CT(Z)` is not finitely presented, so it is not a Boone--Higman host either.
The paper is worth reading for its appendix on formal-discovery methodology,
which is a `notes/` matter, not a graph matter.
