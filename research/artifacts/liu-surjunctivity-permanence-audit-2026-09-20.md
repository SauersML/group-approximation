# Liu consequences: stable finiteness, failed gluing, and intermediate lamps

Date: 2026-09-20. Written mathematical deductions and source audit, not a
Lean certificate or external human referee report. Jihao Liu supplies the
internality input wherever a nonhyperlinearity assertion is used; Andreas
Thom supplies the conditional normalization and double construction.

## 1. All-field stable finiteness really follows from ordinary surjunctivity

Primary source checked: Xuan Kien Phung,
[*A geometric generalization of Kaplansky's direct finiteness conjecture*](https://arxiv.org/html/2111.07930),
Theorem B and its Section 5 proof. Its assumption is finite-alphabet
surjunctivity, not an extra algebraic or linear version. The conclusion
allows every field and every finite matrix size. The route
`phung-surjunctivity-stable-finiteness-citation` records this literature
input; `stable-finiteness-failure-refutes-surjunctivity` already supplies
a separate finite-field contrapositive in Cairn. No novelty is claimed.

The simultaneous witnesses are fixed, not selected independently:

| Witness | Nonhyperlinear input | Surjunctivity input | Extra profile |
| --- | --- | --- | --- |
| W_(2,3,3) | `kun-thom-lamp-wreath-is-not-hyperlinear` | `kun-thom-nonsofic-wreaths-are-surjunctive` | exactly Liu's wreath |
| D_6=G_6 *_(Gamma_6) G_6 | `fp-surjunctive-nonhyperlinear-group-exists` | same combined premise | finitely presented |

Apply the all-field theorem to each same witness. This strengthens the
existing profile but does not overturn Gottschalk or Kaplansky. There is
also an older direct all-field proof for the wreath in
`kun-thom-wreath-stably-finite`; the present route is an alternative input,
not a claim that stable finiteness was first obtained from Liu.

The coefficient-ring warning is essential: L_k(1,2) is not the group
algebra k[L_k(1,2)^times]. A defect in the former cannot be asserted to
be an inverse defect in the latter.

## 2. Exact permanence failures and their orientation

The Kun--Thom Theorem E source is
[*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
already imported as `kun-thom-nonsofic-wreath`. For its q=2,r=d=3 pair,
W=(direct_sum_(G/Gamma) C_2) semidirect G has an abelian locally finite
kernel B and residually finite actor G. The kernel is residually finite
by coordinate projections. Finite quotients and regular permutation
matrices give hyperlinearity of each factor separately. Liu's internality
with Thom's normalization excludes hyperlinearity of W.

The rank-six double likewise has two residually finite vertices and a
residually finite edge, yet is nonhyperlinear. These are closure failures
for semidirect products and for amalgamated free products, not failures
of subgroup closure or of the amenable-quotient extension theorem. Here
the amenable group is the normal kernel, not the quotient.

The edge Gamma is not amenable: it is infinite (the matrices e_12(x_1^m)
give infinitely many distinct elements) and Kazhdan. An amenable discrete
Kazhdan group is finite, since almost invariant unit vectors in its
regular representation would give a nonzero invariant vector. Thus a
theorem requiring an amenable edge cannot be applied to this example.

No claim that these elementary corollaries were absent from the wider
literature is made. They are named reusable safeguards against invalid
generic closure arguments, with the analytic dependency explicit.

## 3. What the finite-quotient gluing algorithm loses

The already-established pair calculation is exact:

    closure_profinite(Gamma in G)=N=EL_r(R).

It occurs in Step 4 of
`kun-thom-wreath-sofic-radical-fibre-parity-proof`. In finite quotients,
one-way conjugate containment of the image of Gamma is equality, and
compressors generate G. Thus that image is normal. Conversely G/N is
residually finite, giving the matching upper bound for the closure.

In particular Gamma is not separable in G. This is stronger information
than saying that separate residual models of the two vertices are
insufficient: it singles out a fixed mixed word they must lose.

Let rho_0,rho_1:G->U(d) have finite images and agree on Gamma. Their
equality set H is a subgroup containing Gamma and the finite-index
normal subgroup ker(rho_0) intersect ker(rho_1). Hence H is profinitely
closed, and N<=H. Take n=e_12(x_1^(-1)). The double word

    w=i_0(n)i_1(n)^(-1)

is reduced and nonidentity because n is not polynomial, but every such
glued model sends w to I. Its trace is exactly 1 at every dimension.
This proves `finite-image-kt-gluings-kill-laurent-differences`.

The earlier canonical-marginal twist construction separates an element
in the SL_d(Z) actor factor, not this n in N. So there is no conflict:
the two vertex images can differ substantially on actor elements while
being forced to coincide throughout the Laurent elementary factor.

This is a bounded completed next step, not a proposed universal gluing
theorem. Arbitrary approximate vertex maps and infinite-image unitary
representations are outside this elementary finite-image argument. The
new analytic theorem is what excludes the full hyperlinear model class.

Separately, `kun-thom-stabilizer-not-co-amenable` already proves that
Gamma is not co-amenable in G. There is no invariant mean on the infinite
coset space to replace the lost finite quotients. This closes a different
repair attempt; nonseparability and non-co-amenability are not synonyms.

## 4. An entire intermediate-coset search branch now closes

Fix the original Gamma<=G, but let Gamma<=K<=G be arbitrary. Put
W_K=(direct_sum_(G/K) C_2) semidirect G, with root lamp a_K.

For any rho:W_K->U(M), let D=rho(Gamma)' cap M. The root lamp image
belongs to D. Liu's universal internality plus Thom's conditional theorem
make rho(G) normalize D, so every translated lamp image is in D. Gamma
therefore acts trivially on all lamp images. Conjugating by G shows that
every conjugate of Gamma does also, and thus N=<<Gamma>> does.

If N is not contained in K, choose n in N\K. The two sites K and nK
are different, while rho(a_(nK)a_K)=1 for every rho. This gives a
nontrivial universal hyperlinear-kernel element and hence nonhyperlinearity
of W_K. Crucially, K need not be Kazhdan or infranormal: the theorem was
applied to the original pair, not the enlarged stabilizer.

This proves `kt-intermediate-wreaths-missing-normal-core-not-hl` and
directly refutes the existing
`kt-pair-hyperlinear-floor-below-normal-closure` existential target.
It is the normalized-Hilbert--Schmidt upgrade of the earlier sofic
intermediate-wreath proof, not an independent analytic mechanism.

At K=N, the fibre-parity calculation embeds W_N into
(C_2 wr SL_d(Z)) times G, a residually finite group. Thus N itself is
an attained positive boundary. No inference that hyperlinearity passes
to arbitrary quotients, or that every K>=N is residually finite, is used.

## 5. Remaining work and certificate boundary

- The two combined profiles inherit their separate surjunctivity proofs,
  rank-six finite-presentation argument where appropriate, and the named
  Liu--Thom analytic chain. Nothing here re-proves all those inputs.
- Gottschalk or Kaplansky for the simple Leavitt unit group is not settled
  by these wreath and double examples.
- The former search for an intermediate K missing N with hyperlinear W_K
  should stop: the new negative theorem refutes its target.
- A useful remaining gluing problem must change the pair, the prescribed
  canonical trace, or the approximation class; no choice of finite
  quotient models can fix the explicit word in Section 3 for this pair.
- No local code or build was run. The parent integration pass performs
  graph validation on MSI. All source edits use the canonical claim/route
  schema and leave correctness dependencies visible.
