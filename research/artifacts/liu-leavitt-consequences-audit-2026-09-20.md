# Liu internality and the Leavitt consequences: conditional proof audit

Date: 2026-09-20. This is a downstream mathematical audit, not a certification
of Liu's proof of Theorem 6.7. No canonical claim or route was edited and no
Lean verification was run. Theorem 6.7 remains a hypothesis throughout.

## 1. Result and trust boundary

Assume the statement of Liu, *Nonhyperlinear groups exist*, Theorem 6.7:
for every finitely generated Kazhdan group G, every specified free ultrafilter
omega, every sequence d_n, and every homomorphism into
M = prod_omega (M_(d_n), tr_(d_n)), its full relative commutant is [A_n]_omega
for unital coordinate star-subalgebras A_n in the original M_(d_n).

Then the two-use heat argument gives

```
H = L_(F_2)(1,2)^x is not hyperlinear.
```

The sequential quantifiers, component selection, and full-commutant endgame
do match. No additional factorial-embedding conjecture, regular block-weight
bound, general channel-rounding theorem, or exact representation repair is
required. I found no gap in these downstream analytic steps after rederiving
the estimates below. This conclusion also uses the repository's structural
identifications of H, its simplicity, and the native compressor data. Their
elementary applications are checked below; this is not a fresh audit of all
foundational proofs of GL = EL, simplicity, or the imported property-(T)
and SOS theorems.

The checked source is the saved PDF
`/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq/lit/liu-nonhyperlinear-2026-09-20.pdf`.
Theorem 6.7 and its continuation were also inspected visually on PDF pages
37-38. Source URL:
[Liu's PDF](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf).
The browser could not fetch that URL during this audit; the saved PDF was
read directly. Proposition 3.1, pp. 6-8, is a compatible expectation-lifting
statement, but the application below supplies its own short norm-witness
argument and does not assume that Liu's particular averaging lengths equal
the repository's heat times.

## 2. Internality supplies exactly the sequential heat rounding needed

Fix a finitely generated property-(T) group G, a finite symmetric list S of
literal generating words paired with their inverse spellings, and a finite
Ozawa SOS certificate

```
Delta^2 - kappa Delta = sum_j xi_j^* xi_j,  kappa > 0.
```

Let V_n be full asymptotic representations: every fixed true relation has
normalized-HS defect tending to zero. Canonical traces are not needed in
this section. Let epsilon_n bound the fixed equality rows in this expanded
SOS identity. Set

```
A_n = I - |S|^(-1) sum_s Ad(V_(n,s)),
P_n = exp(-t_n A_n),
t_n -> infinity, epsilon_n t_n -> 0.
```

Pairing inverse spellings makes A_n exactly self-adjoint and nonnegative.
Poisson expansion makes P_n unital completely positive, trace preserving,
and contractive both in operator norm and normalized L2. The finite SOS
error is bounded on the entire operator unit ball, since
`||(Ad W - Ad Z)x||_2 <= 2 ||W-Z||_2 ||x||_op`.

Writing E_n(x) = <A_n x,x>, the rederived estimates are

```
E_n(P_n(s)x) <= exp(-2 kappa s) E_n(x)
                  + C epsilon_n ||x||_op^2 / kappa,
||P_n(t)x - x||_2^2 <= E_n(x)/kappa
                  + 2 C epsilon_n t ||x||_op^2/kappa.
```

The first follows by differentiating heat energy and applying the SOS
identity to the contraction P_n(s)x. The second follows by integrating
the derivative of squared L2 norm and using `(1-exp(-t a))^2 <=
1-exp(-2t a)`. These are the estimates (6), (8a), (8b) in
[the heat-inclusion artifact](leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md).

In any fixed matrix ultraproduct, the induced P has range in
D = pi(G)' cap M, by the first estimate. It fixes every element of D by
the second: asymptotic commutation gives E_n(x_n) ->_omega 0, and no rate
relative to t_n is needed. P is therefore the trace-preserving expectation
E_D. This is identification of the full external commutant.

If Theorem 6.7 gives D = [B_n]_omega, the maps E_(B_n) also induce E_D.
For example, their outputs lie in D and their differences from their inputs
are orthogonal to every bounded sequence from B_n; hence they induce the
L2 orthogonal projection. It follows that

```
lim_omega ||P_n - E_(B_n)||_(infinity->2) = 0.
```

The norm is genuinely uniform: if it did not converge to zero, choose a
contraction witness x_n at every bad index. Its ultraproduct class would
contradict equality of the two induced maps. Equality merely on fixed group
words would not give this conclusion.

To obtain ordinary sequential convergence, put
`r_n = inf_B ||P_n-E_B||_(infinity->2)`, over unital subalgebras in M_(d_n).
If r_n does not tend to zero, restrict to a subsequence where r_n >= c > 0
and choose a free ultrafilter on its reindexed natural numbers. The full
asymptotic representation, SOS estimates, and admissibility survive this
restriction. Applying Theorem 6.7 there contradicts the preceding limit.
Thus r_n -> 0; choosing B_n within 1/n of the infimum proves (R).

This uses Theorem 6.7 universally over embeddings and ultrafilters. There
is no demand for one choice of algebras working simultaneously for all
models, nor for a numerical rate independent of G. Its same-dimension
conclusion means the separate corner-rounding theorem is unnecessary.

The admissible-time comparison is also correct:

```
||P_n(t)-P_n(s)||_(infinity->2)^2
 <= (2/kappa) exp(-2 kappa min(s,t))
       + (2 C epsilon_n/kappa)|t-s|.
```

Consequently some admissible time suffices for all admissible times of the
same model. See [the time-comparison artifact](leavitt-poissonization-and-admissible-time-rounding-equivalence-2026-09-08.md).

## 3. Component selection preserves canonicality and scalarity

Now G is countable ICC and the original tuples have canonical limiting
trace. Suppose their global heat P_n(t_n) rounds to E_(B_n), with error
eta_n -> 0. Heat energy makes commutators of each generator with P_n(x)
uniformly small on contractions. Therefore generator commutators with
unitaries in B_n are uniformly small. Haar averaging followed by polar
completion replaces each V_(n,s) by W_(n,s) in B_n', with
`gamma_n = max_s ||V_(n,s)-W_(n,s)||_2 -> 0`.

This does not repair the tuple to a genuine group representation.
Fixed-word telescoping preserves all asymptotic relations and traces.
Duhamel's formula gives

```
||P'_n(tau)-P_n(tau)||_(infinity->2) <= 2 tau gamma_n.
```

Choose tau_n <= t_n tending to infinity sufficiently slowly, and increasing
relation prefixes J_n, so that tau_n gamma_n -> 0 and
`tau_n^2 sum_(r in J_n) ||W_(n,r)-I||_2^2 -> 0`.
The time comparison then gives
`xi_n = ||P'_n(tau_n)-E_(B_n)||_(infinity->2) -> 0`.

Write

```
B_n = direct_sum_i (M_(a_i) tensor I_(b_i)),
W_(n,s) = direct_sum_i (I_(a_i) tensor W_(n,i,s)),
lambda_i = a_i b_i / d_n.
```

For component scalar-heat error xi_(n,i), independent contractions in these
blocks show `sum_i lambda_i xi_(n,i)^2 <= xi_n^2`. Relation defects also
average with these physical trace weights. Using algebra dimension weights
instead would be incorrect.

Canonicality is not inherited by an arbitrary component. For each g != 1,
choose M distinct conjugates h_j g h_j^-1 using ICC, and average their
literal evaluations to Z_n. Each component trace of Z_n equals the trace
of W_(n,i,g). Cauchy-Schwarz and global canonicality give

```
limsup_n sum_i lambda_i |tr_(b_i)(W_(n,i,g))|^2
 <= lim_n ||Z_n||_2^2 = 1/M.
```

Letting M grow proves the required mean-square concentration. Choose a
slowly increasing prefix of nonidentity words and select a component whose
sum of scalar-heat error squared, the time-weighted relation errors, and
squared trace errors is at most its weighted mean. That component yields
full canonical G-microstates.

The tau_n^2 penalty is essential: it implies
`tau_n epsilon_selected,n -> 0` for the fixed SOS rows. The retention
estimate in Section 2 now shows every bounded sequence asymptotically
commuting with the selected generators is fixed by selected heat. Since
selected heat tends uniformly to scalar expectation, every such sequence
is scalar in the ultraproduct. Thus the full external commutant is C1.
This is stronger than scalar coordinate commutants, and it does not confuse
factoriality of pi(G)'' with factoriality of its external commutant.

These checks validate Section 2 of
[the two-use artifact](leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md).
The SL_3(Z) counterexample in Sections 2-3 of
[the boundary/countermodel artifact](leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md)
does not refute selection: it refutes scalarity of every given canonical
embedding, whereas selection produces another embedding.

## 4. Native rounding gives the contradictory central height

Use R = L_(F_2)(1,2), H = GL_4(R) = EL_4(R), the native
L = diag(GL_3(R),1), and K = diag(I_3,R^x). Prefix-code matrix
self-similarity and GL = EL identify H and L abstractly with R^x.
Thus both are finitely generated and Kazhdan by
`elementary-groups-over-fg-rings-have-property-t`. Infinite simplicity of H
gives ICC: a finite conjugacy class gives a finite permutation quotient;
simplicity would force it trivial, making the element central.

Write s,t,a,b for the Leavitt generators, with
`ts=ba=1, ta=bs=0, st+ab=1`, and e=ab. The native compressor and inverse are

```
u = [s 0 0 e; 0 s 0 et; 0 0 s et^2; 0 0 0 t^3],
u^-1 = [t 0 0 0; 0 t 0 0; 0 0 t 0; e se s^2e s^3].
```

The identities use `e+set+s^2et^2+s^3t^3=1` and give
u L u^-1 <= L. For k=diag(I_3,1+et) in K, direct multiplication gives
`y=u k u^-1=x_12(e)` in L, nonidentity.

On canonical H-microstates, native heat P for L and its conjugate
Q=Ad(U) P Ad(U*) satisfy `||QP-P||_(infinity->2) -> 0`.
Choose times slow enough to control the fixed compressor and [L,k] rows
as well as SOS rows. Then QY-Y -> 0. The full heat identification gives
P(Y)=E_D(pi(y))=0: pi(L)'' is a factor, D=pi(L)' cap M, and a trace-zero
group unitary in that factor is orthogonal to D. Hence
`||PQ-Q||_(infinity->2) -> 1`. This verifies the stronger reverse witness
in Section 2 of
[the trace-distortion artifact](leavitt-heat-rounding-forces-unbounded-trace-distortion-2026-09-08.md).
The weaker single-commutator bound tending to 1/sqrt(2) is not what is used
to obtain the stated central-height constants.

Round native P to E_A, and conjugate to F=Ad(U)E_A Ad(U*). Both mixed-norm
defects change by at most 3 times the rounding error. Consequently
delta=||FE_A-E_A|| -> 0 and rho=||E_A F-F|| -> 1.

The finite central-height lemma was rechecked from its proof. For central
atoms p_i of A, simple degrees a_i and physical weights t_i, put
`h_i=log(t_i/a_i^2)` and `m_ij=tr(p_i U p_j U*)`.
The physical overlaps form a balanced flow. The Haar covariance/support
bounds `w_i H_ij <= m_ij` and `w_j H_ij <= m_ij` give

```
up <= delta^2,
down >= rho^2/2 - delta^2.
```

Eventually down >= 1/4. A physical-weight median and a monotone ramp of
width 1/16 give z_n in Z(A_n), with trace zero, operator norm at most one,
L2 norm at least 1/8, and
`||[U_n,z_n]||_2^2 <= 2 delta_n^2/(1-exp(-1/16))`.
The variance bound follows from opposite level sets of masses at least
1/2 and 1/32. Stationarity turns the absolute ramp flow into twice its
upward flow. These details do not assume a bounded number of central
atoms, regular trace weights, or a purely atomic limiting center.
See [central heights](leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md),
Section 1, and [central overlap bounds](leavitt-regular-trace-cp-reversal-2026-09-08.md), Section 8.

Uniform heat rounding identifies D=[A_n]_omega, so the bounded central
sequence gives z in Z(D), commuting with pi(u). Since pi(K) is contained
in D, it also commutes with pi(K) and hence with pi(uKu^-1).

The final generation step is genuine native algebra. If
p=diag(1,1,1,0), then upu^-1=diag(st,st,st,0); the complementary support
of uKu^-1 is q=diag(e,e,e,1). It contains x_14(ar), x_41(rb), for r in R.
Then

```
[x_21(b),x_14(ar)] = x_24(r),
[x_41(rb),x_12(a)] = x_42(r).
```

All remaining roots involving coordinate four follow using L roots.
Therefore H=<L,uKu^-1>. It follows that z belongs to the global commutant
C, and since C is contained in D, z belongs to Z(C).

Apply Section 3 to global H-heat, producing a canonical model with C=C1.
Restrict that selected model to L, or precompose with H isomorphic to L.
It is again a full canonical model of a finitely generated Kazhdan group.
Theorem 6.7 and Section 2 supply the second rounding instance in these
selected dimensions. Its z has trace zero and norm at least 1/8 in C1,
a contradiction. This proves the conditional nonhyperlinearity of H.

## 5. Exact downstream scope

* **Finite presentation and simplicity.** H itself is infinite simple and
  Kazhdan by the structural inputs above. Its finite presentation is the
  separate input `leavitt-unit-group-finitely-presented`, citing Khanh,
  arXiv:2609.08428v1, Theorem 6.1. The
  [primary arXiv record](https://arxiv.org/abs/2609.08428) was checked on
  2026-09-20 and still records v1 and finite presentation in its abstract.
  This audit did not independently reprove Khanh. Thus “finitely presented
  infinite simple Kazhdan nonhyperlinear” uses that additional imported
  theorem; finite presentation is not needed in Sections 2-4.
* **Stability.** With the additional finite-presentation and
  Steinberg-comparison inputs of `leavitt-unit-hs-stable-iff-nonhyperlinear`,
  the existing target `leavitt-steinberg-hs-stable` follows. Simplicity makes
  every nontrivial map into a matrix ultraproduct injective, so the
  nonhyperlinear branch has only trivial such maps. This does not derive
  general Kazhdan representation stability from internality.
* **Boundary groups.** For finite k of characteristic 2, d>=2, N>=3,
  `boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el` transfers the
  negative conclusion to S_boundary(d,k). Only its subgroup direction is
  required: put the binary Leavitt algebra in a proper boundary corner,
  then pad by the complementary identity. The resulting elementary group
  meets the scalar center trivially and embeds in the projective boundary
  group. This uses the explicit boundary Leavitt family and simplicity of
  its source algebra. I checked the corner and elementary rank-transport
  steps in the recorded route, not every earlier boundary-ring theorem.
  Do not claim finite presentation of all these boundary groups from this
  hyperlinearity equivalence alone. Odd-characteristic and characteristic
  zero versions do not follow from the binary characteristic-two result.
* **Other characteristic-two Leavitt groups.** The existing mutual-embedding
  theorem `leavitt-unit-groups-over-finite-fields-mutually-embed` transfers
  nonhyperlinearity to L_(F_(2^m))(1,n)^x for n>=2, subject to its recorded
  algebra-embedding inputs. This does not transfer across characteristics.
* **Tensor hosts.** For any nonzero unital F_2-algebra B, the injective map
  r -> 1_B tensor r embeds R^x in (B tensor R)^x and embeds EL_3(R) in
  E_n(B tensor R), n>=3. These hosts are therefore nonhyperlinear without
  K-theory assumptions. To additionally call E_n(B tensor R) simple,
  use the central-simple B hypothesis in
  `central-simple-leavitt-tensor-unit-groups-are-simple`. To call it finitely
  presented, use the actual finite normal generation condition on the
  unstable Steinberg kernel in `leavitt-tensor-elementary-host-criterion`,
  or the stronger appropriate K_1/K_2 vanishing plus imported comparison
  criteria. For full unit-group simplicity and finite presentation the
  stronger criteria remain necessary to the recorded route. This audit
  does not discharge a universal Boone-Higman embedding prerequisite.
* **Subgroups and quotients.** Nonhyperlinearity ascends to overgroups.
  It does not descend to arbitrary subgroups or quotients. In particular
  this gives no negative conclusion for Thompson's V, and gives no
  nonhyperlinearity of a Kazhdan cover merely because it surjects onto H.
  The alternative `leavitt-nonhyperlinear-via-kun-thom-wreath-embedding`
  still needs its group-embedding premise; the heat route bypasses it.

## 6. Proposed canonical wiring, with existing IDs reused

The planned import `kazhdan-commutants-are-internal` must remain OPEN until
its upstream proof review closes. Routes may record the conditional
implications now, without making their targets established.

1. A reusable heat claim is warranted, for example
   `kazhdan-heat-rounds-to-coordinate-expectations`: exactly the statement
   of Section 2 for every fixed finitely generated (T) group and full
   asymptotic representation, fixed SOS rows, and admissible times. It
   does not need canonical trace, quantitative modulus, or simultaneous
   choices across models. A route requires
   `kazhdan-commutants-are-internal` and
   `property-t-laplacian-sos-certificate`, with the bounded SOS residual
   argument and norm-witness subsequence proof written in its body.
2. The specifically negative claim `binary-leavitt-unit-group-is-not-hyperlinear`
   was absent when this audit began. Its route can require the internality
   claim directly (or the reusable heat claim),
   `property-t-laplacian-sos-certificate`,
   `elementary-groups-over-fg-rings-have-property-t`,
   `leavitt-gl-equals-el-and-perfect-unit-group`, and
   `binary-leavitt-unit-group-is-simple`, with Sections 2-4 as its proof.
   The native algebra and central-height argument are supplied here and
   in the linked proof artifacts; they must be cited as actual arguments,
   not replaced by an ESTABLISHED label on a conditional node.
3. Reuse `binary-leavitt-unit-group-hyperlinear` and put the new negative
   claim in its `refuted_by` list. The relationship is conditional until
   the negative claim becomes established. Reuse
   `leavitt-unit-hs-stable-iff-nonhyperlinear` to route the negative claim
   to `leavitt-steinberg-hs-stable`.
4. If desired, the existing intermediate targets can expose the two uses:
   internality plus selection proves
   `leavitt-unit-hyperlinear-gives-factorial-canonical-model`; internality
   plus `factorial-leavitt-models-have-external-corner-commutants` proves
   `leavitt-unit-has-no-factorial-canonical-model`. Then the existing
   `leavitt-hs-stable-from-no-factorial-canonical-model` route applies.
   These are explicit conditional proofs, not an appeal to the open
   general factorial-commutant embedding problem.
5. Leave `bistochastic-near-idempotents-round-dimension-free` unchanged.
   Likewise leave the broad premise of `leavitt-hs-stable-from-channel-rounding`
   unchanged. The title-level proposition of
   `leavitt-channel-rounding-forces-nonhyperlinearity` has that stronger
   premise; its attached artifact proves the narrower (R) theorem, but
   modus ponens with the title-level broad theorem would be invalid here.
6. The existing boundary hyperlinearity claim is parameterized over finite
   fields. A characteristic-two negative theorem should keep that scope
   explicit rather than silently refuting every odd-characteristic instance.

Neither Theorem 6.7 nor the proof above establishes rounding of arbitrary
self-adjoint bistochastic near-idempotents. Poissonizing an arbitrary
channel produces a heat semigroup, but does not produce fixed group
generators, full approximate group relations, a property-(T) source, or a
group-algebra SOS certificate. That is exactly the missing bridge between
the broad channel conjecture and this conditional application.

## 7. What this audit leaves to upstream review

The principal unresolved dependency is the validity of Liu's Theorem 6.7,
including the uniform scalar-expansion decomposition and stitching in
Sections 5-6. This artifact deliberately does not certify those results.
Liu's normalization Theorem 7.4 and wreath Theorem 8.3 are not needed for
the Leavitt deduction above. The existing foundational algebra and imported
SOS/property-(T) results remain explicit trust inputs. The finite
central-height, native generation, trace-concentration, time-penalty, and
ultrafilter-to-sequence steps have been checked here independently of
their previous status labels.
