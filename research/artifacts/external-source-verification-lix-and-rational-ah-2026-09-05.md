# Primary-source problem statements and an independent re-verification

Date: 5 September 2026. This record was produced in a separate session by
a different model instance from the lanes that wrote the proofs under
review. It is therefore independent of those lanes, but it is **not**
external peer review by a human expert, and not formal verification.
Nothing below upgrades any graph status on its own.

Two things are recorded. First, the verbatim primary statements of the
STW problems this repository targets, which until now appeared in the
graph only as paraphrase. Second, a step-level re-check of the two
counterexample manuscripts, with an explicit list of what was and was
not checked.

## 1. Verbatim STW problem statements

Source: C. Schafhauser, A. Tikuisis, S. White, *Nuclear C\*-algebras: 99
problems*, [arXiv:2506.10902](https://arxiv.org/abs/2506.10902),
submitted 12 June 2025, revised 8 May 2026, for a special issue of the
Münster Journal of Mathematics dedicated to Kirchberg's memory. Text
extracted from the arXiv PDF on 5 September 2026.

```text
Problem LVIII.  Is every pure C*-algebra K1-bijective (or even K-stable)?

Problem LIX.    Are all unital simple C*-algebras K1-injective?

Problem LXI.    Are all properly infinite unital C*-algebras K1-injective?

Problem LXXVI.  Is every pure C*-algebra Cuntz semigroup regular?
```

These match the targets recorded on the corresponding root nodes. No
wrong-problem transcription was found in this cluster.

## 2. What STW themselves say around Problem LIX

The surrounding discussion is worth pinning, because it fixes exactly
which regularity a counterexample has to avoid.

- STW record the problem as open: after noting that Villadsen's
  constructions already defeat the surjectivity analogue, they write
  that "to the best of our knowledge, the corresponding question for
  K1-injectivity is open."
- They cite Villadsen for simple separable unital nuclear examples where
  `pi_k(U_n(A)) -> pi_k(U_{n+1}(A))` fails surjectivity below a chosen
  index. So failure of K1-*surjectivity* in the simple nuclear class is
  prior art; K1-*injectivity* is the open direction.
- They cite Rieffel Theorem 2.10 for stable rank one implying
  K1-injectivity. **Any counterexample must therefore not have stable
  rank one.** The tower's separately computed stable rank of exactly two
  is consistent with this, and its non-K1-injectivity independently
  excludes stable rank one. This is a genuine constraint the
  construction had to satisfy and does.
- They cite Lin for K1-injectivity at real rank zero, so a counterexample
  must also avoid real rank zero.

## 3. Re-check of the LIX counterexample manuscript

Reviewed: [the LIX manuscript](stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md).
Each step below was recomputed rather than read along with.

- **Lemma 3 (mapping-torus parity).** The Künneth kernel is correct:
  `K^1(Y)=0` kills the mixed terms, leaving
  `K^1(S^1) tensor K^1(S^5) tensor K^0(Y)`. Since `z^2=0`, the
  exponential collapses and `c_q(delta)=(-1)^{q-1}(q-1)! ch_q(delta)`
  holds exactly, not just modulo decomposables. The coefficient of
  `z prod h_j^{b_j}` is `(|b|+2)(|b|+1)` times a multinomial, even as a
  product of consecutive integers. Degrees check:
  `dim(S^1 x M)=1+5+2m=2r`, and `c_r(V)=0` because `V` is pulled back
  from the `2m`-dimensional `Y` with `2m<2r`.
- **Lemma 2 (cancellation failure).** The derivative at the zero
  recomputes to `(xi,a) -> (1/2)xi - 2a e_3`, a real isomorphism
  `T_{-e_3}S^5 (+) R -> C^3` of dimension `5+1=6`, so the zero is
  isolated and transverse. Signed count `±<c_m(H),[Y]> = ±1`, odd,
  contradicting Lemma 3.
- **The unit evaluation.** `c(H)=prod_j (1+h_j)^{d_j}` with
  `h_j^{d_j+1}=0`, so the only surviving top-degree term is
  `prod_j h_j^{d_j}` with coefficient exactly one. This requires the
  multiplicity of each line to equal the dimension of its projective
  factor. The tower supplies that automatically: the new block is
  `E_i(x_i) tensor L_{i+1}` of multiplicity `rank E_i = r_i` over
  `CP^{r_i}`. The choice of base is forced by the rank, not tuned.
- **The obstruction is not accidental.** All parity sits in `(q-1)!` at
  the minimal `q=3`, i.e. in `2!`. Over `S^3` the minimum would be `q=2`
  with `1!=1` and no obstruction at all. So `S^5`, rank two, and
  `pi_4(U(2))=Z/2` are forced together, and the `S^{2n+1}` generalization
  giving `(q-1)!=n!` against `pi_{2n}(U(n))=Z/n!` is the same mechanism
  rather than a separate construction.
- **Homotopy inputs**, confirmed independently of the cited page:
  `pi_4(U(2))=pi_4(SU(2))=pi_4(S^3)=Z/2`, and `pi_4(U(3))=0` by the
  unitary stable range. So the boundary map is onto, `u^2` is
  null-homotopic, and `u (+) 1` contracts in `U(3)`, giving both the
  order-two statement and stable triviality.
- **Lemma 7 (finite-stage detection).** All estimates check:
  `||b*b-1|| <= 2eps+eps^2 < 1` gives invertibility, the polar unitary
  satisfies `||q-b|| <= eps` via `spec|b| in [1-eps,1+eps]`, and
  `||q_v - q_{v-1}|| < 1/4 + 4eps < 2` puts `-1` outside the spectrum of
  `q_{v-1}^* q_v`, so the principal logarithm exists in the stage.

No error was found in this manuscript.

## 4. Re-check of the rational-AH manuscript

Reviewed: [the torsion Euler tower](stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md).

- **(2.5)** `s_{4k}(beta)=s_k(beta)^4` mod two follows from Frobenius,
  valid because mod-two cohomology is graded-commutative and hence
  commutative in characteristic two.
- **(2.6)** `c(E)=c(F)^4` forces `c_k(E)=0` mod two unless `4|k`, with
  `c_{4j}(E)=c_j(F)^4`. Both sides then reduce to
  `sum_j c_j(F)^4 s_{4(m-j)}(beta)`, so the identity holds.
- **The vanishing.** `P` lies in `H^{2m}` with `m=2^i>=1`, so it has no
  constant term. A monomial meeting the `(RP^2)^4` factor dies because
  `a_i^3=0` forces `a_i^{4alpha}=0`. A pure monomial in the remaining
  factors has `P^4` in degree `8m=2r_i`, inside a subproduct of
  dimension only `2r_i-8`. Either way `P^4=0`. Checked directly at
  stage zero: `Lambda_{E_0}(beta)=s_4(beta)=s_1(beta)^4=0`, so the
  kernel is the full `Z/2` from the first stage.
- **Propagation.** `L` is the complexification of the real tautological
  line, so `c_1(L)` is two-torsion with `rho_2(c_1(L))=w_1^2` nonzero;
  it therefore generates `H^2(RP^{2n};Z)=Z/2` and `c_1(L)^{r_i}`
  generates the top class. The external product carries generator to
  generator, so the kernels do map isomorphically.
- **Monotraciality.** `phi_i` doubles the rank, so the trace pullback is
  `mu -> (1/2)(pr)_* mu + (1/2) delta_{x_i}`, contracting by one half per
  stage. Unique trace, faithful by simplicity, hence stably finite.
- **Rational stability.** Each `X_i` is rationally acyclic, and with
  `BU(N)_Q` a product of `K(Q,2j)` the mapping-space homotopy reduces to
  `H^0`, matching `pi_m U(N) tensor Q` degreewise. The bottom arrow
  `U((l-1)r_i) -> U(l r_i)` is an isomorphism on `pi_m` once
  `m < 2r_i`, which holds at late stages for fixed `m` and `l`.

No error was found in this manuscript.

## 5. A correction to the Vaidyanathan framing

The graph describes the AH question as a published question that
Vaidyanathan "asks" or "raises". The primary text is weaker. In
Section 20 of Sarkar's compendium, printed page 48, the relevant
sentence is:

```text
In [401], we showed that AT-algebras exhibit the same phenomenon,
raising an interesting question about AH-algebras in general.
```

That is an informal remark attached to the AT theorem, not a separately
posed or numbered problem. The same paragraph also states:

```text
we showed in [400] that the notions of rational K-stability and
K-stability are indeed distinct in general
```

So the unrestricted separation of rational from integral K-stability is
**already published prior art**. The contribution of the torsion Euler
tower is therefore precisely that the separation persists inside the AH
class, and moreover for a simple unital monotracial algebra. It is not
a first separation of the two notions. The existing
[literature boundary artifact](rational-k-stability-ah-literature-boundary-2026-09-05.md)
records the prior-art point correctly; only the "raises a question"
attribution needed tightening.

This distinction matters for how the two results should be described.
STW Problem LIX is a numbered problem in a published list, stated open
by its authors. The AH question is an informal remark whose unrestricted
form is already settled.

## 6. What was not checked

The following were taken on citation and would be the first places a
referee should push:

- That the rank-two bundle clutched by `u` is `F`, i.e. the standard
  identification of the fibration boundary map with clutching.
- The gauge-fibration identifications `pi_1 G(E (+) 1) = K^0(X)` and
  `pi_0 G(E (+) 1) = K^1(X)`, deferred to the factorial calculation.
  The connectivity arithmetic supporting them was checked: the section
  space of `E (+) 1` is `0`-connected with `pi_1 = H^{2r}(X;Z)`, and one
  further line gives a `2`-connected section space, so `pi_0` and `pi_1`
  are already stable at `E (+) 1`.
- Klein--Schochet--Smith Theorem 5.6 and Proposition 5.1, used for the
  rational evaluation isomorphism. Both sides were confirmed to compute
  to the same groups; their proof was not read.
- The relative Euler product with torsion coefficients, and its
  Thom-class argument.
- Nistor Theorem 7(a) and Rieffel Theorem 2.10 were read as page images
  in an earlier session rather than re-extracted here.

## 7. Status

Both manuscripts survived a step-level adversarial re-reading by an
independent instance. That raises confidence; it does not establish
correctness. The remaining failure mode is a cited standard step not
saying quite what it is used for, which this kind of review cannot
exclude. Neither result should be described as verified until a human
expert in non-stable K-theory has read them.
