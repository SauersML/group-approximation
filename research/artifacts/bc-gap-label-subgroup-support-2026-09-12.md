# Gap labels on the Kun--Thom actors: the congruence limit and the subgroup-support obstruction

Lane `bc-infinite-spectrum-limits`, 2026-09-12.

**Setting** (as in `research/artifacts/bc-kun-thom-trace-test-2026-09-12.md`):
- `G = EL_r(R) semidirect SL_d(Z)` with `R = F_q[x_1^(+-1), ..., x_d^(+-1)]` and `r, d >= 3`;
- `Lambda^G = Z[1/P]` (`kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p`);
- `tau(x) = sum_i x_ii(1)` is the unnormalized trace on `M_n(C*_r G)`.

The only surviving refutation shape is a gapped spectral projection
`chi = chi_((-inf,c))(lambda(a))` of a self-adjoint `a ∈ M_n(C[G])` with infinite spectrum
(`kun-thom-actor-algebraic-idempotents-pass-trace-test`).

## 1. The congruence limit (landed, 867c6795a)

`bc-kun-thom-gap-label-is-congruence-eigenvalue-limit`, route
`bc-kun-thom-gap-label-limit-proof`:

```text
tau(chi) = lim_(p' -> inf) #{eigenvalues of pi_(p')(a) below c} / [G : N_(p')].
```

- **Proof.** Moments of `pi_(p')(a)` equal moments of `lambda(a)` once `p'` avoids `(supp a)^m`
  (Lemma C). All measures sit on the fixed interval `[-||a||_1, ||a||_1]`. So weak convergence
  holds, and Portmanteau applies at the continuity point `c`.
- **Normalization correction.** In the trace-test artifact, Section 4 divides by `n[G:N]`
  against the unnormalized `tau`. That quotient is `tau/n`, not `tau`.
- **No arithmetic follows.** The denominators `[G:N_(p')]` can be kept prime to any single
  `l` outside `P` (Lemma B). A limit of rationals whose denominators are prime to `l` can
  still be any real number.

## 2. Imports, quoted from the source text

Lück--Reich, *The Baum--Connes and the Farrell--Jones Conjectures in K- and L-Theory*,
arXiv:math/0402405. The PDF was downloaded and extracted with `pdftotext` on MSI
(`/scratch.global/sauer354/bcgl-lit/lr.txt`).

**(I1)** Section 3.3.1, verbatim apart from typesetting:

> Denote by ΛG the subring of Q which is obtained from Z by inverting all orders |H| of finite
> subgroups H of G [...]
> Conjecture 3.21 (Modified Trace Conjecture for a group G). Let G be a group. Then the image
> of the homomorphism induced by the standard trace trC*r(G) : K0(C*r(G)) → R is contained in ΛG.
> The following result is proved in [203, Theorem 0.3].
> Theorem 3.22. Let G be a group. Then the image of the composition
> K0G(EFIN(G)) ⊗Z ΛG --(AFIN ⊗Z id)--> K0(C*r(G)) ⊗Z ΛG --(trC*r(G))--> R
> is ΛG. Here AFIN is the map appearing in the Baum-Connes Conjecture 2.3. In particular the
> Baum-Connes Conjecture 2.3 implies the Modified Trace Conjecture.

Reference [203] is Lück, Invent. Math. 149 (2002).

**(I2)** Section 5.1.1, verbatim apart from typesetting:

> Theorem 5.1. (Baum-Connes Conjecture with Coefficients and a-T-menable Groups). The discrete
> group G satisfies the Baum-Connes Conjecture with Coefficients 4.3 and is K-amenable provided
> that G is a-T-menable.
> This theorem is proved in Higson-Kasparov [149, Theorem 1.1] [...]
> The class of a-T-menable groups is closed under taking subgroups, under extensions with finite
> quotients and under finite products. [...] Examples of a-T-menable groups are countable
> amenable groups, countable free groups, discrete subgroups of SO(n, 1) and SU(n, 1), Coxeter
> groups, countable groups acting properly on trees, products of trees, or simply connected
> CAT(0) cubical complexes. [...] Since SL(n, Z) for n ≥ 3 has property (T), it cannot be
> a-T-menable.

Section 5.1.1 also says that the Conjecture with Coefficients contains Conjecture 2.3 "as a
special case".

## 3. The subgroup-support obstruction

**Theorem.** Let `H <= G` be a subgroup whose assembly map `A_FIN` in degree 0 is surjective
onto `K_0(C*_r H)`. By (I2), every a-T-menable `H` qualifies. Let `a = a* ∈ M_n(C[H])`, and let
`c` lie in a gap of the spectrum of `lambda(a)`. Then `tau(chi_((-inf,c))(lambda(a)))` lies in
`Lambda^H`, which is contained in `Z[1/P]`.

*Proof.*
1. **`C*_r H` sits inside `C*_r G`.** Decompose `l^2(G)` as `⊕_(t ∈ H\G) l^2(Ht)`. Each summand
   is `lambda_G(H)`-invariant and unitarily equivalent to `lambda_H`. So the norm of `lambda_G(x)`
   equals the norm of `lambda_H(x)` for `x ∈ M_n(C[H])`. Hence the closure of `lambda_G(M_n(C[H]))`
   is a unital C*-subalgebra of `M_n(C*_r G)` isomorphic to `M_n(C*_r H)`.
2. **The spectral projection lives in the subalgebra.** By spectral permanence the spectrum of
   `lambda(a)` is the same in both algebras, so `c` lies in a gap of both. Take `f` continuous on
   `R`, equal to 1 on `spec ∩ (-inf, c)` and 0 on `spec ∩ (c, inf)`. Then `chi = f(lambda(a))`
   is a projection in `M_n(C*_r H)`.
3. **The traces agree.** On `M_n(C*_r H)` both `tau_G` and `tau_H` are
   `x ↦ sum_i <x_ii delta_e, delta_e>`.
4. **Lück's theorem applies.** `[chi] ∈ K_0(C*_r H) = A_FIN(K_0^H(E_FIN H))`. For
   `y ∈ K_0^H(E_FIN H)`, `tr(A_FIN(y)) = tr((A_FIN ⊗ id)(y ⊗ 1))`, which lies in `Lambda^H` by (I1).
   So `tau(chi) ∈ Lambda^H`.
5. **The ring shrinks.** Finite subgroups of `H` are finite subgroups of `G`, so `Lambda^H` is
   contained in `Lambda^G = Z[1/P]`. QED

**a-T-menable subgroups of the actor, all ruled out as supports.**
- **Amenable: unipotent and Borel.**
  - The upper unitriangular group `U_r(R)` lies in `EL_r(R)` and is nilpotent.
  - The diagonal matrices of determinant one with unit entries lie in `EL_r(R)` by the Whitehead
    lemma: `diag(u, u^(-1))` is a product of elementary matrices for every unit `u`.
  - Together they generate the solvable Borel subgroup.
- **Amenable: lamplighters.** Put `t = diag(x_1, x_1^(-1), 1, ..., 1)`. Conjugation by `t` sends
  `e_12(f)` to `e_12(x_1^2 f)`. So `<e_12(F_q[x_1^(+-2)]), t>` is `F_q wr Z`, and larger tori
  give `F_q wr Z^k`.
- **Products of trees.** `F_q[x_1, x_1^(-1)]` is the ring of `S`-integers of `F_q(x_1)` for
  `S = {0, inf}`. It is discrete in `F_q((x_1)) × F_q((x_1^(-1)))`: a nonzero Laurent polynomial
  cannot have lowest exponent `>= N > 0` and highest exponent `<= -N`.
  - So `SL_2(F_q[x_1^(+-1)])` is discrete in `SL_2(F_q((x_1))) × SL_2(F_q((x_1^(-1))))`.
  - It acts on the product of the two Bruhat--Tits trees with finite vertex stabilizers
    (discrete intersected with compact open is finite), so the action is proper.
  - `E_2(F_q[x_1^(+-1)])`, sitting as a corner block of `EL_r(R)`, is a subgroup, so it is
    a-T-menable by (I2).
- **Trees.** `SL_2(Z)` is a corner block of `SL_d(Z)`. It acts properly on the Bass--Serre tree
  of `Z/4 *_(Z/2) Z/6`.
- **Products.** Commuting corner blocks of the types above, when `r` or `d` is large enough, by
  closure under finite products (I2).

So any refuting `a` must have support generating a subgroup that lies in no subgroup with
surjective assembly. In particular it lies in no a-T-menable subgroup. Example supports that
remain possible contain `SL_3(Z)`, which cannot be a-T-menable by (I2), or `E_3(F_q[x_1^(+-1)])`.
The explicit operators that can actually be computed (lamplighter Markov operators, Borel-supported
elements, tree-group Laplacians) are exactly the dead ones.

**Consistency with Atiyah-type irrationality (literature context, not imported).** Lamplighter
operators with von Neumann kernel dimensions outside `Lambda` exist, for example Grabowski
(Groups Geom. Dyn. 2016). They sit in amenable subgroups, so by the Theorem their kernel
projections are NOT in `C*_r`: 0 is not isolated in their spectrum. The C*-trace test only sees
gapped atoms, which is why Atiyah counterexamples give nothing here.

## 4. Congruence numerics are infeasible

Take the smallest actor `(q, r, d) = (2, 3, 3)` and the smallest congruence prime `p' = 3`.
- `F_2[(Z/3)^3] ≅ F_2 × F_4^13`, since `ord_3(2) = 2` and the 26 nontrivial characters fall into
  13 Frobenius orbits.
- So `[G : N_3] = |SL_3(F_2)| · |SL_3(F_4)|^13 · |SL_3(F_3)| = 168 · 60480^13 · 5616`.
- `log_10` of this is `2.225 + 13 · 4.782 + 3.749`, about `68.1`.
- The Hermitian matrix `pi_3(a)` has size `n · 10^68`, and larger `p'` only make it larger. The
  avoiding tower cannot be diagonalized on any machine.
- Representation-theoretic splitting still leaves products of 13 `SL_3(F_4)` factors, because
  the generators map diagonally across all factors.

No MSI job was launched. Small non-avoiding quotients do not converge to `mu_a`, so their
spectra would be misleading as guidance.

## 5. What survives

- **The object.** A gapped spectral projection of `a = a* ∈ M_n(C[G])` with infinite spectrum,
  whose support generates a subgroup with no known surjective assembly. For `a` integral, the
  spectrum has capacity at least 1.
- **Its trace.** The congruence limit of Section 1.
- **No mechanism yet.** Nothing forces this limit into `Z[1/P]`: the quotients are non-tempered,
  their gap mass tends to 0 but their operator norm does not, and Lemma B only says the
  denominators avoid `l`. Nothing produces a limit outside `Z[1/P]` either: the only
  isolated-atom mechanisms in the graph (finite spectrum, subgroup averages) are algebraic
  idempotents, and the a-T-menable ones are ruled out above.
