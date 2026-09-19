---
rg: 2
id: stw22-diffuse-spectral-supercarrier-two-sphere-proof
kind: route
title: Select a spectral supercarrier and contract the localized pair
target: stw22-diffuse-stiefel-uniform-two-sphere-fillings
requires:
  - stw22-diffuse-stiefel-uniform-loop-fillings
artifacts:
  - research/artifacts/stw22-diffuse-two-sphere-supercarrier-audit-2026-08-30.md
---

All metrics below are the ambient `2`-metric. The proof bootstraps only
from the already established degree-one Stiefel modulus.

## 1. Fixed-trace projection Grassmannians are uniformly one-connected

For projections `h<=q` and a scalar `s` with

```text
tau(h)<=s<tau(q),
```

put

```text
P(h,q;s)={p:h<=p<=q, p^2=p, tau(p)=s}.
```

Translation by `h` identifies this value with

```text
{r<=q-h: tau(r)=s-tau(h)}.                             (SG1)
```

These values are equi-`LC^1` whenever the ambient corner trace is bounded
below. A sufficiently small loop of projections about `r_0` has,
pointwise, conjugating unitaries close to the corner identity by Takesaki,
Lemma XIV.2.1. The conjugator fibres are cosets of

```text
U(r_0Nr_0) x U((f-r_0)N(f-r_0)).
```

They have a common degree-zero modulus from principal-log paths. Gutev's
controlled Michael theorem, Theorem 5.3 with `n=0`, therefore selects a
continuous conjugating-unitary loop close to the identity. Regard it as a
loop in the unitary Stiefel space of `fNf`, fill it by
`stw22-diffuse-stiefel-uniform-loop-fillings`, and conjugate `r_0`.
This gives a common small-loop filling modulus for (SG1). An arbitrary loop
lifts by Farah--Vaccaro's one-dimensional comparison theorem and contracts
by Jekel's theorem, so every value is simply connected.

In the application below, `tau(h)<=s/2` and `s<tau(q)`. Hence
`tau(q-h)>=tau(q)-s/2>tau(q)/2`; normalized-corner scaling makes the
preceding moduli uniform over all values of the one multifunction.

## 2. The spectral-superprojection multifunction is lower semicontinuous

Let `x:S^2->Nq` be as in the claim, fix `kappa>0`, and put

```text
a_z=|x(z)|,       h_z=1_[kappa,infinity)(a_z),
s=2 delta^2/kappa^2.                                   (SG2)
```

If `delta=0`, then `x=0`; take `e_z=0` and stop. Henceforth assume
`delta>0`. Chebyshev gives `tau(h_z)<=delta^2/kappa^2=s/2`. If
`s>=tau(q)`, take `e_z=q`; in the later lifting argument the base carrier
then has trace `tau(q)`, not `s`. Assume `s<tau(q)` and consider

```text
Phi(z)=P(h_z,q;s).                                      (SG3)
```

The values are nonempty and closed. We verify lower semicontinuity,
including mass crossing the spectral cutoff.

Suppose `z_i->z_0` and `e_0 in Phi(z_0)`. Powers--Stoermer gives
`a_i->a_0` in `L^2`. For `0<theta<kappa`, put
`g_theta=1_[0,kappa-theta](a_0)`. The separated-spectra estimate in
Hilbert--Schmidt norm is

```text
||g_theta h_i||_2 <= theta^(-1)||a_i-a_0||_2.           (SG4)
```

Indeed, on Hilbert--Schmidt operators the commuting left and right
multiplications by `a_0` and `a_i` turn
`g_theta(a_i-a_0)h_i` into a Sylvester operator whose two spectra are
separated by `theta`.

Because the cutoff in (SG2) is inclusive and `h_0<=e_0`,

```text
||(1-e_0)(1-g_theta)||_2^2
 <=tau(1_(kappa-theta,kappa)(a_0)) -> 0                 (SG5)
```

as `theta` decreases to zero. Thus (SG4), followed by (SG5), gives

```text
||(1-e_0)h_i||_2 -> 0.                                 (SG6)
```

An atom at `kappa` is harmless: it belongs to `h_0`, hence already
lies under `e_0`.

Here is the promised close-superprojection construction. Put
`eta_i=||(1-e_0)h_i||_2` and polar-decompose
`e_0h_i=w_i|e_0h_i|`. Its kernel projection
`k_i=h_i meet (1-e_0)` satisfies

```text
tau(k_i)<=eta_i^2,
||h_i-|e_0h_i|||_2<=eta_i.                             (SG7)
```

Complete `w_i` on `k_i` into the unused part of `e_0`; this is
possible because `tau(h_i)<=s/2`. If `v_i` is the completed partial
isometry and `l_i=v_iv_i^*<=e_0`, then

```text
v_i^*v_i=h_i,       tau(l_i)=tau(h_i),
||v_i-h_i||_2<=5 eta_i,
||l_i-h_i||_2<=10 eta_i.                               (SG8)
```

For the first estimate, use
`||(supp|e_0h_i|)-|e_0h_i|||_2<=eta_i`,
`||e_0h_i-h_i||_2=eta_i`, and
`||k_i||_2<=eta_i`; the completion on `k_i` costs at most
`2||k_i||_2`. The second estimate is
`||v_iv_i^*-h_i||_2<=2||v_i-h_i||_2`.

Apply Takesaki's close-projection lemma **inside the finite corner
`qNq`**. Since `h_i,l_i<=q` have equal trace, their complements in `q`
have equal trace too; the corner lemma supplies `u_i in U(qNq)` with
`u_i->q` and `u_ih_iu_i^*=l_i`. Extend `u_i` by `1-q` to a unitary of
`N`. Therefore

```text
e_i=u_i^*e_0u_i
```

lies in `Phi(z_i)` and converges to `e_0`. This proves lower
semicontinuity even though `tau(h_z)` need not be continuous.

By Step 1, the values in (SG3) are simply connected and form an
equi-`LC^1` family in the complete operator-norm unit ball of
`L^2(N)`. Michael's `n=1` theorem selects a continuous
`e_z in Phi(z)`. Since `q-e_z<=q-h_z`, functional calculus gives

```text
||x(z)(q-e_z)||<=kappa,       tau(e_z)=s.               (SG9)
```

This proves (SC2).

## 3. Localize the frame sphere

Normalize the centre of a frame sphere by a fixed left unitary, so its
centre is `q`, and apply (SC2) to `x=v-q`. The controlled direct
rotation from
`stw22-matrix-stiefel-defect-localization-proof`, already used in the
degree-one diffuse proof, is dimension-free. It homotopes `v` within

```text
delta+10 kappa
```

of `q` to

```text
v'(z)=q-e_z+w_z,
w_z^*w_z=e_z,       w_zw_z^* orthogonal to q-e_z.       (SG10)
```

The formula uses bounded multiplication, inversion away from zero, and
functional calculus, so it is `2`-continuous for the selected carrier.

## 4. The localized pair has a fill

Fix a base pair `(e_*,w_*)` of the same trace. First consider

```text
A_z={a in U(qNq): a e_* a^*=e_z}.
```

This multifunction is lower semicontinuous by the close-projection lemma.
Each value is a coset of
`U(e_*Ne_*) x U((q-e_*)N(q-e_*))`. Every nonzero corner is again a
separable-predual II1 factor. Jekel makes the values one-connected, while
the established degree-one unitary Stiefel modulus makes the family
equi-`LC^1`. Michael's `n=1` theorem selects
`a:S^2->U(qNq)`.

Now `wtilde_z=a_z^*w_za_z` has initial projection `e_*` and range in
the fixed corner `1-q+e_*`. The analogous multifunction

```text
C_z={c in U((1-q+e_*)N(1-q+e_*)): c w_*=wtilde_z}
```

has the same lower-semicontinuity and one-connectivity properties, so
Michael selects `c_z`. Thus

```text
e_z=a_ze_*a_z^*,       w_z=a_zc_zw_*a_z^*.             (SG11)
```

Jekel-contract `a` and `c` to their corner identities and substitute
the contractions into (SG11). This fills (SG10). At every stage the
difference from `q` has right support of trace `tau(e_*)`, so the whole
filling has radius at most

```text
2 sqrt(tau(e_*)) <= 2 sqrt(2) delta/kappa.              (SG12)
```

This explicitly removes the possible lifting obstruction: the stabilizers
are strong unitary groups of diffuse corners and are one-connected. The
corresponding assertion is not made for matrix stabilizers.

Take `epsilon_0=min(epsilon,1)`,
`kappa=epsilon_0/40`, and
`delta=epsilon_0^2/1000000`. Then both
`delta+10kappa<epsilon` and the right side of (SG12) is less than
`epsilon`, proving (DS2).

Finally, for an arbitrary sphere `v:S^2->St_N(q)`, take `e_z=q` in
(SG10). The second lifting step selects a unitary sphere carrying one base
frame to `v`; its stabilizer is the unitary group of the complementary
II1 corner, or is trivial. Jekel contracts the lift. Thus every strong
Stiefel space is two-connected.

Primary inputs are I. Farah and A. Vaccaro, *Continuous Selection of
Unitaries in II1 Factors*, Theorem 1.1 and Claims 3.1--3.2; D. Jekel,
*The unitary group of a II1 factor is SOT-contractible*, Theorem A;
E. Michael, *Continuous Selections II*, Theorem 1.2; V. Gutev,
*Constructing selections stepwise over skeletons of nerves of covers*,
Theorem 5.3; and M. Takesaki, *Theory of Operator Algebras III*,
Lemmas XIV.2.1--2.
