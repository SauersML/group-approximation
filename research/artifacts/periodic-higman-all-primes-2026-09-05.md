# Every prime is a periodic-Higman period

Date: 2026-09-05. This strengthens the 2026-09-04 cofinite-spectrum result
and resolves its remaining missing-prime question negatively.

## Theorem and consequence

With `[a,b]=a^{-1}b^{-1}ab`, let

\[
\Sigma=\{\operatorname{ord}(\alpha)>1:\ H=\langle h_0,h_1,h_2,h_3\rangle
\text{ finite},\ \alpha\in\operatorname{Aut}(H),\
\alpha(h_j)=[h_j,h_{j-1}]\quad(j\in\mathbb Z/4)\}.
\]

**Theorem.** Every prime belongs to `Sigma`. Consequently, for every
integer `m>=2`, the group

\[
G_m=\langle x_0,x_1,x_2,x_3,t\mid
t x_jt^{-1}=[x_j,x_{j-1}],\ t^m=1\rangle
\]

has a finite quotient in which every `x_j` is nonidentity.

Thus `periodic-higman-large-prime-period-gap` is false, for any filling
threshold. The missing-period premise in
`periodic-higman-period-spectrum-criterion` fails for every `m>=2`.
This rules out that construction of a non-residually-finite hyperbolic
group. It does **not** prove residual finiteness of any `G_m`, since
detecting the generators does not detect every nonidentity word.
Gromov's residual-finiteness question remains open.

The proof below combines an imported large-period theorem with exact
finite certificates and rigorous interval bounds. It is a computer-assisted
proof at the level of rational arithmetic, not a Lean formalization.

## 1. The algebraic certificate and the range already known

Use the polynomial

\[
P(L)=L^5-(4+3i)L^4+2L^3+2iL^2-(3+4i)L+i,
\]

and the explicit matrices over `Z[i,1/2,L]/(P)` in
[the cofinite-spectrum proof](periodic-higman-cofinite-spectrum-2026-09-04.md).
Those matrices satisfy the four required commutator equations. Over any
finite field of odd characteristic, a root `lambda` of this polynomial of
exact multiplicative order `n>1` therefore supplies a certificate for
`n in Sigma`. The nonzero upper-right entry of `A_0` forces the conjugation
automorphism to have exact order `n`.

The same proof, using Voutier's published primitive-divisor theorem, already
establishes membership for every integer greater than

\[
B=4000\cdot40^{12}=67108864000000000000000.              \tag{1}
\]

It remains to deal with primes at most `B`. All computational checks below
are reproduced by

```sh
python experiments/periodic_higman_algebraic_certificate.py
python experiments/periodic_higman_all_primes_certificate.py
```

Both scripts use only the Python standard library and exact arithmetic.

## 2. The roots of the certificate polynomial

The exact Cayley identity is

\[
(1-iz)^5 P\left(\frac{1+iz}{1-iz}\right)
  =(4+4i)Q(z),\qquad
Q(z)=z^5+7z^4-2z^3+2z^2+z-1.                          \tag{2}
\]

A rational Sturm calculation gives variation counts `4` at negative
infinity and `1` at positive infinity. The final Sturm remainder is a
nonzero constant, so `Q` is square-free and has exactly three real roots.
Sign changes isolate these roots, one each, in

\[
(-8,-7),\quad(-1,0),\quad(0,1).
\]

Denote them by `z_1,z_2,z_3`, and set

\[
u_j=\frac{1+iz_j}{1-iz_j},\qquad
\theta_j=\frac{\arctan z_j}{\pi}.
\]

The three roots `u_j` of `P` are on the unit circle, with
`u_j=exp(2 pi i theta_j)`. There are no additional roots on the unit circle:
`P(-1)!=0`, and the Cayley transform identifies the other unit-circle
points with real `z`.

The identity

\[
P(L)=iL^5\overline P(1/L)                              \tag{3}
\]

shows that the remaining roots are a pair `v,1/bar(v)` with
`|v|=R>1`. Here the bar on `P` conjugates its coefficients. In fact `R>4`.
To see this quantitatively, the same rational root intervals used below
give

\[
\operatorname{Re}\left(4+3i-\sum_{j=1}^3u_j\right)>7/2,
\qquad
\operatorname{Im}\left(4+3i-\sum_{j=1}^3u_j\right)>3.
\]

The expression in parentheses is `v+1/bar(v)`, of modulus `R+1/R`.
Since `(7/2)^2+3^2>(17/4)^2`, it follows that `R+1/R>17/4` and hence
`R>4`.

## 3. A certified separation estimate for all denominators up to B

The verifier proves simultaneously for `j=1,2,3` that

\[
\|n\theta_j\|_{\mathbb R/\mathbb Z}>10^{-30}
       \quad\text{for every integer }1\le n\le B.     \tag{4}
\]

This is a finite certificate for the entire interval of denominators,
not an enumeration of that interval. The details are as follows.

First, exact rational bisection encloses each `z_j` in an interval of width
at most `2^-420`. Subsequent interval endpoints are integers scaled by
`S=2^400`; every arithmetic operation rounds outward. Arctangents are
reduced to arguments of modulus at most `1/2`, then enclosed with 250 terms
of the alternating series. The tail has modulus less than `2^-501`, so
expanding the result by one interval unit is sufficient. The enclosure of
`pi` comes from Machin's identity
`pi=16 atan(1/5)-4 atan(1/239)`. This identity follows directly from the
tangent addition formula and the location of the angles in the first
quadrant.

For each `alpha_j=|theta_j|`, let `[l_j/S,h_j/S]` be the resulting
enclosure. The following coprime rational witnesses are obtained:

| Root interval | Numerator `a_j` | Denominator `q_j` |
| --- | ---: | ---: |
| `(-8,-7)` | 51341047570259481454539 | 112414088011080519127826 |
| `(-1,0)` | 10922152720928369107409 | 67923766550935111593785 |
| `(0,1)` | 19324786994105978347755 | 142188852620220811686829 |

All `q_j>B`. Define the integer

\[
E_j=\max\{|q_j l_j-a_jS|,\ |q_jh_j-a_jS|\}.
\]

The exact checked inequality is

\[
(S-BE_j)10^{30}>q_jS.                                \tag{5}
\]

For any integer `b` and `1<=n<=B<q_j`, coprimality gives
`|n a_j/q_j-b|>=1/q_j`. Hence

\[
|n\alpha_j-b|
\ge\frac1{q_j}-n\left|\alpha_j-\frac{a_j}{q_j}\right|
\ge\frac{S-BE_j}{q_jS}>10^{-30}.
\]

This proves (4). Continued fractions are used only to find the witnesses;
their validity rests on the displayed rational inequalities and does not
require a best-approximation theorem.

## 4. Nonunit cyclotomic resultants for every odd prime

Let

\[
\begin{aligned}
N(L)=P(L)\overline P(L)
={}&L^{10}-8L^9+29L^8-16L^7-14L^6+48L^5\\
&-14L^4-16L^3+29L^2-8L+1.
\end{aligned}
\]

The polynomial product, (2), and (3) are also checked exactly by the
verifier. In particular, `N(1)=32`.

For a prime `ell`, write `Phi_ell(L)=1+L+...+L^(ell-1)` and

\[
R_\ell=\operatorname{Res}(P,\Phi_\ell)\in\mathbb Z[i].
\]

For `200<=ell<=B`, the root product and (4) yield

\[
\begin{aligned}
|R_\ell|^2
 &=\frac{\prod_{P(\rho)=0}|\rho^\ell-1|^2}{32}\\
 &\ge\frac{(R^\ell-1)^2(1-R^{-\ell})^2
       (4\cdot10^{-30})^6}{32}\\
 &>\frac{8\cdot4^{2\ell}}{10^{180}}>1.                \tag{6}
\end{aligned}
\]

For the three unit-circle factors we used
`|exp(2 pi i x)-1|=2 sin(pi ||x||)>=4||x||`.
For the other two roots, `R>4` gives
`R^ell-1>4^ell/2` and `1-R^-ell>1/2`. The final bound in (6) is already
greater than one at `ell=200`, by an exact integer comparison, and then
increases.

For all 45 odd primes below 200, the verifier computes

\[
|R_\ell|^2=\operatorname{Res}(N,1+L+\cdots+L^{\ell-1})>1. \tag{7}
\]

These are exact integer determinants: multiplication by the indicated
polynomial on `Z[L]/(N)` is represented in the basis `1,L,...,L^9` and
its determinant is calculated by fraction-free elimination. Every division
is checked to be exact. For example the outputs for `ell=3,5` are
`20449` and `2070721`. Thus (6) and (7) establish that `R_ell` is a
nonzero nonunit for every odd prime at most `B`.

Choose a Gaussian prime ideal dividing `R_ell`. In its residue field,
the polynomials `P` and `Phi_ell` have a common root in a finite extension.
The characteristic cannot be two: there `P=(L+1)^5`, while
`Phi_ell(1)=1`. Nor can it be `ell`: there
`Phi_ell=(L-1)^(ell-1)`, while `P(1)=-4-4i` has norm 32 and is nonzero
at any odd-characteristic prime. Therefore the common root has exact
multiplicative order `ell`, and the algebraic matrices from Section 1
give `ell in Sigma`.

Together with the cofinite-spectrum theorem for `ell>B`, this handles
every odd prime.

## 5. The prime two

In `PSL_2(5)`, use determinant-one matrices modulo `{I,-I}` and set

\[
s=\begin{pmatrix}0&1\\4&0\end{pmatrix},\quad
h_0=\begin{pmatrix}1&0\\2&1\end{pmatrix},\quad
h_1=\begin{pmatrix}1&1\\2&3\end{pmatrix},\quad
h_2=\begin{pmatrix}1&2\\0&1\end{pmatrix},\quad
h_3=\begin{pmatrix}2&3\\4&4\end{pmatrix}.
\]

Exact multiplication modulo five, modulo scalar signs, gives
`s h_j s^-1=[h_j,h_(j-1)]`. Also `s^2=-I` and conjugation by `s` moves
`h_0`, so its restriction has exact order two. The displayed generators
generate all 60 projective matrices in `PSL_2(5)`, as the verifier checks.
This proves `2 in Sigma` and completes the prime-period theorem.

## 6. Why every nontrivial filling has a finite quotient detecting the base

Let `m>=2` and choose a prime divisor `ell` of `m`. Take its finite
certificate `(H,alpha,h_0,...,h_3)`. No `h_j` can be the identity:
if one were, the recurrence and injectivity of `alpha` would make the
next one the identity, and then all four would be; that contradicts
`ord(alpha)=ell>1`.

Map `G_m` into the finite semidirect product `H rtimes <alpha>` by
`x_j -> h_j` and `t -> alpha`. The recurrence gives the conjugation
relations and `ell|m` gives `t^m=1`. This is the required quotient,
preserving all four marks. QED.

## Audit boundary

The finite calculations certify explicit polynomial identities, root
counts and enclosures, rational separation bounds, integer resultants,
and a small projective-group certificate. The infinite-range argument is
the proof above plus the previously cited primitive-divisor theorem.
Neither a graph status nor a successful script proves Gromov's question.
The resolved claim is the repository's missing-prime premise, which is
false; the major literature problem remains unresolved.
