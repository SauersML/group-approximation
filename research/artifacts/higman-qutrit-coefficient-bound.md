# A three-dimensional Higman tuple rules out coefficient sixteen

2026-09-07. This is an exact counterexample to a proposed inequality,
not a nonhyperlinear group or a separating microstate sequence. The
previous coefficient-two search exhausted only a finite prefix in
dimensions at most two. The present result refutes coefficient two,
and even coefficient sixteen, in dimension three.

For the fixed Higman relators

\[
r_j=g_jg_{j+1}g_j^{-1}g_{j+1}^{-2},\qquad j\in\mathbb Z/4\mathbb Z,
\]

put \(e_v(U)=\|v(U)-I\|_{2,3}^2\), with normalized HS norm.
The explicit tuple below satisfies

\[
e_{g_0}(U)>\frac{16}{7},\qquad
0<\sum_j e_{r_j}(U)<\frac17.                         \tag{1}
\]

Consequently any valid all-dimensions coefficient in
\(e_{g_0}\le C\sum_j e_{r_j}\) must be strictly larger than 16.

## Explicit matrices

For an integer row \(n=(n_0,\ldots,n_8)\), define

\[
K(n)=\frac1{64}
\begin{pmatrix}
 i n_0&n_3+i n_4&n_5+i n_6\\
 -n_3+i n_4&i n_1&n_7+i n_8\\
 -n_5+i n_6&-n_7+i n_8&i n_2
\end{pmatrix},\qquad
U(n)=(I-K(n))(I+K(n))^{-1}.
\]

Use these four rows, in generator order:

| Generator | Integer row n |
| --- | --- |
| a | (-46, -56, -20, 122, -1, -67, 28, -1, 90) |
| b | (-38, -38, 76, 42, 42, 24, -47, -12, -37) |
| c | (-82, 33, -86, 15, 48, -115, -87, -7, 46) |
| d | (-26, -33, 59, 0, 67, 45, -30, 32, 34) |

These formulas alone specify the matrices; no numerical input is needed.
Since \(K^*=-K\), the identity
\(\|(I+K)v\|^2=\|v\|^2+\|Kv\|^2\) proves invertibility of \(I+K\).
The commuting factors \(I-K\) and \(I+K\) then give \(U^*U=I\).
Every entry belongs to \(\mathbb Q(i)\).

## Exact certificate of the inequalities

The full rational entries and exact energies are committed in
`higman-qutrit-coefficient-witness.json`.
`experiments/higman_qutrit_witness.py` reconstructs them from the 36 integers
above, using exact rational elimination, and checks both inequalities (1)
by rational comparison. Its output is byte-for-byte reproducible.

The separate existing verifier `experiments/hs_word_certificate.py` reads
the explicit matrices without using the Cayley parameters. It checks
unitarity, evaluates every signed word, and sums squared entry differences
divided by three. It ignores the stored energies. Its positive strict
margin directly certifies \(e_{g_0}-16\sum_j e_{r_j}>0\).
The regression additionally verifies every word energy using
\(2-2\operatorname{Re}\operatorname{tr}_3(v(U))\).

```sh
python3 experiments/higman_qutrit_witness.py
python3 experiments/hs_word_certificate.py verify research/artifacts/higman-qutrit-coefficient-witness.json
python3 -m unittest discover -s experiments -p test_hs_word_certificate.py -v
```

For orientation only, the marked energy is approximately 2.29819 and the
relator-energy sum is approximately 0.141942, giving ratio approximately
16.1910. The proof uses the rational certificate and (1), not these rounded
numbers. This is one explicitly evaluated tuple, so no exhaustion or
completeness claim about a search is involved.

## Scope and discovery

An exploratory Cayley-coordinate optimization in dimension three found
the seed. Rounding its parameters to multiples of 1/64 produced the
integer data above. Optimization is outside the proof's trust boundary;
replaying the certificate requires only Python's standard library.

Both the earlier two-dimensional lower bound and this three-dimensional
one remain useful: testing a coefficient in dimension two cannot justify
it in larger dimensions. A larger valid coefficient could still exist.
No conclusion about Higman's hyperlinearity follows from rejecting sixteen.

Identity padding multiplies the marked and relator energies by the same
factor \(3/(3+m)\). It preserves their ratio but makes the mark tend to zero,
so it cannot turn this witness into a separating hyperlinear microstate.

Repository and external searches on 2026-09-07 checked the Higman/BS-cycle
and word-energy literature before recording this calculation. The Cayley
method and the underlying question are prior art; no global novelty claim
is made. For the larger existence question,
[Taller--Vidick, version 2](https://arxiv.org/html/2507.22444v2) still requires
perfect completeness for its nonhyperlinear implication, and
[Dogon--Vigdorovich, version 2](https://arxiv.org/html/2506.20843v2) retains
the stability premise of Question 1.4 in Corollary 1.5. This finite
calculation removes neither premise and supplies no Lean certification.
