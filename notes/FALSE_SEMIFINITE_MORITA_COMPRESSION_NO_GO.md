# Semifinite Morita compression trivializes the quasi-regular wall

## 1. The tempting construction

Let \(\Gamma<G\), put \(X=G/\Gamma\), and let
\(\rho:G\to U(\ell^2X)\) be the quasi-regular representation.  The rank-one
projection \(e_o\) at \(o=\Gamma\) is fixed by \(\Gamma\) and moved by every
\(h\notin\Gamma\).  Since the ordinary trace of \(e_o\) is finite, it is
tempting to put this wall in a semifinite factor, cross by \(G\), and pass to
a finite corner.

That operation does produce a finite corner, but the canonical Morita
cocycle cancels the whole quasi-regular coordinate.  What remains is only an
internal representation that had to contain the wall already.

## 2. Exact cancellation theorem

Let \((A,\tau)\) be a finite tracial von Neumann algebra and let
\(\sigma:G\to U(A)\) be a representation.  Put

\[
N=B(\ell^2X)\,\bar\otimes\,A,
\qquad
U_g=\rho(g)\otimes\sigma(g),
\qquad
\alpha_g=\operatorname{Ad}(U_g).
\]

The algebra \(N\) has its canonical semifinite trace.  Let

\[
p=e_o\otimes1
\]

and form the semifinite crossed product \(\mathcal N=N\rtimes_\alpha G\),
with canonical implementing unitaries \(u_g\).

Define

\[
w_g=\rho(g)e_o\otimes1.
\]

Then

\[
w_g^*w_g=p,
\qquad
w_gw_g^*=\alpha_g(p),
\qquad
w_{gh}=\alpha_g(w_h)w_g.
\]

Consequently

\[
V_g=w_g^*u_gp\in U(p\mathcal Np)
\]

is a representation of \(G\).

**Theorem.** Under the standard isomorphism for an inner crossed product

\[
\Theta:N\rtimes_\alpha G\longrightarrow N\,\bar\otimes\,L(G),
\qquad
\Theta(u_g)=U_g\otimes\lambda_g,
\]

the compressed representation is

\[
\boxed{
\Theta(V_g)=p\sigma(g)p\otimes\lambda_g.
}
\]

In particular, its conjugation action on
\(pNp\cong A\) is exactly \(\operatorname{Ad}\sigma(g)\).  The coset action
\(G\curvearrowright G/\Gamma\) has disappeared.

### Proof

The partial-isometry and cocycle identities follow directly from
\(\rho(gh)=\rho(g)\rho(h)\) and from the fact that \(e_o\) is rank one.
They imply

\[
V_gV_h
=w_g^*\alpha_g(w_h^*)u_{gh}p
=w_{gh}^*u_{gh}p
=V_{gh}.
\]

The inner crossed-product formula gives

\[
\Theta(V_g)
=(w_g^*U_gp)\otimes\lambda_g.
\]

Since \(w_g=\rho(g)e_o\otimes1\) while
\(U_gp=\rho(g)e_o\otimes\sigma(g)\), their product is
\(e_o\otimes\sigma(g)\).  This is the displayed formula. \(\square\)

## 3. Consequence for the relative wall

For \(a\in A\), regard \(e_o\otimes a\) as an element of the finite corner.
The theorem gives

\[
V_g(e_o\otimes a)V_g^*
=e_o\otimes\sigma(g)a\sigma(g)^*.
\]

Thus \(e_o\otimes a\) is fixed by the compressed \(\Gamma\)-action and
moved by \(h\) if and only if

\[
a\in\sigma(\Gamma)'\cap A,
\qquad
[a,\sigma(h)]\ne0.
\]

This is exactly the original finite relative-commutant endpoint, now inside
\(A\).  Taking \(a=1\), which is the only choice supplied by the root
projection itself, makes it fixed by all of \(G\).

Therefore stable amplification, an inner semifinite crossed product, and a
finite Morita corner do not convert the quasi-regular rank-one wall into a
finite tracial wall.  Any noncanonical relative cocycle which succeeds must
already encode the missing relative-commutant escape; it is not supplied by
Morita equivalence.

If \(A\) and \(L(G)\) are Connes embeddable, the resulting finite corner is
Connes embeddable as well.  The obstruction is not embeddability of the
corner—it is the exact cancellation above.
