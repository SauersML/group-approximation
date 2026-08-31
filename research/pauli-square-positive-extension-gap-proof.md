---
rg: 2
id: pauli-square-positive-extension-gap-proof
kind: route
title: Measure the translated-row gap on the Pauli square
target: finite-nuclear-quotient-does-not-complete-partial-toeplitz-data
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
---

Write (c=ab), so the Cayley graph of (G=C_2	imes C_2) with
difference set

[
Delta={1,a,b}
]

is a four-cycle.  Every subset (Sigmasubseteq G) satisfying
(Sigma^{-1}SigmasubseteqDelta) has at most two elements: any three
vertices of a four-cycle contain an opposite pair, whose difference is
(c
otinDelta).

For a permitted two-point set, the partial Toeplitz matrix furnished by
(FNQ1) is, up to interchanging the points,

[
egin{pmatrix}1&U\U&1end{pmatrix}
 =
egin{pmatrix}1\Uend{pmatrix}
egin{pmatrix}1&Uend{pmatrix}succeq0,                	ag{PS1}
]

where (U=X) or (U=Z), and (U=U^*=U^{-1}).  Singletons are immediate.
This proves positive definiteness on (Delta).

Now let (F:G	o M_2) be a full normalized positive-definite function.
It induces a ucp map

[
Theta:C^*(G)longrightarrow M_2,qquad
Theta(u_g)=F(g).
]

Choose a Stinespring representation

[
Theta(y)=W^*pi(y)W
]

with (W:mathbb C^2	o K) an isometry.  Set

[
P=WW^*,qquad R=pi(a),qquad S=pi(b),qquad
A=W^*RW,qquad B=W^*SW.                                	ag{PS2}
]

The unitaries (R,S) commute.  For rectangular operators out of
(mathbb C^2), use the normalized Hilbert--Schmidt norm
(|T|_{2,2}^2=rac12operatorname{Tr}(T^*T)).  Define the two leakage
terms

[
alpha=|(1-P)RW|_{2,2},qquad
eta =|(1-P)SW|_{2,2}.
]

Compression gives the exact identities

[
alpha^2=1-|A|_{2,2}^2,qquad
eta^2 =1-|B|_{2,2}^2.                              	ag{PS3}
]

If

[
|A-X|_{2,2}leqeta,qquad
|B-Z|_{2,2}leqeta,
]

and (eta<1), the reverse triangle inequality in (PS3) yields

[
alpha,etaleqsqrt{,2eta-eta^2,}leqsqrt{2eta}. 	ag{PS4}
]

Because (RS=SR),

[
egin{aligned}
|AB-BA|_{2,2}
&leq
 |W^*R(1-P)SW|_{2,2}
 +|W^*S(1-P)RW|_{2,2}\
&leqalpha+eta
 leq2sqrt{2eta}.                                    	ag{PS5}
end{aligned}
]

Both (A) and (B) are contractions.  Hence

[
|XZ-AB|_{2,2}leq2eta,qquad
|BA-ZX|_{2,2}leq2eta.                              	ag{PS6}
]

The Pauli matrices anticommute, so
(|XZ-ZX|_{2,2}=2).  Combining (PS5)--(PS6) gives

[
2leq4eta+2sqrt{2eta}.                              	ag{PS7}
]

Put (y=sqrt{2eta}).  Equation (PS7) says
(y^2+y-1geq0), and therefore

[
etageqrac12left(rac{sqrt5-1}{2}ight)^2
       =rac{3-sqrt5}{4}.                             	ag{PS8}
]

If (etageq1), (PS8) is automatic, so the bound holds without a
restriction on (eta).

At (eta=0) there is also a one-line multiplicative-domain proof:
(Theta(u_a)=X) and (Theta(u_b)=Z) are unitaries, so (u_a,u_b)
belong to the multiplicative domain.  The relation (u_au_b=u_bu_a)
would imply (XZ=ZX), contradicting (XZ=-ZX).

The estimate shows exactly where the missing translated rows enter.
Facewise positivity sees the two edges separately.  A full group table
places both directions in one Stinespring representation; the commuting
square then forces their compressions to approximately commute, with the
only possible error paid by leakage.  Near-unitarity makes that leakage
small, while the Pauli commutator remains of normalized-HS norm two.

Thus even the strongest standard approximation properties of the finite
target algebra cannot manufacture the full table from the partial data.
They become usable only after complete positivity on the concrete Fourier
operator system -- equivalently the missing cross-difference/translated-row
compatibility -- has already been proved.
