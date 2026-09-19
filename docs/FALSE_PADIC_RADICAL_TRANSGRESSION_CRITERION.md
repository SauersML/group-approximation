# A nonintegral p-adic radical transgression implies FALSE

Date: 2026-08-11

## 1. Setup

Fix a finite presentation

`H=<S | R>`,                                                `(PRT1)`

a word

`1!=w in Rad_sof(H)`,                                      `(PRT2)`

and a nonzero base integral relator two-cycle

`v in K_1=ker(A_1^*)`.                                    `(PRT3)`

Let `p` be a prime.  Suppose that for arbitrarily large `k` there is a
connected regular finite presentation cover `X_k`, of degree divisible by
`p^k`, and a cochain `a_k` satisfying

`A_(X_k)a_k=Jv mod p^k`.                                 `(PRT4)`

Let

`h_k=<a_k,b_(w,x_k)> mod p^k`                            `(PRT5)`

be its radical holonomy.  It is independent of the base vertex and of the
chosen solution by the radical-holonomy theorem.

Assume the residues are compatible:

`h_(k+1)=h_k mod p^k`.                                   `(PRT6)`

They then define

`h_infinity=(h_k)_k in Z_p`.                             `(PRT7)`

Compatibility is automatic when `(PRT4)` comes from one inverse-system
solution of the modular Fox equations over a nested pro-`p` cover tower.

## 2. Centered residues detect ordinary integers

For `h_k in Z/p^k Z`, let

`H_k=dist(h_k,p^k Z) in [0,p^k/2]`                     `(PRT8)`

be the absolute value of its centered integer representative.

**Lemma 1.**  The sequence `(H_k)` is bounded if and only if

`h_infinity in Z subset Z_p`.                           `(PRT9)`

**Proof.**  If `h_infinity=m` is an ordinary integer, its centered residue
modulo `p^k` equals `m` for all sufficiently large `k`, so `(H_k)` is
bounded.

Conversely, suppose `H_k<=M`.  Choose centered representatives
`m_k in Z` with `|m_k|<=M`.  The finite set `[-M,M] intersect Z` contains
one value `m` on an infinite subsequence.  For every fixed `j`, choose a
subsequence index `k>=j`.  Compatibility gives

`h_j=m mod p^j`.                                       `(PRT10)`

Thus `(h_j)_j` is exactly the image of the ordinary integer `m` in `Z_p`.
End proof.

In particular,

`h_infinity notin Z  ==>  sup_k H_k=infinity`.         `(PRT11)`

Passing to a subsequence makes `H_k->infinity`.

## 3. The p-adic FALSE certificate

**Theorem 2 (nonintegral p-adic transgression criterion).**  In the setup
above, if

`h_infinity notin Z`,                                  `(PRT12)`

then a hyperlinear nonsofic group exists.

**Proof.**  The base vector `v` is fixed.  By Lemma 1, pass to a subsequence
such that

`H_k/||v|| ->infinity`.                                `(PRT13)`

The amplified transfer-holonomy criterion, Theorem 3a of
`FALSE_TRANSFER_HOLONOMY_CERTIFICATE.md`, applies to `(PRT4)--(PRT5)` with
`q_k=p^k`.  It constructs exact-chart monomial microstates whose relator
defects vanish after conjugate doubling and tensor amplification, while
`w` retains positive normalized Hilbert--Schmidt displacement.  Their
tracial-ultraproduct image is hyperlinear.  It cannot be sofic because the
quotient map from `H` to that image does not kill
`w in Rad_sof(H)`.  End proof.

## 4. Group-ring formulation

Let `T_k` be the deck group.  In the notation of
`FALSE_MODULAR_GROUP_RING_HOLONOMY.md`, equation `(PRT4)` is

`A_(T_k)a_k=N_(T_k)v mod p^k`,                         `(PRT14)`

and

`h_k=[1]<a_k,b_w> mod p^k`.                            `(PRT15)`

Thus the complete new target is qualitative:

> construct a nested pro-`p` finite quotient tower on which the norm-socle
> Fox equation `(PRT14)` has a compatible solution and its radical Fox
> functional `(PRT15)` is a p-adic integer not lying in the diagonally
> embedded copy of `Z`.

No lower bound proportional to `p^k` is required.  Any nonordinary p-adic
value has unbounded centered residues, and tensor powers supply the
macroscopic trace separation.

Equivalently, the varying finite central deformations

`Htilde_(v,p^k)`                                        `(PRT16)`

need compatible finite monomial quotients in which the exponents of the
lifted radical word converge to a nonintegral element of `Z_p`.  This is
strictly weaker than asking those exponents to occupy a fixed positive
fraction of the modulus.

## 5. Necessary degree screen

The earlier transfer identities still impose

`p^k divides |X_k| ||v||^2`                            `(PRT17)`

and, for any fixed base filling `A_1^*z_0=b_w`,

`|X_k| h_k=|X_k|<v,z_0> mod p^k`.                     `(PRT18)`

Hence the cover degrees must carry an unbounded `p`-part.  If the `p`-part
of `|X_k|` were bounded, `(PRT18)` would force `h_infinity` to be the
ordinary integer `<v,z_0>` (and `(PRT17)` would itself eventually fail for
fixed nonzero `v`).  The nonintegral transgression can only live in the
nonsemisimple norm sector where the growing `p`-power divides the cover
degree.

## 6. Profinite-modulus generalization

Nothing in Lemma 1 uses prime powers.  Let

`q_1 | q_2 | q_3 | ...`, `q_k->infinity`,              `(PRT19)`

and let compatible residues `h_k in Z/q_k Z` define an element

`hhat in lim_k Z/q_k Z`.                               `(PRT20)`

Exactly the same finite-subsequence proof gives

`sup_k dist(h_k,q_k Z)<infinity`
` iff hhat lies in the diagonal image of Z`.           `(PRT21)`

Therefore a compatible modular-transfer tower with fixed `v` proves FALSE
whenever its profinite radical transgression `hhat` is not an ordinary
integer.  The prime-power theorem is the special case in which the inverse
limit in `(PRT20)` is `Z_p`.

This version is useful when the profinite compression kernel has finite
quotients of unbounded order but no single pro-`p` quotient tower has yet
been isolated.  Whenever the corresponding solutions can be organized over
a nested divisibility chain (an additional compatibility requirement), the
live target is again nonintegrality, not a quantitative positive-fraction
estimate.
