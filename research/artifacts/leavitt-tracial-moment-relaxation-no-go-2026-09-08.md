# What the ordinary tracial moment relaxation can and cannot detect

2026-09-08.  Ingestion record for a third forwarded dossier
("leavitt-hyperlinearity-complete-mathematical-record"), on the
hyperlinearity of `H = L_(F_2)(1,2)^x`.  The dossier states plainly that it
does not settle the question; this record says which of its parts were
already in the graph and which two were not.

## Almost all of it was already landed, by a peer lane, the same day

The dossier's Parts I and II are the peer lane
`leavitt-24k-relative-unitary-reduction-2026-09-08` and
`leavitt-error-basis-normalizer-obstruction-2026-09-08`, node for node:

| Dossier | Existing node |
| --- | --- |
| `v = s_0t_1+s_1t_0`, `v^2=1`, `vs_0=s_1`, `t_0v=t_1`; `C_3` and `C_2^3` generate | `binary-leavitt-units-generated-by-c3-and-c2-cubed` |
| The `24k` relative-unitary criterion and its recovered separation constant `1` | `binary-leavitt-hyperlinear-iff-24k-feasible` |
| `r_*` and its exact `GL_3(F_8)` model; the commutator bound `(23)` | `leavitt-24k-first-relation-has-exact-finite-model` |
| Finite `T` forcing `theta(c)=1` in every finite quotient (Part II Lemma 2) | `mf-obstruction-gives-a-finite-c-killing-relation-set` |
| Sharp trace gap `|tr U| <= 1/sqrt2` for error-basis normalizers | `error-basis-normalizer-has-a-sharp-trace-gap` |
| `A_0 eps + B_0 delta(X) >= 1/sqrt2` for the blockwise class | `leavitt-24k-models-avoid-blockwise-error-basis-normalizers` |
| The missing recovery step of Part II Section 7 | `hyperlinear-leavitt-models-reduce-to-error-basis-normalizers` |
| Operator-norm gap exists but does not transfer; per-dimension compactness gaps | Attempts of `leavitt-24k-feasibility-has-a-uniform-gap` |

The peer lane also went further than the dossier in one direction: it has a
`4608 = 24 * 192` projective-incidence seed for the first relation
(`leavitt-first-relation-has-a-4608-dimensional-seed`) and a four-word
kernel packet (`leavitt-24k-kernel-packet-excludes-scalar-field-models`)
that rejects the `F_8` model on two further rows.  Nothing in the dossier
supersedes any of that, and none of it is re-landed here.

## The two things that were not in the graph

**1. The tracial moment relaxation has an exact zero-error solution at every
finite level.**  This is the dossier's Part III and it is the substantive
addition: it closes off a whole certificate method for the open branch
`leavitt-24k-feasibility-has-a-uniform-gap`.

Re-derived here.  Let `F` be free on `c,b_1,b_2,b_3` and `q : F -> H` the
map of `binary-leavitt-units-generated-by-c3-and-c2-cubed`, its kernel
containing the internal relators of `P = C_3 * C_2^3`.  Put
`y_w = 1` if `q(w) = 1` and `0` otherwise.  For any finite word set `W`,
`(y_(u^-1 v))_(u,v in W)` is the Gram matrix of the vectors `e_(q(w))` in
`l^2(H)`, since `<e_(q(u)), e_(q(v))> = 1_(q(u)=q(v)) = y_(u^-1 v)`;
equivalently

```text
sum_(u,v) conj(alpha_u) alpha_v y_(u^-1 v)
  = sum_(h in H) | sum_(w : q(w)=h) alpha_w |^2 >= 0.
```

So the moment matrix is positive semidefinite at every level.  `y_1 = 1`,
`y_(w^-1) = conj(y_w)`, and traciality holds because `q(uv) = 1` iff
`q(vu) = 1`.  Every true relation identity holds: for `r in ker q` and any
`a,b`, `y_(arb) = y_(ab)`.  Both finite factors inject into `H` (that is
part of the generation claim), so the values on `C_3` and on `C_2^3` are
exactly their normalized regular characters, which is the extra data the
`24k` criterion prescribes.  For unitary words the squared defect energy is
`sum_(r in T) (2 - y_r - y_(r^-1))`, which is `0` at this point; positivity
of each term gives the matching lower bound.  Hence **every finite level
has optimum exactly zero**, and adding more true relations or more
prescribed canonical moments of `H` does not change that, because the same
point satisfies them too.

The certificate reading is the sharp form.  On `C H` let `tau` take the
coefficient of the identity; then `tau(a^*a) = sum_h |alpha_h|^2 >= 0` and
`tau(ab) = tau(ba)`.  Any contradiction derived only from positivity,
traciality, the true group relations and the prescribed character values
would have to hold under `tau`, where every relator defect is zero.  So no
such certificate exists.

What this does **not** say: it is not evidence for hyperlinearity, it
supplies no finite-dimensional models, and it does not claim that every
method exploiting matrix dimension must fail.  The `24k` criterion's
unknown is a relative unitary `U`, and the moment point above specifies no
`U`; the gap between a positive tracial functional and approximating
finite-dimensional traces is exactly the open question.

**2. The explicit translation of the four generators into units of `R`.**
`binary-leavitt-units-generated-by-c3-and-c2-cubed` names the generators as
elements of `EL_3(R)`.  The dossier also writes them as actual units of the
original ring, through the prefix code

```text
(p_1,p_2,p_3) = (s_0, s_1s_0, s_1s_1),
(r_1,r_2,r_3) = (t_0, t_0t_1, t_1t_1).
```

Checked entry by entry here: `r_i p_j = delta_(ij)` (nine products, each
collapsing by one application of `t_i s_j = delta_(ij)`), and
`sum_i p_i r_i = s_0t_0 + s_1(s_0t_0+s_1t_1)t_1 = s_0t_0+s_1t_1 = 1`.
So `Theta((a_(ij))) = sum_(i,j) p_i a_(ij) r_j` is a unital ring
isomorphism `M_3(R) -> R` with inverse `z |-> (r_i z p_j)`, and the four
generators become the displayed units.  This is a concrete restatement, not
a new theorem; its value is that the `24k` feasibility problem can be
posed against elements of `R` itself.

## Provenance

The dossier reports checking Bilich--Hazrat--Nam, *Embedding k-algebras
into Leavitt algebra L_k(1,2)*, Theorems 2.5 and 3.5 (arXiv:2512.09241v2),
and finding neither supplies the needed embedding, Theorem 3.5 assuming
characteristic zero.  That negative check is recorded, and no node depends
on it.  It also reports checking Dudko--Medynets on Higman--Thompson finite
factor representations and Fournier-Facio--Willett on the LLP, again
without extracting an applicable statement.  No external theorem enters the
two nodes landed from this dossier.

The MF obstruction `binary-leavitt-all-ranks-full-mf-radical` is used only
through the already-landed `mf-obstruction-gives-a-finite-c-killing-relation-set`;
nothing here reproves it.  No Lean certification is asserted.
