# Lin 2304.01940v3: tracial density, synchronous rounding, and state-dependent exactification

Source: Junqiao Lin, *Tracially embeddable strategies: Lifting MIP* tricks to
MIPco*, arXiv:2304.01940v3 (15 September 2025; manuscript dated 17 September
2025), especially Theorems 3.2, 4.1, and 5.1.  The supplied file
`/Users/user/Downloads/2304.01940v3.pdf` has SHA-256
`f6cd6e20db3d2b4db58a5f5fee8b5a3fee10a270ef7a06082c27a04fb36d69bd`.
The theorem pages were checked against that exact PDF, not only against search
snippets.  The `2304` arXiv identifier records the original 2023 submission;
it is not the date of the audited v3 theorem statements.

## Theorem 3.2 is a closure theorem

For finite question and answer sets, Lin proves

```text
closure_l1(C_qc^Tr(X,A)) = C_qc(X,A).
```

Here a tracially embeddable strategy has standard form
`(L^2(A,tau), sigma|tau>, A_x^a, (B_y^b)^op)` for a finite tracial von
Neumann algebra and a positive density `sigma`.  The paper explicitly notes
that exact tracial embeddability of every commuting correlation is not
proved and that the tracially embeddable set need not be closed.  Thus this
result may replace a commuting correlation to arbitrary correlation error;
it does not preserve exact word identities, a marked group element, a
normal-closure condition, or a fixed carrier.

## Theorem 4.1 gives a state-dependent family of corners

For a `delta`-synchronous commuting correlation, Lin constructs a probability
mixture of synchronous correlations at average correlation distance
`O(delta^(1/8))`.  In the tracially embeddable case these symmetric
strategies live in spectral corners `P_lambda A P_lambda`, with

```text
integral P_lambda d lambda = sigma^2,
integral E_x sum_a ||(A_x^a-A_x^{lambda,a})P_lambda||_2^2 d lambda
    <= O(delta^(1/4)+delta).                                      (L4.1)
```

Since `tau(sigma^2)=1`, put `m_lambda=tau(P_lambda)` and let `e_lambda`
denote the row discrepancy in `(L4.1)`.  Then

```text
integral m_lambda d lambda = 1,
integral e_lambda d lambda <= E,
```

so some positive-mass layer satisfies `e_lambda/m_lambda <= E`.  This is a
real one-strategy common-corner selection: on one state-dependent corner the
row error is controlled relative to that corner's normalized trace.

There is no strategy-independent mass floor.  Take a projection `p` with
`tau(p)=alpha` and density `sigma=alpha^(-1/2)p`.  Positivity of the layer
integral forces almost every nonzero `P_lambda` to lie under `p`, hence its
trace is at most `alpha`, while `alpha` is arbitrary.  The layers also depend
on `sigma`; they are not canonical group words or a common algebraic source
shared across independently selected states.

## Theorem 5.1 preserves the complete commutant

Let `G` be finite, `A` a finite tracial von Neumann algebra in standard form,
`rho` a positive density, and `phi:G->U(A)` an average `(epsilon,rho)`
representation.  Lin constructs an isometry

```text
V:H -> H tensor C^{|G|}
```

and an exact representation
`phi':G->U(A tensor B(C^{|G|}))` such that

```text
V B = (B tensor I)V                         for every B in A',
E_g ||phi(g)-V^*phi'(g)V||_rho^2 <= epsilon.             (L5.1)
```

The `A'`-linearity is the nonduplicate feature relative to the ordinary
finite-matrix normalized-Hilbert--Schmidt stability import.  It means that a
finite Alice packet may be exactified without changing the right/opposite
algebra's action through the dilation.  This is directly suited to the
standard-form left/right organization used in MIPco and to a state-dependent
Pauli packet.

It still does not lock a common payload carrier.  The exact object is on the
amplification, while `V^*phi'(g)V` is only a compression on the original
space and need not itself be multiplicative.  The estimate is only in the
chosen `rho`-seminorm, the amplification carries flexible multiplicity, and
neither `V` nor the support of `rho` is a group word.  Independently chosen
densities may therefore select different corners and multiplicity gauges.

## Cairn interface

Theorems 4.1 and 5.1 provide an analytic one-state Pauli standardization
interface: near-synchrony can select one positive state corner with relative
row control, and any finite-group approximate representation already proved
there can be dilated to an exact representation while preserving the
opposite action.  They do not prove the missing groupification step in
`common-partial-isometry-swap-game-compiler`: no theorem here supplies a
word-visible carrier with a strategy-independent marked-mass floor, aligns
the separately selected context types to that carrier, or removes the
amplification/multiplicity gauge.

## Exact left-side formula and relative marked-mass no-go

The proof of Theorem 5.1 uses
`V xi=|G|^(-1/2) direct_sum_g phi(g^(-1))xi`.  Consequently

```text
V^*(a tensor I)V=|G|^(-1) sum_g phi(g^(-1))^*a phi(g^(-1)),
||(p tensor I)V-Vp||_(2,rho)^2
 =|G|^(-1) sum_g ||[p,phi(g^(-1))]||_(2,rho)^2.
```

This identifies the exact boundary of the `A'`-linear conclusion.  The
opposite algebra is fixed because it commutes with every `phi(g)`; an
original left carrier is instead Reynolds-twirled.  For `G=Z_2` in `M_2`,
with `phi(s)=Z`, the compression of `X tensor I` is zero.  Hence the theorem
conclusion itself does not preserve a second left context, even at zero
defect.

The lack of mass is also relative to the mark.  In `M_N`, take a rank-one
`q` inside a rank-`floor(N/2)` marked projection `p` and density
`sigma=sqrt(N)q`.  Every nonzero layer from Theorem 4.1 lies below `q`, so
its trace divided by `tau(p)` tends to zero.  No uniform marked-mass floor
can therefore be recovered by combining the spectral corner with the
commutant-preserving dilation.

## Projection-density exception for the D8 Gram state

The intended common-swap Gram vector is more rigid than the arbitrary
density above.  If `S` is a partial isometry, `q=S^*S`, and
`s=tau(q)>0`, extend `S` to a unitary `U` and write

```text
s^(-1/2)S=U(s^(-1/2)q).
```

After conjugating the left observables by `U`, the same correlation has
positive density `sigma=s^(-1/2)q`.  Lin's actual layers
`P_lambda=chi_[sqrt(lambda),infinity)(sigma)` equal `q` for
`0<lambda<=1/s` and vanish above `1/s`.  Thus every positive-measure layer
has the full D8 source mass; the general relative-mass counterexample does
not apply to this canonical one-Gram state.

In the doubled D8 packet the polar completion is fixed after all.  With
copy projections `e_+,e_-`, put `T=e_+je_-` and `Q=T^*T`.  The literal
reflection satisfies `jQ=T`, so the positive-standard-form left observable
is the packet decode `j diag(A,I) j`.  This gives a word-visible common Lin
corner and polar conjugacy with the full D8 source mass.

The remaining failure is narrower: Lin's analytic rounded PVMs on `Q` do
not make the selected predicate word see the uncovered operator
`(1-P_c)F_cT`, and a later state-dependent exactification can Reynolds-
twirl left payload without additional covariance.  Thus the input resolves
mass/common-carrier/polar naming for the canonical Gram state, but not the
forbidden-weighted return `(CPS12)`.
