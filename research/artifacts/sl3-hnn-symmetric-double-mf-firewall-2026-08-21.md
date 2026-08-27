# The SL3 centralizer HNN group sits in a Shulman symmetric double

Date: 2026-08-21

## Statement

Let `C <= A` be groups and let

\[
G=A*_{C}(C\times\mathbf Z)
 =\langle A,t\mid [t,c]=1\ (c\in C)\rangle .
\]

Set `H=A x Z`, embed `C` in `H` by `c |-> (c,0)`, and let

\[
D=H*_{C}H.
\]

Then `G` embeds in `D`.  Therefore

\[
C^*(H)\text{ MF}\quad\Longrightarrow\quad
D\text{ is group-MF}\quad\Longrightarrow\quad G\text{ is group-MF}.
\]

There is no final implication to hyperlinearity: the MF embedding is in an
operator-norm corona and need not preserve the canonical group trace.  This
is the exact trace gap in the tempting symmetric-double shortcut.

## Proof of the group embedding

Write

\[
H_1=A_1\times\langle z_1\rangle,
\qquad H_2=A_2\times\langle z_2\rangle
\]

for the two factors of `D`, with their copies of `C` identified.  The
subgroups

\[
K_1=A_1\le H_1,
\qquad K_2=C\times\langle z_2\rangle\le H_2
\]

both meet the amalgamating subgroup in exactly `C`.  The universal property
therefore gives a homomorphism

\[
\iota:K_1*_{C}K_2\longrightarrow H_1*_{C}H_2.
\]

It is injective by the normal-form theorem.  Indeed, a reduced word in the
domain alternates between letters of `K_1 minus C` and `K_2 minus C`.
Those letters lie respectively in `H_1 minus C` and `H_2 minus C`, so the
same word is reduced, and hence nontrivial, in the codomain.  Finally

\[
K_1*_{C}K_2=A*_{C}(C\times\mathbf Z)=G.
\]

Concretely, `iota` sends `A` to `A_1` and the stable letter `t` to `z_2`.

## MF consequence

Full group C-star algebras preserve group amalgams:

\[
C^*(D)=C^*(H)*_{C^*(C)}C^*(H).
\]

Shulman, *The MF property for amalgamated free products*,
arXiv:2603.13564v2, Theorem 10, says that for a separable MF C-star algebra
`Q` and any C-star subalgebra `R`, the symmetric double `Q *_R Q` is MF.
This is already source-verified in
`research/artifacts/shulman-2603-13564-verified.md`.  Apply it with
`Q=C*(H)` and `R=C*(C)`.  Thus `C*(D)` is MF.

A discrete group embeds in its full group C-star algebra, so MF of `C*(D)`
implies group-MF of `D`.  Restricting an operator-norm matrix embedding to a
subgroup shows that group-MF passes to subgroups.  Hence `G` is MF.  Every
statement up to this sentence is in Shulman's operator-norm group-MF sense;
it gives no canonical-trace microstates for `G`.

## Why this is a genuine firewall rather than a solution

`A=SL_3(Z[1/2])` is residually finite, but this proves only group-level
finite separation.  It does **not** imply that the full group C-star algebra
`C*(A)` or `C*(A x Z)` is MF.  The direction recorded in the Shulman audit is

\[
C^*(A)\text{ MF}\Longrightarrow A\text{ MF},
\]

not its converse.  Bekka's theorem that `C*(SL_n(Z))` has no faithful trace
also does not decide MF; an MF embedding's ultralimit trace need not be
faithful.  Thus no MF hypothesis has been smuggled in.

One might try to conclude that `G` is hyperlinear from MF of `C*(D)`.  This
is invalid.  An embedding

\[
C^*(D)\longrightarrow \prod_n M_{d_n}/\bigoplus_n M_{d_n}
\]

is norm-faithful, but an ultralimit of the normalized matrix traces on its
image can have a nonzero kernel and need not equal the canonical trace of
`D`.  Hyperlinearity of `D`, or of the subgroup `G` by restriction, requires
microstates for that specified canonical trace.  The source audit
`shulman-2603-13564-verified.md` and
`shulman-symmetric-double-has-no-stable-trace-upgrade` record that the
current theorem contains no trace-preserving upgrade.

Even residual finiteness of `A` does not repair the free-product step.  It
does provide exact finite quotient representations whose traces converge to
the canonical trace on `A`, and a separate norm-MF block could retain norm
injectivity.  But Shulman's symmetric-double construction does not assert
that the two copies become free with amalgamation while retaining that
chosen trace.  Producing exactly that distribution is equivalent to finding
the amalgamated-free Haar unitary of
`hnn-hyperlinearity-is-amalgamated-free-haar-unitary`.

Therefore the symmetric double is a rigorous structural embedding and a
rigorous no-shortcut result, not a conditional obstruction to
non-hyperlinearity.  It shows precisely why an operator-norm MF theorem
cannot decide the SL3 HNN terminal: the missing datum is the canonical trace
on a nonamenable amalgam.
