# FALSE lane: the antipodal sector has a quantitative HS-lifting gap

## Purpose

The one-involution certificate in `FALSE_MACKEY_SPLIT_COCYCLE.md` asks for
asymptotic representations

\[
 U_n:G\longrightarrow U(d_n)
\]

and self-adjoint involutions `T_n` such that

\[
 \|U_n(s)T_nU_n(s)^*+T_n\|_{\mathrm{op}}\longrightarrow0,       \tag{1}
\]

where `s` lies in the sofic radical of `G`.  This note records a
quantitative consequence which uses only (1): these models cannot even be
approximately corrected to honest finite-dimensional representations at
the single coordinate `s`.

This is a necessary-condition theorem, not a construction of the missing
sector.

## The gap theorem

Write `Rad_sof(G)` for the intersection of the kernels of all homomorphisms
from `G` to sofic groups, and use normalized Hilbert--Schmidt norm

\[
 \|A\|_{2,d}=d^{-1/2}\|A\|_{\mathrm{HS}}.
\]

**Theorem (antipodal radical gap).**  Let `s in Rad_sof(G)`.  Suppose
`U_n:G->U(d_n)` are maps and `T_n in U(d_n)` are self-adjoint involutions.
Put

\[
 \eta_n=\|U_n(s)T_nU_n(s)^*+T_n\|_{2,d_n}.
\]

Then

\[
 \|U_n(s)-1\|_{2,d_n}\geq \sqrt{2-\eta_n}.             \tag{2}
\]

Every honest finite-dimensional unitary representation
`pi:G->U(d_n)` satisfies `pi(s)=1`.  Consequently

\[
 \|U_n(s)-\pi(s)\|_{2,d_n}\geq\sqrt{2-\eta_n}.         \tag{3}
\]

In particular, if (1) holds, the distance in (3) has lower limit at least
`sqrt(2)`.

**Proof.**  Decompose `U_n(s)` into its even and odd parts for conjugation by
`T_n`:

\[
 U_n(s)=E_n+O_n,
 \qquad E_n=\frac{U_n(s)+T_nU_n(s)T_n}{2}.
\]

Multiplication on the right by the unitary `U_n(s)T_n` shows that

\[
 \|U_n(s)+T_nU_n(s)T_n\|_{2,d_n}
 =\|U_n(s)T_nU_n(s)^*+T_n\|_{2,d_n}=\eta_n.           \tag{4}
\]

Thus `||E_n||_(2,d_n)<=eta_n/2`.  The odd part has normalized trace zero,
because `T_nO_nT_n=-O_n`.  Cauchy--Schwarz and (4) therefore give

\[
 |\operatorname{tr}_{d_n}(U_n(s))|
 =|\operatorname{tr}_{d_n}(E_n)|
 \leq\|E_n\|_{2,d_n}\leq\frac{\eta_n}{2}.            \tag{5}
\]

Since `U_n(s)` is unitary,

\[
 \|U_n(s)-1\|_{2,d_n}^2
 =2-2\operatorname{Re}\operatorname{tr}_{d_n}(U_n(s))
 \geq2-\eta_n,
\]

which proves (2).

For the remaining assertion, the image of any finite-dimensional unitary
representation is a linear group.  Its finitely generated subgroups are
residually finite by Malcev's theorem, hence sofic; locality of soficity
therefore makes the whole image sofic.  The definition of `Rad_sof(G)` now
forces `pi(s)=1`, and (3) follows from (2).  End proof.

## Flexible stabilization does not hide the gap

The same estimate survives the usual negligible-dimensional padding.

**Corollary (sublinear flexible gap).**  Assume `eta_n->0`.  Let
`D_n>=d_n` with `D_n/d_n->1`, and let

\[
 \widetilde U_n(g)=U_n(g)\oplus1_{D_n-d_n}.
\]

For every honest representation `rho_n:G->U(D_n)`,

\[
 \|\widetilde U_n(s)-\rho_n(s)\|_{2,D_n}
 \geq \sqrt{\frac{d_n}{D_n}}\sqrt{2-\eta_n}
 \longrightarrow\sqrt2.                                         \tag{6}
\]

**Proof.**  Again `rho_n(s)=1`.  Normalized Hilbert--Schmidt norm under the
displayed padding is multiplied by `sqrt(d_n/D_n)`, so (6) is (2).  End
proof.

Thus the one-involution FALSE certificate would automatically exhibit an
extreme, macroscopic form of flexible Hilbert--Schmidt instability of the explicit group
`G`: no correction can get closer than asymptotic distance `sqrt(2)` even
on the single radical word `s`.  The
orbit-commutation condition of the full
certificate is not needed for this obstruction.

## Consequence for the search

This rules out a broad but tempting strategy:

1. start from the operator-norm MF microstates of `G`;
2. use operator--HS or flexible HS stability to correct them to honest
   finite-dimensional representations;
3. try to install the antipodal involution after correction.

Step 2 necessarily destroys (1), quantitatively.  A successful construction
must instead use genuinely nonliftable matrix models of `G`; the failure
cannot be confined to an `o(d_n)` corner or repaired by `o(d_n)` extra
dimensions.

For the concrete Mackey shear, `s=a r_0^{-1}a^{-1}` is conjugate to the
fold witness `r_0 in Rad_sof(H)`, so `s in Rad_sof(G)` and the theorem
applies exactly to `(MSC20as)`.
