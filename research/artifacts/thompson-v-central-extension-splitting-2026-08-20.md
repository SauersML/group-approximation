# Thompson (V) contributes no central sign

Checked 2026-08-20 against the primary source: Markus Szymik and Nathalie
Wahl, *The homology of the Higman--Thompson groups*, Inventiones
Mathematicae 216 (2019), Theorem A; preprint
<https://arxiv.org/abs/1411.5035>.

The specialization of their theorem to the binary Higman--Thompson group
(V=V_{2,1}) says that (V) is integrally acyclic.  In particular

\[
H_1(V;\mathbb Z)=H_2(V;\mathbb Z)=0.                 \tag{1}
\]

Let (A) be an abelian group with trivial (V)-action.  The universal
coefficient sequence gives

\[
0\longrightarrow \operatorname{Ext}(H_1(V;\mathbb Z),A)
 \longrightarrow H^2(V;A)
 \longrightarrow \operatorname{Hom}(H_2(V;\mathbb Z),A)
 \longrightarrow 0.
\]

Both end terms vanish by (1), so (H^2(V;A)=0).  Central extensions of
(V) by (A) are classified by this group; hence every such extension
splits.  If two splittings are compared, their quotient is a homomorphism
(V\to A).  This is zero because (H_1(V;\mathbb Z)=0), so the splitting
is unique.

The conclusion is stronger than the failure of the literal equation
(J=(J,J)): no projective multiplier supported only on the Thompson prefix
mixers can carry the desired sign.  A viable Thompson--Nekrashevych tape must
put its class in the state/Clifford kernel, in a relative extension involving
that kernel, or outside ordinary central extensions of (V).  Prefix swaps
may transport the sign but cannot create its holonomy.
