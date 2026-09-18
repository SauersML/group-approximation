# gq-deep-pp-1 board (family C, deep freedom lane)

**Approach.** Family: piecewise projective / 1-dim dynamics. Signature: "rotation number plus germ rigidity kills
nonstandard copies". Adopted from gq-pp-psl2q's unlanded N(D)=C(D) programme (lane retired after 4a58a2b5b,
which covers only STANDARD copies). First falsifiable step: prove that a group of circle homeomorphisms whose
point-germ groups have no nontrivial divisible subgroup has N(A) = C(A) for every divisible abelian A.

**Established.** 29c2142b0 + f92ba326b `circle-groups-with-divisible-free-germs-omit-gl-n-q` (+ `-proof`), root attempt-10
note a169d6feb. OVERLAP: gq-pp-psl2q had landed the finitely-breakpoint version at d65ff92ff
(`pp-circle-divisible-subgroups-act-freely`, `pp-circle-and-lift-hosts-miss-gl-n-q`); mine is the germ-local form
(hypothesis only on point-germ groups: adds germ extensions with accumulating breakpoints and index-2 overgroups;
does not cover T-bar). Scope as landed: any embedding,
hosts T, Stein–Thompson T-groups, PL circle groups with divisible-free slope groups, finitely-piecewise
PSL_2(A)-groups (A f.g. ring; Lodha's simple S, Lodha–Moore, Monod's H(A)), and their finite germ extensions
with divisible-free singular germs. Excludes GL_n/SL_n/PSL_n/PGL_n(Q) (n>=2), Aff(Q), B_2(Q), U_3(Q).

**Needs.** —

**Dead.** Line version in germ form is FALSE (Aff^+(Q) on R has germ groups ≅ Q_{>0}); the circle/interval
version needs the germ hypothesis at ±∞ too (T̄ fails it there, consistently).

**Sparks.** Higher-dimensional analogue (RP^{n-1}, spheres): no rotation number; the germ step survives but
the fixed-point step does not. Totally disconnected spaces (P^1(Q_p), Cantor): open-closed step fails, as Q ≤ 2V shows.
