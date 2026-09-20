# A direct Leavitt obstruction from compressor normalization

2026-09-20. Written conditional deduction; no new Lean verification. The analytic normalization premise remains a named graph prerequisite.

## Attribution and scope

The proposed analytic input is **Jihao Liu**, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf), Theorem 1.2/6.7 (internality). **Andreas Thom** has priority for the deduction of normalization from universal internality: [*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf), Theorem 1.2. Liu's Theorem 1.3/7.4 also supplies that implication and explicitly credits Thom.

The native group and matrix identities come from Cairn's earlier Leavitt program; see [the September 8 native generation proof](leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md). This note checks an application, not novelty priority, and does not attribute Leavitt nonhyperlinearity to a theorem stated in Liu's paper.

Assume the following exact normalization statement: if L<=H are finitely generated Kazhdan groups, H=<L,t_1,...,t_m>, and t_i L t_i^-1<=L, then every homomorphism pi:H->U(M) into a tracial matrix ultraproduct normalizes D=pi(L)' cap M. No injectivity or trace-preservation assumption is required.

## 1. The ring and native compressors

Let R=L_(F_2)(1,2), written with generators s,t,a,b and relations

```
ts=ba=1,  ta=bs=0,  st+ab=1,  e=ab=1-st.
```

In particular e^2=e, te=es=0, ea=a, be=b and e!=0: otherwise ba=b e a=0 would contradict ba=1. Use the established ring self-similarity and GL=EL to identify

```
R^x ~= H=GL_4(R)=EL_4(R),
L=diag(EL_3(R),1),   K=diag(I_3,R^x).
```

The finitely generated ring theorem of Ershov--Jaikin-Zapirain gives property (T) for H and L. It also gives finite generation; no finite presentation or simplicity is used.

Define the inverse pair

```
u     = [s 0 0 e; 0 s 0 et; 0 0 s et^2; 0 0 0 t^3],
u^-1  = [t 0 0 0; 0 t 0 0; 0 0 t 0; e se s^2e s^3].
```

Multiplication uses e+set+s^2et^2+s^3t^3=1 (a telescoping sum) and te=es=0. For i!=j<=3,

```
u x_ij(r) u^-1=x_ij(srt).
```

Thus uLu^-1<=L, and the inclusion is strict. For A in EL_3(R), the
upper-left block of u diag(A,1) u^-1 is entrywise sAt+eI_3. Its
off-diagonal entries lie in sRt. But e is not in sRt: if e=srt,
multiplying by t on the left and s on the right gives r=tes=0,
contradicting e!=0. Hence x_12(e) lies in L but not in uLu^-1.
This uses the actual block formula, not an inverse for s. The named
claim is `leavitt-native-strict-kazhdan-compression-pair`.

Define

```
k_+=diag(I_3,1+a t^3),   k_-=diag(I_3,1+s^3 b).
```

The added terms square to zero, so these are units. They centralize L, hence are also compressors. All three matrices belong to H by GL_4=EL_4.

## 2. These finitely many compressors generate H with L

Direct multiplication gives

```
u k_+ u^-1=x_14(a),   u k_- u^-1=x_41(b).
```

For example the first difference from the identity is the product of the fourth column of u, a t^3, and the fourth row of u^-1; only its (1,4) entry survives and equals a. The second product has only its (4,1) entry b.

For every r in R, Steinberg commutators and ba=1 yield

```
[x_21(rb),x_14(a)]=x_24(r),
[x_41(b),x_12(ar)]=x_42(r).
```

Both L factors lie in the subgroup already generated. Commuting x_24(r) with x_i2(1), for i=1,3, gives x_i4(r). Commuting x_42(r) with x_2j(1), for j=1,3, gives x_4j(r). Along with the roots of L these are every elementary generator of EL_4(R). Consequently

```
H=<L,u,k_+,k_->.
```

This verifies the finite compression hypothesis literally, without claiming that any arbitrary self-similar subgroup is infranormal.

## 3. One nontrivial element is killed in every matrix-ultraproduct model

Take k=diag(I_3,1+et). Since (et)^2=0, k is a unit and belongs to K, which centralizes L. Another direct multiplication gives

```
y=u k u^-1=x_12(e).
```

For clarity, the first row of the rank-one difference is et times the fourth row (e,se,s^2e,s^3) of u^-1, giving (0,e,0,0); all other rows vanish.

Let pi:H->U(M) be any homomorphism and D=pi(L)' cap M. The normalization premise applies by Sections 1--2. Since pi(k) belongs to D and pi(u) normalizes D, pi(y) belongs to D. Since x_23(1) belongs to L,

```
pi(x_13(e))=pi([x_12(e),x_23(1)])=1.
```

But x_13(e)!=1 because e!=0. An injective matrix-ultraproduct homomorphism is impossible. In particular no canonical-trace model exists, and H, hence R^x, is not hyperlinear.

In fact every such homomorphism is trivial without a simplicity input.
Its normal kernel contains x_13(e). Since be=b and ba=1, it contains

```
[x_41(b),x_13(e)]=x_43(b),
[x_43(b),x_32(a)]=x_42(1),
[x_14(r),x_42(1)]=x_12(r)  for every r in R.
```

Elementary permutation conjugations carry this to all root subgroups;
they generate H. This proves the existing claim
`binary-leavitt-tracial-ultraproduct-images-are-trivial` through the
new native route `leavitt-trivial-images-via-native-commutators`.
It is the supplied September 20 report's explicit normal-generation
argument, consistent with the separate full-defect-ring proof; it
claims neither an independent analytic theorem nor an assembly defect.

## 4. What this improves, and what it does not

This is a short alternate group-theoretic consumer of normalization. It bypasses the Leavitt heat/SOS analysis, global scalar-commutant selection, and central-height argument. It also avoids embedding the Kun--Thom wreath into H. It does **not** shorten or replace Jihao Liu's Sections 3--6 internality proof or Andreas Thom's normalization proof. The other Leavitt route can be logically stronger as a consumer if it uses internality alone and avoids the general normalization theorem; these are different tradeoffs.

The strongest structural package, a single finitely presented infinite simple Kazhdan nonhyperlinear group, additionally uses the existing simplicity and finite-presentation nodes. In particular the Khanh finite-presentation import has its own review boundary and is not proved by this elementary matrix argument.
