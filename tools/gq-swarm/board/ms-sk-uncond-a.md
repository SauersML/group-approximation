# ms-sk-uncond-a
Direction: the K-theory side of the SK open row (tex l.733-735). This covers the LVFreeAlgK2 / NK2 / Gersten chain and its neighbours, only where nobody has touched it in the last 2 h. As of 20:28Z, no SK commit had landed in the last 3 h.

## Gate map (read from origin/main 1d38dc7fd, 09-18 20:30Z)
- The open row reduces to ONE Prop. `LVWire/Chain.lean` gives it as hD : StableK2Trivial CohnLimit. Two equivalent forms:
  - stable K2(C_2(F2)) = 0;
  - `LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`.
  Every other link of the chain (descent to L, superperfect, K2(4,L)=bot, EL_5 fp) is proved.
- Weaker entry points that are also sufficient:
  - `LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement` (K2(4,L) finitely normally generated, not bot);
  - `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`.
- ABC thm:skewyao Step 3: C_{>=0} is filtered by rings F_k with F_0 = F2<x0,x1> (`LVCohnHalf/FreeRep`). The free-algebra K2 (Gersten) is therefore the base input of the route.
- `LVFreeAlgGersten` reduces the Gersten nil part to `skGer_PolyNilStatement` (NK2(F2<x0,x1>) = 0). That residual is a priori STRONGER than the target.

## Landed
(pending probe) Full/LVPolyK2/Basic.lean. It bridges bh-met-94e's K2(N,F_p[X]) = bot into the SK stable-K2 API:
- stable K2(F_p[X]) = 0;
- NK2(F2) = 0, which is the conclusion of skGer_polyNilZModTwo_of_polyNil, now unconditional;
- stable K2 of M_m(F_p)[X] and of (prod M_d(F2))[X];
- stable K2(S[X]) = 0 and untwisted NK2(S) = 0 for every ultramatricial F2-ring S (the phi = id case of LVSkewLaurentK2.NilK2Trivial);
- stable K2(C0[X]) = 0;
- Gersten for ONE generator: stable K2(F_p<x>) = 0 and AugNil(freeAug F2 (Fin 1)).

## Open (not discharged)
- AugNil(freeAug F2 (Fin 2)), i.e. Gersten for two generators, and skGer_PolyNilStatement.
- Twisted NilK2Trivial S (+-1); YaoFactorization.
- Stable K2(C_2(F2)) itself.
