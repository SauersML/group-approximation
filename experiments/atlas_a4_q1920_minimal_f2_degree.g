# Exact proof data for the minimal faithful F2-representation degree of the
# marked perfect group Q=2^5:A5.

Reset(GlobalMersenneTwister,1);;
Reset(GlobalRandomSource,1);;

free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
localUniversal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
localGenerators:=GeneratorsOfGroup(localUniversal);;

Q:=fail;;
for subgroup in LowIndexSubgroupsFpGroup(localUniversal,12) do
  cosets:=RightCosets(localUniversal,subgroup);;
  action:=ActionHomomorphism(localUniversal,cosets,OnRight);;
  images:=List(localGenerators,g->Image(action,g));;
  r:=images[1];; y:=images[2];; u:=images[3];; b:=images[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Group(images))=1920 then
    Q:=Group(images);
    break;
  fi;
od;
if Q=fail then Error("marked Q1920 not found"); fi;

normalOrders:=List(NormalSubgroups(Q),Size);;
if normalOrders<>[1,2,32,1920] then
  Error("unexpected Q normal-subgroup lattice");
fi;

smallLinearOrders:=List([1..4],dimension->Size(GL(dimension,2)));;
smallDivisibility:=List(smallLinearOrders,order->order mod 1920=0);

gl5:=GL(5,2);;
maximals:=MaximalSubgroupClassReps(gl5);;
maximalOrders:=List(maximals,Size);;
eligible:=Filtered(maximals,subgroup->Size(subgroup) mod 1920=0);;
if Length(eligible)<>2 or not ForAll(eligible,subgroup->
    Size(subgroup)=322560) then
  Error("unexpected GL5(2) maximal-subgroup divisibility profile");
fi;

parabolicProfiles:=[];;
for parabolic in eligible do
  radical:=PCore(parabolic,2);;
  quotient:=parabolic/radical;;
  if Size(radical)<>16 or not IsElementaryAbelian(radical) or
     Size(quotient)<>20160 or not IsSimpleGroup(quotient) then
    Error("eligible maximal subgroup is not 2^4:GL4(2)");
  fi;
  nonidentity:=First(Elements(radical),element->not IsOne(element));;
  orbitSize:=Size(Orbit(parabolic,nonidentity));;
  stabilizerOrder:=Size(Stabilizer(parabolic,nonidentity));;
  Add(parabolicProfiles,[Size(parabolic),Size(radical),Size(quotient),
      orbitSize,stabilizerOrder,stabilizerOrder mod 960=0]);
od;

Print("Q_order=",Size(Q)," Q_perfect=",IsPerfectGroup(Q),
    " Q_normal_orders=",normalOrders," center_order=",Size(Center(Q)),"\n");
Print("GL1_to_GL4_orders=",smallLinearOrders,
    " Q_order_divides=",smallDivisibility,"\n");
Print("GL5_order=",Size(gl5)," maximal_orders=",maximalOrders,
    " Q_divisible_maximal_orders=",List(eligible,Size),"\n");
Print("PARABOLIC_[order,radical,quotient,nonzero_orbit,stabilizer,960_divides]=",
    parabolicProfiles,"\n");
QUIT;
