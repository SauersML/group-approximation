# Exact irreducible F3[Q1920] module dimensions and fixed spaces for the two
# marked radial S3 subgroups.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
universal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
universalGenerators:=GeneratorsOfGroup(universal);;

FixedDimension:=function(source,moduleData,module,subgroup)
  local matrixGroup,representation,images,generator;
  matrixGroup:=Group(module.generators);
  representation:=GroupHomomorphismByImages(
      source,matrixGroup,moduleData[1],module.generators);
  images:=[];
  for generator in GeneratorsOfGroup(subgroup) do
    Add(images,Image(representation,generator));
  od;
  return Length(BaseFixedSpace(images));
end;

count:=0;;
for sub in LowIndexSubgroupsFpGroup(universal,MAX_INDEX) do
  cosets:=RightCosets(universal,sub);;
  action:=ActionHomomorphism(universal,cosets,OnRight);;
  marked:=[];;
  for generator in universalGenerators do
    Add(marked,Image(action,generator));
  od;
  r:=marked[1];; y:=marked[2];; u:=marked[3];; b:=marked[4];;
  edgeOrders:=[Size(Group([r^-1,b])),Size(Group([u,y])),
               Size(Group([u*r,y^-1])),Size(Group([r,b*y]))];;
  Q:=Group(marked);;
  if Size(Group([r,u]))=6 and Size(Group([y,b]))=6 and
     edgeOrders=[12,12,12,12] and Size(Q)=1920 then
    count:=count+1;
    A:=Group([r,u]);;
    B:=Group([y,b]);;
    moduleData:=IrreducibleModules(Q,GF(3));;
    profiles:=[];;
    for module in moduleData[2] do
      Add(profiles,[module.dimension,
                    Size(Group(module.generators)),
                    module.IsAbsolutelyIrreducible,
                    FixedDimension(Q,moduleData,module,A),
                    FixedDimension(Q,moduleData,module,B)]);
    od;
    Print("marking_",count,
          "_[dimension,image,absolute,Afix,Bfix]=",profiles,"\n");
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
