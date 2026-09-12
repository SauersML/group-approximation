# Exhaust the exact collision involution equations on the faithful
# six-dimensional F3[Q1920] module with nonzero marked-A fixed space.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
universal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
universalGenerators:=GeneratorsOfGroup(universal);;

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
    moduleData:=IrreducibleModules(Q,GF(3));;
    for module in moduleData[2] do
      if module.dimension=6 and Size(Group(module.generators))=1920 then
        matrixImage:=Group(module.generators);;
        representation:=GroupHomomorphismByImages(
            Q,matrixImage,moduleData[1],module.generators);;
        rMatrix:=Image(representation,r);;
        yMatrix:=Image(representation,y);;
        uMatrix:=Image(representation,u);;
        bMatrix:=Image(representation,b);;
        tMatrix:=yMatrix^-1;;
        sMatrix:=bMatrix*yMatrix;;
        fixedDimension:=Length(BaseFixedSpace([rMatrix,uMatrix]));;
        if fixedDimension>0 then
          centralizer:=Centralizer(GL(6,3),Group([rMatrix,uMatrix]));;
          involutionCount:=0;;
          triangleCount:=0;;
          collisionCount:=0;;
          nonidentityCollisionCount:=0;;
          signalCount:=0;;
          for cMatrix in Elements(centralizer) do
            if cMatrix^2=One(centralizer) then
              involutionCount:=involutionCount+1;
              if (cMatrix*tMatrix)^3=One(centralizer) then
                triangleCount:=triangleCount+1;
                collisionWord:=tMatrix*cMatrix*sMatrix*cMatrix*tMatrix^-1*
                               cMatrix*sMatrix*tMatrix*cMatrix;;
                if collisionWord=One(centralizer) then
                  collisionCount:=collisionCount+1;
                  if cMatrix<>One(centralizer) then
                    nonidentityCollisionCount:=
                        nonidentityCollisionCount+1;
                  fi;
                  minusFixedDimension:=Length(BaseFixedSpace(
                      [rMatrix,uMatrix,-cMatrix]));;
                  if minusFixedDimension>0 then signalCount:=signalCount+1; fi;
                fi;
              fi;
            fi;
          od;
          Print("marking_",count,
                "_[centralizer,involutions,triangle,collision,nonidentity_collision,signal]=",
                [Size(centralizer),involutionCount,triangleCount,
                 collisionCount,nonidentityCollisionCount,signalCount],"\n");
        fi;
      fi;
    od;
  fi;
od;
Print("marking_count=",count,"\n");
QUIT;
