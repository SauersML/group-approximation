# Export exact marked matrices for the F3[Q1920] seam polynomial solver.
# Run in a scratch directory; it writes atlas_a4_q1920_f3_seam_data.py.

MAX_INDEX:=12;;
free:=FreeGroup("r","y","u","b");;
r0:=free.1;; y0:=free.2;; u0:=free.3;; b0:=free.4;;
universal:=free/[
  r0^3,y0^3,u0^2,b0^2,u0*r0*u0*r0,b0*y0*b0*y0,
  (r0^-1*b0)^3,(u0*y0)^3,((u0*r0)*y0^-1)^3,(r0*b0*y0)^3
];;
universalGenerators:=GeneratorsOfGroup(universal);;

MatrixIntegers:=matrix->List(matrix,row->List(row,IntFFE));;
output:="atlas_a4_q1920_f3_seam_data.py";;
PrintTo(output,"modules = [\n");;

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
    moduleIndex:=0;;
    for module in moduleData[2] do
      moduleIndex:=moduleIndex+1;
      dimension:=module.dimension;;
      if dimension in [6,10,15,24] then
        matrixImage:=Group(module.generators);;
        representation:=GroupHomomorphismByImages(
            Q,matrixImage,moduleData[1],module.generators);;
        rMatrix:=Image(representation,r);;
        uMatrix:=Image(representation,u);;
        if Length(BaseFixedSpace([rMatrix,uMatrix]))>0 then
          yMatrix:=Image(representation,y);;
          bMatrix:=Image(representation,b);;
          AppendTo(output,"  {\"marking\":",count,
              ",\"module_index\":",moduleIndex,
              ",\"dimension\":",dimension,
              ",\"image_order\":",Size(matrixImage),
              ",\"r\":",MatrixIntegers(rMatrix),
              ",\"u\":",MatrixIntegers(uMatrix),
              ",\"t\":",MatrixIntegers(yMatrix^-1),
              ",\"s\":",MatrixIntegers(bMatrix*yMatrix),"},\n");
        fi;
      fi;
    od;
  fi;
od;
AppendTo(output,"]\n");
Print("wrote ",output," with marking_count=",count,"\n");
QUIT;
