# Exact modular screen for the first possible 3-chief factor of a finite
# solvable image of the universal Q1920 seam kernel.

G:=AlternatingGroup(5);;
classes:=ConjugacyClassesSubgroups(G);;
s3Classes:=Filtered(classes,class->Size(Representative(class))=6);;
if Length(s3Classes)<>1 then Error("unexpected S3 class count in A5"); fi;
A:=Representative(s3Classes[1]);;

cosets:=RightCosets(G,A);;
action:=ActionHomomorphism(G,cosets,OnRight);;
generators:=GeneratorsOfGroup(G);;
permutationMatrices:=List(generators,g->
    PermutationMat(Image(action,g),Length(cosets),GF(3)));;
permutationModule:=GModuleByMats(permutationMatrices,GF(3));;
factors:=MTX.CompositionFactors(permutationModule);;

irreducibleData:=IrreducibleModules(G,GF(3));;
irreducibles:=irreducibleData[2];;
FixedDimension:=function(module)
  local matrixGroup,representation,images,generator;
  matrixGroup:=Group(module.generators);
  representation:=GroupHomomorphismByImages(
      G,matrixGroup,irreducibleData[1],module.generators);
  images:=[];
  for generator in GeneratorsOfGroup(A) do
    Add(images,Image(representation,generator));
  od;
  return Length(BaseFixedSpace(images));
end;
fixedDimensions:=List(irreducibles,FixedDimension);;

Print("A5_order=",Size(G),"\n");
Print("S3_class_count=",Length(s3Classes),"\n");
Print("coset_degree=",Length(cosets),"\n");
Print("irreducible_F3_dimensions=",
      List(irreducibles,module->module.dimension),"\n");
Print("irreducible_F3_S3_fixed_dimensions=",fixedDimensions,"\n");
Print("Ind_S3_A5_trivial_composition_dimensions=",
      List(factors,module->module.dimension),"\n");
QUIT;
