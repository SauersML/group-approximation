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
module4:=First(irreducibles,module->module.dimension=4);;
image4:=Group(module4.generators);;
centralizer4:=Centralizer(GL(4,3),image4);;

Print("A5_order=",Size(G),"\n");
Print("S3_class_count=",Length(s3Classes),"\n");
Print("coset_degree=",Length(cosets),"\n");
Print("irreducible_F3_dimensions=",
      List(irreducibles,module->module.dimension),"\n");
Print("irreducible_F3_S3_fixed_dimensions=",fixedDimensions,"\n");
Print("four_dimensional_image_order=",Size(image4),"\n");
Print("four_dimensional_is_absolutely_irreducible=",
      module4.IsAbsolutelyIrreducible,"\n");
Print("four_dimensional_GL4_centralizer_order=",Size(centralizer4),"\n");
Print("Ind_S3_A5_trivial_composition_dimensions=",
      List(factors,module->module.dimension),"\n");
QUIT;
