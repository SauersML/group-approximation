# Exact character audit for the GL(3,2) atlas overlap in GL(4,2).
#
# The block subgroup H = diag(GL(3,2),1) is simultaneously the stabilizer of
# the point <e4> and of the hyperplane ker(e4^*).  Since e4^*(e4)=1, G/H is
# the 120-point set of nonincident point--hyperplane flags.  We decompose the
# three associated permutation characters exactly.

F := GF(2);;
G := GL(4,F);;
els := Elements(G);;

zero := Zero(F);;
one := One(F);;

IsPointStabilizerElement := function(g)
  return g[4][1]=zero and g[4][2]=zero and g[4][3]=zero and g[4][4]=one;
end;;

IsHyperplaneStabilizerElement := function(g)
  return g[1][4]=zero and g[2][4]=zero and g[3][4]=zero and g[4][4]=one;
end;;

Mp := Subgroup(G,Filtered(els,IsPointStabilizerElement));;
Mh := Subgroup(G,Filtered(els,IsHyperplaneStabilizerElement));;
H := Intersection(Mp,Mh);;

chiP := InducedClassFunction(TrivialCharacter(Mp),G);;
chiH := InducedClassFunction(TrivialCharacter(Mh),G);;
chiF := InducedClassFunction(TrivialCharacter(H),G);;
irr := Irr(G);;

Mults := function(chi)
  return List(irr,x->ScalarProduct(chi,x));
end;;

degrees := List(irr,DegreeOfCharacter);;
pointMults := Mults(chiP);;
hyperplaneMults := Mults(chiH);;
flagMults := Mults(chiF);;

if Size(G)<>20160 or Size(Mp)<>1344 or Size(Mh)<>1344 or Size(H)<>168 then
  Error("unexpected subgroup orders");
fi;
if degrees<>[1,7,14,20,21,21,21,28,35,45,45,56,64,70] then
  Error("unexpected irreducible character ordering or degrees");
fi;
if pointMults<>[1,0,1,0,0,0,0,0,0,0,0,0,0,0] then
  Error("unexpected point permutation character");
fi;
if hyperplaneMults<>pointMults then
  Error("point and hyperplane permutation characters differ");
fi;
if flagMults<>[1,0,2,0,0,0,0,0,1,0,0,1,0,0] then
  Error("unexpected nonincident-flag permutation character");
fi;

Print("group_order=",Size(G),"\n");
Print("point_stabilizer_order=",Size(Mp)," index=",Index(G,Mp),"\n");
Print("hyperplane_stabilizer_order=",Size(Mh)," index=",Index(G,Mh),"\n");
Print("flag_stabilizer_order=",Size(H)," index=",Index(G,H),"\n");
Print("flag_is_GL3_order=",Size(H)=168,"\n");
Print("irreducible_degrees=",degrees,"\n");
Print("point_multiplicities=",pointMults,"\n");
Print("hyperplane_multiplicities=",hyperplaneMults,"\n");
Print("nonincident_flag_multiplicities=",flagMults,"\n");
Print("point_commutant_dimension=",ScalarProduct(chiP,chiP),"\n");
Print("hyperplane_commutant_dimension=",ScalarProduct(chiH,chiH),"\n");
Print("flag_commutant_dimension=",ScalarProduct(chiF,chiF),"\n");
Print("point_hyperplane_intertwiner_dimension=",ScalarProduct(chiP,chiH),"\n");
Print("point_flag_intertwiner_dimension=",ScalarProduct(chiP,chiF),"\n");
Print("hyperplane_flag_intertwiner_dimension=",ScalarProduct(chiH,chiF),"\n");

QUIT;
