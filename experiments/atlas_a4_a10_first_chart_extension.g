# Extend the first canonical GL(4,2)=A8 chart through the explicit A10
# forward-collision quotient and score the four large-component core edges.

rQ := PermList([1,3,5,6,2,7,4,8,9,10]);;
zQ := PermList([1,3,5,7,2,4,6,8,9,10]);;
cQ := PermList([1,4,6,2,7,3,5,8,10,9]);;
tQ := PermList([1,2,5,4,9,7,10,8,3,6]);;
sQ := PermList([2,1,3,8,9,6,10,4,5,7]);;
bQ := sQ*tQ;;
Q := Group([rQ,zQ,cQ,tQ,sQ]);;

H1 := Stabilizer(Stabilizer(Q,1),8);;
if Order(H1) <> 20160 then Error("pointwise stabilizer is not A8"); fi;
if not IsSubgroup(H1,Group([rQ,zQ,cQ])) then Error("F is not in H1"); fi;

fieldOne := Z(2)^0;;
M := rows -> List(rows,row -> List(row,x -> x*fieldOne));;
source := GL(4,2);;
r0 := M([[1,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]]);;
z0 := M([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,1]]);;
c0 := M([[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,0,1]]);;

baseIso := IsomorphismGroups(source,H1);;
imr := Image(baseIso,r0);; imz := Image(baseIso,z0);; imc := Image(baseIso,c0);;
normalizer := Normalizer(SymmetricGroup(10),H1);;
alignments := Filtered(Elements(normalizer), x ->
  imr^x=rQ and imz^x=zQ and imc^x=cQ);;
if Length(alignments)=0 then Error("canonical F embedding does not extend"); fi;
h18 := List([
 [[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],
 [[1,0,0,0],[1,1,0,0],[0,0,1,0],[0,0,0,1]],
 [[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,1]],
 [[1,1,0,0],[1,0,0,0],[0,0,1,0],[0,0,0,1]],
 [[0,1,0,0],[1,1,0,0],[0,0,1,0],[0,0,0,1]],
 [[1,0,0,0],[0,1,0,0],[0,0,1,1],[0,0,1,0]]
],M);;
secondH18 := [bQ,sQ,zQ,tQ,tQ^-1,zQ^-1];;

# Canonical large-component distinct core pairs, by H18 indices (one-based):
# first 5 -> second 1; first 2 -> second 5; first 1 -> second 4;
# first 4 -> second 2.
records := [];;
for x in alignments do
  firstH18 := List(h18,matrix -> Image(baseIso,matrix)^x);;
  largeChecks := [
    IsOne((firstH18[5]*secondH18[1])^3),
    IsOne((firstH18[2]*secondH18[5])^3),
    IsOne((firstH18[1]*secondH18[4])^3),
    IsOne((firstH18[4]*secondH18[2])^3)
  ];;
  Add(records,largeChecks);
od;
scoreHistogram := Collected(List(records,checks -> Number(checks,x->x)));;
maskHistogram := Collected(List(records,checks -> Sum(
  Filtered([1..4],index -> checks[index]), index -> 2^(index-1))));;

Print("{\n");
Print("  \"A10_order\": ",Order(Q),",\n");
Print("  \"canonical_F_extensions_to_first_A8\": ",Length(alignments),",\n");
Print("  \"first_A8_order\": ",Order(H1),",\n");
Print("  \"large_core_mask_histogram\": ",maskHistogram,",\n");
Print("  \"large_core_score_histogram\": ",scoreHistogram,",\n");
Print("  \"large_core_max_satisfied\": ",Maximum(List(records,
      checks -> Number(checks,x->x))),"\n");
Print("}\n");
