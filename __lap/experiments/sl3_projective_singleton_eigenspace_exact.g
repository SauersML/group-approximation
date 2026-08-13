# Certify the integral involution underlying the q=0 singleton cycles.
# The accompanying proof counts its projective fixed points over every odd
# finite field; this file checks the fixed HAP boundary and eigensublattices.

if LoadPackage("hap") = fail then
    Error("the HAP package is required");
fi;

SingletonComplex := ContractibleGcomplex("SL(3,Z)a");
SingletonResolution := FreeGResolution(SingletonComplex, 3);
SingletonBoundary := SingletonResolution!.boundary(2, 1);
if Length(SingletonBoundary) <> 2 then
    Error("unexpected first vertical degree-two boundary");
fi;

SingletonMatrices := List(
    SingletonBoundary,
    term -> SingletonResolution!.elts[term[2]]
);
SingletonIdentity := IdentityMat(3);
SingletonInvolution := [
    [0, 1, 1],
    [1, 0, 1],
    [0, 0, -1]
];
if Set(SingletonMatrices) <> Set([SingletonIdentity, SingletonInvolution]) then
    Error("the first vertical boundary is not 1+T");
fi;
if SingletonInvolution * SingletonInvolution <> SingletonIdentity then
    Error("T is not an involution");
fi;

SingletonPlus := [1, 1, 1];
SingletonMinus1 := [1, -1, 0];
SingletonMinus2 := [0, 0, 1];
if SingletonPlus * SingletonInvolution <> SingletonPlus then
    Error("wrong plus eigenline");
fi;
if SingletonMinus1 * SingletonInvolution <> -SingletonMinus1
        or SingletonMinus2 * SingletonInvolution <> -SingletonMinus2 then
    Error("wrong minus eigenplane");
fi;
SingletonIndex := AbsInt(DeterminantMat([
    SingletonPlus,
    SingletonMinus1,
    SingletonMinus2
]));
if SingletonIndex <> 2 then
    Error("the two eigensublattices should have index two");
fi;

Print("boundary=1+T involution=true plus_rank=1 minus_rank=2 index=",
      SingletonIndex, "\n");
