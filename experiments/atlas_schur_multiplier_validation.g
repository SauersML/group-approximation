# Exact Schur-multiplier validation for the local atlas central extension.
#
# Run on MSI with Sage's GAP and the project-local HAP package root.  This
# script deliberately contains no storage paths; the caller supplies GAP's
# `-l` root.

if LoadPackage("HAP") <> true then
    Error("HAP is required");
fi;

centralGroup := PerfectGroup(IsPermGroup, 2688, 2);;
centralKernel := Centre(centralGroup);;
quotientMap := NaturalHomomorphismByNormalSubgroup(
    centralGroup, centralKernel);;
baseGroup := Image(quotientMap);;

if Size(centralGroup) <> 2688 then
    Error("unexpected central-group order");
fi;
if Size(centralKernel) <> 2 then
    Error("unexpected center order");
fi;
if Size(baseGroup) <> 1344 then
    Error("unexpected base-group order");
fi;
if not IsPerfectGroup(centralGroup) then
    Error("central group must be perfect");
fi;
if not IsPerfectGroup(baseGroup) then
    Error("base group must be perfect");
fi;

resolution := ResolutionFiniteGroup(baseGroup, 3);;
integerComplex := TensorWithIntegers(resolution);;
schurInvariants := Homology(integerComplex, 2);;

if schurInvariants <> [2, 2] then
    Error("unexpected Schur multiplier");
fi;

Print("central_order=", Size(centralGroup), "\n");
Print("center_order=", Size(centralKernel), "\n");
Print("base_order=", Size(baseGroup), "\n");
Print("central_perfect=", IsPerfectGroup(centralGroup), "\n");
Print("base_perfect=", IsPerfectGroup(baseGroup), "\n");
Print("H2_invariants=", schurInvariants, "\n");

