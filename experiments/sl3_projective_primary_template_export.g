# Export the fixed natural-model templates for symbolic primary analysis.
#
# Load HAP and bind PRIMARY_TEMPLATE_OUTPUT before reading this file.  Each
# matrix is flattened in row-major order.  SOURCE and TARGET rows also carry
# the cellular orientation character.

if not IsBound(ContractibleGcomplex) then
    Error("load HAP before reading sl3_projective_primary_template_export.g");
fi;
if not IsBound(PRIMARY_TEMPLATE_OUTPUT) then
    Error("PRIMARY_TEMPLATE_OUTPUT is not bound");
fi;

PrimaryTemplateOrientation := function(complex, degree, cell, element)
    local position;
    position := Position(complex!.elts, element);
    if position = fail then
        Add(complex!.elts, element);
        position := Length(complex!.elts);
    fi;
    return complex!.action(degree, cell, position);
end;

PrimaryTemplateRun := function(path)
    local complex, stream, element, term;
    complex := ContractibleGcomplex("SL(3,Z)a");
    stream := OutputTextFile(path, false);
    SetPrintFormattingStatus(stream, false);
    for element in Elements(complex!.stabilizer(3, 1)) do
        AppendTo(stream, "SOURCE ",
            PrimaryTemplateOrientation(complex, 3, 1, element), " ",
            JoinStringsWithSeparator(List(Flat(element), String), ","), "\n");
    od;
    for element in Elements(complex!.stabilizer(2, 2)) do
        AppendTo(stream, "TARGET ",
            PrimaryTemplateOrientation(complex, 2, 2, element), " ",
            JoinStringsWithSeparator(List(Flat(element), String), ","), "\n");
    od;
    for term in Filtered(
            complex!.boundary(3, 1), term -> AbsInt(term[1]) = 2) do
        element := complex!.elts[term[2]];
        AppendTo(stream, "BOUNDARY ", SignInt(term[1]), " ",
            JoinStringsWithSeparator(List(Flat(element), String), ","), "\n");
    od;
    CloseStream(stream);
    Print("source_templates=24 target_templates=12 boundary_templates=6\n");
end;

PrimaryTemplateRun(PRIMARY_TEMPLATE_OUTPUT);
