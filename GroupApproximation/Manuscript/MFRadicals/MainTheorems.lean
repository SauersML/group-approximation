import GroupApproximation.Manuscript.MFRadicals.AlternatingFamily
import GroupApproximation.Manuscript.MFRadicals.Compression
import GroupApproximation.Manuscript.MFRadicals.Definitions
import GroupApproximation.Manuscript.MFRadicals.FinitePerfectLamp
import GroupApproximation.Manuscript.MFRadicals.ExplicitSeed
import GroupApproximation.Manuscript.MFRadicals.FullRadical
import GroupApproximation.Manuscript.MFRadicals.PerfectLampExact
import GroupApproximation.Manuscript.MFRadicals.RadicalComputer
import GroupApproximation.Manuscript.MFRadicals.SemanticClosure
import GroupApproximation.Manuscript.MFRadicals.SimpleSofic
import GroupApproximation.Manuscript.MFRadicals.TargetEquivalence

/-!
# What MF approximation forgets: the theorem package

The paper's arc in one module.

```text
   one invisible relation  ──▶  MF semantic closure  ──▶  total invisibility
        ──▶  exact invisible radicals  ──▶  computational complexity
```

| Paper      | Lean declaration                                      |
| ---------- | ----------------------------------------------------- |
| Prop. 2.1  | `manuscriptUniversalMFQuotient`                       |
| Prop. 2.2  | `manuscriptMFIffRadicalTrivial`                       |
| Theorem E  | `manuscriptSemanticClosure`                           |
| Prop. 2.3  | `manuscriptSoundSaturation`                           |
| Theorem 3.1| `manuscriptCompressionCollapse`                       |
| Seed       | `manuscriptExplicitSeed`                              |
| Theorem A  | `manuscriptTheoremA`                                  |
| Theorem B  | `manuscriptTheoremB`                                  |
| Theorem C  | `manuscriptTheoremC`                                  |
| Theorem C' | `manuscriptFinitePerfectLampFamily`                   |
| Cor. C.1   | `manuscriptAlternatingFamilyExactRadicals`            |
| Cor. C.2   | `manuscriptAlternatingFamilySameVisibleQuotient`      |
| Cor. C.3   | `manuscriptAlternatingFamilyNoncommensurable`         |
| Cor. C.4   | `manuscriptAlternatingFamilyBohrColumn`               |
| Cor. C.5   | `manuscriptAlternatingFamilyTargetEquivalence`        |
| Cor. C.6   | `manuscriptFinitePerfectLampFiveRadicals`              |
| Theorem D  | `manuscriptTheoremD`                                  |

Every row is audited in `Endpoint/MFRadicalPaperAudit`.  Peter--Weyl point
separation, previously the only conditional input, is proved in
`Analysis/PeterWeylSeparation`.

What is deliberately *not* advertised here is the exact radical of the literal
seed `E`, which still needs a specialised symmetric-double MF theorem
(`Sofic/SymmetricDoubleMF` records the remaining statement).
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

/-- **The abstract-level theorem suite.**  The five headline results of the
paper as a single closed proposition. -/
def MFRadicalPaperSuite : Prop :=
  UniversalMFQuotient ∧ MFSemanticClosure ∧ MFSoundSaturation ∧
    KazhdanCompressionCollapse ∧ PerfectLampExactRadical ∧
    FinitePerfectLampFamily ∧ FinitePerfectLampFiveRadicals ∧
    AlternatingFamilyExactRadicals ∧ AlternatingFamilySameVisibleQuotient ∧
    AlternatingFamilyNoncommensurable ∧ AlternatingFamilyBohrColumn ∧
    AlternatingFamilyTargetEquivalence

theorem manuscriptMFRadicalPaperSuite : MFRadicalPaperSuite :=
  ⟨manuscriptUniversalMFQuotient, manuscriptSemanticClosure,
    manuscriptSoundSaturation, manuscriptCompressionCollapse,
    manuscriptTheoremC, manuscriptFinitePerfectLampFamily,
    manuscriptFinitePerfectLampFiveRadicals,
    manuscriptAlternatingFamilyExactRadicals,
    manuscriptAlternatingFamilySameVisibleQuotient,
    manuscriptAlternatingFamilyNoncommensurable,
    manuscriptAlternatingFamilyBohrColumn,
    manuscriptAlternatingFamilyTargetEquivalence⟩

end MFRadicals
end Manuscript
end GroupApproximation
