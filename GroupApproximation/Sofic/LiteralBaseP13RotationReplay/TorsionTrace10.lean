import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace9
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace10 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYxZyxzXYZXYZYxyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYxZyxzyxYYZxYxzYXyxyxyzX")) := torsionTrace9
    _ = rotationWord (word (rotationSignedWord "XYxZyxzyxyZxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyxzyxYYZxYxzYXyxyxyzX" "XYxZyxzyxyZxYxzYXyxyxyzX" "XYxZyxzyx" 1 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYxzxyZxyxyxyzX")) :=
      rotationConsequenceStep "XYxZyxzyxyZxYxzYXyxyxyzX" "XYxZyxzXYxzxyZxyxyxyzX" "XYxZyxzXYxzxyZxxyZXy"
        "YxzYXXzYXZXyxyxyZx" false (hrelation := o12_32Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYxzxyzxyxyxyzX")) :=
      rotationStep "XYxZyxzXYxzxyZxyxyxyzX" "XYxZyxzXYxzxyzxyxyxyzX" "XYxZyxzXYxzxy" 2 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXZyzxyxyxyzX")) :=
      rotationStep "XYxZyxzXYxzxyzxyxyxyzX" "XYxZyxzXYZXZyzxyxyxyzX" "XYxZyxzXY" 3 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXzyzxyxyxyzX")) :=
      rotationStep "XYxZyxzXYZXZyzxyxyxyzX" "XYxZyxzXYZXzyzxyxyxyzX" "XYxZyxzXYZX" 2 true
    _ = rotationWord (word (rotationSignedWord "XYxZyxzXYZXYZYxyxyxyzX")) :=
      rotationStep "XYxZyxzXYZXzyzxyxyxyzX" "XYxZyxzXYZXYZYxyxyxyzX" "XYxZyxzXYZXz" 4 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
