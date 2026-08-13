import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace3
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace4 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "YxzXYZyzYXyxYxzYXyxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxyZXYxzYXZXYzYX")) := torsionTrace3
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxyxyZXYxzYzxzYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxyxyZXYxzYXZXYzYX" "YxzYzyxzYXyxYxzYXyxyxyZXYxzYzxzYzYX" "YxzYzyxzYXyxYxzYXyxyxyZXYxzYX" 3 true
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxYxzYXyxyxzYzYX")) :=
      rotationConsequenceStep "YxzYzyxzYXyxYxzYXyxyxyZXYxzYzxzYzYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyxzYzYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyZyZXy"
        "YxzYzYXYxyZXyyxyZX" false (hrelation := o12_13Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYzYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxYxzYXyxyxzYzYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYzYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYZYX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYzYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYZYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxYxzYXyxyxZYZYX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyxyzX" "YxzYzyxzYXyxYxzYXyxYxzYXyxyx" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzXYZyzYXyxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "YxzYzyxzYXyxYxzYXyxYxzYXyxyxyzX" "YxzXYZyzYXyxYxzYXyxYxzYXyxyxyzX" "Yxz" 6 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
