import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace1
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace2 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxyZXYxzYXZXYzYXYxzYXZXYzYX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "YxzYzxyZXYxzYzxzYzYXYxzYXZXYzYXYxzYXZXYzYX")) := torsionTrace1
    _ = rotationWord (word (rotationSignedWord "YxzYzYYxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationConsequenceStep "YxzYzxyZXYxzYzxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzYYxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzYYxzYXyxyZyZXy"
        "YxzYzYXYxyZXyyxyZX" false (hrelation := o12_13Image_eq_one)
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzYYxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYz" 1 true
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxZYzYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxyxzYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxZYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyx" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxZYZYXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxyxZYzYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxZYZYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxZY" 2 false
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxyzXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxyxZYZYXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxyzXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyx" 4 true
    _ = rotationWord (word (rotationSignedWord "YxzYzyxzYXyxyxyZXYxzYXZXYzYXYxzYXZXYzYX")) :=
      rotationStep "YxzYzyxzYXyxyxyzXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxyZXYxzYXZXYzYXYxzYXZXYzYX" "YxzYzyxzYXyxyxy" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
