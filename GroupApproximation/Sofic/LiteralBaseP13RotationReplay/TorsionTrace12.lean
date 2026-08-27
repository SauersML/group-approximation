import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace11
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace12 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYXzxYXzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYxZyxZXzyXYXzX")) := torsionTrace11
    _ = rotationWord (word (rotationSignedWord "XYxZyxZXZyXYXzX")) :=
      rotationStep "XYxZyxZXzyXYXzX" "XYxZyxZXZyXYXzX" "XYxZyxZX" 2 false
    _ = rotationWord (word (rotationSignedWord "XYxZyxxzxyXYXzX")) :=
      rotationStep "XYxZyxZXZyXYXzX" "XYxZyxxzxyXYXzX" "XYxZyx" 3 true
    _ = rotationWord (word (rotationSignedWord "XYxZyXzxyXYXzX")) :=
      rotationStep "XYxZyxxzxyXYXzX" "XYxZyXzxyXYXzX" "XYxZy" 0 false
    _ = rotationWord (word (rotationSignedWord "XYxZXZYXzX")) :=
      rotationStep "XYxZyXzxyXYXzX" "XYxZXZYXzX" "XYxZy" 5 false
    _ = rotationWord (word (rotationSignedWord "XYxxzxYXzX")) :=
      rotationStep "XYxZXZYXzX" "XYxxzxYXzX" "XYx" 3 true
    _ = rotationWord (word (rotationSignedWord "XYXzxYXzX")) :=
      rotationStep "XYxxzxYXzX" "XYXzxYXzX" "XY" 0 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
