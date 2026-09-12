import GroupApproximation.Sofic.LiteralBaseP13RotationReplay
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace7
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_13
import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.O12_32

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionTrace8 :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) =
      rotationWord (word (rotationSignedWord "XYxZyXZXzYXyxYxzYXyxyxyzX")) := by
  calc
    _ = rotationWord (word (rotationSignedWord "XYXZxxYxzYXyxYxzYXyxyxyzX")) := torsionTrace7
    _ = rotationWord (word (rotationSignedWord "XYXzxxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYXZxxYxzYXyxYxzYXyxyxyzX" "XYXzxxYxzYXyxYxzYXyxyxyzX" "XYX" 2 true
    _ = rotationWord (word (rotationSignedWord "XYxxzxxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYXzxxYxzYXyxYxzYXyxyxyzX" "XYxxzxxYxzYXyxYxzYXyxyxyzX" "XY" 0 true
    _ = rotationWord (word (rotationSignedWord "XYxZXZxYxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxxzxxYxzYXyxYxzYXyxyxyzX" "XYxZXZxYxzYXyxYxzYXyxyxyzX" "XYx" 3 false
    _ = rotationWord (word (rotationSignedWord "XYxZyXzxxzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZXZxYxzYXyxYxzYXyxyxyzX" "XYxZyXzxxzYXyxYxzYXyxyxyzX" "XYxZy" 5 true
    _ = rotationWord (word (rotationSignedWord "XYxZyXzXzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyXzxxzYXyxYxzYXyxyxyzX" "XYxZyXzXzYXyxYxzYXyxyxyzX" "XYxZyXz" 0 false
    _ = rotationWord (word (rotationSignedWord "XYxZyXZXzYXyxYxzYXyxyxyzX")) :=
      rotationStep "XYxZyXzXzYXyxYxzYXyxyxyzX" "XYxZyXZXzYXyxYxzYXyxyxyzX" "XYxZyX" 2 false

end

end GroupApproximation.LiteralBaseP13RotationReplay
