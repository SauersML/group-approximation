import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.TorsionTrace13

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem torsionImage_eq_one :
    rotationWord (word (rotationSignedWord "YxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYXYxzYXZXYzYX")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := torsionTrace13
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
