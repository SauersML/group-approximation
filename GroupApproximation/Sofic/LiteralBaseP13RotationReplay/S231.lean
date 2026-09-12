import GroupApproximation.Sofic.LiteralBaseP13RotationReplay.S231Trace1

namespace GroupApproximation.LiteralBaseP13RotationReplay

open LiteralBaseRotationRetract PresentedGroupRelatorReplay

noncomputable section

theorem s231Image_eq_one :
    rotationWord (word (rotationSignedWord "XYxzYxYxzYxyZXyyZXyXZXYXy")) = 1 := by
  calc
    _ = rotationWord (word (rotationSignedWord "")) := s231Trace1
    _ = 1 := by rfl

end

end GroupApproximation.LiteralBaseP13RotationReplay
