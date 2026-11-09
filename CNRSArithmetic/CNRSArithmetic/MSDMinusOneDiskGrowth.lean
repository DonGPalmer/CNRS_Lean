import CNRSArithmetic.MSDRankedObstruction
import Mathlib.Tactic

/-!
# P4 MSD-first division: formal radial confinement-growth inequality

For divisor v = -1, any Gaussian-integer remainder outside the closed
radius-eight disk has strictly increasing squared Euclidean norm after
**every** canonical input/output-digit pair. The proof is exact integer
arithmetic (no square roots or floating-point bounds).

Together with the 15-node deletion certificate on that disk, this is
the missing outer-state growth premise. The full finite-invariant-set
global no-transducer theorem is a separate next proof obligation.
-/

namespace CNRSArithmetic

def msdNormSq (r : GaussianRemainder) : ℤ := r.1 * r.1 + r.2 * r.2

theorem minusOne_outside_disk_strict_growth
    (r : GaussianRemainder) (a d : Fin 5)
    (houtside : (64 : ℤ) < msdNormSq r) :
    msdNormSq r < msdNormSq (msdDivisionStep (-1, 0) r a d) := by
  let q : ℤ := (a.val : ℤ) + (d.val : ℤ)
  have ha : (a.val : ℤ) ≤ 4 := by omega
  have hd : (d.val : ℤ) ≤ 4 := by omega
  have hq0 : 0 ≤ q := by dsimp [q]; omega
  have hq8 : q ≤ 8 := by dsimp [q]; omega
  have hqSq : q * q ≤ 64 := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 8 - q by omega)
      (show (0 : ℤ) ≤ 8 + q by omega)]
  have hxSq : 0 ≤ (r.1 - q) * (r.1 - q) := mul_self_nonneg _
  have hySq : 0 ≤ (2 * r.2 - q) * (2 * r.2 - q) := mul_self_nonneg _
  dsimp [msdNormSq, msdDivisionStep]
  dsimp [q] at hxSq hySq hqSq
  dsimp [msdNormSq] at houtside
  nlinarith [hxSq, hySq, hqSq]

end CNRSArithmetic
