"""Kernel-checked large-signal consumers and strict stability boundaries."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import RESULTS, audit, check_lean


class LargeSignalTests(unittest.TestCase):
    def test_arbitrary_amplitude_and_stability_boundary(self):
        RESULTS.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="large-signal-", dir=RESULTS) as directory:
            proof = Path(directory) / "LargeSignal.lean"
            proof.write_text('''import powerlib
noncomputable section
open powerlib

def circuit : Impedance := ⟨2, ⟨1, by norm_num⟩⟩
def lossless : Impedance := ⟨0, ⟨1, by norm_num⟩⟩
def negativeResistance : Impedance := ⟨-1, ⟨1, by norm_num⟩⟩

-- No certificate, equilibrium, initial-current bound or rate is supplied.
theorem large_signal (v : ℝ) : LargeSignalStable circuit v := by
  have hR : 0 < circuit.resistance := by norm_num [circuit]
  powerlib_auto

theorem every_initial_current (v initial : ℝ) :
    ∃ i, IsTrajectory circuit v i ∧ i 0 = initial :=
  (large_signal v).2.1 initial

theorem all_trajectories_converge (v : ℝ) (i : ℝ → ℝ)
    (hi : IsTrajectory circuit v i) :
    Filter.Tendsto i Filter.atTop (nhds (v / circuit.resistance)) :=
  (large_signal v).2.2.2.2.2 i hi

theorem lossless_not_large_signal (v : ℝ) : ¬ LargeSignalStable lossless v := by
  rw [largeSignalStable_iff_resistance_pos]
  norm_num [lossless]

theorem negative_not_large_signal (v : ℝ) : ¬ LargeSignalStable negativeResistance v := by
  rw [largeSignalStable_iff_resistance_pos]
  norm_num [negativeResistance]

#print axioms powerlib.Accepted.largeSignalStable
#print axioms powerlib.largeSignalStable_iff_resistance_pos
#print axioms powerlib.large_signal_error_exact
''' + audit(["large_signal", "every_initial_current", "all_trajectories_converge",
             "lossless_not_large_signal", "negative_not_large_signal"]))
            check_lean(proof)


if __name__ == "__main__":
    unittest.main()
