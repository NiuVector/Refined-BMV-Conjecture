import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix

namespace RefinedBMV.Supporting

theorem det_four_entries (G : Matrix (Fin 4) (Fin 4) ℝ) :
    G.det = G 0 0 * det (!![G 1 1, G 1 2, G 1 3; G 2 1, G 2 2, G 2 3; G 3 1, G 3 2, G 3 3])
    - G 0 1 * det (!![G 1 0, G 1 2, G 1 3; G 2 0, G 2 2, G 2 3; G 3 0, G 3 2, G 3 3])
    + G 0 2 * det (!![G 1 0, G 1 1, G 1 3; G 2 0, G 2 1, G 2 3; G 3 0, G 3 1, G 3 3])
    - G 0 3 * det (!![G 1 0, G 1 1, G 1 2; G 2 0, G 2 1, G 2 2; G 3 0, G 3 1, G 3 2]) := by
  have h0 : G.submatrix Fin.succ (0 : Fin 4).succAbove = !![G 1 1, G 1 2, G 1 3; G 2 1, G 2 2, G 2 3; G 3 1, G 3 2, G 3 3] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h1 : G.submatrix Fin.succ (1 : Fin 4).succAbove = !![G 1 0, G 1 2, G 1 3; G 2 0, G 2 2, G 2 3; G 3 0, G 3 2, G 3 3] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h2 : G.submatrix Fin.succ (2 : Fin 4).succAbove = !![G 1 0, G 1 1, G 1 3; G 2 0, G 2 1, G 2 3; G 3 0, G 3 1, G 3 3] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h3 : G.submatrix Fin.succ (3 : Fin 4).succAbove = !![G 1 0, G 1 1, G 1 2; G 2 0, G 2 1, G 2 2; G 3 0, G 3 1, G 3 2] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-1 : ℝ)^0 * G 0 0 * (G.submatrix Fin.succ (0 : Fin 4).succAbove).det + (
    (-1 : ℝ)^1 * G 0 1 * (G.submatrix Fin.succ (1 : Fin 4).succAbove).det + (
    (-1 : ℝ)^2 * G 0 2 * (G.submatrix Fin.succ (2 : Fin 4).succAbove).det +
    (-1 : ℝ)^3 * G 0 3 * (G.submatrix Fin.succ (3 : Fin 4).succAbove).det)) = _
  rw [h0, h1, h2, h3]
  ring

theorem det_five_entries (G : Matrix (Fin 5) (Fin 5) ℝ) :
    G.det = G 0 0 * det (!![G 1 1, G 1 2, G 1 3, G 1 4; G 2 1, G 2 2, G 2 3, G 2 4; G 3 1, G 3 2, G 3 3, G 3 4; G 4 1, G 4 2, G 4 3, G 4 4])
    - G 0 1 * det (!![G 1 0, G 1 2, G 1 3, G 1 4; G 2 0, G 2 2, G 2 3, G 2 4; G 3 0, G 3 2, G 3 3, G 3 4; G 4 0, G 4 2, G 4 3, G 4 4])
    + G 0 2 * det (!![G 1 0, G 1 1, G 1 3, G 1 4; G 2 0, G 2 1, G 2 3, G 2 4; G 3 0, G 3 1, G 3 3, G 3 4; G 4 0, G 4 1, G 4 3, G 4 4])
    - G 0 3 * det (!![G 1 0, G 1 1, G 1 2, G 1 4; G 2 0, G 2 1, G 2 2, G 2 4; G 3 0, G 3 1, G 3 2, G 3 4; G 4 0, G 4 1, G 4 2, G 4 4])
    + G 0 4 * det (!![G 1 0, G 1 1, G 1 2, G 1 3; G 2 0, G 2 1, G 2 2, G 2 3; G 3 0, G 3 1, G 3 2, G 3 3; G 4 0, G 4 1, G 4 2, G 4 3]) := by
  have h0 : G.submatrix Fin.succ (0 : Fin 5).succAbove = !![G 1 1, G 1 2, G 1 3, G 1 4; G 2 1, G 2 2, G 2 3, G 2 4; G 3 1, G 3 2, G 3 3, G 3 4; G 4 1, G 4 2, G 4 3, G 4 4] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h1 : G.submatrix Fin.succ (1 : Fin 5).succAbove = !![G 1 0, G 1 2, G 1 3, G 1 4; G 2 0, G 2 2, G 2 3, G 2 4; G 3 0, G 3 2, G 3 3, G 3 4; G 4 0, G 4 2, G 4 3, G 4 4] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h2 : G.submatrix Fin.succ (2 : Fin 5).succAbove = !![G 1 0, G 1 1, G 1 3, G 1 4; G 2 0, G 2 1, G 2 3, G 2 4; G 3 0, G 3 1, G 3 3, G 3 4; G 4 0, G 4 1, G 4 3, G 4 4] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h3 : G.submatrix Fin.succ (3 : Fin 5).succAbove = !![G 1 0, G 1 1, G 1 2, G 1 4; G 2 0, G 2 1, G 2 2, G 2 4; G 3 0, G 3 1, G 3 2, G 3 4; G 4 0, G 4 1, G 4 2, G 4 4] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  have h4 : G.submatrix Fin.succ (4 : Fin 5).succAbove = !![G 1 0, G 1 1, G 1 2, G 1 3; G 2 0, G 2 1, G 2 2, G 2 3; G 3 0, G 3 1, G 3 2, G 3 3; G 4 0, G 4 1, G 4 2, G 4 3] := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-1 : ℝ)^0 * G 0 0 * (G.submatrix Fin.succ (0 : Fin 5).succAbove).det + (
    (-1 : ℝ)^1 * G 0 1 * (G.submatrix Fin.succ (1 : Fin 5).succAbove).det + (
    (-1 : ℝ)^2 * G 0 2 * (G.submatrix Fin.succ (2 : Fin 5).succAbove).det + (
    (-1 : ℝ)^3 * G 0 3 * (G.submatrix Fin.succ (3 : Fin 5).succAbove).det +
    (-1 : ℝ)^4 * G 0 4 * (G.submatrix Fin.succ (4 : Fin 5).succAbove).det))) = _
  rw [h0, h1, h2, h3, h4]
  ring

end RefinedBMV.Supporting
