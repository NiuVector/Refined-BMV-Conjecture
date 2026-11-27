import RefinedBMV.FiniteKernels
import Mathlib.LinearAlgebra.Matrix.Notation

/-! An exact two-Cauchy certificate for `(5,3)`. The Gram coefficients were
reconstructed from the cyclic polynomial identity and are checked over `ℚ`. -/

open Matrix
open scoped BigOperators ComplexOrder

namespace RefinedBMV

noncomputable section

private theorem gram_posSemidef {m : ℕ} (G L : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (hG : G = L * diagonal d * Lᵀ) (hd : ∀ i, 0 ≤ d i) :
    (G.map (Rat.castHom ℂ)).PosSemidef := by
  rw [hG, Matrix.map_mul, Matrix.map_mul, transpose_map, diagonal_map (map_zero (Rat.castHom ℂ))]
  have hD : (diagonal fun i => (d i : ℂ)).PosSemidef := Matrix.PosSemidef.diagonal fun i => by
    change 0 ≤ (↑(d i) : ℂ)
    rw [← Complex.ofReal_ratCast, Complex.zero_le_real]
    exact_mod_cast hd i
  have hL : (L.map (Rat.castHom ℂ))ᴴ = (L.map (Rat.castHom ℂ))ᵀ := by
    ext i j
    simp [← Complex.ofReal_ratCast]
  rw [← hL]
  exact hD.mul_mul_conjTranspose_same _

private def gram {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) (f : ℝ → Fin m → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, f u i * (G i j : ℝ) * f v j

private theorem positive_gram {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} (f : ℝ → Fin m → ℝ)
    (hG : (G.map (Rat.castHom ℂ)).PosSemidef) :
    PositiveKernel (fun u v : PosReal => gram G f u.1 v.1) := by
  intro ι _ x
  let V : Matrix (Fin m) ι ℂ := Matrix.of fun k i => (f (x i).1 k : ℂ)
  convert hG.conjTranspose_mul_mul_same V using 1
  ext i j
  simp only [gram, Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ratCast,
    Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.map_apply,
    Complex.star_def, Complex.conj_ofReal, Finset.sum_mul]
  exact Finset.sum_comm

private theorem gram_rescale {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ)
    (f : ℝ → Fin m → ℝ) (a : ℝ → ℝ) (u v : ℝ) :
    gram G (fun t i => a t * f t i) u v = a u * a v * gram G f u v := by
  simp only [gram, Finset.mul_sum]
  congr! 2
  ring

private def gramP : Matrix (Fin 7) (Fin 7) ℚ :=
  !![12, 36, 36, 60, 60, -70, -6;
    36, 368, 269, 319, 314, -544, -139;
    36, 269, 730, -502, 1911, -1395, 388;
    60, 319, -502, 4594, -2790, 800, -715;
    60, 314, 1911, -2790, 6928, -3292, 1170;
    -70, -544, -1395, 800, -3292, 2828, -816;
    -6, -139, 388, -715, 1170, -816, 600]

private def lowerP : Matrix (Fin 7) (Fin 7) ℚ :=
  !![1, 0, 0, 0, 0, 0, 0;
    3, 1, 0, 0, 0, 0, 0;
    3, (161 / 260), 1, 0, 0, 0, 0;
    5, (139 / 260), (-199699 / 135799), 1, 0, 0, 0;
    5, (67 / 130), (428486 / 135799), (-33412927 / 139882016), 1, 0, 0;
    (-35 / 6), (-167 / 130), (-254326 / 135799), (-14923625 / 419646048), (40611362335 / 165427590699), 1, 0;
    (-1 / 2), (-121 / 260), (125041 / 135799), (3934313 / 139882016), (-3642282261 / 18380843411), (-7466063069151 / 13810301376595), 1]

private def diagP : Fin 7 → ℚ :=
  ![12,
    260,
    (135799 / 260),
    (419646048 / 135799),
    (165427590699 / 139882016),
    (13810301376595 / 165427590699),
    (339459968332556 / 13810301376595)]

set_option maxHeartbeats 4000000 in
private theorem gramP_positive : (gramP.map (Rat.castHom ℂ)).PosSemidef :=
  gram_posSemidef gramP lowerP diagP
    (by decide +kernel) (by decide +kernel)

private def gramQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![116, -448, 336, -112;
    -448, 1856, -1396, 464;
    336, -1396, 1060, -352;
    -112, 464, -352, 124]

private def lowerQ : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    (-112 / 29), 1, 0, 0;
    (84 / 29), (-713 / 912), 1, 0;
    (-28 / 29), (1 / 4), (-684 / 2251), 1]

private def diagQ : Fin 4 → ℚ :=
  ![116,
    (3648 / 29),
    (2251 / 228),
    (15956 / 2251)]

set_option maxHeartbeats 4000000 in
private theorem gramQ_positive : (gramQ.map (Rat.castHom ℂ)).PosSemidef :=
  gram_posSemidef gramQ lowerQ diagQ
    (by decide +kernel) (by decide +kernel)

private def gramR : Matrix (Fin 6) (Fin 6) ℚ :=
  !![120, 20, -452, -412, 36, 36;
    20, 12, -64, -104, -8, 4;
    -452, -64, 2032, 1300, -308, -156;
    -412, -104, 1300, 2116, 156, -112;
    36, -8, -308, 156, 152, 20;
    36, 4, -156, -112, 20, 20]

private def lowerR : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 0;
    (1 / 6), 1, 0, 0, 0, 0;
    (-113 / 30), (17 / 13), 1, 0, 0, 0;
    (-103 / 30), (-53 / 13), (-3342 / 5113), 1, 0, 0;
    (3 / 10), (-21 / 13), (-2504 / 5113), (77848 / 270343), 1, 0;
    (3 / 10), (-3 / 13), (-289 / 5113), (-5227 / 270343), (-26049 / 543793), 1]

private def diagR : Fin 6 → ℚ :=
  ![120,
    (26 / 3),
    (20452 / 65),
    (2162744 / 5113),
    (2175172 / 270343),
    (4109248 / 543793)]

set_option maxHeartbeats 4000000 in
private theorem gramR_positive : (gramR.map (Rat.castHom ℂ)).PosSemidef :=
  gram_posSemidef gramR lowerR diagR
    (by decide +kernel) (by decide +kernel)

private def p (t : ℝ) : Fin 7 → ℝ :=
  ![1 + t + t ^ 2 + 3 * t ^ 3, t ^ 4, t ^ 5, t ^ 6, t ^ 7, t ^ 8, t ^ 9]
private def q (t : ℝ) : Fin 4 → ℝ := ![t ^ 4, t ^ 5, t ^ 6, t ^ 7]
private def r (t : ℝ) : Fin 6 → ℝ := ![t ^ 3, t ^ 4, t ^ 5, t ^ 6, t ^ 7, t ^ 8]

private def a (t : ℝ) : ℝ := (1 - t) / (t ^ 5 * (1 + t ^ 3))
private def b (t : ℝ) : ℝ := (1 - t) / (t ^ 5 * (1 + t))

private def k5 (u v : ℝ) : ℝ := (1 / 84) *
  (gram gramP (fun t i => a t * p t i) u v +
    gram gramQ (fun t i => b t * q t i) u v * harmonic u v +
    gram gramR (fun t i => a t * r t i) u v * harmonic (u ^ 3) (v ^ 3))

private theorem k5_positive : PositiveKernel (fun u v : PosReal => k5 u.1 v.1) :=
  (((positive_gram (fun t i => a t * p t i) gramP_positive).add
    ((positive_gram (fun t i => b t * q t i) gramQ_positive).mul positive_harmonic)).add
    ((positive_gram (fun t i => a t * r t i) gramR_positive).mul
      (positive_harmonic.pullback fun u : PosReal => (⟨u.1 ^ 3, pow_pos u.2 _⟩ : PosReal)))).scale
    (by norm_num : (0 : ℝ) ≤ 1 / 84)

set_option maxHeartbeats 20000000 in
private theorem k5_cyclic (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    k5 (y / x) (z / x) + k5 (z / y) (x / y) + k5 (x / z) (y / z) =
      3 * finiteWeight 5 x y z := by
  simp only [k5, gram_rescale]
  norm_num [gram, gramP, gramQ, gramR, p, q, r, a, b, harmonic, finiteWeight, homogeneous,
    Fin.sum_univ_succ, Finset.sum_range_succ, div_pow]
  field_simp (disch := positivity)
  ring

/-- The independently reconstructed exact `(5,3)` certificate. -/
def certificateFive : FiniteCertificate 5 where
  kernel u v := k5 u.1 v.1
  positive := k5_positive
  cyclic x y z := k5_cyclic x.1 y.1 z.1 x.2 y.2 z.2

end

end RefinedBMV
