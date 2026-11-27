import RefinedBMV.HighOrders
import RefinedBMV.Supporting.TracePower
import RefinedBMV.Supporting.Trotter
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-! The evenly-spread word bound implies the exponential trace lower bound by a
    dyadic trace-power comparison and the Lie–Trotter limit. -/

open Matrix NormedSpace Filter
open scoped MatrixOrder ComplexOrder Topology Matrix.Norms.Operator

namespace RefinedBMV

noncomputable section

variable {d : ℕ}

local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private theorem exp_conjUnitary (U : unitary Mat) (X : Mat) :
    exp (Unitary.conjStarAlgAut ℂ _ U X) = Unitary.conjStarAlgAut ℂ _ U (exp X) := by
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star]
  rw [show ((star U : unitary Mat) : Mat) = (U : Mat)⁻¹ from (Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)).symm]
  exact Matrix.exp_conj _ _ (Unitary.isUnit_coe (U := U))

private theorem spectral_exp (H : Mat) (hH : H.IsHermitian) :
    exp H = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagReal (fun i => Real.exp (hH.eigenvalues i))) := by
  nth_rw 1 [hH.spectral_theorem]
  rw [exp_conjUnitary, Matrix.exp_diagonal]
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  rw [Pi.exp_def]
  change NormedSpace.exp (hH.eigenvalues i : ℂ) = (Real.exp (hH.eigenvalues i) : ℂ)
  rw [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem exp_posDef (H : Mat) (hH : H.IsHermitian) : (exp H).PosDef := by
  have hdiag : (diagReal (fun i => Real.exp (hH.eigenvalues i))).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (Real.exp_pos _).le
  have hpsd : (exp H).PosSemidef := by
    rw [spectral_exp H hH, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
    exact hdiag.mul_mul_conjTranspose_same _
  exact hpsd.posDef_iff_isUnit.mpr (Matrix.isUnit_exp H)

private theorem hermitian_smul (H : Mat) (hH : H.IsHermitian) (r : ℝ) : (r • H).IsHermitian := by
  change (r • H)ᴴ = r • H
  rw [conjTranspose_smul, hH.eq]
  simp

private theorem trace_im_zero {A : Mat} (hA : A.IsHermitian) : (trace A).im = 0 := by
  apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
  change star (trace A) = trace A
  rw [← trace_conjTranspose, hA.eq]

private theorem trace_mul_pow_im_zero {A B : Mat} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (m : ℕ) : (trace ((A * B) ^ m)).im = 0 := by
  apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
  change star (trace _) = _
  rw [← trace_conjTranspose, conjTranspose_pow, conjTranspose_mul, hA.eq, hB.eq]
  cases m with
  | zero => rfl
  | succ m =>
    have he : (B * A) ^ m * B = B * (A * B) ^ m := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, pow_succ]
        calc
          _ = ((B * A) ^ m * B) * (A * B) := by noncomm_ring
          _ = _ := by rw [ih, mul_assoc]
    rw [pow_succ, pow_succ', ← mul_assoc, he, trace_mul_comm, ← mul_assoc]

/-- The real spectral power of an exponential of a Hermitian matrix. -/
theorem spectralPower_exp (H : Mat) (hH : H.IsHermitian) (r : ℝ) :
    spectralPower (exp H) r = exp (r • H) := by
  have h₁ : exp H = cfc Real.exp H := by
    rw [hH.cfc_eq]
    exact spectral_exp H hH
  have h₂ : exp (r • H) = cfc (fun x : ℝ => Real.exp (r * x)) H := by
    have hr : cfc (fun x : ℝ => r * x) H = r • H := cfc_const_mul_id r H hH
    have h : exp (r • H) = cfc Real.exp (r • H) := by
      rw [(hermitian_smul H hH r).cfc_eq]
      exact spectral_exp _ (hermitian_smul H hH r)
    have hc := cfc_comp' (p := IsSelfAdjoint) Real.exp (fun x : ℝ => r*x) H
      Real.continuous_exp.continuousOn (by fun_prop) (show IsSelfAdjoint H from hH)
    rw [hc, hr, ← h]
  have hg : ContinuousOn (fun x : ℝ => x ^ r) (Real.exp '' spectrum ℝ H) := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := hx
    exact (Real.continuousAt_rpow_const _ r (Or.inl (Real.exp_pos _).ne')).continuousWithinAt
  unfold spectralPower
  have hc := cfc_comp' (p := IsSelfAdjoint) (fun x : ℝ => x ^ r) Real.exp H hg
    Real.continuous_exp.continuousOn (show IsSelfAdjoint H from hH)
  rw [h₁, h₂, ← hc]
  congr 1
  funext x
  change Real.exp x ^ r = Real.exp (r * x)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]

section NonemptyDimension
variable [NeZero d]

private def dyadicTrace (r : ℕ) (H K : Mat) (j : ℕ) : ℝ :=
  (trace ((exp (((2 : ℝ) ^ j)⁻¹ • H) * exp (((2 : ℝ) ^ j)⁻¹ • K)) ^ (r * 2 ^ j))).re

omit [NeZero d] in
private theorem dyadicTrace_step (r : ℕ) (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (j : ℕ) : dyadicTrace r H K (j + 1) ≤ dyadicTrace r H K j := by
  let s : ℝ := ((2 : ℝ) ^ (j + 1))⁻¹
  have hs (M : Mat) : (2 : ℕ) • (s • M) = ((2 : ℝ) ^ j)⁻¹ • M := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [s]
    rw [pow_succ, _root_.mul_inv_rev]
    norm_num [← mul_assoc]
  have h := Supporting.trace_mul_two_pow_le (exp (s • H)) (exp (s • K))
    (exp_posDef _ (hermitian_smul H hH s)) (exp_posDef _ (hermitian_smul K hK s)) (r * 2 ^ j)
  rw [← Matrix.exp_nsmul, ← Matrix.exp_nsmul, hs, hs] at h
  rw [show 2 * (r * 2 ^ j) = r * 2 ^ (j + 1) by rw [pow_succ]; ring] at h
  exact h

private theorem dyadicTrace_tendsto {r : ℕ} (hr : 0 < r) (H K : Mat) :
    Tendsto (dyadicTrace r H K) atTop (𝓝 (trace (exp ((r : ℝ) • H + (r : ℝ) • K))).re) := by
  have hc : Continuous (fun A : Mat => (trace A).re) :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  have ht : Tendsto (fun j : ℕ => r * 2 ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide)).const_mul_atTop' hr
  have hh := hc.continuousAt.tendsto.comp
    ((NormedSpace.trotter_product ((r : ℝ) • H) ((r : ℝ) • K)).comp ht)
  have hscalar (j : ℕ) : ((↑(r * 2 ^ j : ℕ) : ℝ)⁻¹ * r) = ((2 : ℝ) ^ j)⁻¹ := by
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr
    push_cast
    field_simp (disch := positivity)
  convert hh using 1
  funext j
  unfold dyadicTrace
  change _ =
    (trace ((exp (((↑(r * 2^j : ℕ) : ℝ)⁻¹) • ((r : ℝ) • H)) *
      exp (((↑(r * 2^j : ℕ) : ℝ)⁻¹) • ((r : ℝ) • K))) ^ (r * 2^j))).re
  rw [smul_smul, smul_smul, hscalar]

/-- The exponential trace is bounded by the trace of the balanced product. -/
theorem exponential_trace_le_pow {r : ℕ} (hr : 0 < r) (H K : Mat)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (trace (exp ((r : ℝ) • H + (r : ℝ) • K))).re ≤
      (trace ((exp H * exp K) ^ r)).re := by
  have h := antitone_nat_of_succ_le (dyadicTrace_step r H K hH hK)
  simpa [dyadicTrace] using
    le_of_tendsto' (dyadicTrace_tendsto hr H K) (fun j => h (Nat.zero_le j))

end NonemptyDimension

private theorem exponential_trace_le_spread_re (n m : ℕ) (hm : 0 < m) (H K : Mat)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (trace (exp ((n : ℝ) • H + (m : ℝ) • K))).re ≤
      (trace ((spectralPower (exp H) (n / m) * exp K) ^ m)).re := by
  by_cases hd : d = 0
  · subst d
    simp [trace_eq_zero_of_isEmpty]
  letI : NeZero d := ⟨hd⟩
  rw [spectralPower_exp H hH]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := exponential_trace_le_pow hm ((n / m : ℝ) • H) K
    (hermitian_smul H hH _) hK
  rw [smul_smul, show (m : ℝ) * (n / m) = n by field_simp [hm'.ne']] at hh
  exact hh

/-- The exponential lower bound compares with the evenly-spread trace. -/
theorem exponential_trace_le_spread (n m : ℕ) (hm : 0 < m) (H K : Mat)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((n : ℝ) • H + (m : ℝ) • K)) ≤
      trace ((spectralPower (exp H) (n / m) * exp K) ^ m) := by
  refine Complex.le_def.mpr ⟨exponential_trace_le_spread_re n m hm H K hH hK, ?_⟩
  rw [spectralPower_exp H hH, trace_im_zero ((hermitian_smul H hH _).add (hermitian_smul K hK _)).exp,
    trace_mul_pow_im_zero (hermitian_smul H hH _).exp hK.exp]

/-- The exponential refined BMV lower bound for the proved cubic cases. -/
theorem exponential_m3_one_through_six (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 6)
    (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((n : ℝ) • H + (3 : ℝ) • K)) ≤ wordAverage n (exp H) (exp K) := by
  exact (exponential_trace_le_spread n 3 (by decide) H K hH hK).trans <|
    even_word_m3_one_through_six n hn hn' _ _
      (exp_posDef H hH).posSemidef (exp_posDef K hK).posSemidef

/-- The cubic exponential lower bound from the analytic scalar-sign hypothesis. -/
theorem exponential_m3_of_mixedDensity (n : ℕ) (hn : 0 < n)
    (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hρ : MixedDensityNonneg ((n : ℝ)⁻¹)) :
    trace (exp ((n : ℝ) • H + (3 : ℝ) • K)) ≤ wordAverage n (exp H) (exp K) :=
  (exponential_trace_le_spread n 3 (by decide) H K hH hK).trans <|
    even_word_m3_of_mixedDensity n hn _ _ (exp_posDef H hH).posSemidef (exp_posDef K hK).posSemidef hρ

/-- The exponential refined BMV lower bound in the seven proved quartic cases. -/
theorem exponential_m4_family (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 8) (h₇ : n ≠ 7)
    (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((n : ℝ) • H + (4 : ℝ) • K)) ≤ quarticWordAverage n (exp H) (exp K) :=
  (exponential_trace_le_spread n 4 (by decide) H K hH hK).trans <|
    even_word_m4_family n hn hn' h₇ _ _ (exp_posDef H hH).posSemidef hK.exp

end

end RefinedBMV
