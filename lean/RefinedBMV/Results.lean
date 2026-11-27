import RefinedBMV.Words
import RefinedBMV.OrderFive
import RefinedBMV.UniformFinite
import RefinedBMV.QuarticWords
import RefinedBMV.QuarticFamily

/-! Main theorems on cubic and quartic word averages. -/

open scoped ComplexOrder
open Matrix

namespace RefinedBMV

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The evenly-spread word inequality `(Eₙ,₃)` for every `1 ≤ n ≤ 6`, for
    all finite-dimensional complex Hermitian positive semidefinite matrices. -/
theorem even_word_m3_one_through_six (n : ℕ) (h₁ : 1 ≤ n) (h₆ : n ≤ 6)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((spectralPower A (n / 3) * B) ^ 3) ≤ wordAverage n A B := by
  interval_cases n
  · exact even_word_of_certificate_matrix certificateOne A B hA hB
  · exact even_word_of_certificate_matrix certificateTwo A B hA hB
  · exact even_word_of_certificate_matrix certificateThree A B hA hB
  · exact even_word_of_certificate_matrix certificateFour A B hA hB
  · exact even_word_of_certificate_matrix certificateFive A B hA hB
  · exact even_word_of_certificate_matrix certificateSix A B hA hB

omit [DecidableEq ι] in
/-- The Duhamel spectral gap is nonnegative given the PSD certificate for the
    positive block at `ε = 0`. Its rank-one negative block is proved positive here. -/
theorem duhamel_spectral_nonneg (eigen : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (hres : PositiveKernel (fun s t : PosReal => residual 0 s.1 t.1)) :
    0 ≤ cycleSum (fun i j k => familyWeight 0 (eigen i) (eigen j) (eigen k)) X :=
  family_cycle_nonneg 0 eigen X hX (fun _ h => (lowerDiagonal_duhamel_pos h).le) hres

/-- Any finite order in the uniform family follows from the two analytic
    positivity hypotheses at the corresponding reciprocal integer. -/
theorem even_word_m3_of_residual (n : ℕ) (hn : 0 < n)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hdiag : ∀ x, 0 < x → 0 ≤ lowerDiagonal ((n : ℝ)⁻¹) x)
    (hres : PositiveKernel (fun s t : PosReal => residual ((n : ℝ)⁻¹) s.1 t.1)) :
    trace ((spectralPower A (n / 3) * B) ^ 3) ≤ wordAverage n A B :=
  even_word_of_certificate_matrix (certificate_of_residual n hn hdiag hres) A B hA hB

/-- The first three evenly-spread quartic inequalities in the updated manuscript. -/
theorem even_word_m4_one_through_three (n : ℕ) (h₁ : 1 ≤ n) (h₃ : n ≤ 3)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    trace ((spectralPower A (n / 4) * B) ^ 4) ≤ quarticWordAverage n A B := by
  interval_cases n
  · exact quartic_word_of_certificate quarticCertificateOne (by decide) (by decide) A B hA hB
  · exact quartic_word_of_certificate quarticCertificateTwo (by decide) (by decide) A B hA hB
  · exact quartic_word_of_certificate quarticCertificateThree (by decide) (by decide) A B hA hB

/-- The seven quartic word inequalities in the updated manuscript, allowing
indefinite Hermitian `B` and singular PSD `A`. -/
theorem even_word_m4_family (n : ℕ) (h₁ : 1 ≤ n) (h₈ : n ≤ 8) (h₇ : n ≠ 7)
    (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    trace ((spectralPower A (n / 4) * B)^4) ≤ quarticWordAverage n A B := by
  by_cases h₃ : n ≤ 3
  · exact even_word_m4_one_through_three n h₁ h₃ A B hA hB
  have h : n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 8 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact quartic_word_of_certificate quarticCertificateFour (by decide) (by decide) A B hA hB
  · exact quartic_word_of_certificate quarticCertificateFive (by decide) (by decide) A B hA hB
  · exact quartic_word_of_certificate quarticCertificateSix (by decide) (by decide) A B hA hB
  · exact quartic_word_of_certificate quarticCertificateEight (by decide) (by decide) A B hA hB

/-- The principal new result `(E₄,₄)`, for arbitrary Hermitian `B` and positive
    semidefinite `A`, in every finite dimension. -/
theorem even_word_44 (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    trace ((A * B) ^ 4) ≤ quarticWordAverage 4 A B := by
  have h := quartic_word_of_certificate quarticCertificateFour (by decide) (by decide) A B hA hB
  have hpow : spectralPower A 1 = A := by
    unfold spectralPower
    simp only [Real.rpow_one]
    exact cfc_id ℝ A hA.isHermitian
  norm_num at h
  simpa only [hpow] using h

/-- The fourth trace power is invariant under the change of variables `X = TBT`,
    where `A = T²`. This identity also holds when `T` is singular. -/
theorem quartic_trace_congruence (T B : Matrix ι ι ℂ) :
    trace (((T ^ 2) * B) ^ 4) = trace ((T * B * T) ^ 4) := by
  let Q := T * B
  let P := Q * T * Q * T * Q * T * Q
  have h₁ : ((T ^ 2) * B) ^ 4 = T * P := by unfold P Q; noncomm_ring
  have h₂ : (T * B * T) ^ 4 = P * T := by unfold P Q; noncomm_ring
  rw [h₁, h₂, trace_mul_comm]

/-- The manuscript's `(4,4)` inequality written directly using `X = TBT`. -/
theorem even_word_44_congruence (T B : Matrix ι ι ℂ) (hT : T.PosSemidef) (hB : B.IsHermitian) :
    trace ((T * B * T) ^ 4) ≤ quarticWordAverage 4 (T ^ 2) B := by
  rw [← quartic_trace_congruence]
  exact even_word_44 _ _ (hT.pow 2) hB

end RefinedBMV
