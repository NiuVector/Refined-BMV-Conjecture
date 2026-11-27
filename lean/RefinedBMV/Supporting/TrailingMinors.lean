import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! A Sylvester criterion using trailing minors, with the last determinant
allowed to vanish. -/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace RefinedBMV.Supporting

noncomputable section

def tailMatrix {n : ℕ} (G : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  G.submatrix Fin.succ Fin.succ

def trailingMinorsPositive : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | n+1, G => 0 < G.det ∧ trailingMinorsPositive n (tailMatrix G)

def properTrailingMinorsPositive : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → Prop
  | 0, _ => True
  | n+1, G => trailingMinorsPositive n (tailMatrix G)

/-- Every proper trailing principal minor is positive and the full determinant
is nonnegative. This is enough for positive semidefiniteness. -/
theorem posSemidef_of_trailing_minors {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.IsHermitian) (hd : 0 ≤ G.det)
    (hproper : properTrailingMinorsPositive n G) :
    G.PosSemidef := by
  induction n with
  | zero =>
    exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hG (fun x => by simp [dotProduct])
  | succ n ih =>
    let D := tailMatrix G
    have hDdet : 0 < D.det := by
      cases n with
      | zero => simp
      | succ n => exact hproper.1
    have hDproper : properTrailingMinorsPositive n D := by
      cases n with
      | zero => trivial
      | succ n => exact hproper.2
    letI : Invertible D := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hDdet.ne')
    have hD : D.PosDef := (ih (hG.submatrix Fin.succ) hDdet.le hDproper).posDef_iff_isUnit.mpr (isUnit_of_invertible D)
    let e : Fin 1 ⊕ Fin n ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n))
    have hl (i : Fin 1) : e (Sum.inl i) = 0 := by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    have hr (i : Fin n) : e (Sum.inr i) = i.succ := by
      apply Fin.ext
      simp [e]
    let A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => G 0 0)
    let B : Matrix (Fin 1) (Fin n) ℝ := Matrix.of (fun _ j => G 0 j.succ)
    have hrepr : G.submatrix e e = fromBlocks A B Bᴴ D := by
      ext i j
      rcases i with i|i <;> rcases j with j|j
      · simp [A, hl]
      · simp [B, hl, hr]
      · simpa only [submatrix_apply, hr, hl, fromBlocks_apply₂₁, conjTranspose_apply, B, of_apply,
          star_trivial] using (hG.apply i.succ 0).symm
      · simp [D, tailMatrix, hr]
    have hminor : 0 ≤ (A - B * D⁻¹ * Bᴴ).det := by
      rw [← Matrix.det_submatrix_equiv_self e G, hrepr, Matrix.det_fromBlocks₂₂,
        invOf_eq_nonsing_inv] at hd
      exact nonneg_of_mul_nonneg_right hd hDdet
    have hscalar {M : Matrix (Fin 1) (Fin 1) ℝ} (h : 0 ≤ M.det) : M.PosSemidef := by
      have hm : M = diagonal (fun _ => M 0 0) := by
        ext i j
        have hi : i = 0 := Subsingleton.elim _ _
        have hj : j = 0 := Subsingleton.elim _ _
        simp [hi, hj]
      rw [det_unique] at h
      exact hm ▸ Matrix.PosSemidef.diagonal (fun _ => h)
    apply (Matrix.posSemidef_submatrix_equiv e).mp
    rw [hrepr]
    exact (Matrix.PosDef.fromBlocks₂₂ A B hD).mpr (hscalar hminor)

/-- Real Gram matrices remain PSD after complexification. -/
theorem posSemidef_complexify {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosSemidef) :
    (G.map Complex.ofReal).PosSemidef := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hG)
  change G = Lᴴ * L at hL
  change (G.map (Complex.ofRealHom : ℝ →+* ℂ)).PosSemidef
  have hstar : Lᴴ.map (Complex.ofRealHom : ℝ →+* ℂ) = (L.map Complex.ofReal)ᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hL, Matrix.map_mul, hstar]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end

end RefinedBMV.Supporting
