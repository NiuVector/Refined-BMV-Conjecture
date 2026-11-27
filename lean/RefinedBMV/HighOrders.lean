import RefinedBMV.Results
import RefinedBMV.MixedDerivative
import RefinedBMV.Supporting.RectangleKernel

/-! A finite proof of the kernel reduction, where the open-rectangle sign of
the mixed derivative is the only hypothesis. -/

open Set
open scoped ComplexOrder

namespace RefinedBMV

noncomputable section

/-- All open upper triangles must have this mixed-derivative sign. -/
def MixedDensityNonneg (ε : ℝ) : Prop :=
  ∀ s v : ℝ, 0 < s → 0 < v → 0 ≤ mixedDensity ε s v

private theorem gauged_rectangle {ε l u v w : ℝ} (hε : 0 ≤ ε)
    (hρ : MixedDensityNonneg ε)
    (hl : 0 < l) (hlu : l ≤ u) (huv : u ≤ v) (hvw : v ≤ w) :
    0 ≤ (gaugedResidual ε u v - gaugedResidual ε l v) -
      (gaugedResidual ε u w - gaugedResidual ε l w) := by
  let K := gaugedResidual ε
  let P (x t : ℝ) := deriv (K x) t
  have hu := hl.trans_le hlu
  have hsub {x : ℝ} (hx : x ≤ v) : Icc v w ⊆ Ici x :=
    fun _ h => hx.trans h.1
  have hcts : ContinuousOn (fun t => K u t - K l t) (Icc v w) :=
    ((gaugedResidual_continuousOn hε hu).mono (hsub huv)).sub
      ((gaugedResidual_continuousOn hε hl).mono (hsub (hlu.trans huv)))
  have hd (t : ℝ) (ht : t ∈ interior (Icc v w)) :
      HasDerivAt (fun y => K u y - K l y) (P u t - P l t) t := by
    rw [interior_Icc] at ht
    exact (gaugedResidual_partial₂ hε hu (huv.trans_lt ht.1)).1.sub
      (gaugedResidual_partial₂ hε hl ((hlu.trans huv).trans_lt ht.1)).1
  have ha : AntitoneOn (fun t => K u t - K l t) (Icc v w) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc v w) hcts
      (fun t ht => (hd t ht).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have hdiff (x : ℝ) (hx : x ∈ Icc l u) : DifferentiableAt ℝ (fun x => P x t) x :=
      (gaugedResidual_partial₂ hε (hl.trans_le hx.1) ((hx.2.trans huv).trans_lt ht.1)).2
    have hanti : AntitoneOn (fun x => P x t) (Icc l u) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc l u)
        (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
        (fun x hx => (hdiff x (interior_subset hx)).differentiableWithinAt) ?_
      intro x hx
      have hx' := interior_subset hx
      have hxt := (hx'.2.trans huv).trans_lt ht.1
      have hs := hρ x (t-x) (hl.trans_le hx'.1) (sub_pos.mpr hxt)
      unfold mixedDensity at hs
      rw [show x+(t-x)=t by ring] at hs
      exact neg_nonneg.mp hs
    exact sub_nonpos.mpr (hanti ⟨le_rfl,hlu⟩ ⟨hlu,le_rfl⟩ hlu)
  exact sub_nonneg.mpr (ha ⟨le_rfl,hvw⟩ ⟨hvw,le_rfl⟩ hvw)

/-- The positive block is a positive kernel once the scalar sign is proved.
The proof uses only exact finite rectangle differences and the two endpoint limits. -/
theorem residual_positive_of_mixedDensity {ε : ℝ} (hε : 0 ≤ ε)
    (hρ : MixedDensityNonneg ε) :
    PositiveKernel (fun s t : PosReal => residual ε s.1 t.1) := by
  have hrect : ∀ ⦃l u v w : ℝ⦄, 0 < l → l ≤ u → u ≤ v → v ≤ w →
      0 ≤ (gaugedResidual ε u v - gaugedResidual ε l v) -
        (gaugedResidual ε u w - gaugedResidual ε l w) :=
    fun _ _ _ _ => gauged_rectangle hε hρ
  have ⟨hn, hl, hr⟩ := Supporting.edge_inequalities_of_rectangle_limits
    (K := gaugedResidual ε) (a := 0) (fun l u v w hl hlu huv hvw => @hrect l u v w hl hlu huv hvw)
    (fun _ ht => gaugedResidual_tendsto_left hε ht) (fun _ hs => gaugedResidual_tendsto_top hε hs)
  have hg : PositiveKernel (fun s t : PosReal => gaugedResidual ε s.1 t.1) := by
    intro ι _ x
    convert Supporting.kernel_gram_posSemidef_of_rectangle hn hl hr
      (fun l u v w hl hlu huv hvw => @hrect l u v w hl hlu huv hvw)
      (fun i => (x i).1) (fun i => (x i).2) using 1
    ext i j
    rcases le_total (x i).1 (x j).1 with h | h
    · simp [min_eq_left h, max_eq_right h]
    · simp [min_eq_right h, max_eq_left h, gaugedResidual_symm ε (x i).1 (x j).1]
  have hu := hg.mul (PositiveKernel.rankOne (fun x : PosReal => Real.exp (x.1/6)))
  convert hu using 1
  ext s t
  unfold gaugedResidual
  have h : ∀ a b c d : ℝ, a * b * (c * d) = (a * c * d) * b := by intros; ring
  rw [h, ← Real.exp_add, ← Real.exp_add]
  rw [show -(s.1+t.1)/6 + s.1/6 + t.1/6 = 0 by ring, Real.exp_zero]
  ring

/-- At any finite order, the scalar sign at `ε = 1/n` implies the full PSD
evenly-spread matrix inequality, including singular inputs. -/
theorem even_word_m3_of_mixedDensity {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hρ : MixedDensityNonneg ((n : ℝ)⁻¹)) :
    Matrix.trace ((spectralPower A (n/3) * B)^3) ≤ wordAverage n A B := by
  have hε : 0 ≤ (n : ℝ)⁻¹ := by positivity
  exact even_word_m3_of_residual n hn A B hA hB
    (fun _ hx => (lowerDiagonal_pos hε hx).le) (residual_positive_of_mixedDensity hε hρ)

/-- The entire finite cubic family follows from the sign on `0 ≤ ε ≤ 1/7`. -/
theorem even_word_m3_of_uniform_mixedDensity {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (A B : Matrix ι ι ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hρ : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/7 → MixedDensityNonneg ε) :
    Matrix.trace ((spectralPower A (n/3) * B)^3) ≤ wordAverage n A B := by
  by_cases h : n ≤ 6
  · exact even_word_m3_one_through_six n hn h A B hA hB
  · have hnR : (7 : ℝ) ≤ n := by exact_mod_cast (show 7 ≤ n by omega)
    exact even_word_m3_of_mixedDensity n hn A B hA hB
      (hρ _ (by positivity) (by rw [one_div]; exact inv_anti₀ (by norm_num) hnR))

/-- The Duhamel endpoint of the scalar-sign reduction. -/
theorem duhamel_spectral_of_mixedDensity {ι : Type} [Fintype ι] (eigen : ι → ℝ)
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef) (hρ : MixedDensityNonneg 0) :
    0 ≤ cycleSum (fun i j k => familyWeight 0 (eigen i) (eigen j) (eigen k)) X :=
  duhamel_spectral_nonneg eigen X hX (residual_positive_of_mixedDensity le_rfl hρ)

end

end RefinedBMV
