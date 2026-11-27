import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Positive kernels and the all-dimension cyclic trace reduction. -/

open scoped BigOperators ComplexOrder Kronecker
open Matrix MeasureTheory

namespace RefinedBMV

noncomputable section

/-- Positive semidefiniteness on every finite list of points, over complex scalars. -/
def PositiveKernel {α : Type} (K : α → α → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → α),
    (Matrix.of fun i j => (K (x i) (x j) : ℂ)).PosSemidef

namespace PositiveKernel

variable {α β : Type} {K L : β → β → ℝ}

theorem pullback (hK : PositiveKernel K) (f : α → β) :
    PositiveKernel (fun a b => K (f a) (f b)) :=
  fun ι _ x => hK ι (f ∘ x)

theorem add (hK : PositiveKernel K) (hL : PositiveKernel L) :
    PositiveKernel (fun a b => K a b + L a b) := by
  intro ι _ x
  convert (hK ι x).add (hL ι x) using 1
  ext i j
  simp

theorem scale (hK : PositiveKernel K) {c : ℝ} (hc : 0 ≤ c) :
    PositiveKernel (fun a b => c * K a b) := by
  intro ι _ x
  convert (hK ι x).smul hc using 1
  ext i j
  simp [Algebra.smul_def]

theorem mul (hK : PositiveKernel K) (hL : PositiveKernel L) :
    PositiveKernel (fun a b => K a b * L a b) := by
  intro ι _ x
  convert ((hK ι x).kronecker (hL ι x)).submatrix (fun i => (i, i)) using 1
  ext i j
  simp

theorem rankOne (f : α → ℝ) : PositiveKernel (fun a b => f a * f b) := by
  intro ι _ x
  classical
  let V : Matrix ι Unit ℂ := Matrix.of fun i _ => (f (x i) : ℂ)
  convert Matrix.posSemidef_self_mul_conjTranspose V using 1
  ext i j
  simp [V, Matrix.mul_apply]

/-- An integral of integrable rank-one kernels is positive semidefinite. -/
theorem integral {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → α → ℝ)
    (hf : ∀ a b, Integrable (fun ω => f ω a * f ω b) μ) :
    PositiveKernel (fun a b => ∫ ω, f ω a * f ω b ∂μ) := by
  intro ι _ x
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · ext i j
    simp [mul_comm]
  let p (i j : ι) (ω : Ω) : ℂ := star (z i) * (↑(f ω (x i) * f ω (x j)) : ℂ) * z j
  have hp (i j) : Integrable (p i j) μ :=
    (((hf (x i) (x j)).ofReal).const_mul _).mul_const _
  have hsum : Integrable (fun ω => ∑ i, ∑ j, p i j ω) μ :=
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hp i j
  have hpoint (ω) : 0 ≤ ∑ i, ∑ j, p i j ω := by
    simpa only [p, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, mul_assoc] using (rankOne (f ω) ι x).dotProduct_mulVec_nonneg z
  have heq : (star z ⬝ᵥ ((Matrix.of fun i j =>
      (↑(∫ ω, f ω (x i) * f ω (x j) ∂μ) : ℂ)) *ᵥ z)) =
      ∫ ω, ∑ i, ∑ j, p i j ω ∂μ := by
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hp i j)]
    simp_rw [integral_finset_sum _ (fun j _ => hp _ j)]
    simp only [p, integral_mul_const,
      integral_const_mul, integral_complex_ofReal, dotProduct, mulVec,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [heq, Complex.nonneg_iff]
  change 0 ≤ RCLike.re (∫ ω, ∑ i, ∑ j, p i j ω ∂μ) ∧
    0 = RCLike.im (∫ ω, ∑ i, ∑ j, p i j ω ∂μ)
  rw [← integral_re hsum, ← integral_im hsum]
  exact ⟨integral_nonneg fun ω => (Complex.nonneg_iff.mp (hpoint ω)).1,
    by
      have him : (fun ω => RCLike.im (∑ i, ∑ j, p i j ω)) = (0 : Ω → ℝ) :=
        funext fun ω => (Complex.nonneg_iff.mp (hpoint ω)).2.symm
      rw [him]
      exact (integral_zero Ω ℝ).symm⟩

/-- The Cauchy kernel `1/(p(a)+p(b))` is the Gram integral of decaying exponentials. -/
theorem cauchy (p : α → ℝ) (hp : ∀ a, 0 < p a) :
    PositiveKernel (fun a b => 1 / (p a + p b)) := by
  have hexp (a b : α) (t : ℝ) :
      Real.exp (-p a * t) * Real.exp (-p b * t) =
      Real.exp (-(p a + p b) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := PositiveKernel.integral (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun t a => Real.exp (-p a * t)) (fun a b => by
      simp_rw [hexp a b]
      exact integrableOn_exp_mul_Ioi (by linarith [hp a, hp b]) 0)
  convert h using 1
  ext a b
  simp_rw [hexp a b]
  rw [integral_exp_mul_Ioi (a := -(p a + p b)) (by linarith [hp a, hp b]),
    mul_zero, Real.exp_zero, div_neg, ← neg_div, neg_neg]

end PositiveKernel

variable {ι : Type} [Fintype ι]

/-- The weighted sum of cyclic products of three entries of a matrix. -/
def cycleSum (W : ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (W i j k : ℂ) * X i j * X j k * X k i

private theorem cycleSum_rotate (W : ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) :
    cycleSum (fun i j k => W j k i) X = cycleSum W X := by
  classical
  unfold cycleSum
  calc
    _ = ∑ j, ∑ i, ∑ k, (W j k i : ℂ) * X i j * X j k * X k i := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, (W j k i : ℂ) * X i j * X j k * X k i := by
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      congr! 3
      ring

private theorem cycleSum_add (W V : ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) :
    cycleSum (fun i j k => W i j k + V i j k) X = cycleSum W X + cycleSum V X := by
  simp [cycleSum, add_mul, Finset.sum_add_distrib]

theorem cycleSum_scale (c : ℝ) (W : ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) :
    cycleSum (fun i j k => c * W i j k) X = (c : ℂ) * cycleSum W X := by
  simp [cycleSum, mul_assoc, Finset.mul_sum]

/-- The cyclic identity in both manuscripts transfers positive kernel matrices to a
    nonnegative cyclic sum over every finite complex Hermitian PSD matrix. -/
theorem cycleSum_nonneg_of_cyclic
    (W K : ι → ι → ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (hK : ∀ i, (Matrix.of fun j k => (K i j k : ℂ)).PosSemidef)
    (hcyc : ∀ i j k, K i j k + K j k i + K k i j = 3 * W i j k) :
    0 ≤ cycleSum W X := by
  classical
  have hrot := cycleSum_rotate K X
  have hrot₂ : cycleSum (fun i j k => K k i j) X = cycleSum K X :=
    (cycleSum_rotate (fun i j k => K j k i) X).trans hrot
  have hEq : cycleSum (fun i j k => K i j k + K j k i + K k i j) X =
      cycleSum (fun i j k => 3 * W i j k) X := by
    exact congrArg (fun V => cycleSum V X) (funext fun i => funext fun j => funext fun k => hcyc i j k)
  rw [cycleSum_add, cycleSum_add, hrot, hrot₂, cycleSum_scale] at hEq
  norm_num at hEq
  have hsum : cycleSum W X = cycleSum K X := by
    linear_combination -hEq / 3
  rw [hsum]
  unfold cycleSum
  apply Finset.sum_nonneg
  intro i _
  let M : Matrix ι ι ℂ := Matrix.of fun j k => (K i j k : ℂ)
  let v (j : ι) : ℂ := X j i
  have h := ((hK i).kronecker hX).submatrix (fun j => (j, j))
  have hstar (j : ι) : star (X j i) = X i j := by
    exact congrFun (congrFun hX.isHermitian.eq i) j
  simpa [M, v, dotProduct, mulVec, Matrix.submatrix_apply, Matrix.kronecker_apply,
    Finset.mul_sum, hstar, mul_assoc, mul_left_comm, mul_comm] using h.dotProduct_mulVec_nonneg v

end

end RefinedBMV
