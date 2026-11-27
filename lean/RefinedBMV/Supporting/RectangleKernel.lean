/- Adapted to Mathlib v4.28.0 from the Apache-2.0 trureturing source:
   https://github.com/the-omega-institute/trureturing/tree/51dca4f1542baa532983864568d6a8ca3470e745/D5/S3/Quantum/Analysis
   RefinedBMVIntervalKernel.lean and RefinedBMVExtremeAnalytic.lean.
   See LICENSE-Apache-2.0.txt. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fin.Tuple.Sort

open Finset Set Filter
open scoped BigOperators ComplexOrder Topology

namespace RefinedBMV.Supporting

noncomputable section
universe u
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A finite array truncated at an outer row and column has a PSD symmetric extension
when the adjacent upper-triangular rectangle increments are nonnegative.
Interior entries of the array have indices `1, …, n`, with endpoints `0, n+1`. -/
theorem posSemidef_truncation {n : ℕ} (A : ℕ → ℕ → ℝ)
    (hrect : ∀ i j : ℕ, i ≤ j → j < n →
      0 ≤ (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2))) :
    (Matrix.of fun i j : Fin n ↦
      ((A (min i.val j.val + 1) (max i.val j.val + 1) - A 0 (max i.val j.val + 1) -
        (A (min i.val j.val + 1) (n + 1) - A 0 (n + 1)) : ℝ) : 𝕜)).PosSemidef := by
  let c (i j : ℕ) :=
    (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2))
  let indices := ((range n) ×ˢ (range n)).filter fun p : ℕ × ℕ ↦ p.1 ≤ p.2
  let v (p : ℕ × ℕ) (i : Fin n) : 𝕜 := if p.1 ≤ i.val ∧ i.val ≤ p.2 then 1 else 0
  let M (p : ℕ × ℕ) := c p.1 p.2 • Matrix.vecMulVec (v p) (star (v p))
  have hPSD : (∑ p ∈ indices, M p).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro p hp
    have hp' := mem_filter.mp hp
    exact (Matrix.posSemidef_vecMulVec_self_star (v p)).smul
      (hrect p.1 p.2 hp'.2 (mem_range.mp (mem_product.mp hp'.1).2))
  convert hPSD using 1
  ext i j
  let r := min i.val j.val
  let s := max i.val j.val
  have hrs : r ≤ s := (min_le_left _ _).trans (le_max_left _ _)
  have hs : s < n := max_lt_iff.mpr ⟨i.isLt, j.isLt⟩
  let included := (range (r + 1)) ×ˢ (Finset.Ico s n)
  have hsubset : included ⊆ indices := by
    intro p hp
    have hp₁ : p.1 ≤ r := Nat.lt_succ_iff.mp (mem_range.mp (mem_product.mp hp).1)
    have hp₂ := Finset.mem_Ico.mp (mem_product.mp hp).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr hp₂.2⟩,
      by omega⟩
  have hmem (p : ℕ × ℕ) (hp : p ∈ indices) :
      p ∈ included ↔ (p.1 ≤ i.val ∧ i.val ≤ p.2) ∧ (p.1 ≤ j.val ∧ j.val ≤ p.2) := by
    have hp₂ := mem_range.mp (mem_product.mp (mem_filter.mp hp).1).2
    simp only [included, mem_product, Finset.mem_Ico, Finset.mem_range, r, s, Nat.lt_succ_iff,
      le_min_iff, max_le_iff]
    tauto
  have hzero (p : ℕ × ℕ) (hp : p ∈ indices) (hp' : p ∉ included) : M p i j = 0 := by
    rw [hmem p hp] at hp'
    rw [not_and_or] at hp'
    simp only [M, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    rcases hp' with hi | hj
    · simp [v, hi]
    · simp [v, hj]
  have hone (p : ℕ × ℕ) (hp : p ∈ included) : M p i j = ((c p.1 p.2 : ℝ) : 𝕜) := by
    obtain ⟨hi, hj⟩ := (hmem p (hsubset hp)).mp hp
    simp only [M, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    simp [v, hi, hj, Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  simp only [Matrix.of_apply, Matrix.sum_apply]
  rw [← sum_subset hsubset hzero, sum_congr rfl hone]
  rw [← map_sum (algebraMap ℝ 𝕜)]
  congr 1
  rw [sum_product]
  have htel (f : ℕ → ℝ) : (∑ q ∈ Finset.Ico s n, (f q - f (q + 1))) = f s - f n := by
    calc
      _ = -(∑ q ∈ Finset.Ico s n, (f (q + 1) - f q)) := by
        rw [← sum_neg_distrib]
        simp only [neg_sub]
      _ = _ := by rw [sum_Ico_sub f hs.le, neg_sub]
  symm
  calc
    _ = ∑ p ∈ range (r + 1), ((A (p + 1) (s + 1) - A p (s + 1)) -
        (A (p + 1) (n + 1) - A p (n + 1))) :=
      sum_congr rfl fun p _ ↦ htel (fun q ↦ A (p + 1) (q + 1) - A p (q + 1))
    _ = _ := by
      rw [sum_sub_distrib, sum_range_sub (fun p ↦ A p (s + 1)),
        sum_range_sub (fun p ↦ A p (n + 1))]

/-- Zero limits at the outer edges give the inequalities for the virtual row and column. -/
theorem edge_inequalities_of_rectangle_limits {a : ℝ} {K : ℝ → ℝ → ℝ}
    (hrect : ∀ ⦃l u v w : ℝ⦄, a < l → l ≤ u → u ≤ v → v ≤ w →
      0 ≤ (K u v - K l v) - (K u w - K l w))
    (hzero : ∀ y > a, Tendsto (fun x ↦ K x y) (𝓝[>] a) (𝓝 0))
    (hinfty : ∀ x > a, Tendsto (K x) atTop (𝓝 0)) :
    (∀ ⦃x y : ℝ⦄, a < x → x ≤ y → 0 ≤ K x y) ∧
      (∀ y > a, MonotoneOn (fun x ↦ K x y) (Ioc a y)) ∧
      (∀ x > a, AntitoneOn (K x) (Ici x)) := by
  have hleft (v : ℝ) (_ : a < v) : MonotoneOn (fun x ↦ K x v) (Ioc a v) := by
    intro l hl u hu hlu
    have ht : Tendsto (fun w ↦ K u w - K l w) atTop (𝓝 0) := by
      simpa only [sub_zero] using (hinfty u hu.1).sub (hinfty l hl.1)
    apply sub_nonneg.mp
    refine le_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop v] with w hvw
    exact sub_nonneg.mp (hrect hl.1 hlu hu.2 hvw)
  have hright (u : ℝ) (hau : a < u) : AntitoneOn (K u) (Ici u) := by
    intro v huv w _ hvw
    change u ≤ v at huv
    have ht (y : ℝ) (hay : a < y) :
        Tendsto (fun l ↦ K u y - K l y) (𝓝[>] a) (𝓝 (K u y)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := K u y)).sub (hzero y hay)
    refine le_of_tendsto_of_tendsto
      (ht w (hau.trans_le (huv.trans hvw))) (ht v (hau.trans_le huv)) ?_
    filter_upwards [Ioo_mem_nhdsGT hau] with l hl
    exact sub_nonneg.mp (hrect hl.1 hl.2.le huv hvw)
  refine ⟨?_, hleft, hright⟩
  intro x y hax hxy
  refine le_of_tendsto (hinfty x hax) ?_
  filter_upwards [eventually_ge_atTop y] with w hyw
  exact hright x hax hxy (hxy.trans hyw) hyw


theorem kernel_gram_posSemidef_of_rectangle {a : ℝ} {K : ℝ → ℝ → ℝ}
    (hnonneg : ∀ ⦃x y : ℝ⦄, a < x → x ≤ y → 0 ≤ K x y)
    (hleft : ∀ y > a, MonotoneOn (fun x ↦ K x y) (Ioc a y))
    (hright : ∀ x > a, AntitoneOn (K x) (Ici x))
    (hrectangle : ∀ ⦃l u v w : ℝ⦄, a < l → l ≤ u → u ≤ v → v ≤ w →
      0 ≤ (K u v - K l v) - (K u w - K l w))
    {ι : Type u} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, a < x i) :
    (Matrix.of fun i j ↦ (K (min (x i) (x j)) (max (x i) (x j)) : ℂ)).PosSemidef := by
  let n := Fintype.card ι
  let e := (Fintype.equivFin ι).symm
  let order : Fin n ≃ ι := (Tuple.sort (x ∘ e)).trans e
  let y := x ∘ order
  have hmono : Monotone y := Tuple.monotone_sort (x ∘ e)
  apply (Matrix.posSemidef_submatrix_equiv order).mp
  change (Matrix.of fun i j ↦ (K (min (y i) (y j)) (max (y i) (y j)) : ℂ)).PosSemidef
  let z (i : ℕ) := if h : i < n then y ⟨i, h⟩ else 0
  -- The sample occupies rows and columns 1 through n. The outer row and column are virtual.
  let A (i j : ℕ) := if i = 0 ∨ n < j then 0 else K (z (i - 1)) (z (j - 1))
  have hz (i : ℕ) (hi : i < n) : a < z i := by
    simpa only [z, dif_pos hi, y, Function.comp_apply] using hx (order ⟨i, hi⟩)
  have hle (i j : ℕ) (hij : i ≤ j) (hj : j < n) : z i ≤ z j := by
    have hi := hij.trans_lt hj
    simpa [z, hi, hj] using hmono (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from hij)
  have hinside (i j : ℕ) (hj : j < n) : A (i + 1) (j + 1) = K (z i) (z j) := by
    simp [A, show ¬ n < j + 1 by omega]
  have hrow (j : ℕ) : A 0 j = 0 := by simp [A]
  have hcol (i : ℕ) : A i (n + 1) = 0 := by simp [A]
  have hrect (i j : ℕ) (hij : i ≤ j) (hj : j < n) :
      0 ≤ (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) (j + 2) - A i (j + 2)) := by
    rw [hinside i j hj]
    by_cases hj' : j + 1 < n
    · rw [hinside i (j + 1) hj']
      cases i with
      | zero =>
        simp only [hrow, sub_zero, sub_nonneg]
        exact hright _ (hz 0 (by omega))
          (hle 0 j (Nat.zero_le _) hj) (hle 0 (j + 1) (Nat.zero_le _) hj') (hle j (j + 1) (Nat.le_succ _) hj')
      | succ i =>
        rw [hinside i j hj, hinside i (j + 1) hj']
        exact hrectangle (hz i (by omega)) (hle i (i + 1) (Nat.le_succ _) (hij.trans_lt hj))
          (hle (i + 1) j hij hj) (hle j (j + 1) (Nat.le_succ _) hj')
    · have he : j + 2 = n + 1 := by omega
      simp only [he, hcol, sub_zero]
      cases i with
      | zero =>
        rw [hrow, sub_zero]
        exact hnonneg (hz 0 (by omega)) (hle 0 j (Nat.zero_le _) hj)
      | succ i =>
        rw [hinside i j hj, sub_nonneg]
        have hi : i + 1 < n := hij.trans_lt hj
        exact hleft _ (hz j hj)
          ⟨hz i (by omega), hle i j (Nat.le_of_succ_le hij) hj⟩ ⟨hz (i + 1) hi, hle (i + 1) j hij hj⟩
          (hle i (i + 1) (Nat.le_succ _) hi)
  have hPSD := posSemidef_truncation (𝕜 := ℂ) A hrect
  convert hPSD using 1
  ext i j
  have hmax : max i.val j.val < n := max_lt_iff.2 ⟨i.isLt, j.isLt⟩
  have hzmin : z (min i.val j.val) = min (y i) (y j) := by
    rcases le_total i j with h | h
    · simp [z, min_eq_left (show i.val ≤ j.val from h), min_eq_left (hmono h), i.isLt]
    · simp [z, min_eq_right (show j.val ≤ i.val from h), min_eq_right (hmono h), j.isLt]
  have hzmax : z (max i.val j.val) = max (y i) (y j) := by
    rcases le_total i j with h | h
    · simp [z, max_eq_right (show i.val ≤ j.val from h), max_eq_right (hmono h), j.isLt]
    · simp [z, max_eq_left (show j.val ≤ i.val from h), max_eq_left (hmono h), i.isLt]
  simp [Matrix.of_apply, hinside _ _ hmax, hrow, hcol, hzmin, hzmax]


end

end RefinedBMV.Supporting
