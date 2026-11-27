import RefinedBMV.FiniteKernels
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The rank-one block split from the uniform family. The exact region predicates
and integral representation remain separate hypotheses for this reduction. -/

open scoped BigOperators ComplexOrder
open MeasureTheory Set

namespace RefinedBMV

noncomputable section

/-- `φ_ε(x)`, with its analytic value at `ε = 0`. -/
def scalePhi (ε x : ℝ) : ℝ := if ε = 0 then x else (Real.exp (ε * x) - 1) / ε

/-- `ψ_ε(x)`, with its analytic value at `ε = 0`. -/
def scalePsi (ε x : ℝ) : ℝ := if ε = 0 then x else (1 - Real.exp (-ε * x)) / ε

def familyPrefactor (ε : ℝ) : ℝ := 6 / ((1 + ε) * (1 + 2 * ε))

/-- The repeated-low-eigenvalue coefficient `3Φ(0,0,x)` in scaled log-coordinates. -/
def lowerDiagonal (ε x : ℝ) : ℝ :=
  if x = 0 then 0 else
    familyPrefactor ε * Real.exp (-x / 3) *
      (Real.exp ((1 + 2 * ε) * x) - 1 - (1 + 2 * ε) * scalePhi ε x) /
      scalePhi ε x ^ 2 - 3

/-- The repeated-high-eigenvalue coefficient `3Φ(0,x,x)`. -/
def upperDiagonal (ε x : ℝ) : ℝ :=
  if x = 0 then 0 else
    familyPrefactor ε * Real.exp (-2 * x / 3) *
      (1 - Real.exp ((1 + 2 * ε) * x) +
        (1 + 2 * ε) * scalePhi ε x * Real.exp ((1 + ε) * x)) /
      scalePhi ε x ^ 2 - 3

/-- The manuscript's `F₃(s,t;ε)` for `0 < s < t`. -/
def scaledDistinct (ε s t : ℝ) : ℝ :=
  familyPrefactor ε * Real.exp (-(s + t) / 3) *
    (1 / (scalePhi ε s * scalePhi ε t) +
      Real.exp ((1 + 2 * ε) * s) / (scalePhi ε s * (scalePhi ε s - scalePhi ε t)) +
      Real.exp ((1 + 2 * ε) * t) / (scalePhi ε t * (scalePhi ε t - scalePhi ε s))) - 3

/-- The divided difference with the repeated-node cases, on `0 ≤ s ≤ t`. -/
def scaledSorted (ε s t : ℝ) : ℝ :=
  if s = 0 then lowerDiagonal ε t else if s = t then upperDiagonal ε s else scaledDistinct ε s t

/-- The positive-argument residual after subtracting the rank-one negative block. -/
def residual (ε s t : ℝ) : ℝ :=
  scaledSorted ε (min s t) (max s t) -
    Real.sqrt (lowerDiagonal ε (max s t)) * Real.sqrt (lowerDiagonal ε |t - s|)

/-- The density with `v = t - s` as the second coordinate. The derivatives are
    taken in `s,t` before substituting `t = s + v`. -/
def mixedDensity (ε s v : ℝ) : ℝ :=
  -deriv (fun a => deriv (fun b => Real.exp (-(a + b) / 6) * residual ε a b) (s + v)) s

/-- The uniform nonnegative interval density gives a PSD kernel once the
    improper-integral identity and termwise integrability are supplied. -/
theorem residual_positive_of_integral (ε : ℝ)
    (hn : ∀ a b : ℝ, 0 < a → a < b → 0 ≤ mixedDensity ε a (b - a))
    (hi : ∀ s t : PosReal, IntegrableOn (fun p : ℝ × ℝ =>
      (if p.1 ≤ s.1 ∧ s.1 ≤ p.2 then Real.exp (s.1 / 6) else 0) *
      (if p.1 ≤ t.1 ∧ t.1 ≤ p.2 then Real.exp (t.1 / 6) else 0) *
      mixedDensity ε p.1 (p.2 - p.1)) {p | 0 < p.1 ∧ p.1 < p.2})
    (hrep : ∀ s t : PosReal, residual ε s.1 t.1 =
      ∫ p : ℝ × ℝ in {p | 0 < p.1 ∧ p.1 < p.2},
        (if p.1 ≤ s.1 ∧ s.1 ≤ p.2 then Real.exp (s.1 / 6) else 0) *
        (if p.1 ≤ t.1 ∧ t.1 ≤ p.2 then Real.exp (t.1 / 6) else 0) *
        mixedDensity ε p.1 (p.2 - p.1)) :
    PositiveKernel (fun s t : PosReal => residual ε s.1 t.1) := by
  let D : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
  let I (p : ℝ × ℝ) (s : PosReal) :=
    if p.1 ≤ s.1 ∧ s.1 ≤ p.2 then Real.exp (s.1 / 6) else 0
  let F (p : ℝ × ℝ) (s : PosReal) := I p s * Real.sqrt (mixedDensity ε p.1 (p.2 - p.1))
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)
  have hEq (s t : PosReal) : (fun p => F p s * F p t) =ᵐ[volume.restrict D]
      fun p => I p s * I p t * mixedDensity ε p.1 (p.2 - p.1) := by
    filter_upwards [ae_restrict_mem hD] with p hp
    have hρ := hn p.1 p.2 hp.1 hp.2
    unfold F
    rw [show I p s * √(mixedDensity ε p.1 (p.2 - p.1)) *
        (I p t * √(mixedDensity ε p.1 (p.2 - p.1))) =
        I p s * I p t * (√(mixedDensity ε p.1 (p.2 - p.1))) ^ 2 by ring,
      Real.sq_sqrt hρ]
  have hGram := PositiveKernel.integral (volume.restrict D) F
    (fun s t => (hi s t).congr (hEq s t).symm)
  convert hGram using 1
  ext s t
  rw [hrep, integral_congr_ae (hEq s t)]

/-- The two derivative regions and the compact and tail regions used by the
    external certificate cover the domain. This lemma checks the gluing step. -/
theorem positive_of_region_bounds (r : ℝ → ℝ → ℝ → ℝ)
    (hbase : ∀ ε v, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v → r ε 0 v = 0)
    (hcont : ∀ ε v, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v →
      ContinuousOn (fun s => r ε s v) (Icc 0 1))
    (hdiff : ∀ ε v, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v →
      DifferentiableOn ℝ (fun s => r ε s v) (Ioo 0 1))
    (hSmallCompact : ∀ ε v s, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v → v ≤ 30 →
      s ∈ Ioo 0 1 → 0 < deriv (fun x => r ε x v) s)
    (hSmallTail : ∀ ε v s, ε ∈ Icc (0 : ℝ) (1 / 7) → 30 ≤ v →
      s ∈ Ioo 0 1 → 0 < deriv (fun x => r ε x v) s)
    (hCompact : ∀ ε v s, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v → v ≤ 30 →
      s ∈ Icc 1 25 → 0 < r ε s v)
    (hLargeS : ∀ ε v s, ε ∈ Icc (0 : ℝ) (1 / 7) → 0 < v → v ≤ 30 →
      25 ≤ s → 0 < r ε s v)
    (hLargeV : ∀ ε v s, ε ∈ Icc (0 : ℝ) (1 / 7) → 30 ≤ v → 1 ≤ s → 0 < r ε s v)
    {ε v s : ℝ} (hε : ε ∈ Icc (0 : ℝ) (1 / 7)) (hv : 0 < v) (hs : 0 < s) :
    0 < r ε s v := by
  by_cases hs1 : s ≤ 1
  · have hcts := (hcont ε v hε hv).mono (Icc_subset_Icc_right hs1)
    have hdf := (hdiff ε v hε hv).mono (Ioo_subset_Ioo_right hs1)
    obtain ⟨u, hu, heq⟩ := exists_deriv_eq_slope (f := fun x => r ε x v) hs hcts hdf
    have hu1 : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le hs1⟩
    have hpos : 0 < deriv (fun x => r ε x v) u := by
      rcases le_total v 30 with h | h
      · exact hSmallCompact ε v u hε hv h hu1
      · exact hSmallTail ε v u hε h hu1
    rw [heq, hbase ε v hε hv, sub_zero, sub_zero, div_pos_iff_of_pos_right hs] at hpos
    exact hpos
  · have hs1 := le_of_not_ge hs1
    rcases le_total v 30 with hv30 | hv30
    · rcases le_total s 25 with hs25 | hs25
      · exact hCompact ε v s hε hv hv30 ⟨hs1, hs25⟩
      · exact hLargeS ε v s hε hv hv30 hs25
    · exact hLargeV ε v s hε hv30 hs1

/-- The repeated-low-eigenvalue coefficient is strictly positive in the
    Duhamel case. This verifies the rank-one block's diagonal without intervals. -/
theorem lowerDiagonal_duhamel_pos {x : ℝ} (hx : 0 < x) : 0 < lowerDiagonal 0 x := by
  let f (z : ℝ) := 1 - (z + 1) * Real.exp (-z) - z ^ 2 / 2 * Real.exp (-2 * z / 3)
  have hf (z : ℝ) : HasDerivAt f
      (z * Real.exp (-2 * z / 3) * (Real.exp (-z / 3) - 1 + z / 3)) z := by
    have ha := ((hasDerivAt_id z).add_const 1).mul (hasDerivAt_id z).neg.exp
    have hb := (((hasDerivAt_id z).pow 2).div_const 2).mul
      (((hasDerivAt_id z).const_mul (-2)).div_const 3).exp
    convert ((hasDerivAt_const z (1 : ℝ)).sub ha).sub hb using 1
    have he : Real.exp (-2 * z / 3) * Real.exp (-z / 3) = Real.exp (-z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [show z * Real.exp (-2 * z / 3) * (Real.exp (-z / 3) - 1 + z / 3) =
        z * (Real.exp (-2 * z / 3) * Real.exp (-z / 3)) -
          z * Real.exp (-2 * z / 3) + z * Real.exp (-2 * z / 3) * (z / 3) by ring, he]
    simp only [Pi.neg_apply, Pi.pow_apply, id_eq]
    ring
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf z).continuousAt
  have hd : Differentiable ℝ f := fun z => (hf z).differentiableAt
  obtain ⟨z, hz, he⟩ := exists_deriv_eq_slope (f := f) hx hcont.continuousOn hd.differentiableOn
  have hderiv : 0 < deriv f z := by
    rw [(hf z).deriv]
    have htail := Real.add_one_lt_exp (show -z / 3 ≠ 0 by linarith [hz.1])
    exact mul_pos (mul_pos hz.1 (Real.exp_pos _)) (by linarith)
  have hf0 : f 0 = 0 := by norm_num [f]
  rw [he, hf0, sub_zero, sub_zero, div_pos_iff_of_pos_right hx] at hderiv
  have h₁ : Real.exp (-(x / 3)) * Real.exp x = Real.exp (2 * x / 3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (2 * x / 3) * Real.exp (-x) = Real.exp (-(x / 3)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₃ : Real.exp (2 * x / 3) * Real.exp (-(2 * x / 3)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hNumer : 6 * Real.exp (-(x / 3)) * (Real.exp x - 1 - x) - 3 * x ^ 2 =
      6 * Real.exp (2 * x / 3) * f x := by
    unfold f
    simp only [neg_mul, neg_div]
    linear_combination 6 * h₁ + (6 + 6 * x) * h₂ + 3 * x ^ 2 * h₃
  have hEq : lowerDiagonal 0 x = (6 * Real.exp (2 * x / 3) / x ^ 2) * f x := by
    norm_num [lowerDiagonal, familyPrefactor, scalePhi, hx.ne', neg_div]
    calc
      _ = (6 * Real.exp (-(x / 3)) * (Real.exp x - 1 - x) - 3 * x ^ 2) / x ^ 2 := by
        field_simp [hx.ne']
      _ = _ := by rw [hNumer]; ring
  rw [hEq]
  positivity

private def negativeFeature (ε s : ℝ) : ℝ :=
  if s < 0 then Real.sqrt (lowerDiagonal ε (-s)) else 0

/-- The full kernel, with the positive residual and the negative rank-one block. -/
def blockKernel (ε s t : ℝ) : ℝ :=
  (if 0 < s ∧ 0 < t then residual ε s t else 0) +
    negativeFeature ε s * negativeFeature ε t

theorem positive_block (ε : ℝ)
    (hp : PositiveKernel (fun s t : PosReal => residual ε s.1 t.1)) :
    PositiveKernel (blockKernel ε) := by
  let point (x : ℝ) : PosReal := if hx : 0 < x then ⟨x, hx⟩ else ⟨1, zero_lt_one⟩
  let mask (x : ℝ) : ℝ := if 0 < x then 1 else 0
  have hPos := (PositiveKernel.rankOne mask).mul (hp.pullback point)
  have h := hPos.add (PositiveKernel.rankOne (negativeFeature ε))
  convert h using 1
  ext s t
  by_cases hs : 0 < s <;> by_cases ht : 0 < t <;> simp [blockKernel, point, mask, hs, ht]

private theorem block_symm (ε s t : ℝ) : blockKernel ε s t = blockKernel ε t s := by
  simp [blockKernel, residual, and_comm, min_comm, max_comm, abs_sub_comm, mul_comm]

private def blockCyclic (ε a b c : ℝ) : ℝ :=
  blockKernel ε (b - a) (c - a) + blockKernel ε (c - b) (a - b) +
    blockKernel ε (a - c) (b - c)

/-- The spectral coefficient, written with the three eigenvalues in sorted order.
    This handles repeated eigenvalues as well as the open region `0 < s < t`. -/
def familyWeight (ε a b c : ℝ) : ℝ :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  let mid := a + b + c - lo - hi
  scaledSorted ε (mid - lo) (hi - lo) / 3

theorem familyWeight_rotate (ε a b c : ℝ) :
    familyWeight ε a b c = familyWeight ε b c a := by
  simp [familyWeight, min_comm, min_left_comm, max_comm, max_left_comm, add_comm, add_left_comm]

theorem familyWeight_swap (ε a b c : ℝ) :
    familyWeight ε a b c = familyWeight ε b a c := by
  simp [familyWeight, min_left_comm, max_left_comm, add_comm, add_left_comm]

private theorem blockCyclic_rotate (ε a b c : ℝ) :
    blockCyclic ε a b c = blockCyclic ε b c a := by
  unfold blockCyclic
  ring

private theorem blockCyclic_swap (ε a b c : ℝ) :
    blockCyclic ε a b c = blockCyclic ε b a c := by
  simp [blockCyclic, block_symm, add_comm, add_left_comm]

private theorem blockCyclic_sorted (ε a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hdiag : ∀ x, 0 < x → 0 ≤ lowerDiagonal ε x) :
    blockCyclic ε a b c = scaledSorted ε (b - a) (c - a) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · rcases eq_or_lt_of_le hbc with rfl | hbc
    · simp [blockCyclic, blockKernel, negativeFeature, scaledSorted, lowerDiagonal]
    · have hcb : 0 < c - a := sub_pos.mpr hbc
      have hbc' : a - c < 0 := sub_neg.mpr hbc
      simp [blockCyclic, blockKernel, negativeFeature, scaledSorted, hcb.not_gt, hbc'.not_gt,
        hcb, hbc', neg_sub, Real.mul_self_sqrt (hdiag _ hcb)]
  · rcases eq_or_lt_of_le hbc with rfl | hbc
    · have hba : 0 < b - a := sub_pos.mpr hab
      have hab' : a - b < 0 := sub_neg.mpr hab
      simp [blockCyclic, blockKernel, negativeFeature, residual, lowerDiagonal, hba.not_gt,
        hab'.not_gt, hba, hab']
    · have hca : 0 < c - a := sub_pos.mpr (hab.trans hbc)
      have hba : 0 < b - a := sub_pos.mpr hab
      have hcb : 0 < c - b := sub_pos.mpr hbc
      have hac : a - c < 0 := sub_neg.mpr (hab.trans hbc)
      have hab' : a - b < 0 := sub_neg.mpr hab
      have hbc' : b - c < 0 := sub_neg.mpr hbc
      have hm : b - a ≤ c - a := by linarith
      simp [blockCyclic, blockKernel, negativeFeature, residual, hca, hba, hcb, hac, hab', hbc',
        hca.not_gt, hba.not_gt, hcb.not_gt, hac.not_gt, hab'.not_gt, hbc'.not_gt,
        min_eq_left hm, max_eq_right hm, neg_sub,
        show c - a - (b - a) = c - b by ring, abs_of_nonneg hcb.le]

/-- A cyclic, swap-invariant property of three reals can be proved on sorted triples. -/
theorem of_sorted_triple {P : ℝ → ℝ → ℝ → Prop}
    (rot : ∀ a b c, P a b c ↔ P b c a) (sw : ∀ a b c, P a b c ↔ P b a c)
    (sorted : ∀ {a b c}, a ≤ b → b ≤ c → P a b c) (a b c : ℝ) : P a b c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact sorted hab hbc
    · rcases le_total a c with hac | hca
      · exact (rot a b c).mpr ((sw b c a).mpr ((rot a c b).mp (sorted hac hcb)))
      · exact (rot c a b).mp (sorted hca hab)
  · rcases le_total a c with hac | hca
    · exact (sw a b c).mpr (sorted hba hac)
    · rcases le_total b c with hbc | hcb
      · exact (rot a b c).mpr (sorted hbc hca)
      · exact (sw a b c).mpr ((rot c b a).mp (sorted hcb hba))

/-- Exact cyclic identity for the block split, including all eigenvalue multiplicities. -/
theorem block_cyclic_identity (ε a b c : ℝ)
    (hdiag : ∀ x, 0 < x → 0 ≤ lowerDiagonal ε x) :
    blockCyclic ε a b c = 3 * familyWeight ε a b c := by
  have sorted {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
      blockCyclic ε u v w = 3 * familyWeight ε u v w := by
    rw [blockCyclic_sorted ε u v w huv hvw hdiag]
    simp only [familyWeight, min_eq_left hvw, min_eq_left huv, max_eq_right hvw,
      max_eq_right (huv.trans hvw)]
    rw [show u + v + w - u - w - u = v - u by ring]
    ring
  have rot (u v w : ℝ) : (blockCyclic ε u v w = 3 * familyWeight ε u v w) ↔
      (blockCyclic ε v w u = 3 * familyWeight ε v w u) := by
    rw [blockCyclic_rotate ε u v w, familyWeight_rotate ε u v w]
  have sw (u v w : ℝ) : (blockCyclic ε u v w = 3 * familyWeight ε u v w) ↔
      (blockCyclic ε v u w = 3 * familyWeight ε v u w) := by
    rw [blockCyclic_swap ε u v w, familyWeight_swap ε u v w]
  exact of_sorted_triple rot sw sorted a b c

/-- The block split gives a nonnegative spectral trace gap from a PSD residual. -/
theorem family_cycle_nonneg {ι : Type} [Fintype ι] (ε : ℝ) (eigen : ι → ℝ)
    (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (hdiag : ∀ x, 0 < x → 0 ≤ lowerDiagonal ε x)
    (hres : PositiveKernel (fun s t : PosReal => residual ε s.1 t.1)) :
    0 ≤ cycleSum (fun i j k => familyWeight ε (eigen i) (eigen j) (eigen k)) X :=
  cycleSum_nonneg_of_cyclic _ _ X hX
    (fun i => positive_block ε hres ι fun j => eigen j - eigen i)
    (fun i j k => block_cyclic_identity ε (eigen i) (eigen j) (eigen k) hdiag)

end

end RefinedBMV
