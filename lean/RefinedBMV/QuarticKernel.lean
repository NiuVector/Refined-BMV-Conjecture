import RefinedBMV.FiniteKernels
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The integer Gram blocks and polynomial identity in the updated `(4,4)` manuscript. -/

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace RefinedBMV

noncomputable section

/-- The complete homogeneous polynomial in four variables. -/
def homogeneousFour (n : ℕ) (a b c d : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), a ^ j * homogeneous (n - j) b c d

def polyGram {m : Type} [Fintype m] (G : Matrix m m ℝ) (f : ℝ → m → ℝ)
    (b d : ℝ) : ℝ := ∑ i, ∑ j, f b i * G i j * f d j

theorem positive_polyGram {m : Type} [Fintype m] (G : Matrix m m ℝ)
    (hG : (G.map Complex.ofReal).PosSemidef) (f : ℝ → m → ℝ) :
    PositiveKernel (fun b d => polyGram G f b d) := by
  intro ι _ x
  let V : Matrix m ι ℂ := Matrix.of fun j i => (f (x i) j : ℂ)
  convert hG.conjTranspose_mul_mul_same V using 1
  ext i j
  simp only [polyGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    V, Matrix.map_apply, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul]
  exact Finset.sum_comm

private lemma two_by_two_of_det (a b c : ℝ) (hc : 0 < c) (hdet : 0 ≤ a * c - b ^ 2) :
    ((!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal).PosSemidef := by
  let f : Fin 2 → ℝ := ![1, 0]
  let g : Fin 2 → ℝ := ![b / c, 1]
  have hδ : 0 ≤ a - b ^ 2 / c := by
    rw [show a - b ^ 2 / c = (a * c - b ^ 2) / c by field_simp [hc.ne']]
    exact div_nonneg hdet hc.le
  have h := ((PositiveKernel.rankOne f).scale hδ |>.add
    ((PositiveKernel.rankOne g).scale hc.le)) (Fin 2) id
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f, g]
  all_goals field_simp [hc.ne']
  all_goals ring

private lemma three_by_three_of_trailing_minors (a b c d e f : ℝ)
    (hf : 0 < f) (hminor : 0 < d * f - e ^ 2)
    (hdet : 0 ≤ a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2) :
    ((!![a, b, c; b, d, e; c, e, f] : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal).PosSemidef := by
  let δ := d - e ^ 2 / f
  let η := b - c * e / f
  let γ := a - c ^ 2 / f - η ^ 2 / δ
  have hδ : 0 < δ := by
    change 0 < d - e ^ 2 / f
    rw [show d - e ^ 2 / f = (d * f - e ^ 2) / f by field_simp [hf.ne']]
    exact div_pos hminor hf
  have hγ : 0 ≤ γ := by
    have eq : γ * (δ * f) = a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2 := by
      unfold γ η
      field_simp [hδ.ne', hf.ne']
      dsimp [δ]
      field_simp [hf.ne']
      ring
    exact nonneg_of_mul_nonneg_left (eq ▸ hdet) (mul_pos hδ hf)
  let u : Fin 3 → ℝ := ![1, 0, 0]
  let v : Fin 3 → ℝ := ![η / δ, 1, 0]
  let w : Fin 3 → ℝ := ![c / f, e / f, 1]
  have h := (((PositiveKernel.rankOne u).scale hγ |>.add
    ((PositiveKernel.rankOne v).scale hδ.le)).add
    ((PositiveKernel.rankOne w).scale hf.le)) (Fin 3) id
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.of_apply, id_eq] <;> apply congrArg Complex.ofReal <;>
    simp [u, v, w, γ] <;> field_simp [hδ.ne', hf.ne'] <;>
    dsimp [δ, η] <;> field_simp [hf.ne'] <;> ring

private def e₀ (a c : ℝ) := 2*a^8 + 2*a^6*c^2 - 3*a^4*c^4 + 2*a^2*c^6 + 2*c^8
private def e₁ (a c : ℝ) := 2 * (a^3 - c^3)^2
private def e₂ (a c : ℝ) := a^4 - 7*a^2*c^2 + c^4
private def e₃ (a c : ℝ) := (a-c)^2 * (9*a^2 + 26*a*c + 9*c^2)
private def e₄ (a c : ℝ) := 2 * (a-c)^2

/-- The manuscript's even Gram block. -/
def quarticEvenBlock (a c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![e₀ a c, e₁ a c, e₂ a c; e₁ a c, e₃ a c, e₄ a c; e₂ a c, e₄ a c, 5]

/-- The manuscript's odd Gram block. -/
def quarticOddBlock (a c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4*a^2*c^2*(a^2+c^2), -8*a^2*c^2; -8*a^2*c^2, 4*(a^2+c^2)]

/-- The even Gram block is positive semidefinite, including the coincident case. -/
theorem quarticEvenBlock_positive (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ((quarticEvenBlock a c).map Complex.ofReal).PosSemidef := by
  by_cases h : a = c
  · subst c
    let u : Fin 3 → ℝ := ![a^4, 0, -1]
    have hK := ((PositiveKernel.rankOne u).scale (by norm_num : (0 : ℝ) ≤ 5)) (Fin 3) id
    convert hK using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quarticEvenBlock, u, e₀, e₁, e₂, e₃, e₄] <;> ring
  · unfold quarticEvenBlock
    apply three_by_three_of_trailing_minors _ _ _ _ _ _ (by norm_num)
    · calc
        _ = (a-c)^2 * (41*a^2 + 138*a*c + 41*c^2) := by unfold e₃ e₄; ring
        _ > 0 := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (by positivity)
    · calc
        _ = (a-c)^4 * (61*a^8 + 332*a^7*c + 768*a^6*c^2 + 1828*a^5*c^3 +
              2582*a^4*c^4 + 1828*a^3*c^5 + 768*a^2*c^6 + 332*a*c^7 + 61*c^8) := by
          unfold e₀ e₁ e₂ e₃ e₄
          ring
        _ ≥ 0 := by positivity

/-- The odd Gram block is positive semidefinite. -/
theorem quarticOddBlock_positive (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ((quarticOddBlock a c).map Complex.ofReal).PosSemidef := by
  unfold quarticOddBlock
  apply two_by_two_of_det _ _ _ (by positivity)
  calc
    _ = 16*a^2*c^2*(a^2-c^2)^2 := by ring
    _ ≥ 0 := by positivity

private def evenVec (u : ℝ) : Fin 3 → ℝ := ![1, u^2, u^4]
private def oddVec (u : ℝ) : Fin 2 → ℝ := ![u, u^3]

/-- The unnormalized quartic kernel at the antipodal pair `(a,c)`. -/
def quarticKernel (a c b d : ℝ) : ℝ :=
  polyGram (quarticEvenBlock a c) evenVec b d + polyGram (quarticOddBlock a c) oddVec b d

/-- Every finite sample of the raw quartic kernel is positive semidefinite. -/
theorem quarticKernel_positive (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    PositiveKernel (quarticKernel a c) :=
  (positive_polyGram _ (quarticEvenBlock_positive a c ha hc) evenVec).add
    (positive_polyGram _ (quarticOddBlock_positive a c ha hc) oddVec)

/-- The exact two-term cyclic identity for the integer Gram blocks. -/
theorem quarticKernel_cyclic (a b c d : ℝ) :
    quarticKernel a c b d + quarticKernel b d a c =
      2 * (homogeneousFour 4 (a^2) (b^2) (c^2) (d^2) - 35 * (a^2 * b^2 * c^2 * d^2)) := by
  norm_num [quarticKernel, polyGram, quarticEvenBlock, quarticOddBlock, evenVec, oddVec,
    e₀, e₁, e₂, e₃, e₄, homogeneousFour, homogeneous, Fin.sum_univ_succ, sum_range_succ]
  ring

/-- A four-cycle kernel. The spectral variable is a positive root, so `p`
    represents the exponent for `A` and `q` the balanced-word exponent. -/
structure QuarticCertificate (n p q : ℕ) where
  kernel : ℝ → ℝ → ℝ → ℝ → ℝ
  positive : ∀ a c : ℝ, 0 < a → 0 < c → PositiveKernel (kernel a c)
  cyclic : ∀ a b c d : ℝ, kernel a c b d + kernel b d a c = 2 *
    (homogeneousFour n (a^p) (b^p) (c^p) (d^p) - ((n + 3).choose 3 : ℝ) * (a*b*c*d)^q)

def quarticCertificateFour : QuarticCertificate 4 2 2 where
  kernel := quarticKernel
  positive := quarticKernel_positive
  cyclic a b c d := by
    rw [quarticKernel_cyclic]
    norm_num [Nat.choose]
    ring

private def smallEvenVec (u : ℝ) : Fin 2 → ℝ := ![1, u^2]

private def oneEven (a c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a^4 - a^2*c^2 + c^4, -a*c; -a*c, 1]

private def twoEven (a c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2*a^4 - a^2*c^2 + 2*c^4, a^2 - 5*a*c + c^2; a^2 - 5*a*c + c^2, 3]

private def oneQuartic (a c b d : ℝ) : ℝ :=
  2 * (polyGram (oneEven a c) smallEvenVec b d + (a-c)^2 * (b*d))

private def twoQuartic (a c b d : ℝ) : ℝ :=
  polyGram (twoEven a c) smallEvenVec b d + (5*(a-c)^2) * (b*d)

/-- The integer Gram identity for `(1,4)`. -/
def quarticCertificateOne : QuarticCertificate 1 4 1 where
  kernel := oneQuartic
  positive a c _ _ := by
    have hg : ((oneEven a c).map Complex.ofReal).PosSemidef := by
      unfold oneEven
      apply two_by_two_of_det _ _ _ (by norm_num)
      calc
        _ = (a^2-c^2)^2 := by ring
        _ ≥ 0 := sq_nonneg _
    exact ((positive_polyGram _ hg smallEvenVec).add
      ((PositiveKernel.rankOne id).scale (sq_nonneg (a-c)))).scale (by norm_num)
  cyclic a b c d := by
    norm_num [oneQuartic, oneEven, polyGram, smallEvenVec, homogeneousFour, homogeneous,
      Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    ring

/-- The integer Gram identity for `(2,4)`. -/
def quarticCertificateTwo : QuarticCertificate 2 2 1 where
  kernel := twoQuartic
  positive a c ha hc := by
    have hg : ((twoEven a c).map Complex.ofReal).PosSemidef := by
      unfold twoEven
      apply two_by_two_of_det _ _ _ (by norm_num)
      calc
        _ = 5 * (a-c)^2 * (a^2+4*a*c+c^2) := by ring
        _ ≥ 0 := by positivity
    exact (positive_polyGram _ hg smallEvenVec).add
      ((PositiveKernel.rankOne id).scale (by positivity : 0 ≤ 5 * (a-c)^2))
  cyclic a b c d := by
    norm_num [twoQuartic, twoEven, polyGram, smallEvenVec, homogeneousFour, homogeneous,
      Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    ring

private theorem four_by_four_of_schur (a b c x d e y f z : ℝ)
    (hS : ((!![a - x^2/7, b - x*y/7, c - x*z/7;
      b - x*y/7, d - y^2/7, e - y*z/7;
      c - x*z/7, e - y*z/7, f - z^2/7] : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal).PosSemidef) :
    ((!![a, b, c, x; b, d, e, y; c, e, f, z; x, y, z, 7] :
      Matrix (Fin 4) (Fin 4) ℝ).map Complex.ofReal).PosSemidef := by
  let E : Matrix (Fin 3) (Fin 4) ℂ := !![1,0,0,0;0,1,0,0;0,0,1,0]
  let v : Fin 4 → ℝ := ![x/7, y/7, z/7, 1]
  have h := (hS.conjTranspose_mul_mul_same E).add
    (((PositiveKernel.rankOne v).scale (by norm_num : (0 : ℝ) ≤ 7)) (Fin 4) id)
  convert h using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [v, E, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def f₀ (a c : ℝ) := 2*a^12 + 2*a^8*c^4 - 7*a^6*c^6 + 2*a^4*c^8 + 2*c^12
private def f₁ (a c : ℝ) := 2*a^8 - 3*a^4*c^4 + 2*c^8
private def f₂ (a c : ℝ) := a^2*c^2*(5*a^4 + 3*a^2*c^2 + 5*c^4)
private def f₃ (a c : ℝ) := 5*a^4 - 3*a^2*c^2 + 5*c^4
private def f₄ (a c : ℝ) := -2*a^3*c^3
private def f₅ (a c : ℝ) := -8*a^3*c^3
private def f₆ (a c : ℝ) := -5*a^2*c^2

private def threeEven (a c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![f₀ a c, 0, f₁ a c, f₄ a c; 0, f₂ a c, f₅ a c, f₆ a c;
    f₁ a c, f₅ a c, f₃ a c, 0; f₄ a c, f₆ a c, 0, 7]

private def threeOdd (a c : ℝ) := 2*(a-c)^2*(a^4 + 2*a^3*c + 7*a^2*c^2 + 2*a*c^3 + c^4)

private theorem threeEven_positive (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ((threeEven a c).map Complex.ofReal).PosSemidef := by
  unfold threeEven
  apply four_by_four_of_schur
  apply three_by_three_of_trailing_minors
  · calc
      _ = (49*(a^2*c^2) + 35*(a^2-c^2)^2) / 7 := by unfold f₃; ring
      _ > 0 := by positivity
  · calc
      _ = (14*(a^2*c^2)^3 + 575*(a^2*c^2)^2*(a^2-c^2)^2 + 175*(a^2*c^2)*(a^2-c^2)^4) / 7 := by
        unfold f₂ f₃ f₅ f₆
        ring
      _ > 0 := by positivity
  · let p := a^2*c^2
    let r := (a^2-c^2)^2
    calc
      _ = r*(644*p^5 + 7015*p^4*r + 5936*p^3*r^2 + 1866*p^2*r^3 + 210*p*r^4) / 7 := by
        unfold p r f₀ f₁ f₂ f₃ f₄ f₅ f₆
        ring
      _ ≥ 0 := by dsimp [p, r]; positivity

private def threeVec (b : ℝ) : Fin 4 → ℝ := ![1, b^2, b^4, b^6]

private def threeQuartic (a c b d : ℝ) : ℝ :=
  polyGram (threeEven a c) threeVec b d + threeOdd a c * (b^3*d^3)

/-- The `(3,4)` block, reconstructed from the updated manuscript's trailing minors. -/
def quarticCertificateThree : QuarticCertificate 3 4 3 where
  kernel := threeQuartic
  positive a c ha hc :=
    (positive_polyGram _ (threeEven_positive a c ha hc) threeVec).add
      ((PositiveKernel.rankOne (fun b : ℝ => b^3)).scale (by unfold threeOdd; positivity))
  cyclic a b c d := by
    norm_num [threeQuartic, threeEven, threeOdd, polyGram, threeVec, f₀, f₁, f₂, f₃, f₄, f₅, f₆,
      homogeneousFour, homogeneous, Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    ring

end

end RefinedBMV
