import RefinedBMV.QuarticKernel
import RefinedBMV.Supporting.TrailingMinors
import RefinedBMV.Supporting.DetEntries

/-! The additional integer Gram blocks in the 17:16 manuscript.
The entries use p = ac and r = (a-c)^2. Lean verifies the determinant
identities and the cyclic average of each kernel. -/

open Matrix Finset
open scoped BigOperators ComplexOrder

namespace RefinedBMV

noncomputable section

open Supporting

private def fiveEvenEntry00 (p r : ℝ) : ℝ :=
  6*p^10 + 140*p^9*r + 931*p^8*r^2 + 2752*p^7*r^3 + 4344*p^6*r^4 + 4016*p^5*r^5 + 2276*p^4*r^6
    + 800*p^3*r^7 + 170*p^2*r^8 + 20*p*r^9 + r^10

private def fiveEvenEntry01 (p r : ℝ) : ℝ :=
  -11*p^8 + 80*p^7*r + 356*p^6*r^2 + 680*p^5*r^3 + 661*p^4*r^4 + 352*p^3*r^5 + 104*p^2*r^6 +
    16*p*r^7 + r^8

private def fiveEvenEntry02 (p r : ℝ) : ℝ :=
  6*p^7 + 3*p^6*r

private def fiveEvenEntry03 (p r : ℝ) : ℝ :=
  -p^6 + 36*p^5*r + 105*p^4*r^2 + 112*p^3*r^3 + 54*p^2*r^4 + 12*p*r^5 + r^6

private def fiveEvenEntry11 (p r : ℝ) : ℝ :=
  50*p^6 + 148*p^5*r + 133*p^4*r^2 + 112*p^3*r^3 + 54*p^2*r^4 + 12*p*r^5 + r^6

private def fiveEvenEntry12 (p _r : ℝ) : ℝ :=
  -14*p^5

private def fiveEvenEntry13 (p r : ℝ) : ℝ :=
  -25*p^4 + 16*p^3*r + 20*p^2*r^2 + 8*p*r^3 + r^4

private def fiveEvenEntry22 (p r : ℝ) : ℝ :=
  14*p^4 + 48*p^3*r + 60*p^2*r^2 + 24*p*r^3 + 3*r^4

private def fiveEvenEntry23 (p r : ℝ) : ℝ :=
  -6*p^3 - 27*p^2*r - 18*p*r^2 - 3*r^3

private def fiveEvenEntry33 (p r : ℝ) : ℝ :=
  32*p^2 + 64*p*r + 16*r^2

private def fiveEven (p r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![fiveEvenEntry00 p r, fiveEvenEntry01 p r, fiveEvenEntry02 p r, fiveEvenEntry03 p r;
    fiveEvenEntry01 p r, fiveEvenEntry11 p r, fiveEvenEntry12 p r, fiveEvenEntry13 p r;
    fiveEvenEntry02 p r, fiveEvenEntry12 p r, fiveEvenEntry22 p r, fiveEvenEntry23 p r;
    fiveEvenEntry03 p r, fiveEvenEntry13 p r, fiveEvenEntry23 p r, fiveEvenEntry33 p r]

set_option maxHeartbeats 4000000 in
private theorem fiveEven_positive (p r : ℝ) (hp : 0 < p) (hr : 0 ≤ r) :
    ((fiveEven p r).map Complex.ofReal).PosSemidef := by
  apply posSemidef_complexify
  have hs : (fiveEven p r).IsHermitian := by
    change (fiveEven p r)ᴴ = fiveEven p r
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h4 : 0 ≤ (fiveEven p r).det := by
    calc
      _ = 848848*p^21*r + 18327388*p^20*r^2 + 149023992*p^19*r^3 + 695388764*p^18*r^4 + 2104062344*p^17*r^5 +
            4391488596*p^16*r^6 + 6588311336*p^15*r^7 + 7306056308*p^14*r^8 + 6096072504*p^13*r^9 +
            3865314474*p^12*r^10 + 1869147468*p^11*r^11 + 687710010*p^10*r^12 + 190782396*p^9*r^13 +
            39194154*p^8*r^14 + 5776128*p^7*r^15 + 577080*p^6*r^16 + 34992*p^5*r^17 + 972*p^4*r^18 := by
        simp only [Matrix.det_fin_three, det_four_entries]
        change
          fiveEvenEntry00 p r * (fiveEvenEntry11 p r * fiveEvenEntry22 p r * fiveEvenEntry33 p r - fiveEvenEntry11
            p r * fiveEvenEntry23 p r * fiveEvenEntry23 p r - fiveEvenEntry12 p r * fiveEvenEntry12 p r *
            fiveEvenEntry33 p r + fiveEvenEntry12 p r * fiveEvenEntry23 p r * fiveEvenEntry13 p r + fiveEvenEntry13
            p r * fiveEvenEntry12 p r * fiveEvenEntry23 p r - fiveEvenEntry13 p r * fiveEvenEntry22 p r *
            fiveEvenEntry13 p r) - fiveEvenEntry01 p r * (fiveEvenEntry01 p r * fiveEvenEntry22 p r *
            fiveEvenEntry33 p r - fiveEvenEntry01 p r * fiveEvenEntry23 p r * fiveEvenEntry23 p r - fiveEvenEntry12
            p r * fiveEvenEntry02 p r * fiveEvenEntry33 p r + fiveEvenEntry12 p r * fiveEvenEntry23 p r *
            fiveEvenEntry03 p r + fiveEvenEntry13 p r * fiveEvenEntry02 p r * fiveEvenEntry23 p r - fiveEvenEntry13
            p r * fiveEvenEntry22 p r * fiveEvenEntry03 p r) + fiveEvenEntry02 p r * (fiveEvenEntry01 p r *
            fiveEvenEntry12 p r * fiveEvenEntry33 p r - fiveEvenEntry01 p r * fiveEvenEntry23 p r * fiveEvenEntry13
            p r - fiveEvenEntry11 p r * fiveEvenEntry02 p r * fiveEvenEntry33 p r + fiveEvenEntry11 p r *
            fiveEvenEntry23 p r * fiveEvenEntry03 p r + fiveEvenEntry13 p r * fiveEvenEntry02 p r * fiveEvenEntry13
            p r - fiveEvenEntry13 p r * fiveEvenEntry12 p r * fiveEvenEntry03 p r) - fiveEvenEntry03 p r *
            (fiveEvenEntry01 p r * fiveEvenEntry12 p r * fiveEvenEntry23 p r - fiveEvenEntry01 p r *
            fiveEvenEntry22 p r * fiveEvenEntry13 p r - fiveEvenEntry11 p r * fiveEvenEntry02 p r * fiveEvenEntry23
            p r + fiveEvenEntry11 p r * fiveEvenEntry22 p r * fiveEvenEntry03 p r + fiveEvenEntry12 p r *
            fiveEvenEntry02 p r * fiveEvenEntry13 p r - fiveEvenEntry12 p r * fiveEvenEntry12 p r * fiveEvenEntry03
            p r) = _
        unfold fiveEvenEntry00 fiveEvenEntry11 fiveEvenEntry22 fiveEvenEntry33 fiveEvenEntry23 fiveEvenEntry12 fiveEvenEntry13 fiveEvenEntry01 fiveEvenEntry02 fiveEvenEntry03
        ring
      _ ≥ 0 := by positivity

  have h3 : 0 < (tailMatrix (fiveEven p r)).det := by
    calc
      _ = 1378*p^12 + 118820*p^11*r + 591366*p^10*r^2 + 1264796*p^9*r^3 + 1637752*p^8*r^4 + 1491468*p^7*r^5 +
            1039806*p^6*r^6 + 551604*p^5*r^7 + 210726*p^4*r^8 + 54720*p^3*r^9 + 9072*p^2*r^10 +
            864*p*r^11 + 36*r^12 := by
        simp only [Matrix.det_fin_three]
        change
          fiveEvenEntry11 p r * fiveEvenEntry22 p r * fiveEvenEntry33 p r - fiveEvenEntry11 p r * fiveEvenEntry23 p
            r * fiveEvenEntry23 p r - fiveEvenEntry12 p r * fiveEvenEntry12 p r * fiveEvenEntry33 p r +
            fiveEvenEntry12 p r * fiveEvenEntry23 p r * fiveEvenEntry13 p r + fiveEvenEntry13 p r * fiveEvenEntry12
            p r * fiveEvenEntry23 p r - fiveEvenEntry13 p r * fiveEvenEntry22 p r * fiveEvenEntry13 p r = _
        unfold fiveEvenEntry11 fiveEvenEntry22 fiveEvenEntry33 fiveEvenEntry23 fiveEvenEntry12 fiveEvenEntry13
        ring
      _ > 0 := by positivity

  have h2 : 0 < (tailMatrix (tailMatrix (fiveEven p r))).det := by
    calc
      _ = 412*p^6 + 2108*p^5*r + 4271*p^4*r^2 + 4368*p^3*r^3 + 2106*p^2*r^4 + 468*p*r^5 + 39*r^6 := by
        simp only [Matrix.det_fin_two]
        change
          fiveEvenEntry22 p r * fiveEvenEntry33 p r - fiveEvenEntry23 p r * fiveEvenEntry23 p r = _
        unfold fiveEvenEntry22 fiveEvenEntry33 fiveEvenEntry23
        ring
      _ > 0 := by positivity

  have h1 : 0 < (tailMatrix (tailMatrix (tailMatrix (fiveEven p r)))).det := by
    calc
      _ = 32*p^2 + 64*p*r + 16*r^2 := by
        simp only [Matrix.det_unique]
        change
          fiveEvenEntry33 p r = _
        unfold fiveEvenEntry33
        ring
      _ > 0 := by positivity

  exact posSemidef_of_trailing_minors hs h4 ⟨h3, h2, h1, trivial⟩

private def fiveOdd (a c : ℝ) : ℝ :=
  14*a^4*c^4*(a - c)^2

private def fiveEvenVec (b : ℝ) : Fin 4 → ℝ := ![1, b^4, b^6, b^8]

private def fiveQuartic (a c b d : ℝ) : ℝ :=
  (2) * (polyGram (fiveEven (a*c) ((a-c)^2)) fiveEvenVec b d + fiveOdd a c * (b^5 * d^5))

set_option maxHeartbeats 4000000 in
/-- The exact integer Gram certificate for `(5,4)`. -/
def quarticCertificateFive : QuarticCertificate 5 4 5 where
  kernel := fiveQuartic
  positive a c ha hc :=
    ((positive_polyGram _ (fiveEven_positive _ _ (mul_pos ha hc) (sq_nonneg _)) fiveEvenVec).add
      ((PositiveKernel.rankOne (fun b : ℝ => b^5)).scale (by unfold fiveOdd; positivity))).scale (by norm_num)
  cyclic a b c d := by
    norm_num [fiveQuartic, fiveEven, fiveOdd, polyGram, fiveEvenVec,
      homogeneousFour, homogeneous, Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    simp only [fiveEvenEntry00, fiveEvenEntry01, fiveEvenEntry02, fiveEvenEntry03, fiveEvenEntry11, fiveEvenEntry12, fiveEvenEntry13, fiveEvenEntry22, fiveEvenEntry23, fiveEvenEntry33]
    ring

private def sixEvenEntry00 (p r : ℝ) : ℝ :=
  2*p^6 + 112*p^5*r + 252*p^4*r^2 + 240*p^3*r^3 + 110*p^2*r^4 + 24*p*r^5 + 2*r^6

private def sixEvenEntry01 (p r : ℝ) : ℝ :=
  -2*p^5 + 63*p^4*r + 112*p^3*r^2 + 72*p^2*r^3 + 20*p*r^4 + 2*r^5

private def sixEvenEntry02 (p r : ℝ) : ℝ :=
  -p^4 + 36*p^3*r + 41*p^2*r^2 + 16*p*r^3 + 2*r^4

private def sixEvenEntry03 (p r : ℝ) : ℝ :=
  p^3 + 9*p^2*r + 6*p*r^2 + r^3

private def sixEvenEntry11 (p r : ℝ) : ℝ :=
  64*p^4 + 156*p^3*r + 71*p^2*r^2 + 16*p*r^3 + 2*r^4

private def sixEvenEntry12 (p r : ℝ) : ℝ :=
  -35*p^3 + 19*p^2*r + 12*p*r^2 + 2*r^3

private def sixEvenEntry13 (p r : ℝ) : ℝ :=
  -27*p^2 + 4*p*r + r^2

private def sixEvenEntry22 (p r : ℝ) : ℝ :=
  22*p^2 + 36*p*r + 9*r^2

private def sixEvenEntry23 (p r : ℝ) : ℝ :=
  14*p + 7*r

private def sixEvenEntry33 (_p _r : ℝ) : ℝ :=
  12

private def sixEven (p r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![sixEvenEntry00 p r, sixEvenEntry01 p r, sixEvenEntry02 p r, sixEvenEntry03 p r;
    sixEvenEntry01 p r, sixEvenEntry11 p r, sixEvenEntry12 p r, sixEvenEntry13 p r;
    sixEvenEntry02 p r, sixEvenEntry12 p r, sixEvenEntry22 p r, sixEvenEntry23 p r;
    sixEvenEntry03 p r, sixEvenEntry13 p r, sixEvenEntry23 p r, sixEvenEntry33 p r]

set_option maxHeartbeats 4000000 in
private theorem sixEven_positive (p r : ℝ) (hp : 0 < p) (hr : 0 ≤ r) :
    ((sixEven p r).map Complex.ofReal).PosSemidef := by
  apply posSemidef_complexify
  have hs : (sixEven p r).IsHermitian := by
    change (sixEven p r)ᴴ = sixEven p r
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h4 : 0 ≤ (sixEven p r).det := by
    calc
      _ = 42920*p^11*r + 1202052*p^10*r^2 + 4559236*p^9*r^3 + 8116689*p^8*r^4 + 8293174*p^7*r^5 +
            5119312*p^6*r^6 + 1923426*p^5*r^7 + 428118*p^4*r^8 + 51620*p^3*r^9 + 2581*p^2*r^10 := by
        simp only [Matrix.det_fin_three, det_four_entries]
        change
          sixEvenEntry00 p r * (sixEvenEntry11 p r * sixEvenEntry22 p r * sixEvenEntry33 p r - sixEvenEntry11 p r *
            sixEvenEntry23 p r * sixEvenEntry23 p r - sixEvenEntry12 p r * sixEvenEntry12 p r * sixEvenEntry33 p r
            + sixEvenEntry12 p r * sixEvenEntry23 p r * sixEvenEntry13 p r + sixEvenEntry13 p r * sixEvenEntry12 p
            r * sixEvenEntry23 p r - sixEvenEntry13 p r * sixEvenEntry22 p r * sixEvenEntry13 p r) - sixEvenEntry01
            p r * (sixEvenEntry01 p r * sixEvenEntry22 p r * sixEvenEntry33 p r - sixEvenEntry01 p r *
            sixEvenEntry23 p r * sixEvenEntry23 p r - sixEvenEntry12 p r * sixEvenEntry02 p r * sixEvenEntry33 p r
            + sixEvenEntry12 p r * sixEvenEntry23 p r * sixEvenEntry03 p r + sixEvenEntry13 p r * sixEvenEntry02 p
            r * sixEvenEntry23 p r - sixEvenEntry13 p r * sixEvenEntry22 p r * sixEvenEntry03 p r) + sixEvenEntry02
            p r * (sixEvenEntry01 p r * sixEvenEntry12 p r * sixEvenEntry33 p r - sixEvenEntry01 p r *
            sixEvenEntry23 p r * sixEvenEntry13 p r - sixEvenEntry11 p r * sixEvenEntry02 p r * sixEvenEntry33 p r
            + sixEvenEntry11 p r * sixEvenEntry23 p r * sixEvenEntry03 p r + sixEvenEntry13 p r * sixEvenEntry02 p
            r * sixEvenEntry13 p r - sixEvenEntry13 p r * sixEvenEntry12 p r * sixEvenEntry03 p r) - sixEvenEntry03
            p r * (sixEvenEntry01 p r * sixEvenEntry12 p r * sixEvenEntry23 p r - sixEvenEntry01 p r *
            sixEvenEntry22 p r * sixEvenEntry13 p r - sixEvenEntry11 p r * sixEvenEntry02 p r * sixEvenEntry23 p r
            + sixEvenEntry11 p r * sixEvenEntry22 p r * sixEvenEntry03 p r + sixEvenEntry12 p r * sixEvenEntry02 p
            r * sixEvenEntry13 p r - sixEvenEntry12 p r * sixEvenEntry12 p r * sixEvenEntry03 p r) = _
        unfold sixEvenEntry00 sixEvenEntry11 sixEvenEntry22 sixEvenEntry33 sixEvenEntry23 sixEvenEntry12 sixEvenEntry13 sixEvenEntry01 sixEvenEntry02 sixEvenEntry03
        ring
      _ ≥ 0 := by positivity

  have h3 : 0 < (tailMatrix (sixEven p r)).det := by
    calc
      _ = 74*p^6 + 15126*p^5*r + 36153*p^4*r^2 + 22794*p^3*r^3 + 6235*p^2*r^4 + 1068*p*r^5 + 89*r^6 := by
        simp only [Matrix.det_fin_three]
        change
          sixEvenEntry11 p r * sixEvenEntry22 p r * sixEvenEntry33 p r - sixEvenEntry11 p r * sixEvenEntry23 p r *
            sixEvenEntry23 p r - sixEvenEntry12 p r * sixEvenEntry12 p r * sixEvenEntry33 p r + sixEvenEntry12 p r
            * sixEvenEntry23 p r * sixEvenEntry13 p r + sixEvenEntry13 p r * sixEvenEntry12 p r * sixEvenEntry23 p
            r - sixEvenEntry13 p r * sixEvenEntry22 p r * sixEvenEntry13 p r = _
        unfold sixEvenEntry11 sixEvenEntry22 sixEvenEntry33 sixEvenEntry23 sixEvenEntry12 sixEvenEntry13
        ring
      _ > 0 := by positivity

  have h2 : 0 < (tailMatrix (tailMatrix (sixEven p r))).det := by
    calc
      _ = 68*p^2 + 236*p*r + 59*r^2 := by
        simp only [Matrix.det_fin_two]
        change
          sixEvenEntry22 p r * sixEvenEntry33 p r - sixEvenEntry23 p r * sixEvenEntry23 p r = _
        unfold sixEvenEntry22 sixEvenEntry33 sixEvenEntry23
        ring
      _ > 0 := by positivity

  have h1 : 0 < (tailMatrix (tailMatrix (tailMatrix (sixEven p r)))).det := by
    calc
      _ = (12 : ℝ) := by
        simp only [Matrix.det_unique]
        change
          sixEvenEntry33 p r = _
        unfold sixEvenEntry33
        ring
      _ > 0 := by positivity

  exact posSemidef_of_trailing_minors hs h4 ⟨h3, h2, h1, trivial⟩

private def sixOdd (a c : ℝ) : ℝ :=
  (a-c)^2 * (a^4 + 2*a^3*c + 44*a^2*c^2 + 2*a*c^3 + c^4)

private def sixEvenVec (b : ℝ) : Fin 4 → ℝ := ![1, b^2, b^4, b^6]

private def sixQuartic (a c b d : ℝ) : ℝ :=
  polyGram (sixEven (a*c) ((a-c)^2)) sixEvenVec b d + sixOdd a c * (b^3 * d^3)

set_option maxHeartbeats 4000000 in
/-- The exact integer Gram certificate for `(6,4)`. -/
def quarticCertificateSix : QuarticCertificate 6 2 3 where
  kernel := sixQuartic
  positive a c ha hc :=
    (positive_polyGram _ (sixEven_positive _ _ (mul_pos ha hc) (sq_nonneg _)) sixEvenVec).add
      ((PositiveKernel.rankOne (fun b : ℝ => b^3)).scale (by unfold sixOdd; positivity))
  cyclic a b c d := by
    norm_num [sixQuartic, sixEven, sixOdd, polyGram, sixEvenVec,
      homogeneousFour, homogeneous, Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    simp only [sixEvenEntry00, sixEvenEntry01, sixEvenEntry02, sixEvenEntry03, sixEvenEntry11, sixEvenEntry12, sixEvenEntry13, sixEvenEntry22, sixEvenEntry23, sixEvenEntry33]
    ring

private def eightEvenEntry00 (p r : ℝ) : ℝ :=
  7*p^8 + 480*p^7*r + 1848*p^6*r^2 + 3168*p^5*r^3 + 2860*p^4*r^4 + 1456*p^3*r^5 + 420*p^2*r^6 +
    64*p*r^7 + 4*r^8

private def eightEvenEntry01 (p r : ℝ) : ℝ :=
  2*p^7 + 321*p^6*r + 1008*p^5*r^2 + 1320*p^4*r^3 + 880*p^3*r^4 + 312*p^2*r^5 + 56*p*r^6 +
    4*r^7

private def eightEvenEntry02 (p r : ℝ) : ℝ :=
  3*p^6 + 224*p^5*r + 504*p^4*r^2 + 480*p^3*r^3 + 220*p^2*r^4 + 48*p*r^5 + 4*r^6

private def eightEvenEntry03 (p r : ℝ) : ℝ :=
  -8*p^5 + 123*p^4*r + 212*p^3*r^2 + 142*p^2*r^3 + 40*p*r^4 + 4*r^5

private def eightEvenEntry04 (p r : ℝ) : ℝ :=
  -4*p^4 + 32*p^3*r + 40*p^2*r^2 + 16*p*r^3 + 2*r^4

private def eightEvenEntry11 (p r : ℝ) : ℝ :=
  144*p^6 + 428*p^5*r + 555*p^4*r^2 + 480*p^3*r^3 + 220*p^2*r^4 + 48*p*r^5 + 4*r^6

private def eightEvenEntry12 (p r : ℝ) : ℝ :=
  -152*p^5 + 43*p^4*r + 176*p^3*r^2 + 136*p^2*r^3 + 40*p*r^4 + 4*r^5

private def eightEvenEntry13 (p r : ℝ) : ℝ :=
  10*p^4 + 106*p^3*r + 82*p^2*r^2 + 32*p*r^3 + 4*r^4

private def eightEvenEntry14 (p r : ℝ) : ℝ :=
  -4*p^3 + 26*p^2*r + 12*p*r^2 + 2*r^3

private def eightEvenEntry22 (p r : ℝ) : ℝ :=
  268*p^4 + 700*p^3*r + 314*p^2*r^2 + 96*p*r^3 + 12*r^4

private def eightEvenEntry23 (p r : ℝ) : ℝ :=
  -68*p^3 + 16*p^2*r - 6*p*r^2 - r^3

private def eightEvenEntry24 (p _r : ℝ) : ℝ :=
  -51*p^2

private def eightEvenEntry33 (p r : ℝ) : ℝ :=
  36*p^2 + 100*p*r + 25*r^2

private def eightEvenEntry34 (p r : ℝ) : ℝ :=
  30*p + 15*r

private def eightEvenEntry44 (_p _r : ℝ) : ℝ :=
  29

private def eightEven (p r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![eightEvenEntry00 p r, eightEvenEntry01 p r, eightEvenEntry02 p r, eightEvenEntry03 p r, eightEvenEntry04 p r;
    eightEvenEntry01 p r, eightEvenEntry11 p r, eightEvenEntry12 p r, eightEvenEntry13 p r, eightEvenEntry14 p r;
    eightEvenEntry02 p r, eightEvenEntry12 p r, eightEvenEntry22 p r, eightEvenEntry23 p r, eightEvenEntry24 p r;
    eightEvenEntry03 p r, eightEvenEntry13 p r, eightEvenEntry23 p r, eightEvenEntry33 p r, eightEvenEntry34 p r;
    eightEvenEntry04 p r, eightEvenEntry14 p r, eightEvenEntry24 p r, eightEvenEntry34 p r, eightEvenEntry44 p r]

set_option maxHeartbeats 4000000 in
private theorem eightEven_positive (p r : ℝ) (hp : 0 < p) (hr : 0 ≤ r) :
    ((eightEven p r).map Complex.ofReal).PosSemidef := by
  apply posSemidef_complexify
  have hs : (eightEven p r).IsHermitian := by
    change (eightEven p r)ᴴ = eightEven p r
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h5 : 0 ≤ (eightEven p r).det := by
    calc
      _ = 101671680*p^19*r + 8599634628*p^18*r^2 + 94023154784*p^17*r^3 + 415044258208*p^16*r^4 +
            1023504058512*p^15*r^5 + 1581946878798*p^14*r^6 + 1634461596064*p^13*r^7 +
            1179521718124*p^12*r^8 + 612958588104*p^11*r^9 + 233982432580*p^10*r^10 +
            66258984080*p^9*r^11 + 13885830484*p^8*r^12 + 2109248288*p^7*r^13 + 220537028*p^6*r^14 +
            14188032*p^5*r^15 + 421264*p^4*r^16 := by
        simp only [Matrix.det_fin_three, det_four_entries, det_five_entries]
        change
          eightEvenEntry00 p r * (eightEvenEntry11 p r * (eightEvenEntry22 p r * eightEvenEntry33 p r *
            eightEvenEntry44 p r - eightEvenEntry22 p r * eightEvenEntry34 p r * eightEvenEntry34 p r -
            eightEvenEntry23 p r * eightEvenEntry23 p r * eightEvenEntry44 p r + eightEvenEntry23 p r *
            eightEvenEntry34 p r * eightEvenEntry24 p r + eightEvenEntry24 p r * eightEvenEntry23 p r *
            eightEvenEntry34 p r - eightEvenEntry24 p r * eightEvenEntry33 p r * eightEvenEntry24 p r) -
            eightEvenEntry12 p r * (eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry44 p r -
            eightEvenEntry12 p r * eightEvenEntry34 p r * eightEvenEntry34 p r - eightEvenEntry23 p r *
            eightEvenEntry13 p r * eightEvenEntry44 p r + eightEvenEntry23 p r * eightEvenEntry34 p r *
            eightEvenEntry14 p r + eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry34 p r -
            eightEvenEntry24 p r * eightEvenEntry33 p r * eightEvenEntry14 p r) + eightEvenEntry13 p r *
            (eightEvenEntry12 p r * eightEvenEntry23 p r * eightEvenEntry44 p r - eightEvenEntry12 p r *
            eightEvenEntry34 p r * eightEvenEntry24 p r - eightEvenEntry22 p r * eightEvenEntry13 p r *
            eightEvenEntry44 p r + eightEvenEntry22 p r * eightEvenEntry34 p r * eightEvenEntry14 p r +
            eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry24 p r - eightEvenEntry24 p r *
            eightEvenEntry23 p r * eightEvenEntry14 p r) - eightEvenEntry14 p r * (eightEvenEntry12 p r *
            eightEvenEntry23 p r * eightEvenEntry34 p r - eightEvenEntry12 p r * eightEvenEntry33 p r *
            eightEvenEntry24 p r - eightEvenEntry22 p r * eightEvenEntry13 p r * eightEvenEntry34 p r +
            eightEvenEntry22 p r * eightEvenEntry33 p r * eightEvenEntry14 p r + eightEvenEntry23 p r *
            eightEvenEntry13 p r * eightEvenEntry24 p r - eightEvenEntry23 p r * eightEvenEntry23 p r *
            eightEvenEntry14 p r)) - eightEvenEntry01 p r * (eightEvenEntry01 p r * (eightEvenEntry22 p r *
            eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry22 p r * eightEvenEntry34 p r *
            eightEvenEntry34 p r - eightEvenEntry23 p r * eightEvenEntry23 p r * eightEvenEntry44 p r +
            eightEvenEntry23 p r * eightEvenEntry34 p r * eightEvenEntry24 p r + eightEvenEntry24 p r *
            eightEvenEntry23 p r * eightEvenEntry34 p r - eightEvenEntry24 p r * eightEvenEntry33 p r *
            eightEvenEntry24 p r) - eightEvenEntry12 p r * (eightEvenEntry02 p r * eightEvenEntry33 p r *
            eightEvenEntry44 p r - eightEvenEntry02 p r * eightEvenEntry34 p r * eightEvenEntry34 p r -
            eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry44 p r + eightEvenEntry23 p r *
            eightEvenEntry34 p r * eightEvenEntry04 p r + eightEvenEntry24 p r * eightEvenEntry03 p r *
            eightEvenEntry34 p r - eightEvenEntry24 p r * eightEvenEntry33 p r * eightEvenEntry04 p r) +
            eightEvenEntry13 p r * (eightEvenEntry02 p r * eightEvenEntry23 p r * eightEvenEntry44 p r -
            eightEvenEntry02 p r * eightEvenEntry34 p r * eightEvenEntry24 p r - eightEvenEntry22 p r *
            eightEvenEntry03 p r * eightEvenEntry44 p r + eightEvenEntry22 p r * eightEvenEntry34 p r *
            eightEvenEntry04 p r + eightEvenEntry24 p r * eightEvenEntry03 p r * eightEvenEntry24 p r -
            eightEvenEntry24 p r * eightEvenEntry23 p r * eightEvenEntry04 p r) - eightEvenEntry14 p r *
            (eightEvenEntry02 p r * eightEvenEntry23 p r * eightEvenEntry34 p r - eightEvenEntry02 p r *
            eightEvenEntry33 p r * eightEvenEntry24 p r - eightEvenEntry22 p r * eightEvenEntry03 p r *
            eightEvenEntry34 p r + eightEvenEntry22 p r * eightEvenEntry33 p r * eightEvenEntry04 p r +
            eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry24 p r - eightEvenEntry23 p r *
            eightEvenEntry23 p r * eightEvenEntry04 p r)) + eightEvenEntry02 p r * (eightEvenEntry01 p r *
            (eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry12 p r *
            eightEvenEntry34 p r * eightEvenEntry34 p r - eightEvenEntry23 p r * eightEvenEntry13 p r *
            eightEvenEntry44 p r + eightEvenEntry23 p r * eightEvenEntry34 p r * eightEvenEntry14 p r +
            eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry34 p r - eightEvenEntry24 p r *
            eightEvenEntry33 p r * eightEvenEntry14 p r) - eightEvenEntry11 p r * (eightEvenEntry02 p r *
            eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry02 p r * eightEvenEntry34 p r *
            eightEvenEntry34 p r - eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry44 p r +
            eightEvenEntry23 p r * eightEvenEntry34 p r * eightEvenEntry04 p r + eightEvenEntry24 p r *
            eightEvenEntry03 p r * eightEvenEntry34 p r - eightEvenEntry24 p r * eightEvenEntry33 p r *
            eightEvenEntry04 p r) + eightEvenEntry13 p r * (eightEvenEntry02 p r * eightEvenEntry13 p r *
            eightEvenEntry44 p r - eightEvenEntry02 p r * eightEvenEntry34 p r * eightEvenEntry14 p r -
            eightEvenEntry12 p r * eightEvenEntry03 p r * eightEvenEntry44 p r + eightEvenEntry12 p r *
            eightEvenEntry34 p r * eightEvenEntry04 p r + eightEvenEntry24 p r * eightEvenEntry03 p r *
            eightEvenEntry14 p r - eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry04 p r) -
            eightEvenEntry14 p r * (eightEvenEntry02 p r * eightEvenEntry13 p r * eightEvenEntry34 p r -
            eightEvenEntry02 p r * eightEvenEntry33 p r * eightEvenEntry14 p r - eightEvenEntry12 p r *
            eightEvenEntry03 p r * eightEvenEntry34 p r + eightEvenEntry12 p r * eightEvenEntry33 p r *
            eightEvenEntry04 p r + eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry14 p r -
            eightEvenEntry23 p r * eightEvenEntry13 p r * eightEvenEntry04 p r)) - eightEvenEntry03 p r *
            (eightEvenEntry01 p r * (eightEvenEntry12 p r * eightEvenEntry23 p r * eightEvenEntry44 p r -
            eightEvenEntry12 p r * eightEvenEntry34 p r * eightEvenEntry24 p r - eightEvenEntry22 p r *
            eightEvenEntry13 p r * eightEvenEntry44 p r + eightEvenEntry22 p r * eightEvenEntry34 p r *
            eightEvenEntry14 p r + eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry24 p r -
            eightEvenEntry24 p r * eightEvenEntry23 p r * eightEvenEntry14 p r) - eightEvenEntry11 p r *
            (eightEvenEntry02 p r * eightEvenEntry23 p r * eightEvenEntry44 p r - eightEvenEntry02 p r *
            eightEvenEntry34 p r * eightEvenEntry24 p r - eightEvenEntry22 p r * eightEvenEntry03 p r *
            eightEvenEntry44 p r + eightEvenEntry22 p r * eightEvenEntry34 p r * eightEvenEntry04 p r +
            eightEvenEntry24 p r * eightEvenEntry03 p r * eightEvenEntry24 p r - eightEvenEntry24 p r *
            eightEvenEntry23 p r * eightEvenEntry04 p r) + eightEvenEntry12 p r * (eightEvenEntry02 p r *
            eightEvenEntry13 p r * eightEvenEntry44 p r - eightEvenEntry02 p r * eightEvenEntry34 p r *
            eightEvenEntry14 p r - eightEvenEntry12 p r * eightEvenEntry03 p r * eightEvenEntry44 p r +
            eightEvenEntry12 p r * eightEvenEntry34 p r * eightEvenEntry04 p r + eightEvenEntry24 p r *
            eightEvenEntry03 p r * eightEvenEntry14 p r - eightEvenEntry24 p r * eightEvenEntry13 p r *
            eightEvenEntry04 p r) - eightEvenEntry14 p r * (eightEvenEntry02 p r * eightEvenEntry13 p r *
            eightEvenEntry24 p r - eightEvenEntry02 p r * eightEvenEntry23 p r * eightEvenEntry14 p r -
            eightEvenEntry12 p r * eightEvenEntry03 p r * eightEvenEntry24 p r + eightEvenEntry12 p r *
            eightEvenEntry23 p r * eightEvenEntry04 p r + eightEvenEntry22 p r * eightEvenEntry03 p r *
            eightEvenEntry14 p r - eightEvenEntry22 p r * eightEvenEntry13 p r * eightEvenEntry04 p r)) +
            eightEvenEntry04 p r * (eightEvenEntry01 p r * (eightEvenEntry12 p r * eightEvenEntry23 p r *
            eightEvenEntry34 p r - eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry24 p r -
            eightEvenEntry22 p r * eightEvenEntry13 p r * eightEvenEntry34 p r + eightEvenEntry22 p r *
            eightEvenEntry33 p r * eightEvenEntry14 p r + eightEvenEntry23 p r * eightEvenEntry13 p r *
            eightEvenEntry24 p r - eightEvenEntry23 p r * eightEvenEntry23 p r * eightEvenEntry14 p r) -
            eightEvenEntry11 p r * (eightEvenEntry02 p r * eightEvenEntry23 p r * eightEvenEntry34 p r -
            eightEvenEntry02 p r * eightEvenEntry33 p r * eightEvenEntry24 p r - eightEvenEntry22 p r *
            eightEvenEntry03 p r * eightEvenEntry34 p r + eightEvenEntry22 p r * eightEvenEntry33 p r *
            eightEvenEntry04 p r + eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry24 p r -
            eightEvenEntry23 p r * eightEvenEntry23 p r * eightEvenEntry04 p r) + eightEvenEntry12 p r *
            (eightEvenEntry02 p r * eightEvenEntry13 p r * eightEvenEntry34 p r - eightEvenEntry02 p r *
            eightEvenEntry33 p r * eightEvenEntry14 p r - eightEvenEntry12 p r * eightEvenEntry03 p r *
            eightEvenEntry34 p r + eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry04 p r +
            eightEvenEntry23 p r * eightEvenEntry03 p r * eightEvenEntry14 p r - eightEvenEntry23 p r *
            eightEvenEntry13 p r * eightEvenEntry04 p r) - eightEvenEntry13 p r * (eightEvenEntry02 p r *
            eightEvenEntry13 p r * eightEvenEntry24 p r - eightEvenEntry02 p r * eightEvenEntry23 p r *
            eightEvenEntry14 p r - eightEvenEntry12 p r * eightEvenEntry03 p r * eightEvenEntry24 p r +
            eightEvenEntry12 p r * eightEvenEntry23 p r * eightEvenEntry04 p r + eightEvenEntry22 p r *
            eightEvenEntry03 p r * eightEvenEntry14 p r - eightEvenEntry22 p r * eightEvenEntry13 p r *
            eightEvenEntry04 p r)) = _
        unfold eightEvenEntry00 eightEvenEntry11 eightEvenEntry22 eightEvenEntry33 eightEvenEntry44 eightEvenEntry34 eightEvenEntry23 eightEvenEntry24 eightEvenEntry12 eightEvenEntry13 eightEvenEntry14 eightEvenEntry01 eightEvenEntry02 eightEvenEntry03 eightEvenEntry04
        ring
      _ ≥ 0 := by positivity

  have h4 : 0 < (tailMatrix (eightEven p r)).det := by
    calc
      _ = 28884*p^12 + 21562320*p^11*r + 369556796*p^10*r^2 + 937375532*p^9*r^3 + 1257934641*p^8*r^4 +
            1145951412*p^7*r^5 + 726159114*p^6*r^6 + 318238400*p^5*r^7 + 97268221*p^4*r^8 +
            20786960*p^3*r^9 + 3022124*p^2*r^10 + 271488*p*r^11 + 11312*r^12 := by
        simp only [Matrix.det_fin_three, det_four_entries]
        change
          eightEvenEntry11 p r * (eightEvenEntry22 p r * eightEvenEntry33 p r * eightEvenEntry44 p r -
            eightEvenEntry22 p r * eightEvenEntry34 p r * eightEvenEntry34 p r - eightEvenEntry23 p r *
            eightEvenEntry23 p r * eightEvenEntry44 p r + eightEvenEntry23 p r * eightEvenEntry34 p r *
            eightEvenEntry24 p r + eightEvenEntry24 p r * eightEvenEntry23 p r * eightEvenEntry34 p r -
            eightEvenEntry24 p r * eightEvenEntry33 p r * eightEvenEntry24 p r) - eightEvenEntry12 p r *
            (eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry12 p r *
            eightEvenEntry34 p r * eightEvenEntry34 p r - eightEvenEntry23 p r * eightEvenEntry13 p r *
            eightEvenEntry44 p r + eightEvenEntry23 p r * eightEvenEntry34 p r * eightEvenEntry14 p r +
            eightEvenEntry24 p r * eightEvenEntry13 p r * eightEvenEntry34 p r - eightEvenEntry24 p r *
            eightEvenEntry33 p r * eightEvenEntry14 p r) + eightEvenEntry13 p r * (eightEvenEntry12 p r *
            eightEvenEntry23 p r * eightEvenEntry44 p r - eightEvenEntry12 p r * eightEvenEntry34 p r *
            eightEvenEntry24 p r - eightEvenEntry22 p r * eightEvenEntry13 p r * eightEvenEntry44 p r +
            eightEvenEntry22 p r * eightEvenEntry34 p r * eightEvenEntry14 p r + eightEvenEntry24 p r *
            eightEvenEntry13 p r * eightEvenEntry24 p r - eightEvenEntry24 p r * eightEvenEntry23 p r *
            eightEvenEntry14 p r) - eightEvenEntry14 p r * (eightEvenEntry12 p r * eightEvenEntry23 p r *
            eightEvenEntry34 p r - eightEvenEntry12 p r * eightEvenEntry33 p r * eightEvenEntry24 p r -
            eightEvenEntry22 p r * eightEvenEntry13 p r * eightEvenEntry34 p r + eightEvenEntry22 p r *
            eightEvenEntry33 p r * eightEvenEntry14 p r + eightEvenEntry23 p r * eightEvenEntry13 p r *
            eightEvenEntry24 p r - eightEvenEntry23 p r * eightEvenEntry23 p r * eightEvenEntry14 p r) = _
        unfold eightEvenEntry11 eightEvenEntry22 eightEvenEntry33 eightEvenEntry44 eightEvenEntry34 eightEvenEntry23 eightEvenEntry24 eightEvenEntry12 eightEvenEntry13 eightEvenEntry14
        ring
      _ > 0 := by positivity

  have h3 : 0 < (tailMatrix (tailMatrix (eightEven p r))).det := by
    calc
      _ = 18940*p^6 + 494884*p^5*r + 1476983*p^4*r^2 + 1005688*p^3*r^3 + 352142*p^2*r^4 + 71652*p*r^5 +
            5971*r^6 := by
        simp only [Matrix.det_fin_three]
        change
          eightEvenEntry22 p r * eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry22 p r *
            eightEvenEntry34 p r * eightEvenEntry34 p r - eightEvenEntry23 p r * eightEvenEntry23 p r *
            eightEvenEntry44 p r + eightEvenEntry23 p r * eightEvenEntry34 p r * eightEvenEntry24 p r +
            eightEvenEntry24 p r * eightEvenEntry23 p r * eightEvenEntry34 p r - eightEvenEntry24 p r *
            eightEvenEntry33 p r * eightEvenEntry24 p r = _
        unfold eightEvenEntry22 eightEvenEntry33 eightEvenEntry44 eightEvenEntry34 eightEvenEntry23 eightEvenEntry24
        ring
      _ > 0 := by positivity

  have h2 : 0 < (tailMatrix (tailMatrix (tailMatrix (eightEven p r)))).det := by
    calc
      _ = 144*p^2 + 2000*p*r + 500*r^2 := by
        simp only [Matrix.det_fin_two]
        change
          eightEvenEntry33 p r * eightEvenEntry44 p r - eightEvenEntry34 p r * eightEvenEntry34 p r = _
        unfold eightEvenEntry33 eightEvenEntry44 eightEvenEntry34
        ring
      _ > 0 := by positivity

  have h1 : 0 < (tailMatrix (tailMatrix (tailMatrix (tailMatrix (eightEven p r))))).det := by
    calc
      _ = (29 : ℝ) := by
        simp only [Matrix.det_unique]
        change
          eightEvenEntry44 p r = _
        unfold eightEvenEntry44
        ring
      _ > 0 := by positivity

  exact posSemidef_of_trailing_minors hs h5 ⟨h4, h3, h2, h1, trivial⟩

private def eightOddEntry00 (p r : ℝ) : ℝ :=
  280*p^5 + 332*p^4*r + 144*p^3*r^2 + 24*p^2*r^3

private def eightOddEntry01 (p r : ℝ) : ℝ :=
  -280*p^4 - 136*p^3*r - 34*p^2*r^2

private def eightOddEntry11 (p r : ℝ) : ℝ :=
  280*p^3 + 380*p^2*r + 180*p*r^2 + 30*r^3

private def eightOdd (p r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![eightOddEntry00 p r, eightOddEntry01 p r;
    eightOddEntry01 p r, eightOddEntry11 p r]

set_option maxHeartbeats 4000000 in
private theorem eightOdd_positive (p r : ℝ) (hp : 0 < p) (hr : 0 ≤ r) :
    ((eightOdd p r).map Complex.ofReal).PosSemidef := by
  apply posSemidef_complexify
  have hs : (eightOdd p r).IsHermitian := by
    change (eightOdd p r)ᴴ = eightOdd p r
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

  have h2 : 0 ≤ (eightOdd p r).det := by
    calc
      _ = 123200*p^7*r + 179344*p^6*r^2 + 120352*p^5*r^3 + 43844*p^4*r^4 + 8640*p^3*r^5 + 720*p^2*r^6 := by
        simp only [Matrix.det_fin_two]
        change
          eightOddEntry00 p r * eightOddEntry11 p r - eightOddEntry01 p r * eightOddEntry01 p r = _
        unfold eightOddEntry00 eightOddEntry11 eightOddEntry01
        ring
      _ ≥ 0 := by positivity

  have h1 : 0 < (tailMatrix (eightOdd p r)).det := by
    calc
      _ = 280*p^3 + 380*p^2*r + 180*p*r^2 + 30*r^3 := by
        simp only [Matrix.det_unique]
        change
          eightOddEntry11 p r = _
        unfold eightOddEntry11
        ring
      _ > 0 := by positivity

  exact posSemidef_of_trailing_minors hs h2 ⟨h1, trivial⟩

private def eightEvenVec (b : ℝ) : Fin 5 → ℝ := ![1, b^2, b^4, b^6, b^8]

private def eightOddVec (b : ℝ) : Fin 2 → ℝ := ![b^3, b^5]

private def eightQuartic (a c b d : ℝ) : ℝ :=
  (1/2) * (polyGram (eightEven (a*c) ((a-c)^2)) eightEvenVec b d + polyGram (eightOdd (a*c) ((a-c)^2)) eightOddVec b d)

set_option maxHeartbeats 4000000 in
/-- The exact integer Gram certificate for `(8,4)`. -/
def quarticCertificateEight : QuarticCertificate 8 2 4 where
  kernel := eightQuartic
  positive a c ha hc :=
    ((positive_polyGram _ (eightEven_positive _ _ (mul_pos ha hc) (sq_nonneg _)) eightEvenVec).add
      (positive_polyGram _ (eightOdd_positive _ _ (mul_pos ha hc) (sq_nonneg _)) eightOddVec)).scale (by norm_num)
  cyclic a b c d := by
    norm_num [eightQuartic, eightEven, eightOdd, polyGram, eightEvenVec, eightOddVec,
      homogeneousFour, homogeneous, Fin.sum_univ_succ, sum_range_succ, Nat.choose]
    simp only [eightEvenEntry00, eightEvenEntry01, eightEvenEntry02, eightEvenEntry03, eightEvenEntry04, eightEvenEntry11, eightEvenEntry12, eightEvenEntry13, eightEvenEntry14, eightEvenEntry22, eightEvenEntry23, eightEvenEntry24, eightEvenEntry33, eightEvenEntry34, eightEvenEntry44, eightOddEntry00, eightOddEntry01, eightOddEntry11]
    ring


end

end RefinedBMV
