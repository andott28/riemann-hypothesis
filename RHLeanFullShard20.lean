import RHLeanFullShard19


set_option maxHeartbeats 2000000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option maxRecDepth 1000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option maxHeartbeats 800000

section Inline_ExplicitFormula_RH46




































noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ComplexConjugate

namespace RHLean.ExplicitFormula



theorem spectralTest_eq_normSq {f : ℝ → ℂ} (hf : f ∈ oddCore) (r : ℝ) :
    spectralTest f r = ((‖transf f ((r : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
  rw [spectralTest, transf_autocorr hf.1.continuous hf.2.1]
  have hstar : -(star ((r : ℂ) * I)) = (r : ℂ) * I := by
    rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hstar, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem spectralTest_im_eq_zero {f : ℝ → ℂ} (hf : f ∈ oddCore) (r : ℝ) :
    (spectralTest f r).im = 0 := by
  rw [spectralTest_eq_normSq hf r, Complex.ofReal_im]



theorem integral_cos_mul_spectralTest {f : ℝ → ℂ} (hf : f ∈ oddCore) (x : ℝ) :
    (∫ r : ℝ, Real.cos (x * r) * (spectralTest f r).re)
      = 2 * Real.pi * (autocorr f x).re := by
  have hexp : ∀ r : ℝ, Complex.exp (-(Complex.I * (x : ℂ)) * (r : ℂ))
      = (Real.cos (x * r) : ℂ) - (Real.sin (x * r) : ℂ) * I := by
    intro r
    rw [show -(Complex.I * (x : ℂ)) * (r : ℂ) = (((-(x * r) : ℝ)) : ℂ) * I by
        push_cast
        ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hpt : ∀ r : ℝ,
      (spectralTest f r * Complex.exp (-(Complex.I * (x : ℂ)) * (r : ℂ))).re
        = Real.cos (x * r) * (spectralTest f r).re := by
    intro r
    rw [hexp r]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [spectralTest_im_eq_zero hf r]
    ring
  have hint : Integrable (fun r : ℝ =>
      spectralTest f r * Complex.exp (-(Complex.I * (x : ℂ)) * (r : ℂ))) volume := by
    refine (integrable_spectralTest hf).mul_bdd (c := 1)
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with r
    have hre : (-(Complex.I * (x : ℂ)) * (r : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im]
    rw [Complex.norm_exp, hre, Real.exp_zero]
  calc (∫ r : ℝ, Real.cos (x * r) * (spectralTest f r).re)
      = ∫ r : ℝ, (spectralTest f r
          * Complex.exp (-(Complex.I * (x : ℂ)) * (r : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards with r
        rw [hpt r]
    _ = (∫ r : ℝ, spectralTest f r
          * Complex.exp (-(Complex.I * (x : ℂ)) * (r : ℂ))).re := integral_re hint
    _ = 2 * Real.pi * (autocorr f x).re := ghatAt_eq_aux hf x






theorem integral_autocorr_mul_fourierKernel {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {K : ℝ → ℝ} (hK_cont : Continuous K) (hK_int : Integrable K) :
    (∫ x : ℝ, K x * (autocorr f x).re)
      = (1 / (2 * Real.pi)) * ∫ r : ℝ,
          (∫ x : ℝ, K x * Real.cos (x * r)) * (spectralTest f r).re := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hpt : ∀ x : ℝ, K x * (autocorr f x).re
      = (1 / (2 * Real.pi))
          * (K x * ∫ r : ℝ, Real.cos (x * r) * (spectralTest f r).re) := by
    intro x
    rw [integral_cos_mul_spectralTest hf x]
    field_simp
  have hswap : (∫ x : ℝ, ∫ r : ℝ, K x * (Real.cos (x * r) * (spectralTest f r).re))
      = ∫ r : ℝ, ∫ x : ℝ, K x * (Real.cos (x * r) * (spectralTest f r).re) := by
    apply integral_integral_swap
    have hprod : Integrable (fun p : ℝ × ℝ => ‖K p.1‖ * ‖spectralTest f p.2‖)
        (volume.prod volume) :=
      hK_int.norm.mul_prod (integrable_spectralTest hf).norm
    refine Integrable.mono' hprod ?_ ?_
    · have hcont : Continuous (fun p : ℝ × ℝ =>
          K p.1 * (Real.cos (p.1 * p.2) * (spectralTest f p.2).re)) :=
        (hK_cont.comp continuous_fst).mul
          ((Real.continuous_cos.comp (continuous_fst.mul continuous_snd)).mul
            (Complex.continuous_re.comp ((continuous_spectralTest hf).comp continuous_snd)))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      have hcos : |Real.cos (p.1 * p.2)| ≤ 1 := Real.abs_cos_le_one _
      calc ‖K p.1 * (Real.cos (p.1 * p.2) * (spectralTest f p.2).re)‖
          = |K p.1| * (|Real.cos (p.1 * p.2)| * |(spectralTest f p.2).re|) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
        _ ≤ |K p.1| * (1 * ‖spectralTest f p.2‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact mul_le_mul hcos (Complex.abs_re_le_norm _) (abs_nonneg _) zero_le_one
        _ = ‖K p.1‖ * ‖spectralTest f p.2‖ := by rw [Real.norm_eq_abs]; ring
  calc (∫ x : ℝ, K x * (autocorr f x).re)
      = ∫ x : ℝ, (1 / (2 * Real.pi))
          * (K x * ∫ r : ℝ, Real.cos (x * r) * (spectralTest f r).re) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hpt x]
    _ = (1 / (2 * Real.pi)) * ∫ x : ℝ,
          K x * ∫ r : ℝ, Real.cos (x * r) * (spectralTest f r).re :=
        integral_const_mul _ _
    _ = (1 / (2 * Real.pi))
          * ∫ x : ℝ, ∫ r : ℝ, K x * (Real.cos (x * r) * (spectralTest f r).re) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        rw [← integral_const_mul]
    _ = (1 / (2 * Real.pi))
          * ∫ r : ℝ, ∫ x : ℝ, K x * (Real.cos (x * r) * (spectralTest f r).re) := by
        rw [hswap]
    _ = (1 / (2 * Real.pi)) * ∫ r : ℝ,
          (∫ x : ℝ, K x * Real.cos (x * r)) * (spectralTest f r).re := by
        congr 1
        apply integral_congr_ae
        filter_upwards with r
        rw [show (∫ x : ℝ, K x * (Real.cos (x * r) * (spectralTest f r).re))
            = ∫ x : ℝ, (K x * Real.cos (x * r)) * (spectralTest f r).re from
              integral_congr_ae (Eventually.of_forall fun x => by ring)]
        rw [integral_mul_const]



theorem integrable_exp_neg_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-(b * |x|))) volume := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-(b * |x|))) (Set.Ioi 0) volume := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
    ring_nf
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-(b * |x|))) (Set.Iic 0) volume := by
    refine (integrableOn_exp_mul_Iic (a := b) (by linarith) 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [abs_of_nonpos hx]
    congr 1
    ring
  have h := h2.union h1
  rw [Set.Iic_union_Ioi] at h
  simpa [IntegrableOn, Measure.restrict_univ] using h

theorem integrable_exp_neg_abs_mul_exp {b r : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ =>
      (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
      volume := by
  have hbase : Integrable (fun x : ℝ => ((Real.exp (-(b * |x|)) : ℝ) : ℂ)) volume :=
    (integrable_exp_neg_abs hb).ofReal
  refine hbase.mul_bdd (c := 1)
    ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with x
  have hre : (Complex.I * (r : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [Complex.norm_exp, hre, Real.exp_zero]



theorem integral_exp_neg_abs_mul_exp {b r : ℝ} (hb : 0 < b) :
    (∫ x : ℝ,
      (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
      = ((2 * b / (b ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  have hden : ((b : ℂ) + Complex.I * (r : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re, Complex.I_re, Complex.I_im] at hre
    linarith
  have hden' : (-(b : ℂ) + Complex.I * (r : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.mul_re, Complex.I_re, Complex.I_im] at hre
    linarith
  have hIoi : (∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
      = -1 / (-(b : ℂ) + Complex.I * (r : ℂ)) := by
    rw [show (∫ x in Set.Ioi (0 : ℝ),
          (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
        = ∫ x in Set.Ioi (0 : ℝ),
            Complex.exp (((-(b : ℂ)) + Complex.I * (r : ℂ)) * (x : ℂ)) from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))
          = Complex.exp (((-(b : ℂ)) + Complex.I * (r : ℂ)) * (x : ℂ))
      rw [abs_of_pos hx, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring]
    rw [integral_exp_mul_complex_Ioi (a := (-(b : ℂ)) + Complex.I * (r : ℂ)) ?_ 0]
    · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    · simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero]
      linarith
  have hIic : (∫ x in Set.Iic (0 : ℝ),
        (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
      = 1 / ((b : ℂ) + Complex.I * (r : ℂ)) := by
    rw [show (∫ x in Set.Iic (0 : ℝ),
          (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ)))
        = ∫ x in Set.Iic (0 : ℝ),
            Complex.exp (((b : ℂ) + Complex.I * (r : ℂ)) * (x : ℂ)) from by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      change (Real.exp (-(b * |x|)) : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))
          = Complex.exp (((b : ℂ) + Complex.I * (r : ℂ)) * (x : ℂ))
      rw [abs_of_nonpos hx, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring]
    rw [integral_exp_mul_complex_Iic (a := (b : ℂ) + Complex.I * (r : ℂ)) ?_ 0]
    · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero]
      linarith
  have hden2 : ((b : ℂ) ^ 2 + (r : ℂ) ^ 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, ← Complex.ofReal_pow b 2, ← Complex.ofReal_pow r 2,
      Complex.ofReal_re, Complex.ofReal_re, Complex.zero_re] at hre
    nlinarith [sq_nonneg r, hb]
  have hsum : -1 / (-(b : ℂ) + Complex.I * (r : ℂ))
      + 1 / ((b : ℂ) + Complex.I * (r : ℂ)) = ((2 * b / (b ^ 2 + r ^ 2) : ℝ) : ℂ) := by
    rw [show ((2 * b / (b ^ 2 + r ^ 2) : ℝ) : ℂ)
        = 2 * (b : ℂ) / ((b : ℂ) ^ 2 + (r : ℂ) ^ 2) by push_cast; ring]
    field_simp [hden, hden', hden2]
    ring_nf
    rw [show ((Complex.I : ℂ) ^ 2) = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  rw [← integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    (integrable_exp_neg_abs_mul_exp hb), Set.compl_Ioi, hIoi, hIic]
  exact hsum


theorem integral_exp_neg_abs_mul_cos {b r : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, Real.exp (-(b * |x|)) * Real.cos (x * r)) = 2 * b / (b ^ 2 + r ^ 2) := by
  have hint := integrable_exp_neg_abs_mul_exp (b := b) (r := r) hb
  have hpt : ∀ x : ℝ, ((Real.exp (-(b * |x|)) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))).re
      = Real.exp (-(b * |x|)) * Real.cos (x * r) := by
    intro x
    have hexp : Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))
        = (Real.cos (x * r) : ℂ) + (Real.sin (x * r) : ℂ) * I := by
      rw [show Complex.I * (r : ℂ) * (x : ℂ) = ((x * r : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hexp]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have h1 : (∫ x : ℝ, ((Real.exp (-(b * |x|)) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))).re)
      = (∫ x : ℝ, (Real.exp (-(b * |x|)) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))).re := integral_re hint
  rw [integral_exp_neg_abs_mul_exp hb, Complex.ofReal_re] at h1
  rw [show (∫ x : ℝ, ((Real.exp (-(b * |x|)) : ℂ)
        * Complex.exp (Complex.I * (r : ℂ) * (x : ℂ))).re)
      = ∫ x : ℝ, Real.exp (-(b * |x|)) * Real.cos (x * r) from
        integral_congr_ae (Eventually.of_forall hpt)] at h1
  exact h1






theorem integral_spectralTest_expKernel {f : ℝ → ℂ} (hf : f ∈ oddCore) {b : ℝ}
    (hb : 0 < b) :
    (1 / (2 * Real.pi)) * ∫ r : ℝ,
        (2 * b / (b ^ 2 + r ^ 2)) * (spectralTest f r).re
      = ∫ x : ℝ, Real.exp (-(b * |x|)) * (autocorr f x).re := by
  have hbridge := integral_autocorr_mul_fourierKernel hf
    (K := fun x : ℝ => Real.exp (-(b * |x|)))
    (Real.continuous_exp.comp ((continuous_const.mul continuous_abs).neg))
    (integrable_exp_neg_abs hb)
  rw [hbridge]
  rw [show (∫ r : ℝ, (∫ x : ℝ, Real.exp (-(b * |x|)) * Real.cos (x * r))
        * (spectralTest f r).re)
      = ∫ r : ℝ, (2 * b / (b ^ 2 + r ^ 2)) * (spectralTest f r).re from
        integral_congr_ae (Eventually.of_forall fun r => by
          change (∫ x : ℝ, Real.exp (-(b * |x|)) * Real.cos (x * r))
              * (spectralTest f r).re
            = (2 * b / (b ^ 2 + r ^ 2)) * (spectralTest f r).re
          rw [integral_exp_neg_abs_mul_cos hb])]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.spectralTest_im_eq_zero
#print axioms RHLean.ExplicitFormula.integral_cos_mul_spectralTest
#print axioms RHLean.ExplicitFormula.integral_autocorr_mul_fourierKernel
#print axioms RHLean.ExplicitFormula.integrable_exp_neg_abs
#print axioms RHLean.ExplicitFormula.integral_exp_neg_abs_mul_exp
#print axioms RHLean.ExplicitFormula.integral_exp_neg_abs_mul_cos
#print axioms RHLean.ExplicitFormula.integral_spectralTest_expKernel

end

end Inline_ExplicitFormula_RH46

section Inline_ExplicitFormula_RH47





























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ComplexConjugate

namespace RHLean.ExplicitFormula



theorem digammaDensity_eq_tsum (r : ℝ) :
    digammaDensity r = -Real.eulerMascheroniConstant
      + ∑' n : ℕ, (1 / ((n : ℝ) + 1)
          - ((n : ℝ) + 1 / 4) / (((n : ℝ) + 1 / 4) ^ 2 + r ^ 2 / 4)) := by
  set z : ℂ := (1 / 4 : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hz
  have hz_ne : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    rw [hz] at hre
    simp at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsumm : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) :=
    (Complex.hasSum_digamma hz_ne).summable
  have h := Complex.digamma_eq_tsum (z := z) hz_ne
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at hre
  rw [show Complex.re (∑'
      = Complex.reCLM (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))) from rfl,
    ContinuousLinearMap.map_tsum Complex.reCLM hsumm] at hre
  rw [tsum_congr (fun n => ?_)] at hre
  · rw [hz] at hre
    simpa [digammaDensity] using hre
  · rw [show Complex.reCLM (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
        = (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)).re from rfl]
    rw [Complex.sub_re]
    congr 1
    · rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      field_simp
      ring
    · have hzexp : (n : ℂ) + z
          = (((n : ℝ) + 1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I := by
        rw [hz]
        push_cast
        ring
      rw [hzexp, show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
      ring_nf




theorem tsum_exp_neg_two_mul_add_half {x : ℝ} (hx : x ≠ 0) :
    (∑'
      = Real.exp (-(|x| / 2)) / (1 - Real.exp (-(2 * |x|))) := by
  have hu : 0 < |x| := abs_pos.mpr hx
  have hr : ‖Real.exp (-(2 * |x|))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg : HasSum (fun n : ℕ => (Real.exp (-(2 * |x|))) ^ n)
      (1 - Real.exp (-(2 * |x|)))⁻¹ :=
    hasSum_geometric_of_norm_lt_one hr
  have hrew : ∀ n : ℕ, Real.exp (-(((2 * n + 1 / 2 : ℝ)) * |x|))
      = Real.exp (-(|x| / 2)) * (Real.exp (-(2 * |x|))) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [tsum_congr hrew, tsum_mul_left, hg.tsum_eq]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.digammaDensity_eq_tsum
#print axioms RHLean.ExplicitFormula.tsum_exp_neg_two_mul_add_half

end

end Inline_ExplicitFormula_RH47

section Inline_ExplicitFormula_RH48






































noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ComplexConjugate Interval

namespace RHLean.ExplicitFormula





theorem physicalConstant_add_logPi :
    physicalConstant + Real.log Real.pi
      = -Real.log 2 - Real.eulerMascheroniConstant := by
  unfold physicalConstant
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring



theorem endpointPotential_eq (a x : ℝ) :
    endpointPotential a x = -(1 / 2) * Real.log (a ^ 2 - x ^ 2) := rfl








theorem integral_truncated_inv_sub {a x ε : ℝ} (hx : |x| < a)
    (hε : 0 < ε) :
    (∫ y in (-a)..(x - ε), (x - y)⁻¹)
      + (∫ y in (x + ε)..a, (y - x)⁻¹)
      = Real.log (a ^ 2 - x ^ 2) - 2 * Real.log ε := by
  obtain ⟨hxa, hxa'⟩ := abs_lt.mp hx
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hxpa : 0 < x + a := by linarith
  have hax : 0 < a - x := by linarith
  have h1 : (∫ y in (-a)..(x - ε), (x - y)⁻¹) = ∫ u in ε..(x + a), u⁻¹ := by
    have h := intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => u⁻¹) (d := x)
      (a := -a) (b := x - ε)
    rw [show x - (x - ε) = ε by ring, show x - -a = x + a by ring] at h
    exact h
  have h2 : (∫ y in (x + ε)..a, (y - x)⁻¹) = ∫ u in ε..(a - x), u⁻¹ := by
    have h := intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u⁻¹) (d := x)
      (a := x + ε) (b := a)
    rw [show x + ε - x = ε by ring, show a - x = a - x by ring] at h
    exact h
  have h3 : (0 : ℝ) ∉ Set.uIcc ε (x + a) := by
    rw [Set.mem_uIcc]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  have h4 : (0 : ℝ) ∉ Set.uIcc ε (a - x) := by
    rw [Set.mem_uIcc]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  have hlog : Real.log (x + a) + Real.log (a - x) = Real.log (a ^ 2 - x ^ 2) := by
    rw [← Real.log_mul (ne_of_gt hxpa) (ne_of_gt hax),
      show (x + a) * (a - x) = a ^ 2 - x ^ 2 by ring]
  rw [h1, h2, integral_inv h3, integral_inv h4,
    Real.log_div (ne_of_gt hxpa) hεne, Real.log_div (ne_of_gt hax) hεne]
  linarith [hlog]


theorem endpoint_reg_trunc {a x ε : ℝ} (hx : |x| < a) (hε : 0 < ε) :
    endpointPotential a x
      + (1 / 2) * ((∫ y in (-a)..(x - ε), (x - y)⁻¹)
          + (∫ y in (x + ε)..a, (y - x)⁻¹))
      = -Real.log ε := by
  rw [integral_truncated_inv_sub hx hε, endpointPotential_eq]
  ring








theorem fourth_normSq_sub (u v : ℂ) :
    (1 / 4) * ‖u - v‖ ^ 2
      = (1 / 4) * ‖u‖ ^ 2 + (1 / 4) * ‖v‖ ^ 2 - (1 / 2) * (u * conj v).re := by
  have h1 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * conj v).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [h1]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.physicalConstant_add_logPi
#print axioms RHLean.ExplicitFormula.integral_truncated_inv_sub
#print axioms RHLean.ExplicitFormula.endpoint_reg_trunc
#print axioms RHLean.ExplicitFormula.fourth_normSq_sub

end

end Inline_ExplicitFormula_RH48

section Inline_ExplicitFormula_RH50
















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem digamma_partialSum_eq_integral {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)))
      = ∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ (z - 1)) * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n := by
  have hrexp : ∀ n : ℕ, -1 < ((n : ℂ) + (z - 1)).re := by
    intro n
    have hre : ((n : ℂ) + (z - 1)).re = (n : ℝ) + z.re - 1 := by
      simp [Complex.add_re, Complex.sub_re, Complex.one_re]
      ring
    rw [hre]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpow : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((n : ℂ)))
      = 1 / ((n : ℂ) + 1) := by
    intro n
    have hr : -1 < ((n : ℂ)).re := by
      rw [Complex.natCast_re]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h0 : (0 : ℂ) ^ ((n : ℂ) + 1) = 0 := by
      apply zero_cpow
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.one_re] at hre
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [integral_cpow (r := (n : ℂ)) (a := 0) (b := 1) (Or.inl hr),
      Complex.ofReal_one, Complex.ofReal_zero, one_cpow, h0]
    ring
  have hcpow : ∀ n : ℕ, (∫ x in (0 : ℝ)..1, (x : ℂ) ^ ((n : ℂ) + (z - 1)))
      = 1 / ((n : ℂ) + z) := by
    intro n
    have h0 : (0 : ℂ) ^ (((n : ℂ) + (z - 1)) + 1) = 0 := by
      apply zero_cpow
      intro h
      have hre := congrArg Complex.re h
      simp [Complex.add_re, Complex.sub_re, Complex.one_re] at hre
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hden : ((n : ℂ) + (z - 1)) + 1 = (n : ℂ) + z := by ring
    rw [integral_cpow (r := (n : ℂ) + (z - 1)) (a := 0) (b := 1) (Or.inl (hrexp n)),
      Complex.ofReal_one, Complex.ofReal_zero, one_cpow, h0, hden]
    ring
  have hInt : ∀ n : ℕ, IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ ((n : ℂ)) - (x : ℂ) ^ ((n : ℂ) + (z - 1)))
      volume 0 1 :=
    fun n => (intervalIntegral.intervalIntegrable_cpow (r := (n : ℂ))
        (a := 0) (b := 1) (Or.inl (Nat.cast_nonneg n))).sub
      (intervalIntegral.intervalIntegrable_cpow' (r := (n : ℂ) + (z - 1))
        (a := 0) (b := 1) (hrexp n))
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)
      = ∫ x in (0 : ℝ)..1, ((x : ℂ) ^ ((n : ℂ)) - (x : ℂ) ^ ((n : ℂ) + (z - 1))) := by
    intro n
    rw [← hpow n, ← hcpow n]
    exact (intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_cpow (r := (n : ℂ))
        (a := 0) (b := 1) (Or.inl (Nat.cast_nonneg n)))
      (intervalIntegral.intervalIntegrable_cpow' (r := (n : ℂ) + (z - 1))
        (a := 0) (b := 1) (hrexp n))).symm
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  rw [← intervalIntegral.integral_finsetSum (fun n _ => hInt n)]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    refine (ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 0)).mpr ?_
    have hset : {a : ℝ | ¬a ≠ 0} = {0} := by
      ext a
      simp
    rw [hset]
    exact measure_singleton 0
  filter_upwards [hne] with x hxne _
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hxne
  calc ∑ n ∈ Finset.range (N + 1), ((x : ℂ) ^ ((n : ℂ)) - (x : ℂ) ^ ((n : ℂ) + (z - 1)))
      = ∑ n ∈ Finset.range (N + 1),
          ((x : ℂ) ^ ((n : ℂ)) - (x : ℂ) ^ ((n : ℂ)) * (x : ℂ) ^ (z - 1)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.cpow_add _ _ hxc]
    _ = ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ ((n : ℂ)) * (1 - (x : ℂ) ^ (z - 1)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ = (∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ ((n : ℂ))) * (1 - (x : ℂ) ^ (z - 1)) := by
        rw [← Finset.sum_mul]
    _ = (1 - (x : ℂ) ^ (z - 1)) * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ ((n : ℂ)) := by
        ring
    _ = (1 - (x : ℂ) ^ (z - 1)) * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n := by
        congr 1
        exact Finset.sum_congr rfl fun n _ => Complex.cpow_natCast x n

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.digamma_partialSum_eq_integral

end

end Inline_ExplicitFormula_RH50

section Inline_ExplicitFormula_RH51




















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


noncomputable def digammaZ (r : ℝ) : ℂ :=
  (1 / 4 : ℂ) + ((r / 2 : ℝ) : ℂ) * I

theorem digammaZ_re (r : ℝ) : (digammaZ r).re = 1 / 4 := by
  unfold digammaZ
  simp

theorem digammaZ_sub_one_re (r : ℝ) : (digammaZ r - 1).re = -(3 / 4) := by
  unfold digammaZ
  simp
  ring

theorem digammaZ_ne_one (r : ℝ) : digammaZ r ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [digammaZ_re] at hre
  norm_num at hre


theorem norm_one_sub_digammaZ_le_of_pos {r : ℝ} {x : ℝ} (hx : 0 < x) :
    ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖ ≤ 1 + x ^ (-(3 / 4 : ℝ)) := by
  have hnorm : ‖(x : ℂ) ^ ((digammaZ r) - 1)‖ = x ^ (-(3 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, digammaZ_sub_one_re]
  calc ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖
      ≤ ‖(1 : ℂ)‖ + ‖(x : ℂ) ^ ((digammaZ r) - 1)‖ := norm_sub_le _ _
    _ = 1 + x ^ (-(3 / 4 : ℝ)) := by rw [norm_one, hnorm]



theorem norm_one_sub_digammaZ_le_of_half_le {r : ℝ} {x : ℝ}
    (hx : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖
      ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hz2 : digammaZ r - 2 ≠ -1 := by
    intro h
    apply digammaZ_ne_one r
    linear_combination h
  have hnotmem : (0 : ℝ) ∉ Set.uIcc x 1 := by
    rw [Set.mem_uIcc]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · linarith
    · linarith
  have hid : (1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)
      = ((digammaZ r) - 1) * ∫ s in x..1, (s : ℂ) ^ ((digammaZ r) - 2) := by
    have h : (∫ s in x..1, (s : ℂ) ^ ((digammaZ r) - 2))
        = (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / ((digammaZ r) - 1) := by
      rw [integral_cpow (r := (digammaZ r) - 2) (a := x) (b := 1)
        (Or.inr ⟨hz2, hnotmem⟩),
        show (digammaZ r - 2) + 1 = digammaZ r - 1 by ring,
        Complex.ofReal_one, one_cpow]
    rw [h]
    field_simp [sub_ne_zero.mpr (digammaZ_ne_one r)]
  rw [hid, norm_mul]
  have hInt : ‖∫ s in x..1, (s : ℂ) ^ ((digammaZ r) - 2)‖
      ≤ (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x) := by
    have hbound : ∀ s ∈ Set.uIoc x 1,
        ‖(s : ℂ) ^ ((digammaZ r) - 2)‖ ≤ (2 : ℝ) ^ (7 / 4 : ℝ) := by
      intro s hs
      rw [Set.uIoc_of_le hx1] at hs
      have hs1 : 1 / 2 ≤ s := by linarith [hs.1]
      have hspos : (0 : ℝ) < s := by linarith
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hspos]
      have hre : ((digammaZ r) - 2).re = -(7 / 4 : ℝ) := by
        unfold digammaZ
        simp
        ring
      rw [hre]
      calc s ^ (-(7 / 4 : ℝ)) = (s ^ (7 / 4 : ℝ))⁻¹ :=
            Real.rpow_neg (le_of_lt hspos) _
        _ ≤ (((1 / 2 : ℝ) ^ (7 / 4 : ℝ)))⁻¹ := by
            rw [inv_le_inv₀ (Real.rpow_pos_of_pos hspos _)
              (Real.rpow_pos_of_pos (by norm_num) _)]
            exact Real.rpow_le_rpow (by norm_num) hs1 (by norm_num)
        _ = (2 : ℝ) ^ (7 / 4 : ℝ) := by
            rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := 1)
      (C := (2 : ℝ) ^ (7 / 4 : ℝ)) hbound
    simpa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - x)] using h1
  calc ‖(digammaZ r) - 1‖ * ‖∫ s in x..1, (s : ℂ) ^ ((digammaZ r) - 2)‖
      ≤ ‖(digammaZ r) - 1‖ * ((2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x)) :=
        mul_le_mul_of_nonneg_left hInt (norm_nonneg _)
    _ = ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x) := by ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.digammaZ_re
#print axioms RHLean.ExplicitFormula.norm_one_sub_digammaZ_le_of_pos
#print axioms RHLean.ExplicitFormula.norm_one_sub_digammaZ_le_of_half_le

end

end Inline_ExplicitFormula_RH51

section Inline_ExplicitFormula_RH52






















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


noncomputable def digammaMajorant (r : ℝ) (x : ℝ) : ℝ :=
  max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)) * (1 + x ^ (-(3 / 4 : ℝ)))

theorem integrable_digammaMajorant (r : ℝ) :
    Integrable (digammaMajorant r) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Set.Ioc (0 : ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
  have htarget : IntegrableOn (fun x : ℝ =>
      max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)) * (1 + x ^ (-(3 / 4 : ℝ))))
      (Set.Ioc (0 : ℝ) 1) volume :=
    ((integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (C := (1 : ℝ))
      (hs := by rw [Real.volume_Ioc]; norm_num)).add hbase).const_mul _
  exact htarget.congr_fun (fun x _ => rfl) measurableSet_Ioc


theorem norm_digamma_integrand_le_majorant (r : ℝ) (N : ℕ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖(1 - (x : ℂ) ^ ((digammaZ r) - 1))
          * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n‖
        ≤ digammaMajorant r x := by
  have hae1 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ≠ 1 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
      ext a
      simp
    filter_upwards [(ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 1)).mpr
      (by rw [hset]; exact measure_singleton 1)] with x hx _
    exact hx
  have hae2 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ∈ Set.Ioc (0 : ℝ) 1 :=
    self_mem_ae_restrict measurableSet_Ioc
  filter_upwards [hae1, hae2] with x hxne hxmem
  have hx0 : 0 < x := hxmem.1
  have hxle : x ≤ 1 := hxmem.2
  have hxlt : x < 1 := lt_of_le_of_ne hxle hxne

  have hxnormR : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0.le]
    exact hxlt
  have hgs : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hxnormR
  have hgeom : ∑ n ∈ Finset.range (N + 1), x ^ n ≤ (1 - x)⁻¹ := by
    have h := hgs.summable.sum_le_tsum (Finset.range (N + 1))
      (fun i _ => pow_nonneg hx0.le i)
    rwa [hgs.tsum_eq] at h
  have hnormsum : ‖∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n‖ ≤ (1 - x)⁻¹ := by
    calc ‖∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n‖
        ≤ ∑ n ∈ Finset.range (N + 1), ‖(x : ℂ) ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range (N + 1), x ^ n := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_pow, norm_ofReal_complex, abs_of_nonneg hx0.le]
      _ ≤ (1 - x)⁻¹ := hgeom
  have hne1 : (1 : ℝ) - x ≠ 0 := by linarith
  have hK2 : (2 : ℝ) ≤ max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)) :=
    le_max_left _ _
  have hKz : ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)
      ≤ max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)) := le_max_right _ _
  have hone_le : (1 : ℝ) ≤ 1 + x ^ (-(3 / 4 : ℝ)) := by
    have := Real.rpow_nonneg hx0.le (-(3 / 4 : ℝ))
    linarith
  rw [norm_mul, digammaMajorant]
  by_cases hxhalf : x ≤ 1 / 2
  · have h1 : ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖ ≤ 1 + x ^ (-(3 / 4 : ℝ)) :=
      norm_one_sub_digammaZ_le_of_pos hx0
    have h2 : (1 - x)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < 1 - x)]
      linarith
    calc ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖
          * ‖∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n‖
        ≤ (1 + x ^ (-(3 / 4 : ℝ))) * (1 - x)⁻¹ :=
          mul_le_mul h1 hnormsum (norm_nonneg _) (by positivity)
      _ ≤ (1 + x ^ (-(3 / 4 : ℝ))) * 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ))
            * (1 + x ^ (-(3 / 4 : ℝ))) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hK2 (by positivity)
  · have hxhalf' : 1 / 2 ≤ x := le_of_lt (lt_of_not_ge hxhalf)
    have h1 : ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖
        ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x) :=
      norm_one_sub_digammaZ_le_of_half_le hxhalf' hxle
    calc ‖(1 : ℂ) - (x : ℂ) ^ ((digammaZ r) - 1)‖
          * ‖∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n‖
        ≤ (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - x)) * (1 - x)⁻¹ :=
          mul_le_mul h1 hnormsum (norm_nonneg _) (by positivity)
      _ = ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) := by
          rw [mul_assoc, mul_inv_cancel₀ hne1, mul_one]
      _ ≤ max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ)) := hKz
      _ ≤ max 2 (‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ))
            * (1 + x ^ (-(3 / 4 : ℝ))) :=
          le_mul_of_one_le_right (le_trans (by norm_num) hK2) hone_le

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrable_digammaMajorant
#print axioms RHLean.ExplicitFormula.norm_digamma_integrand_le_majorant

end

end Inline_ExplicitFormula_RH52

section Inline_ExplicitFormula_RH53






















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem tendsto_partialSum_mul (r : ℝ) :
    ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Tendsto (fun N : ℕ =>
          (1 - (x : ℂ) ^ ((digammaZ r) - 1))
            * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
        atTop (𝓝 ((1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ)))) := by
  have hae1 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ≠ 1 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
      ext a
      simp
    filter_upwards [(ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 1)).mpr
      (by rw [hset]; exact measure_singleton 1)] with x hx _
    exact hx
  have hae2 : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), x ∈ Set.Ioc (0 : ℝ) 1 :=
    self_mem_ae_restrict measurableSet_Ioc
  filter_upwards [hae1, hae2] with x hxne hxmem
  have hx0 : 0 < x := hxmem.1
  have hxlt : x < 1 := lt_of_le_of_ne hxmem.2 hxne
  have hxc1 : (x : ℂ) ≠ 1 := by exact_mod_cast hxne
  have hnorm : ‖(x : ℂ)‖ < 1 := by
    rw [norm_ofReal_complex, abs_of_nonneg hx0.le]
    exact hxlt
  have hpow : Tendsto (fun N : ℕ => (x : ℂ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).comp (tendsto_add_atTop_nat 1)
  have hgeomtend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
      atTop (𝓝 (1 / (1 - (x : ℂ)))) := by
    have h : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n
        = ((x : ℂ) ^ (N + 1) - 1) / ((x : ℂ) - 1) :=
      fun N => geom_sum_eq hxc1 (N + 1)
    rw [show (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
        = fun N : ℕ => ((x : ℂ) ^ (N + 1) - 1) / ((x : ℂ) - 1) from funext h]
    have hsub : Tendsto (fun N : ℕ => (x : ℂ) ^ (N + 1) - 1) atTop (𝓝 ((0 : ℂ) - 1)) :=
      hpow.sub (tendsto_const_nhds (x := (1 : ℂ)))
    have htend := hsub.div_const ((x : ℂ) - 1)
    have hx1 : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hxc1
    have h1x : 1 - (x : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hxc1)
    have htarget : (0 - 1) / ((x : ℂ) - 1) = 1 / (1 - (x : ℂ)) := by
      field_simp [hx1, h1x]
      ring
    rwa [htarget] at htend
  have hmul := (tendsto_const_nhds (x := (1 - (x : ℂ) ^ ((digammaZ r) - 1)))).mul hgeomtend
  convert hmul using 1
  ring


theorem tendsto_integral_partialSum (r : ℝ) :
    Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1))
          * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ)))) := by
  have hcont : ∀ N : ℕ, ContinuousOn (fun x : ℝ =>
      (1 - (x : ℂ) ^ ((digammaZ r) - 1))
        * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n) (Set.Ioc (0 : ℝ) 1) := by
    intro N
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.sub continuousOn_const ?_
      refine continuousOn_of_forall_continuousAt fun x hx =>
        Complex.continuousAt_ofReal_cpow_const x ((digammaZ r) - 1)
          (Or.inr (ne_of_gt hx.1))
    · have hp : Continuous (fun x : ℝ =>
          ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n) := by
        fun_prop
      exact hp.continuousOn
  have hconv : Tendsto (fun N : ℕ => ∫ x in Set.Ioc (0 : ℝ) 1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1))
          * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
      atTop (𝓝 (∫ x in Set.Ioc (0 : ℝ) 1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ)))) :=
    tendsto_integral_of_dominated_convergence (digammaMajorant r)
      (fun N => (hcont N).aestronglyMeasurable measurableSet_Ioc)
      (integrable_digammaMajorant r)
      (fun N => norm_digamma_integrand_le_majorant r N)
      (tendsto_partialSum_mul r)
  simpa only [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hconv



theorem digamma_digammaZ_eq_integral (r : ℝ) :
    Complex.digamma (digammaZ r) + (Real.eulerMascheroniConstant : ℂ)
      = ∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ)) := by
  have hzr : 0 < (digammaZ r).re := by
    rw [digammaZ_re]
    norm_num
  have hz_ne : ∀ n : ℕ, digammaZ r ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    rw [digammaZ_re] at hre
    simp at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsum : HasSum (fun n : ℕ =>
      1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + digammaZ r))
      (Complex.digamma (digammaZ r) + (Real.eulerMascheroniConstant : ℂ)) :=
    Complex.hasSum_digamma hz_ne
  have hlim_sum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + digammaZ r))) atTop
      (𝓝 (Complex.digamma (digammaZ r) + (Real.eulerMascheroniConstant : ℂ))) :=
    hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim_int := tendsto_integral_partialSum r
  have hEq : (fun N : ℕ => ∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1))
          * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n)
      = fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
          (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + digammaZ r)) :=
    funext fun N => (digamma_partialSum_eq_integral hzr N).symm
  rw [hEq] at hlim_int
  exact (tendsto_nhds_unique hlim_int hlim_sum).symm


theorem digammaDensity_eq_integral (r : ℝ) :
    digammaDensity r = -Real.eulerMascheroniConstant
      + (∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re := by
  have h := congrArg Complex.re (digamma_digammaZ_eq_integral r)
  rw [Complex.add_re, Complex.ofReal_re] at h
  have hd : (Complex.digamma (digammaZ r)).re = digammaDensity r := rfl
  rw [hd] at h
  linarith

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.tendsto_partialSum_mul
#print axioms RHLean.ExplicitFormula.tendsto_integral_partialSum
#print axioms RHLean.ExplicitFormula.digamma_digammaZ_eq_integral
#print axioms RHLean.ExplicitFormula.digammaDensity_eq_integral

end

end Inline_ExplicitFormula_RH53

section Inline_ExplicitFormula_RH54




















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula

theorem norm_digammaZ_sub_one_le (r : ℝ) : ‖(digammaZ r) - 1‖ ≤ 1 + |r| := by
  have h : (digammaZ r) - 1
      = (((-(3 / 4) : ℝ)) : ℂ) + (((r / 2 : ℝ)) : ℂ) * I := by
    unfold digammaZ
    push_cast
    ring
  rw [h]
  calc ‖((( -(3 / 4) : ℝ)) : ℂ) + (((r / 2 : ℝ)) : ℂ) * I‖
      ≤ ‖((( -(3 / 4) : ℝ)) : ℂ)‖ + ‖(((r / 2 : ℝ)) : ℂ) * I‖ := norm_add_le _ _
    _ = 3 / 4 + |r| / 2 := by
        rw [norm_ofReal_complex, norm_mul, Complex.norm_I, mul_one, norm_ofReal_complex,
          abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4),
          abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 1 + |r| := by
        have := abs_nonneg r
        linarith

theorem two_rpow_seven_fourths_le_four : (2 : ℝ) ^ (7 / 4 : ℝ) ≤ 4 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)


theorem norm_digammaRatio_le {r : ℝ} {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ‖(1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))‖
      ≤ 4 * (1 + |r|) * (1 + t ^ (-(3 / 4 : ℝ))) := by
  have htne : (1 : ℝ) - t ≠ 0 := by linarith
  have hratio : ‖(1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))‖
      = ‖(1 - (t : ℂ) ^ ((digammaZ r) - 1))‖ / (1 - t) := by
    rw [norm_div, show (1 : ℂ) - (t : ℂ) = (((1 - t : ℝ)) : ℂ) by push_cast; ring,
      norm_ofReal_complex, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
  rw [hratio]
  have hnum : ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ ≤ 1 + t ^ (-(3 / 4 : ℝ)) :=
    norm_one_sub_digammaZ_le_of_pos ht
  have hone : (1 : ℝ) ≤ 1 + t ^ (-(3 / 4 : ℝ)) := by
    have := Real.rpow_nonneg ht.le (-(3 / 4 : ℝ))
    linarith
  have hK : (0 : ℝ) ≤ 1 + |r| := by positivity
  by_cases hthalf : t ≤ 1 / 2
  · have hden : (1 - t)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < 1 - t)]
      linarith
    have h2 : ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ / (1 - t)
        ≤ 2 * (1 + t ^ (-(3 / 4 : ℝ))) := by
      rw [div_eq_mul_inv]
      calc ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ * (1 - t)⁻¹
          ≤ (1 + t ^ (-(3 / 4 : ℝ))) * 2 :=
            mul_le_mul hnum hden (by positivity) (by positivity)
        _ = 2 * (1 + t ^ (-(3 / 4 : ℝ))) := by ring
    calc ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ / (1 - t)
        ≤ 2 * (1 + t ^ (-(3 / 4 : ℝ))) := h2
      _ ≤ 4 * (1 + |r|) * (1 + t ^ (-(3 / 4 : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [abs_nonneg r]
  · have hthalf' : 1 / 2 ≤ t := le_of_lt (lt_of_not_ge hthalf)
    have hnum' : ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖
        ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - t) :=
      norm_one_sub_digammaZ_le_of_half_le hthalf' ht1.le
    have hcancel : ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ / (1 - t)
        ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - t)]
      calc ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖
          ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - t) := hnum'
        _ = ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) * (1 - t) := rfl
    calc ‖(1 : ℂ) - (t : ℂ) ^ ((digammaZ r) - 1)‖ / (1 - t)
        ≤ ‖(digammaZ r) - 1‖ * (2 : ℝ) ^ (7 / 4 : ℝ) := hcancel
      _ ≤ (1 + |r|) * (2 : ℝ) ^ (7 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (norm_digammaZ_sub_one_le r) (by positivity)
      _ ≤ (1 + |r|) * 4 :=
          mul_le_mul_of_nonneg_left two_rpow_seven_fourths_le_four hK
      _ ≤ 4 * (1 + |r|) * (1 + t ^ (-(3 / 4 : ℝ))) := by
          have := mul_le_mul_of_nonneg_left hone (by positivity : (0 : ℝ) ≤ 4 * (1 + |r|))
          nlinarith

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.norm_digammaZ_sub_one_le
#print axioms RHLean.ExplicitFormula.norm_digammaRatio_le

end

end Inline_ExplicitFormula_RH54

section Inline_ExplicitFormula_RH55


















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem digammaZ_cpow_re {r t : ℝ} (ht : 0 < t) :
    ((t : ℂ) ^ ((digammaZ r) - 1)).re
      = t ^ (-(3 / 4 : ℝ)) * Real.cos ((r / 2) * Real.log t) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hlog : Complex.log (t : ℂ) = ((Real.log t : ℝ) : ℂ) := by
    rw [show (t : ℂ) = ((t : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (le_of_lt ht)).symm
  rw [Complex.cpow_def_of_ne_zero htC, hlog]
  rw [show ((Real.log t : ℝ) : ℂ) * ((digammaZ r) - 1)
      = ((-(3 / 4) * Real.log t : ℝ) : ℂ) + (((r / 2) * Real.log t : ℝ) : ℂ) * I by
        unfold digammaZ
        push_cast
        ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.rpow_def_of_pos ht]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
  congr 1
  congr 1
  ring


theorem re_digammaRatio {r t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re
      = (1 - t ^ (-(3 / 4 : ℝ)) * Real.cos ((r / 2) * Real.log t)) / (1 - t) := by
  have htne : (1 : ℝ) - t ≠ 0 := by linarith
  have hden : ((1 : ℂ) - (t : ℂ)).re = 1 - t := by
    simp
  have him : ((1 : ℂ) - (t : ℂ)).im = 0 := by
    simp
  have hnorm : Complex.normSq ((1 : ℂ) - (t : ℂ)) = (1 - t) ^ 2 := by
    rw [Complex.normSq_apply, hden, him]
    ring
  rw [Complex.div_re]
  rw [hden, him, hnorm, Complex.sub_re, Complex.one_re]
  rw [digammaZ_cpow_re ht]
  field_simp [htne]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.digammaZ_cpow_re
#print axioms RHLean.ExplicitFormula.re_digammaRatio

end

end Inline_ExplicitFormula_RH55

section Inline_ExplicitFormula_RH56



















set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrable_cos_mul_spectralTest {f : ℝ → ℂ} (hf : f ∈ oddCore) (a : ℝ) :
    Integrable (fun r : ℝ => Real.cos (a * r) * (spectralTest f r).re) volume := by
  have hcont : Continuous (fun r : ℝ => Real.cos (a * r)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have h := ((integrable_spectralTest hf).re).mul_bdd hcont.aestronglyMeasurable
    (by
      filter_upwards with r
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _)
  exact h.congr (Eventually.of_forall fun r => by
    change (spectralTest f r).re * Real.cos (a * r)
      = Real.cos (a * r) * (spectralTest f r).re
    ring)


theorem integral_one_sub_cos_mul_spectralTest {f : ℝ → ℂ} (hf : f ∈ oddCore) (t : ℝ) :
    (∫ r : ℝ, (1 - t ^ (-(3 / 4 : ℝ)) * Real.cos ((r / 2) * Real.log t))
        * (spectralTest f r).re)
      = 2 * Real.pi * (autocorr f 0).re
        - t ^ (-(3 / 4 : ℝ)) * (2 * Real.pi * (autocorr f (Real.log t / 2)).re) := by
  have hspec : Integrable (fun r : ℝ => (spectralTest f r).re) volume :=
    (integrable_spectralTest hf).re
  have hcos : Integrable (fun r : ℝ =>
      (spectralTest f r).re * Real.cos ((r / 2) * Real.log t)) volume := by
    have hcont : Continuous (fun r : ℝ => Real.cos ((r / 2) * Real.log t)) :=
      Real.continuous_cos.comp ((continuous_id.div_const 2).mul continuous_const)
    refine hspec.mul_bdd (c := 1) hcont.aestronglyMeasurable ?_
    filter_upwards with r
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hpt : (fun r : ℝ => (1 - t ^ (-(3 / 4 : ℝ)) * Real.cos ((r / 2) * Real.log t))
        * (spectralTest f r).re)
      = fun r : ℝ => (spectralTest f r).re
          - t ^ (-(3 / 4 : ℝ))
            * ((spectralTest f r).re * Real.cos ((r / 2) * Real.log t)) := by
    funext r
    ring
  rw [hpt, integral_sub hspec (hcos.const_mul _), integral_const_mul,
    integral_spectralTest_re_eq hf]
  have hg0 : (autocorr f 0).re = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [autocorr_zero hf]
    rw [show (∫ x : ℝ, ((‖f x‖ ^ 2 : ℝ) : ℂ))
        = (((∫ x : ℝ, ‖f x‖ ^ 2 : ℝ)) : ℂ) from _root_.integral_ofReal]
    rw [Complex.ofReal_re]
  have harg : (∫ r : ℝ, (spectralTest f r).re * Real.cos ((r / 2) * Real.log t))
      = 2 * Real.pi * (autocorr f (Real.log t / 2)).re := by
    have hcongr : (fun r : ℝ => (spectralTest f r).re * Real.cos ((r / 2) * Real.log t))
        = fun r : ℝ => Real.cos ((Real.log t / 2) * r) * (spectralTest f r).re := by
      funext r
      rw [show (r / 2) * Real.log t = (Real.log t / 2) * r by ring]
      ring
    rw [hcongr]
    exact integral_cos_mul_spectralTest hf (Real.log t / 2)
  rw [harg]
  rw [hg0]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrable_cos_mul_spectralTest
#print axioms RHLean.ExplicitFormula.integral_one_sub_cos_mul_spectralTest

end

end Inline_ExplicitFormula_RH56

section Inline_ExplicitFormula_RH57



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrable_spectralTest_weighted {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Integrable (fun r : ℝ => (1 + |r|) * ‖spectralTest f r‖) volume := by
  obtain ⟨C, hC0, hC⟩ := exists_spectralTest_norm_pow_mul_le hf 3
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C)
    (((continuous_const.add continuous_abs).mul (continuous_spectralTest hf).norm).aestronglyMeasurable) ?_
  filter_upwards with r
  have h1 : (1 + |r|) ^ 3 * ‖spectralTest f r‖ ≤ C := hC r
  have h2 : (0 : ℝ) < 1 + |r| := by positivity
  have hsq : (1 + r ^ 2) ≤ (1 + |r|) ^ 2 := by
    nlinarith [sq_abs r, abs_nonneg r]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |r|),
    abs_of_nonneg (norm_nonneg _)]
  calc (1 + |r|) * ‖spectralTest f r‖
      = (1 + |r|) ^ 3 * ‖spectralTest f r‖ / (1 + |r|) ^ 2 := by
        field_simp
    _ ≤ C / (1 + |r|) ^ 2 := by
        exact div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ C * (1 + r ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ hC0
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact hsq


theorem integrable_digammaMajorantT :
    Integrable (fun t : ℝ => 1 + t ^ (-(3 / 4 : ℝ))) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 / 4 : ℝ))) (Set.Ioc (0 : ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
  exact (integrableOn_const (s := Set.Ioc (0 : ℝ) 1) (C := (1 : ℝ))
    (hs := by rw [Real.volume_Ioc]; norm_num)).add hbase

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrable_spectralTest_weighted
#print axioms RHLean.ExplicitFormula.integrable_digammaMajorantT

end

end Inline_ExplicitFormula_RH57

section Inline_ExplicitFormula_RH58

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrable_fubiniMajorant {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Integrable (fun p : ℝ × ℝ =>
        ((1 + |p.1|) * ‖spectralTest f p.1‖) * (1 + p.2 ^ (-(3 / 4 : ℝ))))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
  (integrable_spectralTest_weighted hf).mul_prod integrable_digammaMajorantT

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrable_fubiniMajorant

end

end Inline_ExplicitFormula_RH58

section Inline_ExplicitFormula_RH59




















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula

theorem norm_digammaDoubleIntegrand_le {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {r t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ‖(((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re
        * (spectralTest f r).re)‖
      ≤ 4 * ((1 + |r|) * ‖spectralTest f r‖) * (1 + t ^ (-(3 / 4 : ℝ))) := by
  have hA : |(((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)|
      ≤ ‖(1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))‖ :=
    Complex.abs_re_le_norm _
  have hB : |(spectralTest f r).re| ≤ ‖spectralTest f r‖ := Complex.abs_re_le_norm _
  have hratio := norm_digammaRatio_le (r := r) ht ht1
  rw [Real.norm_eq_abs, abs_mul]
  calc |(((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)|
        * |(spectralTest f r).re|
      ≤ ‖(1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))‖
          * ‖spectralTest f r‖ :=
        mul_le_mul hA hB (abs_nonneg _) (norm_nonneg _)
    _ ≤ (4 * (1 + |r|) * (1 + t ^ (-(3 / 4 : ℝ)))) * ‖spectralTest f r‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ = 4 * ((1 + |r|) * ‖spectralTest f r‖) * (1 + t ^ (-(3 / 4 : ℝ))) := by ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.norm_digammaDoubleIntegrand_le

end

end Inline_ExplicitFormula_RH59

section Inline_ExplicitFormula_RH60














noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula

theorem continuous_digammaZ : Continuous digammaZ := by
  unfold digammaZ
  fun_prop

theorem continuousOn_digammaDoubleIntegrand {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (((1 - (p.2 : ℂ) ^ ((digammaZ p.1) - 1)) / (1 - (p.2 : ℂ))).re)
          * (spectralTest f p.1).re)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) := by
  refine continuousOn_of_forall_continuousAt fun p hp => ?_
  have hcpow : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ) ^ ((digammaZ q.1) - 1)) p := by
    refine ContinuousAt.cpow ?_ ?_ ?_
    · exact (Complex.continuous_ofReal.comp continuous_snd).continuousAt
    · exact ((continuous_digammaZ.comp continuous_fst).sub continuous_const).continuousAt
    · rw [Complex.mem_slitPlane_iff]
      left
      simpa using hp.2.1
  have hnum : ContinuousAt (fun q : ℝ × ℝ => 1 - (q.2 : ℂ) ^ ((digammaZ q.1) - 1)) p :=
    continuousAt_const.sub hcpow
  have hden : ContinuousAt (fun q : ℝ × ℝ => (1 : ℂ) - (q.2 : ℂ)) p :=
    continuousAt_const.sub (Complex.continuous_ofReal.comp continuous_snd).continuousAt
  have hdenne : (1 : ℂ) - (p.2 : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (Ne.symm (ne_of_lt hp.2.2))
  have hdiv : ContinuousAt (fun q : ℝ × ℝ =>
      (1 - (q.2 : ℂ) ^ ((digammaZ q.1) - 1)) / (1 - (q.2 : ℂ))) p :=
    hnum.div hden hdenne
  have hre : ContinuousAt (fun q : ℝ × ℝ =>
      ((1 - (q.2 : ℂ) ^ ((digammaZ q.1) - 1)) / (1 - (q.2 : ℂ))).re) p :=
    Complex.continuous_re.continuousAt.comp hdiv
  have hspec : ContinuousAt (fun q : ℝ × ℝ => (spectralTest f q.1).re) p :=
    (Complex.continuous_re.comp ((continuous_spectralTest hf).comp continuous_fst)).continuousAt
  exact hre.mul hspec

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.continuous_digammaZ
#print axioms RHLean.ExplicitFormula.continuousOn_digammaDoubleIntegrand

end

end Inline_ExplicitFormula_RH60

section Inline_ExplicitFormula_RH61



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem ae_mem_univ_prod_Ioo :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))),
      p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) 1 := by
  have hcompl : (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
    have hscompl : ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) 1)ᶜ
        = (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) 1)ᶜ := by
      rw [Set.compl_prod_eq_union, Set.compl_univ, Set.empty_prod, Set.empty_union]
    rw [hscompl, Measure.prod_prod]
    have hν : (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1)ᶜ = 0 := by
      rw [Measure.restrict_apply (t := (Set.Ioo (0 : ℝ) 1)ᶜ) measurableSet_Ioo.compl]
      have hset : (Set.Ioo (0 : ℝ) 1)ᶜ ∩ Set.Ioc (0 : ℝ) 1 = {1} := by
        ext x
        constructor
        · rintro ⟨hx1, hx2⟩
          rw [Set.mem_compl_iff, Set.mem_Ioo] at hx1
          rw [Set.mem_Ioc] at hx2
          rw [Set.mem_singleton_iff]
          by_contra hne
          exact hx1 ⟨hx2.1, lt_of_le_of_ne hx2.2 hne⟩
        · rintro rfl
          simp
      rw [hset, measure_singleton]
    rw [hν, mul_zero]
  exact mem_ae_iff.mpr hcompl



theorem aestronglyMeasurable_digammaDoubleIntegrand {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (((1 - (p.2 : ℂ) ^ ((digammaZ p.1) - 1)) / (1 - (p.2 : ℂ))).re)
          * (spectralTest f p.1).re)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  let s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) 1
  let Φ : ℝ × ℝ → ℝ := fun p =>
    (((1 - (p.2 : ℂ) ^ ((digammaZ p.1) - 1)) / (1 - (p.2 : ℂ))).re)
      * (spectralTest f p.1).re
  have hs : MeasurableSet s := MeasurableSet.univ.prod measurableSet_Ioo
  have hcont : ContinuousOn Φ s := by
    change ContinuousOn (fun p : ℝ × ℝ =>
        (((1 - (p.2 : ℂ) ^ ((digammaZ p.1) - 1)) / (1 - (p.2 : ℂ))).re)
          * (spectralTest f p.1).re) (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
    exact continuousOn_digammaDoubleIntegrand hf
  have h1 : AEStronglyMeasurable Φ
      ((volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).restrict s) :=
    hcont.aestronglyMeasurable hs
  have hind : AEStronglyMeasurable (s.indicator Φ)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    (aestronglyMeasurable_indicator_iff hs).mpr h1
  have hae : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))), p ∈ s :=
    ae_mem_univ_prod_Ioo
  have heq : s.indicator Φ =ᵐ[volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))] Φ := by
    filter_upwards [hae] with p hp
    rw [Set.indicator_of_mem hp]
  exact hind.congr heq


theorem integrable_digammaRatio (r : ℝ) :
    Integrable (fun t : ℝ => (1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hmaj : Integrable (fun t : ℝ => 4 * (1 + |r|) * (1 + t ^ (-(3 / 4 : ℝ))))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    integrable_digammaMajorantT.const_mul (4 * (1 + |r|))
  refine Integrable.mono' hmaj ?_ ?_
  · have hcont : ∀ N : ℕ, ContinuousOn (fun x : ℝ =>
        (1 - (x : ℂ) ^ ((digammaZ r) - 1))
          * ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n) (Set.Ioc (0 : ℝ) 1) := by
      intro N
      refine ContinuousOn.mul ?_ ?_
      · refine ContinuousOn.sub continuousOn_const ?_
        refine continuousOn_of_forall_continuousAt fun x hx =>
          Complex.continuousAt_ofReal_cpow_const x ((digammaZ r) - 1)
            (Or.inr (ne_of_gt hx.1))
      · have hp : Continuous (fun x : ℝ =>
            ∑ n ∈ Finset.range (N + 1), (x : ℂ) ^ n) := by
          fun_prop
        exact hp.continuousOn
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (hcont N).aestronglyMeasurable measurableSet_Ioc)
      (tendsto_partialSum_mul r)
  · have hae1 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ≠ 1 := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
        ext a
        simp
      filter_upwards [(ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 1)).mpr
        (by rw [hset]; exact measure_singleton 1)] with x hx _
      exact hx
    have hae2 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        t ∈ Set.Ioc (0 : ℝ) 1 := self_mem_ae_restrict measurableSet_Ioc
    filter_upwards [hae1, hae2] with t htne htmem
    have ht : 0 < t := htmem.1
    have ht1 : t < 1 := lt_of_le_of_ne htmem.2 htne
    exact norm_digammaRatio_le ht ht1



theorem integrable_digammaDoubleIntegrand {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Integrable (fun p : ℝ × ℝ =>
        (((1 - (p.2 : ℂ) ^ ((digammaZ p.1) - 1)) / (1 - (p.2 : ℂ))).re)
          * (spectralTest f p.1).re)
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      ((1 + |p.1|) * ‖spectralTest f p.1‖) * (1 + p.2 ^ (-(3 / 4 : ℝ))))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    integrable_fubiniMajorant hf
  have hmaj4 : Integrable (fun p : ℝ × ℝ =>
      4 * (((1 + |p.1|) * ‖spectralTest f p.1‖) * (1 + p.2 ^ (-(3 / 4 : ℝ)))))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    hmaj.const_mul 4
  refine Integrable.mono' hmaj4 (aestronglyMeasurable_digammaDoubleIntegrand hf) ?_
  filter_upwards [ae_mem_univ_prod_Ioo] with p hp
  simpa only [mul_assoc] using norm_digammaDoubleIntegrand_le hf hp.2.1 hp.2.2

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.ae_mem_univ_prod_Ioo
#print axioms RHLean.ExplicitFormula.aestronglyMeasurable_digammaDoubleIntegrand
#print axioms RHLean.ExplicitFormula.integrable_digammaRatio
#print axioms RHLean.ExplicitFormula.integrable_digammaDoubleIntegrand

end

end Inline_ExplicitFormula_RH61

section Inline_ExplicitFormula_RH62

























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem autocorr_zero_re {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    (autocorr f 0).re = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  rw [autocorr_zero hf]
  rw [show (∫ x : ℝ, ((‖f x‖ ^ 2 : ℝ) : ℂ))
      = (((∫ x : ℝ, ‖f x‖ ^ 2 : ℝ)) : ℂ) from _root_.integral_ofReal]
  rw [Complex.ofReal_re]


theorem re_integral_digammaRatio (r : ℝ) :
    (∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re
      = ∫ x in (0 : ℝ)..1,
          ((1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact (integral_re (integrable_digammaRatio r)).symm


theorem integral_digammaRatio_re_mul_spectralTest {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    (∫ r : ℝ, ((∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
        * (spectralTest f r).re)
      = ∫ t : ℝ, (∫ r : ℝ,
          (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
            * (spectralTest f r).re)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [← integral_integral_swap (integrable_digammaDoubleIntegrand hf)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  dsimp only
  rw [integral_mul_const]
  congr 1
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact re_integral_digammaRatio r



theorem integral_digammaDoubleIntegrand_inner {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (∫ r : ℝ,
        (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
          * (spectralTest f r).re)
      = (2 * Real.pi * (autocorr f 0).re
          - t ^ (-(3 / 4 : ℝ)) * (2 * Real.pi * (autocorr f (Real.log t / 2)).re))
          / (1 - t) := by
  have hpt : (fun r : ℝ =>
        (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
          * (spectralTest f r).re)
      = fun r : ℝ =>
          ((1 - t ^ (-(3 / 4 : ℝ)) * Real.cos ((r / 2) * Real.log t))
            * (spectralTest f r).re) / (1 - t) := by
    funext r
    rw [re_digammaRatio ht ht1, div_mul_eq_mul_div]
  rw [hpt, integral_div, integral_one_sub_cos_mul_spectralTest hf t]


theorem digammaSpectralBlock_eq_positionSpace {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    digammaSpectralBlock f
      = -Real.eulerMascheroniConstant * (autocorr f 0).re
        + ∫ t in (0 : ℝ)..1,
            ((autocorr f 0).re
              - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t) := by
  have hdensity : ∀ r : ℝ, digammaDensity r
      = -Real.eulerMascheroniConstant
        + (∫ x in (0 : ℝ)..1,
            (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re :=
    digammaDensity_eq_integral
  have hIntGamma : Integrable (fun r : ℝ =>
      (-Real.eulerMascheroniConstant) * (spectralTest f r).re) volume :=
    ((integrable_spectralTest hf).re).const_mul _
  have hIntGamma' : Integrable (fun r : ℝ =>
      Real.eulerMascheroniConstant * (spectralTest f r).re) volume :=
    ((integrable_spectralTest hf).re).const_mul _
  have hIntRatioMain : Integrable (fun r : ℝ =>
      ((∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
        * (spectralTest f r).re) volume := by
    refine ((integrable_digammaDensity_mul_spectralTest hf).add hIntGamma').congr
      (Eventually.of_forall fun r => ?_)
    change digammaDensity r * (spectralTest f r).re
        + Real.eulerMascheroniConstant * (spectralTest f r).re
      = (∫ x in (0 : ℝ)..1,
          (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re
        * (spectralTest f r).re
    have hI : (∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re
        = digammaDensity r + Real.eulerMascheroniConstant := by
      rw [hdensity r]
      ring
    rw [hI]
    ring
  have hEq1 : (∫ r : ℝ, digammaDensity r * (spectralTest f r).re)
      = (-Real.eulerMascheroniConstant) * (∫ r : ℝ, (spectralTest f r).re)
        + ∫ r : ℝ, ((∫ x in (0 : ℝ)..1,
            (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
            * (spectralTest f r).re := by
    rw [show (∫ r : ℝ, digammaDensity r * (spectralTest f r).re)
        = ∫ r : ℝ, ((-Real.eulerMascheroniConstant)
            + (∫ x in (0 : ℝ)..1,
                (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
            * (spectralTest f r).re from
          integral_congr_ae (Eventually.of_forall fun r => by
            dsimp only
            rw [hdensity r])]
    rw [show (∫ r : ℝ, ((-Real.eulerMascheroniConstant)
            + (∫ x in (0 : ℝ)..1,
                (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
            * (spectralTest f r).re)
        = (∫ r : ℝ, (-Real.eulerMascheroniConstant) * (spectralTest f r).re)
          + ∫ r : ℝ, ((∫ x in (0 : ℝ)..1,
              (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
              * (spectralTest f r).re from by
          rw [← integral_add hIntGamma hIntRatioMain]
          exact integral_congr_ae (Eventually.of_forall fun r => by
            dsimp only
            ring)]
    rw [integral_const_mul]
  have hG0 : (∫ r : ℝ, (spectralTest f r).re) = 2 * Real.pi * (autocorr f 0).re := by
    rw [integral_spectralTest_re_eq hf, autocorr_zero_re hf]
  have hEq2 : (∫ r : ℝ, ((∫ x in (0 : ℝ)..1,
        (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
        * (spectralTest f r).re)
      = ∫ t : ℝ, (∫ r : ℝ,
          (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
            * (spectralTest f r).re)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    integral_digammaRatio_re_mul_spectralTest hf
  have hae1 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), t ≠ 1 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
      ext a
      simp
    filter_upwards [(ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 1)).mpr
      (by rw [hset]; exact measure_singleton 1)] with x hx _
    exact hx
  have hae2 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      t ∈ Set.Ioc (0 : ℝ) 1 := self_mem_ae_restrict measurableSet_Ioc
  have hinner : (fun t : ℝ => (∫ r : ℝ,
        (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
          * (spectralTest f r).re))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t : ℝ => (2 * Real.pi * (autocorr f 0).re
          - t ^ (-(3 / 4 : ℝ)) * (2 * Real.pi * (autocorr f (Real.log t / 2)).re))
          / (1 - t)) := by
    filter_upwards [hae1, hae2] with t htne htmem
    exact integral_digammaDoubleIntegrand_inner hf htmem.1 (lt_of_le_of_ne htmem.2 htne)
  have hEq3 : (∫ t : ℝ, (∫ r : ℝ,
        (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
          * (spectralTest f r).re)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      = 2 * Real.pi * ∫ t in (0 : ℝ)..1,
          ((autocorr f 0).re
            - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t) := by
    rw [integral_congr_ae hinner]
    have hpull : (∫ t : ℝ, (2 * Real.pi * (autocorr f 0).re
          - t ^ (-(3 / 4 : ℝ)) * (2 * Real.pi * (autocorr f (Real.log t / 2)).re))
          / (1 - t) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = 2 * Real.pi * ∫ t : ℝ,
            ((autocorr f 0).re
              - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun t => by
        dsimp only
        ring)
    rw [hpull,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc digammaSpectralBlock f
      = (1 / (2 * Real.pi)) * ∫ r : ℝ,
          digammaDensity r * (spectralTest f r).re := rfl
    _ = (1 / (2 * Real.pi)) * ((-Real.eulerMascheroniConstant)
          * (∫ r : ℝ, (spectralTest f r).re)
          + ∫ r : ℝ, ((∫ x in (0 : ℝ)..1,
              (1 - (x : ℂ) ^ ((digammaZ r) - 1)) / (1 - (x : ℂ))).re)
              * (spectralTest f r).re) := by rw [hEq1]
    _ = (1 / (2 * Real.pi)) * ((-Real.eulerMascheroniConstant)
          * (2 * Real.pi * (autocorr f 0).re)
          + ∫ t : ℝ, (∫ r : ℝ,
              (((1 - (t : ℂ) ^ ((digammaZ r) - 1)) / (1 - (t : ℂ))).re)
                * (spectralTest f r).re)
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by rw [hEq2, hG0]
    _ = (1 / (2 * Real.pi)) * ((-Real.eulerMascheroniConstant)
          * (2 * Real.pi * (autocorr f 0).re)
          + 2 * Real.pi * ∫ t in (0 : ℝ)..1,
              ((autocorr f 0).re
                - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t)) := by
        rw [hEq3]
    _ = -Real.eulerMascheroniConstant * (autocorr f 0).re
          + ∫ t in (0 : ℝ)..1,
              ((autocorr f 0).re
                - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t) := by
        field_simp [Real.pi_ne_zero]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.autocorr_zero_re
#print axioms RHLean.ExplicitFormula.re_integral_digammaRatio
#print axioms RHLean.ExplicitFormula.integral_digammaRatio_re_mul_spectralTest
#print axioms RHLean.ExplicitFormula.integral_digammaDoubleIntegrand_inner
#print axioms RHLean.ExplicitFormula.digammaSpectralBlock_eq_positionSpace

end

end Inline_ExplicitFormula_RH62

section Inline_ExplicitFormula_RH63



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem autocorr_re_even {f : ℝ → ℂ} (hf : f ∈ oddCore) (u : ℝ) :
    (autocorr f (-u)).re = (autocorr f u).re :=
  congrArg Complex.re (autocorr_neg hf.2.2 u)


theorem digammaKernel_eq_uIntegral {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    (∫ t in (0 : ℝ)..1,
        ((autocorr f 0).re
            - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t))
      = ∫ u in Set.Ioi (0 : ℝ),
          ((autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re)
            * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))) := by
  have hIoc : (∫ t in (0 : ℝ)..1,
        ((autocorr f 0).re
            - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t))
      = ∫ t in Set.Ioc (0 : ℝ) 1,
          ((autocorr f 0).re
            - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t) :=
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)
  rw [hIoc]
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    have hset : {a : ℝ | ¬a ≠ 1} = {1} := by
      ext a
      simp
    exact (ae_iff (μ := volume) (p := fun x : ℝ => x ≠ 1)).mpr
      (by rw [hset]; exact measure_singleton 1)
  have hae : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Ioo (0 : ℝ) 1 := by
    filter_upwards [hne] with x hx
    rw [Set.mem_Ioc, Set.mem_Ioo]
    exact propext ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 hx⟩, fun h => ⟨h.1, h.2.le⟩⟩
  rw [setIntegral_congr_set hae]
  have himage : (fun u : ℝ => Real.exp (-(2 * u))) '' Set.Ioi (0 : ℝ)
      = Set.Ioo (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu'
      exact ⟨Real.exp_pos _, by rw [Real.exp_lt_one_iff]; linarith⟩
    · intro ht
      refine ⟨-(Real.log t) / 2, ?_, ?_⟩
      · have hlog : Real.log t < 0 := Real.log_neg ht.1 ht.2
        show (0 : ℝ) < -(Real.log t) / 2
        linarith
      · show Real.exp (-(2 * (-(Real.log t) / 2))) = t
        rw [show -(2 * (-(Real.log t) / 2)) = Real.log t by ring, Real.exp_log ht.1]
  rw [← himage]
  have hderiv : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (-(2 * u)))
        (-(2 * Real.exp (-(2 * u)))) (Set.Ioi (0 : ℝ)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => -(2 * u)) (-(2 : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(2 : ℝ))
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(2 * u)))
        (Real.exp (-(2 * u)) * (-(2 : ℝ))) u := h1.exp
    have h3 : Real.exp (-(2 * u)) * (-(2 : ℝ)) = -(2 * Real.exp (-(2 * u))) := by
      ring
    rw [h3] at h2
    exact h2.hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => Real.exp (-(2 * u))) (Set.Ioi (0 : ℝ)) := by
    intro x _ y _ hxy
    have h : -(2 * x) = -(2 * y) := Real.exp_injective hxy
    linarith
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun t : ℝ => ((autocorr f 0).re
      - t ^ (-(3 / 4 : ℝ)) * (autocorr f (Real.log t / 2)).re) / (1 - t))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have hrpow : (Real.exp (-(2 * u))) ^ (-(3 / 4 : ℝ)) = Real.exp (3 * u / 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hlog : Real.log (Real.exp (-(2 * u))) / 2 = -u := by
    rw [Real.log_exp]
    ring
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-(2 * u))),
    hrpow, hlog, autocorr_re_even hf u]
  ring


theorem digammaSpectralBlock_eq_positionSpaceU {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    digammaSpectralBlock f
      = -Real.eulerMascheroniConstant * (autocorr f 0).re
        + ∫ u in Set.Ioi (0 : ℝ),
            ((autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re)
              * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))) := by
  rw [digammaSpectralBlock_eq_positionSpace hf, digammaKernel_eq_uIntegral hf]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.autocorr_re_even
#print axioms RHLean.ExplicitFormula.digammaKernel_eq_uIntegral
#print axioms RHLean.ExplicitFormula.digammaSpectralBlock_eq_positionSpaceU

end

end Inline_ExplicitFormula_RH63

section Inline_ExplicitFormula_RH64
























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


noncomputable def digammaKernel (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  ((autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re)
    * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))


noncomputable def digammaKernelTerm (f : ℝ → ℂ) (n : ℕ) (u : ℝ) : ℝ :=
  ((autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re)
    * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))


noncomputable def digammaKernelTermBound (f : ℝ → ℂ) (n : ℕ) (u : ℝ) : ℝ :=
  |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
    * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))




theorem exists_autocorr_re_bound {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, |(autocorr f u).re| ≤ B := by
  obtain ⟨R, hR0, hR⟩ := exists_support_radius (hasCompactSupport_autocorr hf)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    ((contDiff_autocorr hf).continuous.continuousOn)
  refine ⟨max B 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ Set.Icc (-R) R
  · exact le_trans (Complex.abs_re_le_norm _)
      (le_trans (hB u hu) (le_max_left _ _))
  · have hdev : u < -R ∨ R < u := by
      by_cases h1 : -R ≤ u
      · exact Or.inr (lt_of_not_ge fun h2 => hu ⟨h1, h2⟩)
      · exact Or.inl (lt_of_not_ge h1)
    have hgt : R < |u| := by
      rcases hdev with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hR u hgt]
    simp


theorem exists_autocorr_re_exp_bound {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re| ≤ C * u := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_autocorr hf).continuous_deriv (by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_autocorr hf).continuous).continuousOn
  refine ⟨max K 0 + max B 0 * ((3 / 2) * Real.exp (3 / 2)), by positivity, fun u hu => ?_⟩
  have hu0 : (0 : ℝ) < u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hderivBound : ∀ x ∈ Set.Ico (0 : ℝ) u, ‖deriv (autocorr f) x‖ ≤ max K 0 := by
    intro x hx
    exact le_trans (hK x ⟨hx.1, le_trans hx.2.le hu1⟩) (le_max_left K 0)
  have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := u)
    (f := autocorr f) (f' := fun x => deriv (autocorr f) x) (C := max K 0)
    (fun x hx => ((contDiff_autocorr hf).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
    hderivBound
  have hgu : |(autocorr f u).re - (autocorr f 0).re| ≤ max K 0 * u := by
    have h1 := hMVT u ⟨hu0.le, le_rfl⟩
    calc |(autocorr f u).re - (autocorr f 0).re|
        = |((autocorr f u - autocorr f 0).re)| := by rw [Complex.sub_re]
      _ ≤ ‖autocorr f u - autocorr f 0‖ := Complex.abs_re_le_norm _
      _ ≤ max K 0 * (u - 0) := h1
      _ = max K 0 * u := by ring
  have hBu : |(autocorr f u).re| ≤ max B 0 :=
    le_trans (Complex.abs_re_le_norm _)
      (le_trans (hB u ⟨hu0.le, hu1⟩) (le_max_left _ _))
  have hexp : |Real.exp (3 * u / 2) - 1| ≤ (3 / 2) * Real.exp (3 / 2) * u := by
    have hMVT2 := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ))
      (b := 3 * u / 2) (f := Real.exp) (f' := Real.exp) (C := Real.exp (3 / 2))
      (fun x hx => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hx2 : x ≤ 3 * u / 2 := hx.2.le
        nlinarith [hx2, hu1])
    have h3 := hMVT2 (3 * u / 2) ⟨by positivity, le_rfl⟩
    have h4 : Real.exp (3 * u / 2) - Real.exp 0 = Real.exp (3 * u / 2) - 1 := by
      rw [Real.exp_zero]
    rw [h4] at h3
    calc |Real.exp (3 * u / 2) - 1| = ‖Real.exp (3 * u / 2) - 1‖ := by rw [Real.norm_eq_abs]
      _ ≤ Real.exp (3 / 2) * (3 * u / 2 - 0) := h3
      _ = (3 / 2) * Real.exp (3 / 2) * u := by ring
  have hsplit : (autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re
      = ((autocorr f 0).re - (autocorr f u).re)
        + (autocorr f u).re * (1 - Real.exp (3 * u / 2)) := by ring
  rw [hsplit]
  calc |((autocorr f 0).re - (autocorr f u).re)
        + (autocorr f u).re * (1 - Real.exp (3 * u / 2))|
      ≤ |(autocorr f 0).re - (autocorr f u).re|
        + |(autocorr f u).re * (1 - Real.exp (3 * u / 2))| := abs_add_le _ _
    _ = |(autocorr f 0).re - (autocorr f u).re|
        + |(autocorr f u).re| * |1 - Real.exp (3 * u / 2)| := by rw [abs_mul]
    _ ≤ max K 0 * u + max B 0 * ((3 / 2) * Real.exp (3 / 2) * u) := by
        have h1 : |(autocorr f 0).re - (autocorr f u).re| ≤ max K 0 * u := by
          rw [abs_sub_comm]
          exact hgu
        have h2 : |1 - Real.exp (3 * u / 2)| = |Real.exp (3 * u / 2) - 1| := abs_sub_comm _ _
        rw [h2]
        have h3 : |(autocorr f u).re| * |Real.exp (3 * u / 2) - 1|
            ≤ |(autocorr f u).re| * ((3 / 2) * Real.exp (3 / 2) * u) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        have h4 : |(autocorr f u).re| * ((3 / 2) * Real.exp (3 / 2) * u)
            ≤ max B 0 * ((3 / 2) * Real.exp (3 / 2) * u) :=
          mul_le_mul_of_nonneg_right hBu (by positivity)
        exact add_le_add h1 (h3.trans h4)
    _ = (max K 0 + max B 0 * ((3 / 2) * Real.exp (3 / 2))) * u := by ring




theorem digammaKernel_le_inv {u : ℝ} (hu : 0 < u) :
    2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))) ≤ 1 / u := by
  have hden : 0 < 1 - Real.exp (-(2 * u)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hkey : Real.exp (-(2 * u)) * (2 * u + 1) ≤ 1 := by
    have h := Real.add_one_le_exp (2 * u)
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos (-(2 * u))).le
    have h3 : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [h2, h3]
  rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hu]
  nlinarith [hkey]



theorem digammaKernel_majorant {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Ioi (0 : ℝ),
      |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
        * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))
      ≤ C * (Real.exp (-(u / 2)) + (1 + u ^ 2)⁻¹) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_autocorr_re_exp_bound hf
  obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf
  have hg0B : |(autocorr f 0).re| ≤ B := hB 0
  have hden2 : 0 < 1 - Real.exp (-(2 : ℝ)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hD0 : 0 ≤ 2 / (1 - Real.exp (-(2 : ℝ))) := by positivity
  refine ⟨2 * C₁ + 2 * (2 / (1 - Real.exp (-(2 : ℝ)))) * B + 1,
    by nlinarith [hC₁0, hB0, hD0], fun u hu => ?_⟩
  have hKpos : 0 ≤ 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))) := by
    have hu' : (0 : ℝ) < u := hu
    apply div_nonneg (by positivity)
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr (by linarith)
  by_cases hu1 : u ≤ 1
  · have hu0 : (0 : ℝ) < u := hu
    have hA := hC₁ u ⟨hu, hu1⟩
    have hK := digammaKernel_le_inv hu
    have hfrac : (1 / 2 : ℝ) ≤ Real.exp (-(u / 2)) + (1 + u ^ 2)⁻¹ := by
      have h2 : (1 / 2 : ℝ) ≤ (1 + u ^ 2)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
        rw [inv_le_inv₀ (by norm_num : (0 : ℝ) < 2)
          (by have : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u; linarith)]
        nlinarith [hu0.le, hu1, sq_nonneg u]
      linarith [Real.exp_pos (-(u / 2))]
    have hCu : C₁ ≤ (2 * C₁ + 2 * (2 / (1 - Real.exp (-(2 : ℝ)))) * B + 1) * (1 / 2) := by
      nlinarith [hC₁0, hB0, hD0]
    calc |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
          * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))
        ≤ (C₁ * u) * (1 / u) :=
          mul_le_mul hA hK hKpos (mul_nonneg hC₁0 hu0.le)
      _ = C₁ := by field_simp [ne_of_gt hu0]
      _ ≤ (2 * C₁ + 2 * (2 / (1 - Real.exp (-(2 : ℝ)))) * B + 1)
            * (Real.exp (-(u / 2)) + (1 + u ^ 2)⁻¹) :=
          le_trans hCu (mul_le_mul_of_nonneg_left hfrac (by positivity))
  · push_neg at hu1
    have hA : |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
        ≤ B + B * Real.exp (3 * u / 2) := by
      have h1 : |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
          ≤ |(autocorr f 0).re| + |Real.exp (3 * u / 2)| * |(autocorr f u).re| := by
        calc |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
            = |(autocorr f 0).re + -(Real.exp (3 * u / 2) * (autocorr f u).re)| := by ring_nf
          _ ≤ |(autocorr f 0).re| + |-(Real.exp (3 * u / 2) * (autocorr f u).re)| :=
              abs_add_le _ _
          _ = |(autocorr f 0).re| + |Real.exp (3 * u / 2) * (autocorr f u).re| := by
              rw [abs_neg]
          _ = |(autocorr f 0).re| + |Real.exp (3 * u / 2)| * |(autocorr f u).re| := by
              rw [abs_mul]
      rw [abs_of_pos (Real.exp_pos _)] at h1
      linarith [h1, hg0B, mul_le_mul_of_nonneg_left (hB u) (Real.exp_pos (3 * u / 2)).le]
    have hK : 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))
        ≤ 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 : ℝ))) := by
      have hnum : 0 ≤ 2 * Real.exp (-(2 * u)) := by positivity
      apply div_le_div_of_nonneg_left hnum hden2
      rw [sub_le_sub_iff_left]
      exact Real.exp_le_exp.mpr (by linarith)
    have hexp_le : Real.exp (-(2 * u)) ≤ Real.exp (-(u / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hEe : Real.exp (3 * u / 2) * Real.exp (-(2 * u)) = Real.exp (-(u / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hEq : (B + B * Real.exp (3 * u / 2))
          * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 : ℝ))))
        = (2 / (1 - Real.exp (-(2 : ℝ)))) * B
            * (Real.exp (-(2 * u)) + Real.exp (-(u / 2))) := by
      rw [show (B + B * Real.exp (3 * u / 2))
            * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 : ℝ))))
          = B * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 : ℝ))))
            + B * (2 * (Real.exp (3 * u / 2) * Real.exp (-(2 * u)))
                / (1 - Real.exp (-(2 : ℝ)))) by ring]
      rw [hEe]
      ring
    calc |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
          * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))
        ≤ (B + B * Real.exp (3 * u / 2))
            * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 : ℝ)))) :=
          mul_le_mul hA hK hKpos (by positivity)
      _ = (2 / (1 - Real.exp (-(2 : ℝ)))) * B
            * (Real.exp (-(2 * u)) + Real.exp (-(u / 2))) := hEq
      _ ≤ (2 * C₁ + 2 * (2 / (1 - Real.exp (-(2 : ℝ)))) * B + 1)
            * (Real.exp (-(u / 2)) + (1 + u ^ 2)⁻¹) := by
          have hinv : 0 ≤ (1 + u ^ 2)⁻¹ := by positivity
          nlinarith [hexp_le, Real.exp_pos (-(u / 2)), hinv, hC₁0, hB0, hD0, mul_nonneg hD0 hB0]


theorem integrableOn_exp_neg_mul_form {a b : ℝ} (hb : 0 < b) :
    Integrable (fun u : ℝ => Real.exp (-(b * u))) (volume.restrict (Set.Ioi a)) := by
  have h := exp_neg_integrableOn_Ioi a hb
  refine h.congr (Eventually.of_forall fun u => ?_)
  apply congrArg Real.exp
  ring


theorem integrable_exp_neg_half_add_inv (C : ℝ) :
    Integrable (fun u : ℝ => C * (Real.exp (-(u / 2)) + (1 + u ^ 2)⁻¹))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(u / 2))) (Set.Ioi (0 : ℝ)) volume := by
    have h := integrableOn_exp_neg_mul_form (a := (0 : ℝ)) (b := (1 / 2)) (by norm_num)
    refine h.congr (Eventually.of_forall fun u => ?_)
    apply congrArg Real.exp
    ring
  have h2 : IntegrableOn (fun u : ℝ => (1 + u ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) volume :=
    integrable_inv_one_add_sq.integrableOn
  exact (h1.add h2).const_mul C




theorem hasSum_exp_geometric {c : ℝ} {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => c * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u))))
      (c * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))) := by
  have hr : ‖Real.exp (-(2 * u))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (2 * Real.exp (-(2 * u)))
  have hterm : (fun n : ℕ => (2 * Real.exp (-(2 * u))) * (Real.exp (-(2 * u))) ^ n)
      = fun n : ℕ => 2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)) := by
    funext n
    rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hterm] at hg
  have hg2 := hg.mul_left c
  simpa [div_eq_mul_inv, mul_assoc] using hg2


theorem digammaKernelTermBound_hasSum {f : ℝ → ℂ} (hf : f ∈ oddCore) {u : ℝ}
    (hu : 0 < u) :
    HasSum (fun n : ℕ => digammaKernelTermBound f n u)
      (|(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
        * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))) :=
  hasSum_exp_geometric (c := |(autocorr f 0).re
    - Real.exp (3 * u / 2) * (autocorr f u).re|) hu


theorem digammaKernelTermBound_tsum {f : ℝ → ℂ} (hf : f ∈ oddCore) {u : ℝ}
    (hu : 0 < u) :
    (∑' n : ℕ, digammaKernelTermBound f n u)
      = |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
        * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))) :=
  (digammaKernelTermBound_hasSum hf hu).tsum_eq


theorem integrable_tsum_digammaKernelTermBound {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Integrable (fun u : ℝ => ∑'
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := digammaKernel_majorant hf
  refine Integrable.mono' (integrable_exp_neg_half_add_inv C) ?_ ?_
  · have heq : (fun u : ℝ => ∑' n : ℕ, digammaKernelTermBound f n u)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun u : ℝ => |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
          * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      exact digammaKernelTermBound_tsum hf hu
    have hgcont : Continuous (fun u : ℝ => (autocorr f u).re) :=
      Complex.continuous_re.comp (contDiff_autocorr hf).continuous
    have hbase : Continuous (fun u : ℝ =>
        |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|) :=
      (continuous_const.sub ((Real.continuous_exp.comp
        (by fun_prop : Continuous fun u : ℝ => 3 * u / 2)).mul hgcont)).abs
    have hnum : Continuous (fun u : ℝ => 2 * Real.exp (-(2 * u))) :=
      continuous_const.mul (Real.continuous_exp.comp
        (by fun_prop : Continuous fun u : ℝ => -(2 * u)))
    have hden : Continuous (fun u : ℝ => 1 - Real.exp (-(2 * u))) :=
      continuous_const.sub (Real.continuous_exp.comp
        (by fun_prop : Continuous fun u : ℝ => -(2 * u)))
    have hcont : ContinuousOn (fun u : ℝ =>
        |(autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re|
          * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))))) (Set.Ioi (0 : ℝ)) :=
      hbase.continuousOn.mul (hnum.continuousOn.div hden.continuousOn (fun u hu => by
        have hu'
        rw [sub_ne_zero]
        exact ne_of_gt (Real.exp_lt_one_iff.mpr (by linarith))))
    exact (hcont.aestronglyMeasurable measurableSet_Ioi).congr heq.symm
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu' : (0 : ℝ) < u := hu
    rw [digammaKernelTermBound_tsum hf hu, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    · exact hC u hu
    · exact mul_nonneg (abs_nonneg _) (by
        apply div_nonneg (by positivity)
        rw [sub_nonneg]
        exact Real.exp_le_one_iff.mpr (by linarith))




theorem integral_exp_neg_abs_mul_eq {g : ℝ → ℝ} (hg_even : ∀ u, g (-u) = g u) (b : ℝ) :
    (∫ u : ℝ, Real.exp (-(b * |u|)) * g u)
      = 2 * ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(b * u)) * g u := by
  have h := integral_comp_abs (f := fun x : ℝ => Real.exp (-(b * x)) * g x)
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  rcases lt_or_ge x 0 with hx | hx
  · rw [abs_of_neg hx, ← hg_even (-x)]
    ring_nf
  · rw [abs_of_nonneg hx]


theorem integral_digammaKernelTerm {f : ℝ → ℂ} (hf : f ∈ oddCore) (n : ℕ) :
    (∫ u : ℝ, digammaKernelTerm f n u ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      = (autocorr f 0).re / ((n : ℝ) + 1)
        - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|))
            * (autocorr f u).re := by
  set b : ℝ := (2 : ℝ) * n + 1 / 2 with hb_def
  have hb : 0 < b := by rw [hb_def]; positivity
  have ha : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hpt : digammaKernelTerm f n = fun u : ℝ =>
      (autocorr f 0).re * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))
        - (2 * Real.exp (-(b * u))) * (autocorr f u).re := by
    funext u
    unfold digammaKernelTerm
    have hEb : Real.exp (3 * u / 2) * Real.exp (-(2 * ((n : ℝ) + 1) * u))
        = Real.exp (-(b * u)) := by
      rw [← Real.exp_add, hb_def]
      congr 1
      push_cast
      ring
    calc ((autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re)
          * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))
        = (autocorr f 0).re * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))
          - (2 * (Real.exp (3 * u / 2) * Real.exp (-(2 * ((n : ℝ) + 1) * u))))
              * (autocorr f u).re := by ring
      _ = (autocorr f 0).re * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))
          - (2 * Real.exp (-(b * u))) * (autocorr f u).re := by rw [hEb]
  rw [hpt]
  have hInt1 : Integrable (fun u : ℝ =>
      (autocorr f 0).re * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := integrableOn_exp_neg_mul_form (a := (0 : ℝ))
      (b := 2 * ((n : ℝ) + 1)) ha
    exact (h.const_mul 2).const_mul _
  have hInt2 : Integrable (fun u : ℝ =>
      (2 * Real.exp (-(b * u))) * (autocorr f u).re)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf
    have hexp : Integrable (fun u : ℝ => Real.exp (-(b * u)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      integrableOn_exp_neg_mul_form (a := (0 : ℝ)) hb
    have hmeas : AEStronglyMeasurable (fun u : ℝ => (autocorr f u).re)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (Complex.continuous_re.comp (contDiff_autocorr hf).continuous).continuousOn.aestronglyMeasurable
        measurableSet_Ioi
    have hbdd : ∀ᵐ u ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖(autocorr f u).re‖ ≤ B := by
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact hB u
    have h1 : Integrable (fun u : ℝ => Real.exp (-(b * u)) * (autocorr f u).re)
        (volume.restrict (Set.Ioi (0 : ℝ))) := hexp.mul_bdd hmeas hbdd
    refine (h1.const_mul 2).congr (Eventually.of_forall fun u => ?_)
    ring
  rw [integral_sub hInt1 hInt2]
  have hExp : (∫ u : ℝ, Real.exp (-(2 * ((n : ℝ) + 1) * u))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 1 / (2 * ((n : ℝ) + 1)) := by
    have h := integral_exp_mul_Ioi (a := -(2 * ((n : ℝ) + 1))) (by linarith) 0
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hval1 : (∫ u : ℝ,
      (autocorr f 0).re * (2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = (autocorr f 0).re / ((n : ℝ) + 1) := by
    rw [integral_const_mul]
    have h2 : (∫ u : ℝ, 2 * Real.exp (-(2 * ((n : ℝ) + 1) * u))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 1 / ((n : ℝ) + 1) := by
      have hsplit2 : (∫ u : ℝ, 2 * Real.exp (-(2 * ((n : ℝ) + 1) * u))
          ∂(volume.restrict (Set.Ioi (0 : ℝ))))
          = 2 * ∫ u : ℝ, Real.exp (-(2 * ((n : ℝ) + 1) * u))
              ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
        rw [← integral_const_mul]
      rw [hsplit2, hExp]
      field_simp
    rw [h2]
    ring
  have hval2 : (∫ u : ℝ, (2 * Real.exp (-(b * u))) * (autocorr f u).re
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      = ∫ u : ℝ, Real.exp (-(b * |u|)) * (autocorr f u).re := by
    have h1 : (∫ u : ℝ, (2 * Real.exp (-(b * u))) * (autocorr f u).re
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))
        = 2 * ∫ u : ℝ, Real.exp (-(b * u)) * (autocorr f u).re
            ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    rw [h1, ← integral_exp_neg_abs_mul_eq (g := fun u => (autocorr f u).re) (b := b)
      (fun u => autocorr_re_even hf u)]
  rw [hval1, hval2, hb_def]




theorem digammaKernel_uIntegral_eq_tsum {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    (∫ u : ℝ, digammaKernel f u ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      = ∑' n : ℕ, ((autocorr f 0).re / ((n : ℝ) + 1)
          - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|))
              * (autocorr f u).re) := by
  have hmain : HasSum
      (fun n : ℕ => ∫ u : ℝ, digammaKernelTerm f n u
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      (∫ u : ℝ, digammaKernel f u ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hasSum_integral_of_dominated_convergence
      (fun n : ℕ => digammaKernelTermBound f n)
      (fun n => by
        have hgcont : Continuous (fun u : ℝ => (autocorr f u).re) :=
          Complex.continuous_re.comp (contDiff_autocorr hf).continuous
        have hcont : Continuous (fun u : ℝ => digammaKernelTerm f n u) := by
          simp only [digammaKernelTerm]
          exact (continuous_const.sub (((Real.continuous_exp.comp
            (by fun_prop : Continuous fun u : ℝ => 3 * u / 2)).mul hgcont))).mul
            (continuous_const.mul (Real.continuous_exp.comp
              (by fun_prop : Continuous fun u : ℝ => -(2 * ((n : ℝ) + 1) * u))))
        exact hcont.aestronglyMeasurable)
      (fun n => by
        filter_upwards with u
        simp only [digammaKernelTerm, digammaKernelTermBound]
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-(2 * ((n : ℝ) + 1) * u)))])
      (by
        filter_upwards [self_mem_ae_restrict (μ := volume)
          (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi] with u hu
        exact (digammaKernelTermBound_hasSum hf hu).summable)
      (integrable_tsum_digammaKernelTermBound hf)
      (by
        filter_upwards [self_mem_ae_restrict (μ := volume)
          (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi] with u hu
        have h := hasSum_exp_geometric
          (c := (autocorr f 0).re - Real.exp (3 * u / 2) * (autocorr f u).re) hu
        simpa [digammaKernel, digammaKernelTerm, div_eq_mul_inv, mul_assoc] using h)
  rw [← hmain.tsum_eq]
  apply tsum_congr
  intro n
  exact integral_digammaKernelTerm hf n


theorem digammaSpectralBlock_eq_tsum {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    digammaSpectralBlock f
      = -Real.eulerMascheroniConstant * (autocorr f 0).re
        + ∑'
            - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|))
                * (autocorr f u).re) := by
  rw [digammaSpectralBlock_eq_positionSpaceU hf]
  congr 1
  simpa only [digammaKernel] using digammaKernel_uIntegral_eq_tsum hf

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_autocorr_re_bound
#print axioms RHLean.ExplicitFormula.exists_autocorr_re_exp_bound
#print axioms RHLean.ExplicitFormula.digammaKernel_le_inv
#print axioms RHLean.ExplicitFormula.digammaKernel_majorant
#print axioms RHLean.ExplicitFormula.integrable_exp_neg_half_add_inv
#print axioms RHLean.ExplicitFormula.hasSum_exp_geometric
#print axioms RHLean.ExplicitFormula.digammaKernelTermBound_hasSum
#print axioms RHLean.ExplicitFormula.digammaKernelTermBound_tsum
#print axioms RHLean.ExplicitFormula.integrable_tsum_digammaKernelTermBound
#print axioms RHLean.ExplicitFormula.integral_exp_neg_abs_mul_eq
#print axioms RHLean.ExplicitFormula.integral_digammaKernelTerm
#print axioms RHLean.ExplicitFormula.digammaKernel_uIntegral_eq_tsum
#print axioms RHLean.ExplicitFormula.digammaSpectralBlock_eq_tsum

end

end Inline_ExplicitFormula_RH64

section Inline_ExplicitFormula_RH22
























noncomputable section

open MeasureTheory Complex Set
open scoped Real Topology BigOperators

namespace RHLean.ExplicitFormula



theorem weilOdd_eq_real : @weilOdd = @RHLean.weilOdd := rfl

theorem localizedForm_eq_real : @localizedForm = @RHLean.localizedForm := rfl

theorem localizedCore_eq_real : @localizedCore = @RHLean.localizedCore := rfl


theorem weilExplicitFormulaOddAt_iff_real (a : ℝ) :
    WeilExplicitFormulaOddAt a ↔
      (0 < a → ∀ f : ℝ → ℂ, f ∈ RHLean.localizedCore a →
        RHLean.weilOdd f = RHLean.localizedForm a f) :=
  Iff.rfl






theorem weilExplicitFormulaOddAt_of_two_obligations {a : ℝ}
    (hGW : EvenGuinandWeilAt a) (hArch : ArchimedeanMatchAt a) :
    WeilExplicitFormulaOddAt a :=
  weilExplicitFormulaOddAt_of_evenGuinandWeil hGW hArch


theorem weilExplicitFormulaOddNonnegAt_of_two_obligations {a : ℝ}
    (hGW : EvenGuinandWeilAt a) (hArch : ArchimedeanMatchAt a) :
    WeilExplicitFormulaOddNonnegAt a :=
  nonnegAt_of_explicitFormulaAt (weilExplicitFormulaOddAt_of_two_obligations hGW hArch)





theorem riemannXi_zero_tail_le_real (h : RiemannVonMangoldtCountBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      (∑' p : XiZero, (if X < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ C * (Real.log X / X) :=
  riemannXi_zero_tail_le h

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOddAt_of_two_obligations
#print axioms RHLean.ExplicitFormula.riemannXi_zero_tail_le_real

end

end Inline_ExplicitFormula_RH22

section Inline_ExplicitFormula_RH49


























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators

namespace RHLean.ExplicitFormula




theorem weilExplicitFormulaOdd_of_obligations
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hArch : ∀ a : ℝ, ArchimedeanMatchAt a) :
    WeilExplicitFormulaOdd :=
  fun a => weilExplicitFormulaOddAt_of_two_obligations (hGW a) (hArch a)


theorem weilExplicitFormulaOddNonneg_of_obligations
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hArch : ∀ a : ℝ, ArchimedeanMatchAt a) :
    WeilExplicitFormulaOddNonneg :=
  fun a => weilExplicitFormulaOddNonnegAt_of_two_obligations (hGW a) (hArch a)





theorem weilExplicitFormulaOdd_of_evenGuinandWeil_digammaMatch
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hDM : ∀ a : ℝ, DigammaArchimedeanMatchAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_obligations hGW
    (fun a => archimedeanMatchAt_of_digammaMatch (hDM a))


theorem weilExplicitFormulaOddNonneg_of_evenGuinandWeil_digammaMatch
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hDM : ∀ a : ℝ, DigammaArchimedeanMatchAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_obligations hGW
    (fun a => archimedeanMatchAt_of_digammaMatch (hDM a))

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_obligations
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOddNonneg_of_obligations
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_evenGuinandWeil_digammaMatch
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOddNonneg_of_evenGuinandWeil_digammaMatch

end

end Inline_ExplicitFormula_RH49

section Inline_ExplicitFormula_RH65























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula










def MehlerDirichletKernelAt (a : ℝ) : Prop :=
  0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a →
    (∑'
        - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|))
            * (autocorr f u).re))
      = archForm a f + (-Real.log 2) * (autocorr f 0).re
        + potentialForm a f - gammaForm a f



theorem digammaMatchAt_of_mehlerDirichlet {a : ℝ} (h : MehlerDirichletKernelAt a) :
    DigammaArchimedeanMatchAt a := by
  intro ha f hf
  have hodd : f ∈ oddCore := localizedCore_subset_oddCore a hf
  rw [digammaSpectralBlock_eq_tsum hodd, h ha f hf, physicalConstant_add_logPi,
    ← integral_normSq_eq_setIntegral hf, ← autocorr_zero_re hodd]
  ring


theorem archimedeanMatchAt_of_mehlerDirichlet {a : ℝ} (h : MehlerDirichletKernelAt a) :
    ArchimedeanMatchAt a :=
  archimedeanMatchAt_of_digammaMatch (digammaMatchAt_of_mehlerDirichlet h)



theorem weilExplicitFormulaOdd_of_evenGuinandWeil_mehler
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hMD : ∀ a : ℝ, MehlerDirichletKernelAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_evenGuinandWeil_digammaMatch hGW
    (fun a => digammaMatchAt_of_mehlerDirichlet (hMD a))


theorem weilExplicitFormulaOddNonneg_of_evenGuinandWeil_mehler
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hMD : ∀ a : ℝ, MehlerDirichletKernelAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_evenGuinandWeil_digammaMatch hGW
    (fun a => digammaMatchAt_of_mehlerDirichlet (hMD a))

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.digammaMatchAt_of_mehlerDirichlet
#print axioms RHLean.ExplicitFormula.archimedeanMatchAt_of_mehlerDirichlet
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_evenGuinandWeil_mehler
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOddNonneg_of_evenGuinandWeil_mehler

end

end Inline_ExplicitFormula_RH65

section Inline_ExplicitFormula_RH66















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem exp_sub_one_sub_id_le_mul (s : ℝ) (hs : 0 ≤ s) :
    Real.exp s - 1 - s ≤ s * (Real.exp s - 1) := by
  by_cases hs1 : s ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le (x := s) (by
      rw [abs_of_nonneg hs]; exact hs1)
    have hnn : 0 ≤ Real.exp s - 1 - s := by
      have := Real.add_one_le_exp s
      linarith
    rw [abs_of_nonneg hnn] at h
    have h2 : s ^ 2 ≤ s * (Real.exp s - 1) := by
      have := Real.add_one_le_exp s
      nlinarith [hs, this]
    linarith
  · push_neg at hs1
    have h3 : 0 ≤ Real.exp s - 1 := by
      have := Real.add_one_le_exp s
      linarith
    have h1 : Real.exp s - 1 - s ≤ Real.exp s - 1 := by linarith
    have h2 : Real.exp s - 1 ≤ s * (Real.exp s - 1) := by nlinarith [hs1.le, h3]
    linarith


theorem one_lt_exp_two_mul {u : ℝ} (hu : 0 < u) : 1 < Real.exp (2 * u) :=
  Real.one_lt_exp_iff.mpr (by linarith)


theorem continuous_exp_two_mul : Continuous (fun u : ℝ => Real.exp (2 * u)) := by
  have h : Continuous fun u : ℝ => (2 : ℝ) * u := continuous_const.mul continuous_id
  exact Real.continuous_exp.comp h


theorem continuous_exp_neg_two_mul : Continuous (fun u : ℝ => Real.exp (-(2 * u))) := by
  have h : Continuous fun u : ℝ => -((2 : ℝ) * u) :=
    (continuous_const.mul continuous_id).neg
  exact Real.continuous_exp.comp h


theorem abs_two_div_exp_sub_one_sub_inv_le {u : ℝ} (hu : 0 < u) :
    |2 / (Real.exp (2 * u) - 1) - 1 / u| ≤ 2 := by
  have hpos : 0 < Real.exp (2 * u) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    linarith
  have hnum : 0 ≤ Real.exp (2 * u) - 1 - 2 * u := by
    have := Real.add_one_le_exp (2 * u)
    linarith
  have hkey := exp_sub_one_sub_id_le_mul (2 * u) (by linarith)
  have hrewrite : 2 / (Real.exp (2 * u) - 1) - 1 / u
      = -((Real.exp (2 * u) - 1 - 2 * u) / (u * (Real.exp (2 * u) - 1))) := by
    field_simp
    ring
  rw [hrewrite, abs_neg, abs_of_nonneg (div_nonneg hnum (mul_nonneg hu.le hpos.le))]
  rw [div_le_iff₀ (mul_pos hu hpos)]
  nlinarith [hkey]


theorem hasDerivAt_log_one_sub_exp {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
      (2 / (Real.exp (2 * u) - 1)) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(2 * u)))
      (2 * Real.exp (-(2 * u))) u := by
    have hlin : HasDerivAt (fun u : ℝ => -(2 * u)) (-(2 : ℝ)) u := by
      simpa using (hasDerivAt_id u).const_mul (-(2 : ℝ))
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(2 * u)))
        (Real.exp (-(2 * u)) * (-(2 : ℝ))) u := hlin.exp
    have hsub := (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub hexp
    convert hsub using 1
    ring
  have hne : 1 - Real.exp (-(2 * u)) ≠ 0 := by
    have : Real.exp (-(2 * u)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hpos : 0 < Real.exp (2 * u) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    linarith
  have h2 := h1.log hne
  convert h2 using 1
  have hmul : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [div_eq_div_iff (ne_of_gt hpos) hne]
  nlinarith [hmul]




theorem integral_two_div_exp_sub_one_Ioi {R : ℝ} (hR : 0 < R) :
    (∫ u in Set.Ioi R, 2 / (Real.exp (2 * u) - 1))
      = -Real.log (1 - Real.exp (-(2 * R))) := by
  have hderiv : ∀ u ∈ Set.Ioi R,
      HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
        (2 / (Real.exp (2 * u) - 1)) u := fun u hu =>
    hasDerivAt_log_one_sub_exp (lt_trans hR hu)
  have hint : IntegrableOn (fun u : ℝ => 2 / (Real.exp (2 * u) - 1)) (Set.Ioi R) := by
    have hden : 0 < 1 - Real.exp (-(2 * R)) := by
      have : Real.exp (-(2 * R)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    have hmaj : Integrable (fun u : ℝ => (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-u))
        (volume.restrict (Set.Ioi R)) := by
      refine ((integrableOn_exp_neg_mul_form (a := R) (b := (1 : ℝ)) (by norm_num)).const_mul
        (2 / (1 - Real.exp (-(2 * R))))).congr (Eventually.of_forall fun u => ?_)
      simp only [one_mul]
    refine hmaj.mono' ?_ ?_
    · have hcont : ContinuousOn (fun u : ℝ => 2 / (Real.exp (2 * u) - 1)) (Set.Ioi R) :=
        (continuousOn_const.div ((continuous_exp_two_mul.sub continuous_const).continuousOn)
          (fun u hu => sub_ne_zero.mpr (ne_of_gt (one_lt_exp_two_mul (by
            have huR : R < u := hu
            linarith)))))
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have huR : R < u := hu
      have hpos : 0 < Real.exp (2 * u) - 1 :=
        sub_pos.mpr (one_lt_exp_two_mul (by linarith))
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hpos)]
      have hkey : Real.exp (2 * u) * (1 - Real.exp (-(2 * R))) ≤ Real.exp (2 * u) - 1 := by
        have h1 : 1 ≤ Real.exp (2 * (u - R)) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp (2 * u) * Real.exp (-(2 * R)) = Real.exp (2 * (u - R)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        nlinarith [h1, h2, Real.exp_pos (2 * u)]
      calc 2 / (Real.exp (2 * u) - 1)
          ≤ 2 / (Real.exp (2 * u) * (1 - Real.exp (-(2 * R)))) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hkey
        _ = (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-(2 * u)) := by
            rw [div_eq_mul_inv, mul_inv, ← Real.exp_neg]
            ring
        _ ≤ (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-u) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hR, huR]))
              (by positivity)
  have hcont : ContinuousWithinAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
      (Set.Ici R) R := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.log
    · exact continuousAt_const.sub continuous_exp_neg_two_mul.continuousAt
    · have : Real.exp (-(2 * R)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
  have hlim : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => -(2 * u)) atTop atBot := by
      simpa only [id_eq, neg_mul] using
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(2 : ℝ)) < 0))
    have h2 : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    have h3 : Tendsto (fun u : ℝ => 1 - Real.exp (-(2 * u))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h2
    have h4 : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))))
        atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp (by simpa using h3)
    simpa using h4
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := R) hcont hderiv hint hlim
  rw [h]
  ring


theorem integral_two_div_exp_sub_one_sub_inv {R : ℝ} (hR : 0 < R) :
    (∫ u in (0 : ℝ)..R, (2 / (Real.exp (2 * u) - 1) - 1 / u))
      = Real.log (1 - Real.exp (-(2 * R))) - Real.log R - Real.log 2 := by
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) R,
      HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))) - Real.log u)
        (2 / (Real.exp (2 * u) - 1) - 1 / u) u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have h2 := hasDerivAt_log_one_sub_exp hu0
    have h3 : HasDerivAt (fun u : ℝ => Real.log u) (1 / u) u := by
      simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hu0)
    have h4 := h2.sub h3
    convert h4 using 1
  have hint : IntervalIntegrable
      (fun u : ℝ => 2 / (Real.exp (2 * u) - 1) - 1 / u) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    have hbase : Integrable (fun _ : ℝ => (2 : ℝ)) (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
      integrableOn_const (s := Set.Ioc (0 : ℝ) R) (C := (2 : ℝ)) (hs := by
        rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    refine hbase.mono' ?_ ?_
    · have hcont : ContinuousOn
          (fun u : ℝ => 2 / (Real.exp (2 * u) - 1) - 1 / u) (Set.Ioc (0 : ℝ) R) := by
        apply ContinuousOn.sub
        · exact continuousOn_const.div ((continuous_exp_two_mul.sub continuous_const).continuousOn)
            (fun u hu => sub_ne_zero.mpr (ne_of_gt (one_lt_exp_two_mul hu.1)))
        · exact continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt hu.1)
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs]
      exact abs_two_div_exp_sub_one_sub_inv_le hu.1
  have hratio : Tendsto (fun u : ℝ => (1 - Real.exp (-(2 * u))) / u) (𝓝[>] 0) (𝓝 2) := by
    have h0 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(2 * u))) 2 0 := by
      have hlin : HasDerivAt (fun u : ℝ => -(2 * u)) (-(2 : ℝ)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-(2 : ℝ))
      have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(2 * u)))
          (Real.exp (-(2 * 0)) * (-(2 : ℝ))) 0 := hlin.exp
      have hsub := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp
      have hfun : ((fun _ : ℝ => (1 : ℝ)) - fun u : ℝ => Real.exp (-(2 * u)))
          = fun u : ℝ => 1 - Real.exp (-(2 * u)) := by
        funext u
        rw [Pi.sub_apply]
      have hval : (0 : ℝ) - Real.exp (-(2 * 0)) * (-(2 : ℝ)) = 2 := by
        simp only [mul_zero, neg_zero, Real.exp_zero]
        ring
      rw [hfun, hval] at hsub
      exact hsub
    have hslope := hasDerivAt_iff_tendsto_slope.mp h0
    have h1 : Tendsto (fun u : ℝ => (1 - Real.exp (-(2 * u))) / u) (𝓝[≠] 0) (𝓝 2) := by
      refine hslope.congr' ?_
      filter_upwards with u
      simp only [slope, sub_zero, mul_zero, neg_zero, Real.exp_zero, sub_self,
        smul_eq_mul, div_eq_inv_mul, vsub_eq_sub]
    exact h1.mono_left (nhdsWithin_mono 0 (fun u hu => ne_of_gt hu))
  have ha : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))) - Real.log u)
      (𝓝[>] 0) (𝓝 (Real.log 2)) := by
    have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hratio
    have heq : ∀ᶠ u in 𝓝[>] 0,
        Real.log ((1 - Real.exp (-(2 * u))) / u)
          = Real.log (1 - Real.exp (-(2 * u))) - Real.log u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : (0 : ℝ) < u := hu
      rw [Real.log_div (ne_of_gt (sub_pos.mpr (by rw [Real.exp_lt_one_iff]; linarith)))
        (ne_of_gt hu')]
    exact hlog.congr' heq
  have hb : Tendsto (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))) - Real.log u)
      (𝓝[<] R) (𝓝 (Real.log (1 - Real.exp (-(2 * R))) - Real.log R)) := by
    have hcont : ContinuousAt
        (fun u : ℝ => Real.log (1 - Real.exp (-(2 * u))) - Real.log u) R := by
      apply ContinuousAt.sub
      · apply ContinuousAt.log
        · exact continuousAt_const.sub continuous_exp_neg_two_mul.continuousAt
        · have : Real.exp (-(2 * R)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
          linarith
      · exact Real.continuousAt_log (ne_of_gt hR)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
    (b := R) hR hderiv hint ha hb
  rw [h]


theorem digammaKernel_constant {R : ℝ} (hR : 0 < R) :
    Real.log R + (∫ u in (0 : ℝ)..R, (2 / (Real.exp (2 * u) - 1) - 1 / u))
      + (∫ u in Set.Ioi R, 2 / (Real.exp (2 * u) - 1)) = -Real.log 2 := by
  rw [integral_two_div_exp_sub_one_Ioi hR, integral_two_div_exp_sub_one_sub_inv hR]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exp_sub_one_sub_id_le_mul
#print axioms RHLean.ExplicitFormula.abs_two_div_exp_sub_one_sub_inv_le
#print axioms RHLean.ExplicitFormula.hasDerivAt_log_one_sub_exp
#print axioms RHLean.ExplicitFormula.integral_two_div_exp_sub_one_Ioi
#print axioms RHLean.ExplicitFormula.integral_two_div_exp_sub_one_sub_inv
#print axioms RHLean.ExplicitFormula.digammaKernel_constant

end

end Inline_ExplicitFormula_RH66

section Inline_ExplicitFormula_RH67


















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrable_autocorr_integrand {f : ℝ → ℂ} (hf : f ∈ oddCore) (u : ℝ) :
    Integrable (fun x : ℝ => f (x + u) * star (f x)) volume := by
  obtain ⟨R, hR0, hR⟩ := exists_support_radius hf.2.1
  have hcont : Continuous (fun x : ℝ => f (x + u) * star (f x)) :=
    (hf.1.continuous.comp (continuous_id.add continuous_const)).mul
      (continuous_star.comp hf.1.continuous)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (2 * R + 1))
    fun x hx => ?_
  have hx1 : f (x + u) ≠ 0 := fun h => hx (by simp [h])
  have hx2 : f x ≠ 0 := fun h => hx (by simp [h])
  have h1 : |x + u| ≤ R := by
    by_contra h
    exact hx1 (hR (x + u) (lt_of_not_ge h))
  have h2 : |x| ≤ R := by
    by_contra h
    exact hx2 (hR x (lt_of_not_ge h))
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  calc |x| ≤ R := h2
    _ ≤ 2 * R + 1 := by linarith


theorem autocorr_re_eq_integral {f : ℝ → ℂ} (hf : f ∈ oddCore) (u : ℝ) :
    (autocorr f u).re = ∫ x : ℝ, (f (x + u) * star (f x)).re := by
  rw [autocorr]
  exact (integral_re (integrable_autocorr_integrand hf u)).symm


theorem integral_kernel_mul_autocorr_eq {f : ℝ → ℂ} (hf : f ∈ oddCore) {K : ℝ → ℝ}
    (hK_meas : Measurable K) (hK_bound : ∃ M : ℝ, ∀ u : ℝ, |K u| ≤ M) :
    (∫ u : ℝ, K u * (autocorr f u).re)
      = ∫ p : ℝ × ℝ, K (p.2 - p.1) * (f p.2 * star (f p.1)).re
          ∂(volume.prod volume) := by
  obtain ⟨R, hR0, hR⟩ := exists_support_radius hf.2.1
  obtain ⟨B, hB⟩ := hf.2.1.isCompact.exists_bound_of_continuousOn
    hf.1.continuous.continuousOn
  obtain ⟨M, hM⟩ := hK_bound
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (K 0)) (hM 0)
  have hB' : ∀ x : ℝ, ‖f x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ tsupport f
    · exact le_trans (hB x hx) (le_max_left _ _)
    · have hzero : f x = 0 := by
        by_contra h
        exact hx (subset_tsupport f (Function.mem_support.mpr h))
      rw [hzero]
      simp
  have hs : MeasurableSet (Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hfin : volume (Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R) ≠ ⊤ :=
    ne_of_lt ((isCompact_Icc (a := -(2 * R)) (b := 2 * R)).prod
      (isCompact_Icc (a := -R) (b := R))).measure_lt_top
  have hmaj : Integrable
      ((Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R).indicator
        (fun _ => M * (max B 0) ^ 2)) (volume.prod volume) := by
    rw [integrable_indicator_iff hs]
    exact integrableOn_const (s := Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R)
      (C := M * (max B 0) ^ 2) hfin
  have hbd : ∀ (g : ℝ × ℝ → ℝ),
      AEStronglyMeasurable g (volume.prod volume) →
      (∀ p, p ∉ Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R → g p = 0) →
      (∀ p ∈ Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R,
        ‖g p‖ ≤ M * (max B 0) ^ 2) →
      Integrable g (volume.prod volume) := by
    intro g hg hsupp hbound
    refine Integrable.mono' hmaj hg ?_
    filter_upwards with p
    by_cases hp : p ∈ Set.Icc (-(2 * R)) (2 * R) ×ˢ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hp]
      exact hbound p hp
    · rw [Set.indicator_of_notMem hp, hsupp p hp, norm_zero]
  have hprod_int : Integrable (fun p : ℝ × ℝ =>
      K p.1 * (f (p.2 + p.1) * star (f p.2)).re) (volume.prod volume) := by
    refine hbd _ ?_ ?_ ?_
    · have hcont : Continuous (fun p : ℝ × ℝ =>
          (f (p.2 + p.1) * star (f p.2)).re) :=
        Complex.continuous_re.comp
          (((hf.1.continuous.comp (continuous_snd.add continuous_fst)).mul
            (continuous_star.comp (hf.1.continuous.comp continuous_snd))))
      exact ((hK_meas.comp measurable_fst).mul hcont.measurable).aestronglyMeasurable
    · intro p hp
      have hp' : ¬(p.1 ∈ Set.Icc (-(2 * R)) (2 * R) ∧ p.2 ∈ Set.Icc (-R) R) :=
        fun h => hp ⟨h.1, h.2⟩
      have hz : f (p.2 + p.1) = 0 ∨ f p.2 = 0 := by
        by_cases hp2' : |p.2| ≤ R
        · left
          have hp2mem : p.2 ∈ Set.Icc (-R) R := by
            rw [abs_le] at hp2'
            exact ⟨hp2'.1, hp2'.2⟩
          have hp1 : ¬(p.1 ∈ Set.Icc (-(2 * R)) (2 * R)) := fun h1 => hp' ⟨h1, hp2mem⟩
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp1
          have hgt : R < |p.2 + p.1| := by
            rw [abs_le] at hp2'
            rcases hp1 with h | h
            · have hneg : p.2 + p.1 < 0 := by linarith [hp2'.2, h]
              rw [abs_of_neg hneg]
              linarith [hp2'.2, h]
            · have hpos : 0 < p.2 + p.1 := by linarith [hp2'.1, h]
              rw [abs_of_pos hpos]
              linarith [hp2'.1, h]
          by_contra h
          exact absurd (hR (p.2 + p.1) hgt) (by simp [h])
        · right
          have hgt : R < |p.2| := lt_of_not_ge hp2'
          by_contra h
          exact absurd (hR p.2 hgt) (by simp [h])
      rcases hz with hz | hz
      · rw [hz]; simp
      · rw [hz]; simp
    · intro p hp
      have h1 : |K p.1| ≤ M := hM p.1
      have h2 : |(f (p.2 + p.1) * star (f p.2)).re| ≤ (max B 0) ^ 2 := by
        calc |(f (p.2 + p.1) * star (f p.2)).re|
            ≤ ‖f (p.2 + p.1) * star (f p.2)‖ := Complex.abs_re_le_norm _
          _ = ‖f (p.2 + p.1)‖ * ‖f p.2‖ := by rw [norm_mul, norm_star]
          _ ≤ max B 0 * max B 0 :=
              mul_le_mul (hB' _) (hB' _) (norm_nonneg _) (le_max_right _ _)
          _ = (max B 0) ^ 2 := by ring
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hprod_int2 : Integrable (fun p : ℝ × ℝ =>
      K (p.2 - p.1) * (f p.2 * star (f p.1)).re) (volume.prod volume) := by
    refine hbd _ ?_ ?_ ?_
    · have hcont : Continuous (fun p : ℝ × ℝ => (f p.2 * star (f p.1)).re) :=
        Complex.continuous_re.comp
          (((hf.1.continuous.comp continuous_snd).mul
            (continuous_star.comp (hf.1.continuous.comp continuous_fst))))
      exact (((hK_meas.comp (continuous_snd.sub continuous_fst).measurable)).mul
        hcont.measurable).aestronglyMeasurable
    · intro p hp
      have hp' : ¬(p.1 ∈ Set.Icc (-(2 * R)) (2 * R) ∧ p.2 ∈ Set.Icc (-R) R) :=
        fun h => hp ⟨h.1, h.2⟩
      rcases not_and_or.mp hp' with hp1 | hp2
      · have hgt : R < |p.1| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp1
          rcases hp1 with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hz : f p.1 = 0 := by
          by_contra h
          exact absurd (hR p.1 hgt) (by simp [h])
        rw [hz]
        simp
      · have hgt : R < |p.2| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hp2
          rcases hp2 with h | h
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        have hz : f p.2 = 0 := by
          by_contra h
          exact absurd (hR p.2 hgt) (by simp [h])
        rw [hz]
        simp
    · intro p hp
      have h1 : |K (p.2 - p.1)| ≤ M := hM _
      have h2 : |(f p.2 * star (f p.1)).re| ≤ (max B 0) ^ 2 := by
        calc |(f p.2 * star (f p.1)).re|
            ≤ ‖f p.2 * star (f p.1)‖ := Complex.abs_re_le_norm _
          _ = ‖f p.2‖ * ‖f p.1‖ := by rw [norm_mul, norm_star]
          _ ≤ max B 0 * max B 0 :=
              mul_le_mul (hB' _) (hB' _) (norm_nonneg _) (le_max_right _ _)
          _ = (max B 0) ^ 2 := by ring
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hstep : (∫ u : ℝ, K u * (autocorr f u).re)
      = ∫ u : ℝ, ∫ x : ℝ, K u * (f (x + u) * star (f x)).re := by
    apply integral_congr_ae
    filter_upwards with u
    rw [autocorr_re_eq_integral hf u, integral_const_mul]
  rw [hstep]
  calc (∫ u : ℝ, ∫ x : ℝ, K u * (f (x + u) * star (f x)).re)
      = ∫ x : ℝ, ∫ u : ℝ, K u * (f (x + u) * star (f x)).re :=
        integral_integral_swap hprod_int
    _ = ∫ x : ℝ, ∫ y : ℝ, K (y - x) * (f y * star (f x)).re := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← integral_add_right_eq_self (μ := volume)
          (fun z : ℝ => K (z - x) * (f z * star (f x)).re) x]
        apply integral_congr_ae
        filter_upwards with y
        have hk : y + x - x = y := by ring
        rw [hk, add_comm x y]
    _ = ∫ p : ℝ × ℝ, K (p.2 - p.1) * (f p.2 * star (f p.1)).re
          ∂(volume.prod volume) :=
        integral_integral (μ := volume) (ν := volume)
          (f := fun x y => K (y - x) * (f y * star (f x)).re) hprod_int2


theorem integral_kernel_mul_autocorr_eq' {f : ℝ → ℂ} (hf : f ∈ oddCore) {K : ℝ → ℝ}
    (hK_meas : Measurable K) (hK_bound : ∃ M : ℝ, ∀ u : ℝ, |K u| ≤ M) :
    (∫ u : ℝ, K u * (autocorr f u).re)
      = ∫ p : ℝ × ℝ, K (p.2 - p.1) * (f p.1 * star (f p.2)).re
          ∂(volume.prod volume) := by
  rw [integral_kernel_mul_autocorr_eq hf hK_meas hK_bound]
  apply integral_congr_ae
  filter_upwards with p
  congr 1
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrable_autocorr_integrand
#print axioms RHLean.ExplicitFormula.autocorr_re_eq_integral
#print axioms RHLean.ExplicitFormula.integral_kernel_mul_autocorr_eq
#print axioms RHLean.ExplicitFormula.integral_kernel_mul_autocorr_eq'

end

end Inline_ExplicitFormula_RH67

section Inline_ExplicitFormula_RH68
















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    intro t
    simpa using (hasDerivAt_neg t).exp
  rcases le_total a b with hab | hab
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := a) (b := b)
      (f := fun t : ℝ => Real.exp (-t)) (f' := fun t : ℝ => -Real.exp (-t)) (C := 1)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by linarith [ht.1]))
    have h2 := h b ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs] at h2
    have habs : |a - b| = b - a := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hab)
    rw [habs, abs_sub_comm]
    simpa using h2
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := b) (b := a)
      (f := fun t : ℝ => Real.exp (-t)) (f' := fun t : ℝ => -Real.exp (-t)) (C := 1)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by linarith [ht.1]))
    have h2 := h a ⟨hab, le_rfl⟩
    rw [Real.norm_eq_abs] at h2
    rw [abs_of_nonneg (by linarith : 0 ≤ a - b)]
    simpa using h2


theorem gammaKernel_abs_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, 0 ≤ z → |gammaKernel z| ≤ M := by
  have hden2 : 0 < 1 - Real.exp (-(2 : ℝ)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  refine ⟨max (1 / 4) (max 5 (1 / (1 - Real.exp (-(2 : ℝ))) + 1 / 2)),
    by positivity, fun z hz => ?_⟩
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · rw [gammaKernel_zero]
    exact le_trans (by norm_num : |(1 : ℝ) / 4| ≤ 1 / 4) (le_max_left _ _)
  · have hsinh : Real.sinh z = (Real.exp z - Real.exp (-z)) / 2 := Real.sinh_eq z
    have hrew1 : Real.exp (z / 2) / (2 * Real.sinh z)
        = Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z))) := by
      rw [hsinh]
      have he : Real.exp (z / 2) = Real.exp (-(z / 2)) * Real.exp z := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hden_eq : Real.exp z - Real.exp (-z)
          = Real.exp z * (1 - Real.exp (-(2 * z))) := by
        rw [mul_sub, mul_one]
        have hz2 : Real.exp z * Real.exp (-(2 * z)) = Real.exp (-z) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hz2]
      rw [he, hden_eq,
        show (2 : ℝ) * ((Real.exp z * (1 - Real.exp (-(2 * z)))) / 2)
          = Real.exp z * (1 - Real.exp (-(2 * z))) by ring]
      field_simp
    by_cases hzle : z ≤ 1
    ·
      have hdenz : 0 < 1 - Real.exp (-(2 * z)) := by
        rw [sub_pos, Real.exp_lt_one_iff]
        linarith
      have hnum : |2 * z * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * z)))| ≤ 4 * z ^ 2 := by
        have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) z,
            HasDerivWithinAt
              (fun t : ℝ => 2 * t * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * t))))
              (2 * Real.exp (-(z / 2)) - 2 * Real.exp (-(2 * t))) (Set.Icc 0 z) t := by
          intro t _
          have h1 : HasDerivAt (fun t : ℝ => 2 * t * Real.exp (-(z / 2)))
              (2 * Real.exp (-(z / 2))) t := by
            have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
              simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              hlin.mul_const (Real.exp (-(z / 2)))
          have h2 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(2 * t)))
              (2 * Real.exp (-(2 * t))) t := by
            have hlin : HasDerivAt (fun t : ℝ => -(2 * t)) (-(2 : ℝ)) t := by
              simpa using (hasDerivAt_id t).const_mul (-(2 : ℝ))
            have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(2 * t)))
                (Real.exp (-(2 * t)) * (-(2 : ℝ))) t := hlin.exp
            have hsub := (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hexp
            have hval : (0 : ℝ) - Real.exp (-(2 * t)) * (-(2 : ℝ))
                = 2 * Real.exp (-(2 * t)) := by ring
            rw [hval] at hsub
            exact hsub
          have h3 := h1.sub h2
          have hfun : ((fun t : ℝ => 2 * t * Real.exp (-(z / 2)))
                - fun t : ℝ => 1 - Real.exp (-(2 * t)))
              = fun t : ℝ => 2 * t * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * t))) := by
            funext t
            rw [Pi.sub_apply]
          rw [hfun] at h3
          exact h3.hasDerivWithinAt
        have hbdd : ∀ t ∈ Set.Ico (0 : ℝ) z,
            ‖2 * Real.exp (-(z / 2)) - 2 * Real.exp (-(2 * t))‖ ≤ 4 * z := by
          intro t ht
          rw [Real.norm_eq_abs]
          have h := abs_exp_neg_sub_le (a := z / 2) (b := 2 * t)
            (by linarith [hzpos]) (by linarith [ht.1])
          have hle1 : z / 2 - 2 * t ≤ 2 * z := by nlinarith [ht.1, hzpos]
          have hle2 : -(2 * z) ≤ z / 2 - 2 * t := by nlinarith [ht.2.le, hzpos]
          have h2 : |z / 2 - 2 * t| ≤ 2 * z := abs_le.mpr ⟨hle2, hle1⟩
          calc |2 * Real.exp (-(z / 2)) - 2 * Real.exp (-(2 * t))|
              = 2 * |Real.exp (-(z / 2)) - Real.exp (-(2 * t))| := by
                rw [show (2 : ℝ) * Real.exp (-(z / 2)) - 2 * Real.exp (-(2 * t))
                    = 2 * (Real.exp (-(z / 2)) - Real.exp (-(2 * t))) by ring, abs_mul]
                norm_num
            _ ≤ 2 * (2 * z) := by linarith
            _ = 4 * z := by ring
        have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := z)
          (f := fun t : ℝ => 2 * t * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * t))))
          (f' := fun t : ℝ => 2 * Real.exp (-(z / 2)) - 2 * Real.exp (-(2 * t)))
          (C := 4 * z) hderiv hbdd
        have h2 := hMVT z ⟨hzpos.le, le_rfl⟩
        have hg0 : 2 * (0 : ℝ) * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * 0))) = 0 := by
          simp [Real.exp_zero]
        rw [hg0, sub_zero, Real.norm_eq_abs] at h2
        calc |2 * z * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * z)))|
            ≤ 4 * z * (z - 0) := h2
          _ = 4 * z ^ 2 := by ring
      have hden : z ^ 2 ≤ 2 * z * (1 - Real.exp (-(2 * z))) := by
        have h1 : Real.exp (-(2 * z)) ≤ (1 + 2 * z)⁻¹ := by
          have h : 1 + 2 * z ≤ Real.exp (2 * z) := by
            have := Real.add_one_le_exp (2 * z)
            linarith
          rw [Real.exp_neg]
          exact (inv_le_inv₀ (Real.exp_pos _) (by linarith)).mpr h
        have h2 : (1 + 2 * z)⁻¹ ≤ 1 - z / 2 := by
          rw [inv_le_iff_one_le_mul₀ (by linarith : (0 : ℝ) < 1 + 2 * z)]
          nlinarith [hzpos, hzle]
        have h3 : z / 2 ≤ 1 - Real.exp (-(2 * z)) := by linarith
        nlinarith [hzpos, h3]
      have hrewrite : gammaKernel z
          = (2 * z * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * z))))
              / (2 * z * (1 - Real.exp (-(2 * z)))) := by
        rw [gammaKernel, if_neg hzpos.ne', hrew1]
        have h2z : (2 * z) ≠ 0 := by positivity
        have he2 : (1 - Real.exp (-(2 * z))) ≠ 0 := ne_of_gt hdenz
        rw [div_sub_div _ _ he2 h2z]
        ring
      have hD : 0 < 2 * z * (1 - Real.exp (-(2 * z))) := by positivity
      rw [hrewrite, abs_div, abs_of_pos hD]
      have hfrac : |2 * z * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * z)))|
            / (2 * z * (1 - Real.exp (-(2 * z)))) ≤ 4 := by
        rw [div_le_iff₀ hD]
        nlinarith [hnum, hden, hzpos]
      calc |2 * z * Real.exp (-(z / 2)) - (1 - Real.exp (-(2 * z)))|
            / (2 * z * (1 - Real.exp (-(2 * z))))
          ≤ 4 := hfrac
        _ ≤ max (1 / 4) (max 5 (1 / (1 - Real.exp (-(2 : ℝ))) + 1 / 2)) := by
            refine le_trans (by norm_num : (4 : ℝ) ≤ 5) ?_
            exact le_trans (le_max_left _ _) (le_max_right _ _)
    ·
      push_neg at hzle
      have hdenz : 0 < 1 - Real.exp (-(2 * z)) := by
        rw [sub_pos, Real.exp_lt_one_iff]
        linarith
      have hrewrite : gammaKernel z
          = Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z))) - 1 / (2 * z) := by
        rw [gammaKernel, if_neg hzpos.ne', hrew1]
      rw [hrewrite]
      have htri : |Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z))) - 1 / (2 * z)|
          ≤ |Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z)))| + |1 / (2 * z)| := by
        have := abs_sub_le (Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z)))) 0 (1 / (2 * z))
        simpa using this
      have hfirst : |Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z)))|
          ≤ 1 / (1 - Real.exp (-(2 : ℝ))) := by
        rw [abs_of_pos (div_pos (Real.exp_pos _) hdenz)]
        have hnum_le : Real.exp (-(z / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hden_ge : 1 - Real.exp (-(2 : ℝ)) ≤ 1 - Real.exp (-(2 * z)) := by
          rw [sub_le_sub_iff_left]
          exact Real.exp_le_exp.mpr (by linarith)
        calc Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z)))
            ≤ 1 / (1 - Real.exp (-(2 * z))) :=
              div_le_div_of_nonneg_right hnum_le hdenz.le
          _ ≤ 1 / (1 - Real.exp (-(2 : ℝ))) :=
              div_le_div_of_nonneg_left (by norm_num) hden2 hden_ge
      have hsecond : |1 / (2 * z)| ≤ 1 / 2 := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * z)),
          div_le_iff₀ (by positivity : (0 : ℝ) < 2 * z)]
        linarith
      calc |Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z))) - 1 / (2 * z)|
          ≤ |Real.exp (-(z / 2)) / (1 - Real.exp (-(2 * z)))| + |1 / (2 * z)| := htri
        _ ≤ 1 / (1 - Real.exp (-(2 : ℝ))) + 1 / 2 := add_le_add hfirst hsecond
        _ ≤ max (1 / 4) (max 5 (1 / (1 - Real.exp (-(2 : ℝ))) + 1 / 2)) :=
            le_trans (le_max_right _ _) (le_max_right _ _)


theorem measurable_gammaKernel : Measurable gammaKernel := by
  rw [show gammaKernel = fun z : ℝ =>
      if z = 0 then 1 / 4
      else Real.exp (z / 2) / (2 * Real.sinh z) - 1 / (2 * z) from rfl]
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have h1 : Measurable (fun z : ℝ => Real.exp (z / 2) / (2 * Real.sinh z)) := by
    refine Measurable.div ?_ ?_
    · fun_prop
    · fun_prop
  have h2 : Measurable (fun z : ℝ => 1 / (2 * z)) := by
    refine Measurable.div measurable_const ?_
    fun_prop
  exact h1.sub h2




theorem integral_truncKernel_mul_autocorr_eq {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, (if ε < |u| then (|u|)⁻¹ else 0) * (autocorr f u).re)
      = ∫ p : ℝ × ℝ,
          (if ε < |p.2 - p.1| then (|p.2 - p.1|)⁻¹ else 0)
            * (f p.2 * star (f p.1)).re ∂(volume.prod volume) := by
  refine integral_kernel_mul_autocorr_eq hf ?_ ⟨1 / ε, fun u => ?_⟩
  · have hmeas : Measurable (fun u : ℝ => (|u|)⁻¹) := continuous_abs.measurable.inv
    exact Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
      hmeas measurable_const
  · by_cases h : ε < |u|
    · rw [if_pos h, one_div]
      have hu : 0 < |u| := lt_trans hε h
      rw [abs_of_pos (inv_pos.mpr hu)]
      exact (inv_le_inv₀ hu hε).mpr h.le
    · rw [if_neg h, abs_zero]
      positivity


theorem integral_gammaKernel_mul_autocorr_eq {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    (∫ u : ℝ, gammaKernel |u| * (autocorr f u).re)
      = ∫ p : ℝ × ℝ, gammaKernel |p.2 - p.1| * (f p.2 * star (f p.1)).re
          ∂(volume.prod volume) := by
  obtain ⟨M, hM0, hM⟩ := gammaKernel_abs_le
  refine integral_kernel_mul_autocorr_eq hf ?_ ⟨M, fun u => hM |u| (abs_nonneg u)⟩
  exact measurable_gammaKernel.comp continuous_abs.measurable

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.abs_exp_neg_sub_le
#print axioms RHLean.ExplicitFormula.gammaKernel_abs_le
#print axioms RHLean.ExplicitFormula.measurable_gammaKernel
#print axioms RHLean.ExplicitFormula.integral_truncKernel_mul_autocorr_eq
#print axioms RHLean.ExplicitFormula.integral_gammaKernel_mul_autocorr_eq

end

end Inline_ExplicitFormula_RH68

section Inline_ExplicitFormula_RH69

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integral_eq_setIntegral_of_forall_eq_zero_of_notMem {f : ℝ → ℝ} {s : Set ℝ}
    (hs : MeasurableSet s) (h : ∀ x ∉ s, f x = 0) :
    (∫ x : ℝ, f x) = ∫ x in s, f x := by
  have hfun : f = s.indicator f := by
    funext x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h x hx]
  calc (∫ x : ℝ, f x) = ∫ x : ℝ, s.indicator f x := by
        conv_lhs => rw [hfun]
    _ = ∫ x in s, f x := integral_indicator hs


noncomputable def truncKernel (ε u : ℝ) : ℝ := if ε < |u| then (|u|)⁻¹ else 0

theorem measurable_truncKernel (ε : ℝ) : Measurable (truncKernel ε) := by
  unfold truncKernel
  exact Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
    continuous_abs.measurable.inv measurable_const

theorem abs_truncKernel_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    |truncKernel ε u| ≤ 1 / ε := by
  unfold truncKernel
  by_cases h : ε < |u|
  · rw [if_pos h, abs_of_pos (inv_pos.mpr (lt_trans hε h)), one_div]
    exact (inv_le_inv₀ (lt_trans hε h) hε).mpr h.le
  · rw [if_neg h, abs_zero]
    positivity


theorem intervalIntegrable_truncKernel {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (truncKernel ε) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (s_finite := ?_) (f_mble := ?_) (M := 1 / ε) ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · exact (measurable_truncKernel ε).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs]
    exact abs_truncKernel_le hε u


theorem integral_truncKernel_Icc {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    (∫ u in Set.Icc (-R) R, truncKernel ε u) = 2 * Real.log (R / ε) := by
  have hneR : ∀ᵐ x : ℝ ∂volume, x ≠ -R := by
    have hset : {a : ℝ | ¬a ≠ -R} = {-R} := by
      ext a
      simp
    exact (ae_iff (μ := volume) (p := fun x : ℝ => x ≠ -R)).mpr
      (by rw [hset]; exact measure_singleton (-R))
  have hae : Set.Icc (-R) R =ᵐ[volume] Set.Ioc (-R) R := by
    filter_upwards [hneR] with x hx
    rw [Set.mem_Icc, Set.mem_Ioc]
    exact propext ⟨fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm hx), h.2⟩, fun h => ⟨h.1.le, h.2⟩⟩
  have hneε : ∀ᵐ u : ℝ ∂volume, u ≠ ε := by
    have hset : {a : ℝ | ¬a ≠ ε} = {ε} := by
      ext a
      simp
    exact (ae_iff (μ := volume) (p := fun x : ℝ => x ≠ ε)).mpr
      (by rw [hset]; exact measure_singleton ε)
  rw [setIntegral_congr_set hae,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_truncKernel hε (by linarith : -R ≤ -ε))
      (intervalIntegrable_truncKernel hε (by linarith : -ε ≤ R))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_truncKernel hε (by linarith : -ε ≤ ε))
      (intervalIntegrable_truncKernel hε (by linarith : ε ≤ R))]
  have hright : (∫ u in ε..R, truncKernel ε u) = ∫ u in ε..R, u⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hneε] with u hne hu
    rw [Set.uIoc_of_le hεR.le] at hu
    have hu' : ε < u := hu.1
    unfold truncKernel
    rw [if_pos (by rw [abs_of_pos (lt_trans hε hu')]; exact hu'),
      abs_of_pos (lt_trans hε hu')]
  have hleft : (∫ u in (-R)..(-ε), truncKernel ε u) = ∫ u in ε..R, u⁻¹ := by
    have h1 : (∫ u in (-R)..(-ε), truncKernel ε u)
        = ∫ u in (-R)..(-ε), truncKernel ε (-u) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hneε] with u hne hu
      unfold truncKernel
      rw [abs_neg]
    rw [h1, intervalIntegral.integral_comp_neg, neg_neg, neg_neg, hright]
  have hmid : (∫ u in (-ε)..ε, truncKernel ε u) = 0 := by
    rw [show (∫ u in (-ε)..ε, truncKernel ε u) = ∫ u in (-ε)..ε, (0 : ℝ) from
      intervalIntegral.integral_congr fun u hu => ?_]
    · rw [intervalIntegral.integral_zero]
    · unfold truncKernel
      rw [if_neg]
      rw [not_lt, abs_le]
      rw [Set.mem_uIcc] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hleft, hmid, hright, integral_inv (by
    rw [Set.mem_uIcc]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith)]
  ring


theorem trunc_kernel_algebra {f : ℝ → ℂ} (hf : f ∈ oddCore) {R ε : ℝ}
    (hR : ∀ y : ℝ, R < |y| → (autocorr f y).re = 0) (hε : 0 < ε) (hεR : ε < R) :
    -Real.log ε * (autocorr f 0).re
        - (1 / 2) * (∫ u : ℝ, truncKernel ε u * (autocorr f u).re)
      = -Real.log R * (autocorr f 0).re
        - (1 / 2) * (∫ u in Set.Icc (-R) R,
            truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re)) := by
  obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf
  have hfin : volume (Set.Icc (-R) R) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hcont : Continuous (fun u : ℝ => (autocorr f u).re) :=
    Complex.continuous_re.comp (contDiff_autocorr hf).continuous
  have hInt1 : IntegrableOn
      (fun u : ℝ => truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
      (Set.Icc (-R) R) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := hfin)
      (f_mble := ?_) (M := (1 / ε) * (B + |(autocorr f 0).re|)) ?_
    · exact ((measurable_truncKernel ε).mul
        (hcont.measurable.sub measurable_const)).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_truncKernel_le hε u
      have h2 : |(autocorr f u).re - (autocorr f 0).re| ≤ B + |(autocorr f 0).re| := by
        have h := abs_sub_le ((autocorr f u).re) 0 ((autocorr f 0).re)
        rw [sub_zero, zero_sub, abs_neg] at h
        exact le_trans h (add_le_add (hB u) le_rfl)
      exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hInt2 : IntegrableOn
      (fun u : ℝ => truncKernel ε u * (autocorr f 0).re) (Set.Icc (-R) R) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := hfin)
      (f_mble := ?_) (M := (1 / ε) * |(autocorr f 0).re|) ?_
    · exact ((measurable_truncKernel ε).mul measurable_const).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_truncKernel_le hε u) le_rfl (abs_nonneg _) (by positivity)
  have hsupp : ∀ u ∉ Set.Icc (-R) R,
      truncKernel ε u * (autocorr f u).re = 0 := by
    intro u hu
    have hgt : R < |u| := by
      rw [Set.mem_Icc] at hu
      rcases not_and_or.mp hu with h | h
      · rw [not_le] at h
        rw [abs_of_neg (by linarith)]
        linarith
      · rw [not_le] at h
        rw [abs_of_pos (by linarith)]
        linarith
    rw [hR u hgt, mul_zero]
  have hA : (∫ u : ℝ, truncKernel ε u * (autocorr f u).re)
      = ∫ u in Set.Icc (-R) R, truncKernel ε u * (autocorr f u).re :=
    integral_eq_setIntegral_of_forall_eq_zero_of_notMem measurableSet_Icc hsupp
  have hB' : (∫ u in Set.Icc (-R) R, truncKernel ε u * (autocorr f u).re)
      = (∫ u in Set.Icc (-R) R,
            truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
        + (autocorr f 0).re * (∫ u in Set.Icc (-R) R, truncKernel ε u) := by
    rw [show (∫ u in Set.Icc (-R) R, truncKernel ε u * (autocorr f u).re)
        = ∫ u in Set.Icc (-R) R,
            (truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re)
              + truncKernel ε u * (autocorr f 0).re) from
          setIntegral_congr_fun measurableSet_Icc (fun u _ => by ring)]
    rw [integral_add hInt1 hInt2, integral_mul_const]
    ring
  have hC : (∫ u in Set.Icc (-R) R, truncKernel ε u) = 2 * Real.log (R / ε) :=
    integral_truncKernel_Icc hε hεR
  rw [hA, hB', hC]
  rw [Real.log_div (ne_of_gt (lt_trans hε hεR)) (ne_of_gt hε)]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_eq_setIntegral_of_forall_eq_zero_of_notMem
#print axioms RHLean.ExplicitFormula.abs_truncKernel_le
#print axioms RHLean.ExplicitFormula.intervalIntegrable_truncKernel
#print axioms RHLean.ExplicitFormula.integral_truncKernel_Icc
#print axioms RHLean.ExplicitFormula.trunc_kernel_algebra

end

end Inline_ExplicitFormula_RH69

section Inline_ExplicitFormula_RH70













noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem exists_lipschitzOn_localizedCore {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (-a) a, ∀ y ∈ Set.Icc (-a) a,
      ‖f x - f y‖ ≤ C * |x - y| := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -a) (b := a)).exists_bound_of_continuousOn
    (hf.1.1.continuous_deriv (by norm_num)).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have hderiv : ∀ t : ℝ, HasDerivAt f (deriv f t) t :=
    fun t => (hf.1.1.differentiable (by simp) t).hasDerivAt
  have hbound : ∀ t ∈ Set.Icc (-a) a, ‖deriv f t‖ ≤ max K 0 :=
    fun t ht => le_trans (hK t ht) (le_max_left _ _)
  rcases le_total x y with hxy | hyx
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := x) (b := y)
      (f := f) (f' := deriv f) (C := max K 0)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => hbound t ⟨le_trans hx.1 ht.1, le_trans ht.2.le hy.2⟩)
    have h2 := h y ⟨hxy, le_rfl⟩
    rw [norm_sub_rev] at h2
    have h3 : |x - y| = y - x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    rw [h3]
    exact h2
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := y) (b := x)
      (f := f) (f' := deriv f) (C := max K 0)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => hbound t ⟨le_trans hy.1 ht.1, le_trans ht.2.le hx.2⟩)
    have h2 := h x ⟨hyx, le_rfl⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h2


theorem normSq_div_le_lipschitz {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (-a) a, ∀ y ∈ Set.Icc (-a) a,
      ‖f x - f y‖ ^ 2 / |x - y| ≤ C ^ 2 * |x - y| := by
  obtain ⟨C, hC0, hC⟩ := exists_lipschitzOn_localizedCore hf
  refine ⟨C, hC0, fun x hx y hy => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hz : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have h1 := hC x hx y hy
    have h2 : ‖f x - f y‖ ^ 2 ≤ (C * |x - y|) ^ 2 := by
      exact sq_le_sq' (by nlinarith [norm_nonneg (f x - f y), hC0, abs_nonneg (x - y)])
        h1
    rw [div_le_iff₀ hz]
    calc ‖f x - f y‖ ^ 2 ≤ (C * |x - y|) ^ 2 := h2
      _ = C ^ 2 * |x - y| ^ 2 := by ring
      _ = C ^ 2 * |x - y| * |x - y| := by ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_lipschitzOn_localizedCore
#print axioms RHLean.ExplicitFormula.normSq_div_le_lipschitz

end

end Inline_ExplicitFormula_RH70

section Inline_ExplicitFormula_RH71

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem nearDiagonal_integral_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      (1 / 4) * (∫ p in (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a),
          (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
        ≤ C * ε := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := normSq_div_le_lipschitz hf
  refine ⟨C₁ ^ 2 * a ^ 2, by positivity, fun ε hεmem => ?_⟩
  have hε : 0 < ε := hεmem.1
  have hD : MeasurableSet (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hfin : volume (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) ≠ ⊤ := by
    have hc : IsCompact (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) :=
      (isCompact_Icc (a := -a) (b := a)).prod (isCompact_Icc (a := -a) (b := a))
    exact ne_of_lt (lt_of_le_of_lt
      (measure_mono fun p hp => Set.mem_prod.mpr
        ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
      hc.measure_lt_top)
  have hbdd : ∀ᵐ p ∂(volume.restrict (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a)),
      ‖(if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0)‖
        ≤ C₁ ^ 2 * ε := by
    filter_upwards [self_mem_ae_restrict hD] with p hp
    by_cases h : |p.1 - p.2| < ε
    · rw [if_pos h, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))]
      have h1 := hC₁ p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 ⟨hp.2.1.le, hp.2.2.le⟩
      calc ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| ≤ C₁ ^ 2 * |p.1 - p.2| := h1
        _ ≤ C₁ ^ 2 * ε := mul_le_mul_of_nonneg_left h.le (by positivity)
    · rw [if_neg h, norm_zero]
      positivity
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      (volume.restrict (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a)) := by
    have hm1 : Measurable (fun p : ℝ × ℝ =>
        ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2|) := by
      refine Measurable.div ?_ ?_
      · exact (((hf.1.1.continuous.comp continuous_fst).sub
          (hf.1.1.continuous.comp continuous_snd)).norm.pow 2).measurable
      · exact ((continuous_fst.sub continuous_snd).abs).measurable
    exact (Measurable.ite
      (((continuous_fst.sub continuous_snd).abs.measurable) measurableSet_Iio)
      hm1 measurable_const).aestronglyMeasurable
  have hInt1 : IntegrableOn
      (fun p : ℝ × ℝ =>
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) volume :=
    (integrableOn_const (s := Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) (C := C₁ ^ 2 * ε)
      hfin).mono' hmeas hbdd
  have hInt2 : IntegrableOn (fun _ : ℝ × ℝ => C₁ ^ 2 * ε)
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) volume :=
    integrableOn_const (s := Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) (C := C₁ ^ 2 * ε) hfin
  have hpoint : ∀ p ∈ Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
      (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0)
        ≤ C₁ ^ 2 * ε := by
    intro p hp
    by_cases h : |p.1 - p.2| < ε
    · rw [if_pos h]
      have h1 := hC₁ p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 ⟨hp.2.1.le, hp.2.2.le⟩
      calc ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| ≤ C₁ ^ 2 * |p.1 - p.2| := h1
        _ ≤ C₁ ^ 2 * ε := mul_le_mul_of_nonneg_left h.le (by positivity)
    · rw [if_neg h]
      positivity
  have hmono := setIntegral_mono_on (μ := volume)
    (f := fun p : ℝ × ℝ =>
      (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
    (g := fun _ : ℝ × ℝ => C₁ ^ 2 * ε) hInt1 hInt2 hD hpoint
  have hvol : volume.real (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) = (2 * a) ^ 2 := by
    show (volume (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a)).toReal = (2 * a) ^ 2
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
    rw [Measure.prod_prod, Real.volume_Ioo]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ a - -a)]
    ring
  calc (1 / 4) * (∫ p in (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a),
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      ≤ (1 / 4) * (∫ p in (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a), C₁ ^ 2 * ε) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = (1 / 4) * ((C₁ ^ 2 * ε) * volume.real (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a)) := by
        rw [setIntegral_const, smul_eq_mul]
        ring
    _ = C₁ ^ 2 * a ^ 2 * ε := by
        rw [hvol]
        ring


theorem tendsto_nearDiagonal {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    Tendsto (fun ε : ℝ => (1 / 4) * (∫ p in (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a),
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := nearDiagonal_integral_le ha hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℝ => 0) (h := fun ε : ℝ => C * ε) tendsto_const_nhds ?_ ?_ ?_
  · have h1 : Tendsto (fun _ : ℝ => C) (𝓝[>] 0) (𝓝 C) := tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    have h := h1.mul h2
    simpa only [Pi.mul_apply, mul_zero] using h
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have h1 : 0 ≤ (∫ p in (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a),
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0)) := by
      apply setIntegral_nonneg (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      by_cases h : |p.1 - p.2| < ε
      · rw [if_pos h]
        positivity
      · rw [if_neg h]
    exact mul_nonneg (by norm_num) h1
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
      with ε hε hε1
    exact hC ε ⟨hε, hε1.2.le⟩

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.nearDiagonal_integral_le
#print axioms RHLean.ExplicitFormula.tendsto_nearDiagonal

end

end Inline_ExplicitFormula_RH71

section Inline_ExplicitFormula_RH72















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integral_log_div {ε : ℝ} (hε : 0 < ε) :
    (∫ u in (0 : ℝ)..ε, Real.log (ε / u)) = ε := by
  have h2 : (∫ s in (0 : ℝ)..1, Real.log (1 / s)) = 1 := by
    have hlog_inv : (fun s : ℝ => Real.log (1 / s)) = fun s : ℝ => -Real.log s := by
      funext s
      rw [one_div, Real.log_inv]
    rw [hlog_inv, intervalIntegral.integral_neg, integral_log]
    norm_num
  have h3 : (∫ s in (0 : ℝ)..1, Real.log (ε / (ε * s))) = 1 := by
    refine (intervalIntegral.integral_congr_ae ?_).trans h2
    filter_upwards with s hs
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hs' : s ≠ 0 := ne_of_gt hs.1
    rw [mul_comm]
    congr 1
    field_simp
  have hmain : ε * (∫ s in (0 : ℝ)..1, Real.log (ε / (ε * s)))
      = ∫ u in (0 : ℝ)..ε, Real.log (ε / u) := by
    have h := intervalIntegral.integral_comp_mul_left (f := fun u : ℝ => Real.log (ε / u))
      (a := (0 : ℝ)) (b := 1) (c := ε) (by positivity)
    rw [mul_zero, mul_one] at h
    rw [h, smul_eq_mul]
    exact mul_inv_cancel_left₀ (ne_of_gt hε) _
  calc (∫ u in (0 : ℝ)..ε, Real.log (ε / u))
      = ε * (∫ s in (0 : ℝ)..1, Real.log (ε / (ε * s))) := hmain.symm
    _ = ε := by rw [h3]; ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_log_div

end

end Inline_ExplicitFormula_RH72

section Inline_ExplicitFormula_RH73














noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem truncKernel_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    ‖truncKernel ε u‖ ≤ 1 / ε := by
  rw [Real.norm_eq_abs]
  exact abs_truncKernel_le hε u


theorem integrableOn_sq_of_bound {a C : ℝ} {g : ℝ × ℝ → ℝ} (hC : 0 ≤ C)
    (hg : Measurable g)
    (h : ∀ z ∈ Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a, ‖g z‖ ≤ C) :
    IntegrableOn g (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) (volume.prod volume) := by
  have hfin : volume (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) ≠ ⊤ := by
    have hc : IsCompact (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) :=
      (isCompact_Icc (a := -a) (b := a)).prod (isCompact_Icc (a := -a) (b := a))
    exact ne_of_lt (lt_of_le_of_lt
      (measure_mono fun p hp => Set.mem_prod.mpr
        ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
      hc.measure_lt_top)
  exact (integrableOn_const (s := Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) (C := C)
    hfin).mono' hg.aestronglyMeasurable
    (by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)]
        with z hz
      exact h z hz)

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncKernel_bound
#print axioms RHLean.ExplicitFormula.integrableOn_sq_of_bound

end

end Inline_ExplicitFormula_RH73

section Inline_ExplicitFormula_RH74














noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem exists_norm_le_of_localizedCore {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf.1.2.1.isCompact.exists_bound_of_continuousOn
    hf.1.1.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hB x hx) (le_max_left _ _)
  · have hzero : f x = 0 := by
      by_contra h
      exact hx (subset_tsupport f (Function.mem_support.mpr h))
    rw [hzero]
    simp


theorem trunc_symm {a ε : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a) (hε : 0 < ε) :
    (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2))
      = (1 / 2) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2) := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  have hD : MeasurableSet (D ×ˢ D) := measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hKbdd : ∀ u : ℝ, ‖truncKernel ε u‖ ≤ 1 / ε := fun u => truncKernel_bound hε u
  have hA_meas : Measurable (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2) :=
    ((measurable_truncKernel ε).comp (continuous_fst.sub continuous_snd).measurable).mul
      ((hf.1.1.continuous.comp continuous_fst).norm.pow 2).measurable
  have hB_meas : Measurable (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2) :=
    ((measurable_truncKernel ε).comp (continuous_fst.sub continuous_snd).measurable).mul
      ((hf.1.1.continuous.comp continuous_snd).norm.pow 2).measurable
  have hIntA : IntegrableOn (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2) (D ×ˢ D) volume :=
    integrableOn_sq_of_bound (C := (1 / ε) * B ^ 2) (by positivity) hA_meas
      (fun z _ => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |truncKernel ε (z.1 - z.2)| ≤ 1 / ε := by
          rw [← Real.norm_eq_abs]
          exact hKbdd _
        have h2 : |‖f z.1‖ ^ 2| ≤ B ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          nlinarith [hB z.1, hB0, norm_nonneg (f z.1)]
        calc |truncKernel ε (z.1 - z.2)| * |‖f z.1‖ ^ 2|
            ≤ (1 / ε) * B ^ 2 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ ≤ (1 / ε) * B ^ 2 := le_rfl)
  have hIntB : IntegrableOn (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2) (D ×ˢ D) volume :=
    integrableOn_sq_of_bound (C := (1 / ε) * B ^ 2) (by positivity) hB_meas
      (fun z _ => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |truncKernel ε (z.1 - z.2)| ≤ 1 / ε := by
          rw [← Real.norm_eq_abs]
          exact hKbdd _
        have h2 : |‖f z.2‖ ^ 2| ≤ B ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          nlinarith [hB z.2, hB0, norm_nonneg (f z.2)]
        calc |truncKernel ε (z.1 - z.2)| * |‖f z.2‖ ^ 2|
            ≤ (1 / ε) * B ^ 2 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ ≤ (1 / ε) * B ^ 2 := le_rfl)
  have hswap : (∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2)
      = ∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2 := by
    have h := setIntegral_prod_swap (μ := volume) (ν := volume) (s := D) (t := D)
      (f := fun z : ℝ × ℝ => truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2)
    have hK : ∀ z : ℝ × ℝ,
        truncKernel ε (z.2 - z.1) = truncKernel ε (z.1 - z.2) := by
      intro z
      unfold truncKernel
      rw [abs_sub_comm]
    calc (∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2)
        = ∫ z in D ×ˢ D,
            (fun z : ℝ × ℝ => truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2) z.swap := by
          apply setIntegral_congr_fun hD
          intro z _
          simp only [Prod.fst_swap, Prod.snd_swap]
          rw [hK z]
      _ = ∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2 := h
  have hpt : ∀ z : ℝ × ℝ, truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
      = truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2
        + truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2 := by
    intro z
    ring
  rw [show (∫ z in D ×ˢ D,
        truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2))
      = ∫ z in D ×ˢ D, (truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2
          + truncKernel ε (z.1 - z.2) * ‖f z.2‖ ^ 2) from
        setIntegral_congr_fun hD (fun z _ => hpt z)]
  rw [integral_add hIntA hIntB, hswap]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_norm_le_of_localizedCore
#print axioms RHLean.ExplicitFormula.trunc_symm

end

end Inline_ExplicitFormula_RH74

section Inline_ExplicitFormula_RH75

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem archForm_trunc_split {a ε : ℝ} {f : ℝ → ℂ} (ha : 0 < a)
    (hf : f ∈ localizedCore a) :
    archForm a f
      = (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2 ∂(volume.prod volume))
        + (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
            ∂(volume.prod volume)) := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  set F : ℝ × ℝ → ℝ := fun z => ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| with hF
  have hD : MeasurableSet (D ×ˢ D) := measurableSet_Ioo.prod measurableSet_Ioo
  have hF_meas : Measurable F := by
    refine Measurable.div ?_ ?_
    · exact (((hf.1.1.continuous.comp continuous_fst).sub
        (hf.1.1.continuous.comp continuous_snd)).norm.pow 2).measurable
    · exact ((continuous_fst.sub continuous_snd).abs).measurable
  obtain ⟨C, hC0, hC⟩ := normSq_div_le_lipschitz hf
  have hF_bound : ∀ z ∈ D ×ˢ D, ‖F z‖ ≤ C ^ 2 * (2 * a) := by
    intro z hz
    have hz1 : |z.1| ≤ a := by
      rw [abs_le]
      exact ⟨hz.1.1.le, hz.1.2.le⟩
    have hz2 : |z.2| ≤ a := by
      rw [abs_le]
      exact ⟨hz.2.1.le, hz.2.2.le⟩
    rw [abs_le] at hz1 hz2
    have h1 := hC z.1 ⟨hz.1.1.le, hz.1.2.le⟩ z.2 ⟨hz.2.1.le, hz.2.2.le⟩
    have h2 : 0 ≤ F z := div_nonneg (sq_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    calc F z ≤ C ^ 2 * |z.1 - z.2| := h1
      _ ≤ C ^ 2 * (2 * a) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [abs_le]
          constructor <;> linarith
  have hInt : Integrable F ((volume.prod volume).restrict (D ×ˢ D)) :=
    integrableOn_sq_of_bound (C := C ^ 2 * (2 * a)) (by positivity) hF_meas hF_bound
  have harch : archForm a f
      = (1 / 4) * (∫ z in D ×ˢ D, F z ∂(volume.prod volume)) := by
    unfold archForm
    rw [setIntegral_prod F hInt]
    simp only [hF, hDdef, Real.norm_eq_abs]
  have hs : MeasurableSet {z : ℝ × ℝ | ε < |z.1 - z.2|} :=
    measurableSet_lt measurable_const ((continuous_fst.sub continuous_snd).abs.measurable)
  have hsplit := integral_add_compl (μ := (volume.prod volume).restrict (D ×ˢ D)) hs hInt
  have hsplit4 : (1 / 4) * (∫ z in D ×ˢ D, F z ∂(volume.prod volume))
      = (1 / 4) * ((∫ z in {z : ℝ × ℝ | ε < |z.1 - z.2|}, F z
            ∂((volume.prod volume).restrict (D ×ˢ D)))
          + ∫ z in {z : ℝ × ℝ | ε < |z.1 - z.2|}ᶜ, F z
            ∂((volume.prod volume).restrict (D ×ˢ D))) := by
    rw [hsplit]
  rw [harch, hsplit4]
  have hleft : (∫ z in {z : ℝ × ℝ | ε < |z.1 - z.2|}, F z
        ∂((volume.prod volume).restrict (D ×ˢ D)))
      = ∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2
          ∂(volume.prod volume) := by
    change (∫ z, F z
        ∂(((volume.prod volume).restrict (D ×ˢ D)).restrict {z : ℝ × ℝ | ε < |z.1 - z.2|}))
      = ∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2
          ∂(volume.prod volume)
    rw [Measure.restrict_restrict hs, Set.inter_comm]
    rw [← setIntegral_indicator hs]
    apply setIntegral_congr_fun hD (fun z _ => ?_)
    by_cases h : ε < |z.1 - z.2|
    · rw [Set.indicator_of_mem (by exact h), hF]
      unfold truncKernel
      rw [if_pos h]
      field_simp
    · rw [Set.indicator_of_notMem (by exact h)]
      unfold truncKernel
      rw [if_neg h, zero_mul]
  have hright : (∫ z in {z : ℝ × ℝ | ε < |z.1 - z.2|}ᶜ, F z
        ∂((volume.prod volume).restrict (D ×ˢ D)))
      = ∫ z in D ×ˢ D,
          (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
            ∂(volume.prod volume) := by
    change (∫ z, F z
        ∂(((volume.prod volume).restrict (D ×ˢ D)).restrict {z : ℝ × ℝ | ε < |z.1 - z.2|}ᶜ))
      = ∫ z in D ×ˢ D,
          (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
            ∂(volume.prod volume)
    rw [Measure.restrict_restrict hs.compl, Set.inter_comm]
    rw [← setIntegral_indicator hs.compl]
    apply setIntegral_congr_fun hD (fun z _ => ?_)
    by_cases h : ε < |z.1 - z.2|
    · rw [Set.indicator_of_notMem (by simp [h]), if_neg (not_le.mpr h)]
    · rw [Set.indicator_of_mem (by simp [h]), hF]
      rw [if_pos (le_of_not_gt h)]
  rw [hleft, hright]
  ring


theorem trunc_normSq_split {a ε : ℝ} {f : ℝ → ℂ} (ha : 0 < a)
    (hf : f ∈ localizedCore a) (hε : 0 < ε) :
    (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2 ∂(volume.prod volume))
      = (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
            ∂(volume.prod volume))
        - (1 / 2) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re
            ∂(volume.prod volume)) := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  have hD : MeasurableSet (D ×ˢ D) := measurableSet_Ioo.prod measurableSet_Ioo
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hKbdd : ∀ u : ℝ, ‖truncKernel ε u‖ ≤ 1 / ε := fun u => truncKernel_bound hε u
  have hK_meas : Measurable (fun z : ℝ × ℝ => truncKernel ε (z.1 - z.2)) :=
    (measurable_truncKernel ε).comp (continuous_fst.sub continuous_snd).measurable
  have hmeas1 : Measurable (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)) :=
    hK_meas.mul (((hf.1.1.continuous.comp continuous_fst).norm.pow 2).measurable.add
      ((hf.1.1.continuous.comp continuous_snd).norm.pow 2).measurable)
  have hmeas2 : Measurable (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re) :=
    hK_meas.mul (Complex.continuous_re.comp
      ((hf.1.1.continuous.comp continuous_fst).mul
        (continuous_star.comp (hf.1.1.continuous.comp continuous_snd)))).measurable
  have hInt1 : IntegrableOn (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)) (D ×ˢ D) volume := by
    refine integrableOn_sq_of_bound (C := (1 / ε) * (B ^ 2 + B ^ 2)) (by positivity)
      hmeas1 (fun z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |truncKernel ε (z.1 - z.2)| ≤ 1 / ε := by
      rw [← Real.norm_eq_abs]
      exact hKbdd _
    have h2 : |‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2| ≤ B ^ 2 + B ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      have h3 : ‖f z.1‖ ^ 2 ≤ B ^ 2 := by nlinarith [hB z.1, hB0, norm_nonneg (f z.1)]
      have h4 : ‖f z.2‖ ^ 2 ≤ B ^ 2 := by nlinarith [hB z.2, hB0, norm_nonneg (f z.2)]
      linarith
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hInt2 : IntegrableOn (fun z : ℝ × ℝ =>
      truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re) (D ×ˢ D) volume := by
    refine integrableOn_sq_of_bound (C := (1 / ε) * (B * B)) (by positivity)
      hmeas2 (fun z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |truncKernel ε (z.1 - z.2)| ≤ 1 / ε := by
      rw [← Real.norm_eq_abs]
      exact hKbdd _
    have h2 : |(f z.1 * star (f z.2)).re| ≤ B * B := by
      calc |(f z.1 * star (f z.2)).re| ≤ ‖f z.1 * star (f z.2)‖ := Complex.abs_re_le_norm _
        _ = ‖f z.1‖ * ‖f z.2‖ := by rw [norm_mul, norm_star]
        _ ≤ B * B := mul_le_mul (hB z.1) (hB z.2) (norm_nonneg _) hB0
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hpoint : ∀ z : ℝ × ℝ,
      truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2
        = truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
          - 2 * (truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re) := by
    intro z
    have h := fourth_normSq_sub (f z.1) (f z.2)
    have h' : ‖f z.1 - f z.2‖ ^ 2
        = ‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2 - 2 * (f z.1 * star (f z.2)).re := by
      simp only [starRingEnd_apply] at h
      linear_combination (4 : ℝ) * h
    rw [h']
    ring
  have hpoint_int : (∫ z in D ×ˢ D,
        truncKernel ε (z.1 - z.2) * ‖f z.1 - f z.2‖ ^ 2 ∂(volume.prod volume))
      = ∫ z in D ×ˢ D, (truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
          - 2 * (truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re))
          ∂(volume.prod volume) :=
    setIntegral_congr_fun hD (fun z _ => hpoint z)
  rw [hpoint_int, integral_sub (μ := (volume.prod volume).restrict (D ×ˢ D))
    hInt1 (hInt2.const_mul 2), integral_const_mul]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.archForm_trunc_split
#print axioms RHLean.ExplicitFormula.trunc_normSq_split

end

end Inline_ExplicitFormula_RH75

section Inline_ExplicitFormula_RH76

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem exists_autocorr_re_sub_bound {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |u| ≤ 1 →
      |(autocorr f u).re - (autocorr f 0).re| ≤ C * |u| := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_autocorr hf).continuous_deriv (by norm_num)).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun u hu => ?_⟩
  rw [abs_le] at hu
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖deriv (autocorr f) x‖ ≤ max K 0 :=
    fun x hx => le_trans (hK x hx) (le_max_left K 0)
  rcases le_total 0 u with hu0 | hu0
  · have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (a := (0 : ℝ)) (b := u)
      (f := autocorr f) (f' := fun x => deriv (autocorr f) x) (C := max K 0)
      (fun x hx => ((contDiff_autocorr hf).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => hderiv x ⟨by linarith [hx.1], by linarith [hx.2.le, hu.2]⟩)
    have h1 := hMVT u ⟨hu0, le_rfl⟩
    calc |(autocorr f u).re - (autocorr f 0).re|
        = |((autocorr f u - autocorr f 0).re)| := by rw [Complex.sub_re]
      _ ≤ ‖autocorr f u - autocorr f 0‖ := Complex.abs_re_le_norm _
      _ ≤ max K 0 * (u - 0) := h1
      _ = max K 0 * |u| := by rw [sub_zero, abs_of_nonneg hu0]
  · have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (a := u) (b := 0)
      (f := autocorr f) (f' := fun x => deriv (autocorr f) x) (C := max K 0)
      (fun x hx => ((contDiff_autocorr hf).differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => hderiv x ⟨by linarith [hx.1, hu.1], by linarith [hx.2.le]⟩)
    have h1 := hMVT 0 ⟨hu0, le_rfl⟩
    have h2 : (0 : ℝ) - u = |u| := by rw [abs_of_nonpos hu0]; ring
    calc |(autocorr f u).re - (autocorr f 0).re|
        = |((autocorr f 0 - autocorr f u).re)| := by
          rw [Complex.sub_re]
          exact abs_sub_comm _ _
      _ ≤ ‖autocorr f 0 - autocorr f u‖ := Complex.abs_re_le_norm _
      _ ≤ max K 0 * (0 - u) := h1
      _ = max K 0 * |u| := by rw [h2]




theorem tendsto_truncKernel_mul_autocorr_sub {f : ℝ → ℂ} (hf : f ∈ oddCore) (R : ℝ) :
    Tendsto (fun ε : ℝ => ∫ u in Set.Icc (-R) R,
        truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
      (𝓝[>] 0)
      (𝓝 (∫ u in Set.Icc (-R) R,
        (|u|)⁻¹ * ((autocorr f u).re - (autocorr f 0).re))) := by
  obtain ⟨C, hC0, hC⟩ := exists_autocorr_re_sub_bound hf
  obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf
  set g : ℝ → ℝ := fun u => (autocorr f u).re with hg
  have hcont : Continuous g := by
    rw [hg]
    exact Complex.continuous_re.comp (contDiff_autocorr hf).continuous
  have hmeas_g : Measurable g := hcont.measurable
  set G : ℝ → ℝ := fun u => (|u|)⁻¹ * |g u - g 0| with hG
  have hG_bound : ∀ u : ℝ, ‖G u‖ ≤ max C (2 * B) := by
    intro u
    have hGnn : 0 ≤ G u := by rw [hG]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hGnn]
    by_cases hu : u = 0
    · rw [hG, hu]
      simp only [abs_zero, inv_zero, zero_mul, sub_self, abs_zero]
      exact le_trans (by linarith [hB0] : (0 : ℝ) ≤ 2 * B) (le_max_right _ _)
    · have hupos : 0 < |u| := abs_pos.mpr hu
      have hM : |g u - g 0| ≤ max C (2 * B) * |u| := by
        by_cases hle : |u| ≤ 1
        · exact le_trans (hC u hle)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        · have h2 : |g u - g 0| ≤ B + B := by
            have h := abs_sub_le (g u) 0 (g 0)
            rw [sub_zero, zero_sub, abs_neg] at h
            linarith [h, hB u, hB 0]
          calc |g u - g 0| ≤ B + B := h2
            _ = 2 * B := by ring
            _ ≤ 2 * B * |u| := by nlinarith [hle, hB0]
            _ ≤ max C (2 * B) * |u| :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
      rw [hG]
      simp only
      rw [← div_eq_inv_mul]
      exact (div_le_iff₀ hupos).mpr hM
  have hG_meas : Measurable G := by
    rw [hG]
    exact (continuous_abs.measurable.inv).mul
      (continuous_abs.measurable.comp (hmeas_g.sub measurable_const))
  have hG_int : Integrable G (volume.restrict (Set.Icc (-R) R)) := by
    refine Measure.integrableOn_of_bounded (s_finite := ?_) (f_mble := ?_)
      (M := max C (2 * B)) ?_
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · exact hG_meas.aestronglyMeasurable
    · filter_upwards with u
      exact hG_bound u
  have hmain : Tendsto (fun ε : ℝ => ∫ u, truncKernel ε u * (g u - g 0)
      ∂(volume.restrict (Set.Icc (-R) R))) (𝓝[>] 0)
      (𝓝 (∫ u, (|u|)⁻¹ * (g u - g 0) ∂(volume.restrict (Set.Icc (-R) R)))) :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (-R) R)) G ?_ ?_ hG_int ?_
  · simpa only [hg] using hmain
  · filter_upwards with ε
    exact ((measurable_truncKernel ε).mul (hmeas_g.sub measurable_const)).aestronglyMeasurable
  · filter_upwards with ε
    filter_upwards with u
    by_cases hu : u = 0
    · subst hu
      rw [hG]
      simp only [truncKernel, abs_zero, if_false, zero_mul, sub_self,
        abs_zero, norm_zero, inv_zero, mul_zero]
      exact le_rfl
    · have hupos : 0 < |u| := abs_pos.mpr hu
      rw [Real.norm_eq_abs, abs_mul]
      have hK : |truncKernel ε u| ≤ (|u|)⁻¹ := by
        unfold truncKernel
        by_cases h : ε < |u|
        · rw [if_pos h, abs_of_pos (inv_pos.mpr hupos)]
        · rw [if_neg h, abs_zero]
          exact inv_nonneg.mpr (abs_nonneg u)
      rw [hG]
      simp only
      exact mul_le_mul hK le_rfl (abs_nonneg _) (inv_nonneg.mpr (abs_nonneg u))
  · filter_upwards with u
    by_cases hu : u = 0
    · subst hu
      have hzero : (fun ε : ℝ => truncKernel ε 0 * ((autocorr f 0).re - (autocorr f 0).re))
          = fun _ => 0 := by
        funext ε
        simp only [sub_self, mul_zero, truncKernel, abs_zero, lt_self_iff_false, if_false,
          zero_mul]
      rw [show g 0 = (autocorr f 0).re from rfl, hzero]
      simpa using tendsto_const_nhds
    · have hupos : 0 < |u| := abs_pos.mpr hu
      have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < |u| := (tendsto_order.1 ht).2 |u| hupos
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with ε hε
      simp only [truncKernel, hε, if_pos]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_autocorr_re_sub_bound
#print axioms RHLean.ExplicitFormula.tendsto_truncKernel_mul_autocorr_sub

end

end Inline_ExplicitFormula_RH76

section Inline_ExplicitFormula_RH77



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



theorem exp_three_halves_mul_two_div_exp {u : ℝ} (hu : 0 < u) :
    Real.exp (3 * u / 2) * (2 / (Real.exp (2 * u) - 1)) = 1 / u + 2 * gammaKernel u := by
  have hden : Real.exp (2 * u) - 1 ≠ 0 := by
    have h : 1 < Real.exp (2 * u) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    linarith
  have huu : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hfac : Real.exp (2 * u) - 1 = Real.exp u * (Real.exp u - Real.exp (-u)) := by
    rw [show Real.exp (2 * u) = Real.exp u * Real.exp u from by
      rw [← Real.exp_add]; ring_nf]
    linear_combination huu
  have he3 : Real.exp (3 * u / 2) = Real.exp (u / 2) * Real.exp u := by
    rw [← Real.exp_add]; ring_nf
  rw [gammaKernel, if_neg (ne_of_gt hu), Real.sinh_eq, hfac, he3]
  have h2 : (2 : ℝ) * ((Real.exp u - Real.exp (-u)) / 2) = Real.exp u - Real.exp (-u) := by
    ring
  rw [h2]
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have h1 : Real.exp u - Real.exp (-u) ≠ 0 := by
    have h : Real.exp (-u) < Real.exp u := Real.exp_lt_exp.mpr (by linarith)
    linarith
  field_simp
  all_goals first | linear_combination huu | ring


theorem integrableOn_two_div_exp_sub_one_Ioi {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun u : ℝ => 2 / (Real.exp (2 * u) - 1)) (Set.Ioi R) volume := by
  have hden : 0 < 1 - Real.exp (-(2 * R)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hbase : Integrable (fun u : ℝ => (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-(2 * u)))
      (volume.restrict (Set.Ioi R)) :=
    (integrableOn_exp_neg_mul_form (a := R) (b := 2) (by norm_num)).const_mul _
  refine hbase.mono' ?_ ?_
  · exact ((measurable_const.div ((Real.continuous_exp.measurable.comp
      (measurable_id.const_mul 2)).sub measurable_const))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have huR : R < u := hu
    rw [Real.norm_eq_abs]
    have hpos : 0 < Real.exp (2 * u) - 1 := by
      have h : 1 < Real.exp (2 * u) := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
      linarith
    rw [abs_of_pos (div_pos (by norm_num) hpos)]
    have heu : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hfac : Real.exp (2 * u) - 1 = Real.exp (2 * u) * (1 - Real.exp (-(2 * u))) := by
      rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [div_le_iff₀ hpos]
    have hstep : (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-(2 * u)) * (Real.exp (2 * u) - 1)
        = (2 / (1 - Real.exp (-(2 * R)))) * (1 - Real.exp (-(2 * u))) := by
      rw [hfac]
      rw [show (2 / (1 - Real.exp (-(2 * R)))) * Real.exp (-(2 * u))
            * (Real.exp (2 * u) * (1 - Real.exp (-(2 * u))))
          = (2 / (1 - Real.exp (-(2 * R)))) * (Real.exp (-(2 * u)) * Real.exp (2 * u))
            * (1 - Real.exp (-(2 * u))) from by ring,
        heu, mul_one]
    rw [hstep, div_mul_eq_mul_div, le_div_iff₀ hden]
    have h2 : Real.exp (-(2 * u)) ≤ Real.exp (-(2 * R)) :=
      Real.exp_le_exp.mpr (by linarith)
    nlinarith


theorem mehler_u_split {f : ℝ → ℂ} (hf : f ∈ oddCore) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ u : ℝ, R < |u| → (autocorr f u).re = 0) :
    (∑' n : ℕ, ((autocorr f 0).re / ((n : ℝ) + 1)
        - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|)) * (autocorr f u).re))
      = (-Real.log 2 - Real.log R) * (autocorr f 0).re
        - (∫ u in (0 : ℝ)..R, ((autocorr f u).re - (autocorr f 0).re) / u)
        - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re) := by
  obtain ⟨Mρ, hMρ0, hMρ⟩ := gammaKernel_abs_le
  obtain ⟨C, hC0, hC⟩ := exists_autocorr_re_sub_bound hf
  obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf
  obtain ⟨Cmaj, hCmaj0, hCmaj⟩ := digammaKernel_majorant hf
  set g : ℝ → ℝ := fun u => (autocorr f u).re with hg
  have hg_cont : Continuous g := by
    rw [hg]
    exact Complex.continuous_re.comp (contDiff_autocorr hf).continuous
  have hg_meas : Measurable g := hg_cont.measurable
  set f0 : ℝ → ℝ := fun u => (g 0 - Real.exp (3 * u / 2) * g u)
    * (2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))) with hf0
  set f1 : ℝ → ℝ := fun u => (g 0 - Real.exp (3 * u / 2) * g u)
    * (2 / (Real.exp (2 * u) - 1)) with hf1

  have hS : (∑'
      - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|)) * g u))
      = ∫ u in Set.Ioi (0 : ℝ), f0 u := by
    have h1 : digammaSpectralBlock f = -Real.eulerMascheroniConstant * g 0
        + ∑' n : ℕ, (g 0 / ((n : ℝ) + 1)
            - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|)) * g u) :=
      digammaSpectralBlock_eq_tsum hf
    have h2 : digammaSpectralBlock f = -Real.eulerMascheroniConstant * g 0
        + ∫ u in Set.Ioi (0 : ℝ), f0 u :=
      digammaSpectralBlock_eq_positionSpaceU hf
    linarith [h1, h2]

  have hKpt : ∀ u : ℝ, 0 < u → f0 u = f1 u := by
    intro u hu
    simp only [hf0, hf1]
    have hK : 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))) = 2 / (Real.exp (2 * u) - 1) := by
      have h1 : 1 - Real.exp (-(2 * u)) ≠ 0 := by
        intro h
        have : Real.exp (-(2 * u)) = 1 := by linarith
        rw [Real.exp_eq_one_iff] at this
        linarith
      have h2 : Real.exp (2 * u) - 1 ≠ 0 := by
        have h : 1 < Real.exp (2 * u) := by
          rw [← Real.exp_zero]
          exact Real.exp_lt_exp.mpr (by linarith)
        linarith
      rw [div_eq_div_iff h1 h2]
      rw [show Real.exp (2 * u) = Real.exp u * Real.exp u from by
        rw [← Real.exp_add]; ring_nf]
      have heu : Real.exp u * Real.exp u * Real.exp (-(2 * u)) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add, show u + u + -(2 * u) = 0 by ring, Real.exp_zero]
      linear_combination (2 : ℝ) * heu
    rw [hK]

  have hInt0 : Integrable f0 (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (integrable_exp_neg_half_add_inv Cmaj).mono'
    · have hA : Measurable (fun u : ℝ => Real.exp (3 * u / 2) * g u) :=
        (Real.continuous_exp.measurable.comp ((measurable_id.const_mul 3).div_const 2)).mul hg_meas
      have hB : Measurable (fun u : ℝ => 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u)))) :=
        (measurable_const.mul (Real.continuous_exp.measurable.comp
          ((measurable_id.const_mul 2).neg))).div
          (measurable_const.sub (Real.continuous_exp.measurable.comp ((measurable_id.const_mul 2).neg)))
      exact ((measurable_const.sub hA).mul hB).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      rw [Real.norm_eq_abs, abs_mul]
      have hKpos : 0 ≤ 2 * Real.exp (-(2 * u)) / (1 - Real.exp (-(2 * u))) := by
        apply div_nonneg (by positivity)
        rw [sub_nonneg]
        exact Real.exp_le_one_iff.mpr (by linarith)
      rw [abs_of_nonneg hKpos]
      exact hCmaj u hu

  have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd hu.2 (not_le.mpr hu')
  have hunion : Set.Ioc (0 : ℝ) R ∪ Set.Ioi R = Set.Ioi (0 : ℝ) := by
    ext u
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_trans hR h
    · intro h
      by_cases hle : u ≤ R
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr (not_le.mp hle)
  have hsplit0 : (∫ u in Set.Ioi (0 : ℝ), f0 u)
      = (∫ u in Set.Ioc (0 : ℝ) R, f0 u) + (∫ u in Set.Ioi R, f0 u) := by
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (hInt0.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl))
      (hInt0.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi hR.le) le_rfl)), hunion]

  have hfin : volume (Set.Ioc (0 : ℝ) R) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hI1 : IntegrableOn (fun u : ℝ => g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u))
      (Set.Ioc (0 : ℝ) R) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := hfin)
      (f_mble := (by
        exact (measurable_const.mul (((measurable_const.div ((Real.continuous_exp.measurable.comp
          (measurable_id.const_mul 2)).sub measurable_const)).sub
            (measurable_const.div measurable_id)))).aestronglyMeasurable))
      (M := 2 * |g 0|) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (abs_two_div_exp_sub_one_sub_inv_le hu.1) (abs_nonneg (g 0))]
  have hI2 : IntegrableOn (fun u : ℝ => (g u - g 0) / u) (Set.Ioc (0 : ℝ) R) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := hfin)
      (f_mble := (by
        exact ((hg_meas.sub measurable_const).div measurable_id).aestronglyMeasurable))
      (M := max C (2 * B)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
    by_cases hle : u ≤ 1
    · have h1 : |g u - g 0| ≤ C * u := by
        have h := hC u (by rw [abs_of_pos hu0]; exact hle)
        rwa [abs_of_pos hu0] at h
      rw [div_le_iff₀ hu0]
      calc |g u - g 0| ≤ C * u := h1
        _ ≤ max C (2 * B) * u := mul_le_mul_of_nonneg_right (le_max_left _ _) hu0.le
    · have hle1 : 1 ≤ u := le_of_lt (lt_of_not_ge hle)
      have h2 : |g u - g 0| ≤ B + B := by
        have h := abs_sub_le (g u) 0 (g 0)
        rw [sub_zero, zero_sub, abs_neg] at h
        linarith [h, hB u, hB 0]
      rw [div_le_iff₀ hu0]
      calc |g u - g 0| ≤ B + B := h2
        _ ≤ (2 * B) * u := by nlinarith [hB0, hle1]
        _ ≤ max C (2 * B) * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0.le
  have hI3 : IntegrableOn (fun u : ℝ => 2 * (gammaKernel u * g u)) (Set.Ioc (0 : ℝ) R) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := hfin)
      (f_mble := (by
        exact (measurable_const.mul (measurable_gammaKernel.mul hg_meas)).aestronglyMeasurable))
      (M := 2 * Mρ * B) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : |gammaKernel u| ≤ Mρ := hMρ u hu.1.le
    have h2 : |g u| ≤ B := hB u
    calc 2 * |gammaKernel u * g u| = 2 * (|gammaKernel u| * |g u|) := by rw [abs_mul]
      _ ≤ 2 * (Mρ * B) := by
          nlinarith [h1, h2, hMρ0, hB0, abs_nonneg (gammaKernel u), abs_nonneg (g u)]
      _ = 2 * Mρ * B := by ring

  have hleft : (∫ u in Set.Ioc (0 : ℝ) R, f0 u) = ∫ u in Set.Ioc (0 : ℝ) R, f1 u :=
    setIntegral_congr_fun measurableSet_Ioc (fun u hu => hKpt u hu.1)
  have hleft2 : (∫ u in Set.Ioc (0 : ℝ) R, f1 u)
      = g 0 * (∫ u in (0 : ℝ)..R, (2 / (Real.exp (2 * u) - 1) - 1 / u))
        - (∫ u in (0 : ℝ)..R, (g u - g 0) / u)
        - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * g u) := by
    have hpt : ∀ u ∈ Set.Ioc (0 : ℝ) R, f1 u
        = g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u) - (g u - g 0) / u
          - 2 * (gammaKernel u * g u) := by
      intro u hu
      simp only [hf1]
      have hK := exp_three_halves_mul_two_div_exp hu.1
      have hstep : (g 0 - Real.exp (3 * u / 2) * g u) * (2 / (Real.exp (2 * u) - 1))
          = g 0 * (2 / (Real.exp (2 * u) - 1))
            - g u * (Real.exp (3 * u / 2) * (2 / (Real.exp (2 * u) - 1))) := by
        ring
      rw [hstep, hK]
      ring
    calc (∫ u in Set.Ioc (0 : ℝ) R, f1 u)
        = ∫ u in Set.Ioc (0 : ℝ) R, (g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u)
            - (g u - g 0) / u - 2 * (gammaKernel u * g u)) :=
          setIntegral_congr_fun measurableSet_Ioc hpt
      _ = (∫ u in Set.Ioc (0 : ℝ) R, g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u))
            - (∫ u in Set.Ioc (0 : ℝ) R, (g u - g 0) / u)
            - (∫ u in Set.Ioc (0 : ℝ) R, 2 * (gammaKernel u * g u)) := by
          have hsub1 : (∫ u in Set.Ioc (0 : ℝ) R, g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u)
                - (g u - g 0) / u - 2 * (gammaKernel u * g u))
              = (∫ u in Set.Ioc (0 : ℝ) R,
                    g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u) - (g u - g 0) / u)
                - (∫ u in Set.Ioc (0 : ℝ) R, 2 * (gammaKernel u * g u)) :=
            integral_sub (μ := volume.restrict (Set.Ioc (0 : ℝ) R))
              (f := fun u : ℝ => g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u) - (g u - g 0) / u)
              (g := fun u : ℝ => 2 * (gammaKernel u * g u)) (hI1.sub hI2) hI3
          have hsub2 : (∫ u in Set.Ioc (0 : ℝ) R,
                g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u) - (g u - g 0) / u)
              = (∫ u in Set.Ioc (0 : ℝ) R, g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u))
                - (∫ u in Set.Ioc (0 : ℝ) R, (g u - g 0) / u) :=
            integral_sub (μ := volume.restrict (Set.Ioc (0 : ℝ) R))
              (f := fun u : ℝ => g 0 * (2 / (Real.exp (2 * u) - 1) - 1 / u))
              (g := fun u : ℝ => (g u - g 0) / u) hI1 hI2
          rw [hsub1, hsub2]
      _ = g 0 * (∫ u in Set.Ioc (0 : ℝ) R, (2 / (Real.exp (2 * u) - 1) - 1 / u))
            - (∫ u in Set.Ioc (0 : ℝ) R, (g u - g 0) / u)
            - 2 * (∫ u in Set.Ioc (0 : ℝ) R, gammaKernel u * g u) := by
          rw [integral_const_mul, integral_const_mul]
      _ = g 0 * (∫ u in (0 : ℝ)..R, (2 / (Real.exp (2 * u) - 1) - 1 / u))
            - (∫ u in (0 : ℝ)..R, (g u - g 0) / u)
            - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * g u) := by
          rw [← intervalIntegral.integral_of_le
                (f := fun u : ℝ => 2 / (Real.exp (2 * u) - 1) - 1 / u) hR.le,
              ← intervalIntegral.integral_of_le (f := fun u : ℝ => (g u - g 0) / u) hR.le,
              ← intervalIntegral.integral_of_le (f := fun u : ℝ => gammaKernel u * g u) hR.le]

  have hright : (∫ u in Set.Ioi R, f0 u) = ∫ u in Set.Ioi R, f1 u :=
    setIntegral_congr_fun measurableSet_Ioi (fun u hu => hKpt u (lt_trans hR hu))
  have hright2 : (∫ u in Set.Ioi R, f1 u)
      = g 0 * (∫ u in Set.Ioi R, 2 / (Real.exp (2 * u) - 1)) := by
    have hpt : ∀ u ∈ Set.Ioi R, f1 u = g 0 * (2 / (Real.exp (2 * u) - 1)) := by
      intro u hu
      have huR : R < |u| := by rw [abs_of_pos (lt_trans hR hu)]; exact hu
      simp only [hf1]
      rw [show g u = 0 from hsupp u huR]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]

  have hgoal : (∑' n : ℕ, (g 0 / ((n : ℝ) + 1)
      - ∫ u : ℝ, Real.exp (-(((2 : ℝ) * n + 1 / 2) * |u|)) * g u))
      = (-Real.log 2 - Real.log R) * g 0
        - (∫ u in (0 : ℝ)..R, (g u - g 0) / u)
        - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * g u) := by
    rw [hS, hsplit0, hleft, hleft2, hright, hright2]
    have hc := digammaKernel_constant hR
    linear_combination (g 0) * hc
  simpa only [hg] using hgoal

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exp_three_halves_mul_two_div_exp
#print axioms RHLean.ExplicitFormula.integrableOn_two_div_exp_sub_one_Ioi
#print axioms RHLean.ExplicitFormula.mehler_u_split

end

end Inline_ExplicitFormula_RH77

section Inline_ExplicitFormula_RH78















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



theorem integral_inv_abs_mul_even {h : ℝ → ℝ} (he : ∀ u, h (-u) = h u) {R : ℝ}
    (hR : 0 ≤ R)
    (hint1 : IntervalIntegrable (fun u : ℝ => (|u|)⁻¹ * h u) volume (-R) 0)
    (hint2 : IntervalIntegrable (fun u : ℝ => (|u|)⁻¹ * h u) volume 0 R) :
    (∫ u in Set.Icc (-R) R, (|u|)⁻¹ * h u) = 2 * ∫ u in (0 : ℝ)..R, h u / u := by
  have h1 : (∫ u in Set.Icc (-R) R, (|u|)⁻¹ * h u)
      = ∫ u in (-R)..R, (|u|)⁻¹ * h u := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h2 : (∫ u in (-R)..0, (|u|)⁻¹ * h u) = ∫ u in (0 : ℝ)..R, (|u|)⁻¹ * h u := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R)
      (f := fun u : ℝ => (|u|)⁻¹ * h u)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    change |(-u)|⁻¹ * h (-u) = |u|⁻¹ * h u
    rw [abs_neg, he]
  have h3 : (∫ u in (0 : ℝ)..R, (|u|)⁻¹ * h u) = ∫ u in (0 : ℝ)..R, h u / u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := by
      have hmin : min (0 : ℝ) R = 0 := min_eq_left hR
      rw [Set.uIcc_of_le hR, Set.mem_Icc] at hu
      exact hu.1
    rcases eq_or_lt_of_le hu0 with h0 | hpos
    · rw [← h0]
      simp
    · change |u|⁻¹ * h u = h u / u
      rw [abs_of_pos hpos, inv_mul_eq_div]
  rw [h2, h3]
  ring



theorem integral_gammaKernel_even {h : ℝ → ℝ} (he : ∀ u, h (-u) = h u) {R : ℝ}
    (hR : 0 ≤ R)
    (hint1 : IntervalIntegrable (fun u : ℝ => gammaKernel |u| * h u) volume (-R) 0)
    (hint2 : IntervalIntegrable (fun u : ℝ => gammaKernel |u| * h u) volume 0 R) :
    (∫ u in Set.Icc (-R) R, gammaKernel |u| * h u)
      = 2 * ∫ u in (0 : ℝ)..R, gammaKernel u * h u := by
  have h1 : (∫ u in Set.Icc (-R) R, gammaKernel |u| * h u)
      = ∫ u in (-R)..R, gammaKernel |u| * h u := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h2 : (∫ u in (-R)..0, gammaKernel |u| * h u)
      = ∫ u in (0 : ℝ)..R, gammaKernel |u| * h u := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := R)
      (f := fun u : ℝ => gammaKernel |u| * h u)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro u _
    change gammaKernel |(-u)| * h (-u) = gammaKernel |u| * h u
    rw [abs_neg, he]
  have h3 : (∫ u in (0 : ℝ)..R, gammaKernel |u| * h u)
      = ∫ u in (0 : ℝ)..R, gammaKernel u * h u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := by
      rw [Set.uIcc_of_le hR, Set.mem_Icc] at hu
      exact hu.1
    change gammaKernel |u| * h u = gammaKernel u * h u
    rw [abs_of_nonneg hu0]
  rw [h2, h3]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_inv_abs_mul_even
#print axioms RHLean.ExplicitFormula.integral_gammaKernel_even

end

end Inline_ExplicitFormula_RH78

section Inline_ExplicitFormula_RH79



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem truncKernel_self_integral_eq {a x ε : ℝ} (hx : |x| < a) (hε : 0 < ε) :
    (∫ y in Set.Ioo (-a) a, truncKernel ε (x - y))
      = (∫ y in (-a)..(x - ε), (x - y)⁻¹) + (∫ y in (x + ε)..a, (y - x)⁻¹)
        + Real.log (ε / (x + a)) * (if x + a < ε then 1 else 0)
        + Real.log (ε / (a - x)) * (if a - x < ε then 1 else 0) := by
  have hxa1 : -a < x := (abs_lt.mp hx).1
  have hxa2 : x < a := (abs_lt.mp hx).2
  have hxpa : 0 < x + a := by linarith
  have hax : 0 < a - x := by linarith

  have hpt : ∀ y ∈ Set.Ioo (-a) a, truncKernel ε (x - y)
      = (x - y)⁻¹ * (if y < x - ε then (1 : ℝ) else 0)
        + (y - x)⁻¹ * (if x + ε < y then (1 : ℝ) else 0) := by
    intro y _
    by_cases h1 : y < x - ε
    · have h2 : ¬ x + ε < y := by linarith
      rw [if_pos h1, if_neg h2, mul_one, mul_zero, add_zero]
      unfold truncKernel
      rw [if_pos (by rw [abs_of_pos (by linarith : (0 : ℝ) < x - y)]; linarith),
        abs_of_pos (by linarith : (0 : ℝ) < x - y)]
    · by_cases h2 : x + ε < y
      · rw [if_neg h1, if_pos h2, mul_zero, mul_one, zero_add]
        unfold truncKernel
        rw [if_pos (by rw [abs_of_neg (by linarith : x - y < 0)]; linarith),
          abs_of_neg (by linarith : x - y < 0), neg_sub]
      · rw [if_neg h1, if_neg h2, mul_zero, mul_zero, add_zero]
        unfold truncKernel
        rw [if_neg]
        rw [not_lt, abs_le]
        constructor <;> linarith

  have hIntA : IntegrableOn
      (fun y : ℝ => (x - y)⁻¹ * (if y < x - ε then (1 : ℝ) else 0))
      (Set.Ioo (-a) a) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := ?_)
      (f_mble := (by
        exact ((measurable_const.sub measurable_id).inv.mul
          (measurable_const.indicator
            (measurableSet_lt measurable_id measurable_const))).aestronglyMeasurable))
      (M := ε⁻¹) ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · filter_upwards with y
      by_cases h : y < x - ε
      · rw [if_pos h, mul_one, Real.norm_eq_abs, abs_inv,
          abs_of_pos (by linarith : (0 : ℝ) < x - y)]
        exact (inv_le_inv₀ (by linarith : (0 : ℝ) < x - y) hε).mpr (by linarith)
      · rw [if_neg h, mul_zero, norm_zero]
        positivity
  have hIntB : IntegrableOn
      (fun y : ℝ => (y - x)⁻¹ * (if x + ε < y then (1 : ℝ) else 0))
      (Set.Ioo (-a) a) volume := by
    refine Measure.integrableOn_of_bounded (s_finite := ?_)
      (f_mble := (by
        exact ((measurable_id.sub measurable_const).inv.mul
          (measurable_const.indicator
            (measurableSet_lt measurable_const measurable_id))).aestronglyMeasurable))
      (M := ε⁻¹) ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · filter_upwards with y
      by_cases h : x + ε < y
      · rw [if_pos h, mul_one, Real.norm_eq_abs, abs_inv,
          abs_of_pos (by linarith : (0 : ℝ) < y - x)]
        exact (inv_le_inv₀ (by linarith : (0 : ℝ) < y - x) hε).mpr (by linarith)
      · rw [if_neg h, mul_zero, norm_zero]
        positivity

  have hfirst : (∫ y in Set.Ioo (-a) a,
        (x - y)⁻¹ * (if y < x - ε then (1 : ℝ) else 0))
      = ∫ y in Set.Ioo (-a) (x - ε), (x - y)⁻¹ := by
    have hind : (fun y : ℝ => (x - y)⁻¹ * (if y < x - ε then (1 : ℝ) else 0))
        = fun y : ℝ => ({z : ℝ | z < x - ε}.indicator (fun z => (x - z)⁻¹)) y := by
      funext y
      by_cases h : y < x - ε <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have hset : Set.Ioo (-a) a ∩ {y : ℝ | y < x - ε} = Set.Ioo (-a) (x - ε) := by
      ext y
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [hind, ← hset, ← setIntegral_indicator (μ := volume)
      (t := {z : ℝ | z < x - ε}) (f := fun z => (x - z)⁻¹)
      (measurableSet_lt measurable_id measurable_const)]
  have hsecond : (∫ y in Set.Ioo (-a) a,
        (y - x)⁻¹ * (if x + ε < y then (1 : ℝ) else 0))
      = ∫ y in Set.Ioo (x + ε) a, (y - x)⁻¹ := by
    have hind : (fun y : ℝ => (y - x)⁻¹ * (if x + ε < y then (1 : ℝ) else 0))
        = fun y : ℝ => ({z : ℝ | x + ε < z}.indicator (fun z => (z - x)⁻¹)) y := by
      funext y
      by_cases h : x + ε < y <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have hset : Set.Ioo (-a) a ∩ {y : ℝ | x + ε < y} = Set.Ioo (x + ε) a := by
      ext y
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [hind, ← hset, ← setIntegral_indicator (μ := volume)
      (t := {z : ℝ | x + ε < z}) (f := fun z => (z - x)⁻¹)
      (measurableSet_lt measurable_const measurable_id)]

  have hAset : (∫ y in Set.Ioo (-a) (x - ε), (x - y)⁻¹)
      = (∫ y in (-a)..(x - ε), (x - y)⁻¹)
        + Real.log (ε / (x + a)) * (if x + a < ε then 1 else 0) := by
    by_cases h : x - ε < -a
    · have hempty : Set.Ioo (-a) (x - ε) = ∅ := Set.Ioo_eq_empty (not_lt.mpr h.le)
      rw [hempty, setIntegral_empty, if_pos (by linarith : x + a < ε), mul_one]
      have hiv : (∫ y in (-a)..(x - ε), (x - y)⁻¹) = Real.log (x + a) - Real.log ε := by
        have h1 : (∫ y in (-a)..(x - ε), (x - y)⁻¹) = ∫ u in ε..(x + a), u⁻¹ := by
          have hh := intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => u⁻¹) (d := x)
            (a := -a) (b := x - ε)
          rw [show x - (x - ε) = ε by ring, show x - -a = x + a by ring] at hh
          exact hh
        rw [h1, integral_inv (by
          rw [Set.mem_uIcc]
          rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith),
          Real.log_div (ne_of_gt hxpa) (ne_of_gt hε)]
      rw [hiv, Real.log_div (ne_of_gt hε) (ne_of_gt hxpa)]
      ring
    · rw [if_neg (not_lt.mpr (by linarith : ε ≤ x + a)), mul_zero, add_zero]
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : -a ≤ x - ε)]
  have hBset : (∫ y in Set.Ioo (x + ε) a, (y - x)⁻¹)
      = (∫ y in (x + ε)..a, (y - x)⁻¹)
        + Real.log (ε / (a - x)) * (if a - x < ε then 1 else 0) := by
    by_cases h : a < x + ε
    · have hempty : Set.Ioo (x + ε) a = ∅ := Set.Ioo_eq_empty (not_lt.mpr h.le)
      rw [hempty, setIntegral_empty, if_pos (by linarith : a - x < ε), mul_one]
      have hiv : (∫ y in (x + ε)..a, (y - x)⁻¹) = Real.log (a - x) - Real.log ε := by
        have h1 : (∫ y in (x + ε)..a, (y - x)⁻¹) = ∫ u in ε..(a - x), u⁻¹ := by
          have hh := intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u⁻¹) (d := x)
            (a := x + ε) (b := a)
          rw [show x + ε - x = ε by ring, show a - x = a - x by ring] at hh
          exact hh
        rw [h1, integral_inv (by
          rw [Set.mem_uIcc]
          rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith),
          Real.log_div (ne_of_gt hax) (ne_of_gt hε)]
      rw [hiv, Real.log_div (ne_of_gt hε) (ne_of_gt hax)]
      ring
    · rw [if_neg (not_lt.mpr (by linarith : ε ≤ a - x)), mul_zero, add_zero]
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith : x + ε ≤ a)]

  rw [setIntegral_congr_fun measurableSet_Ioo hpt,
    integral_add hIntA hIntB, hfirst, hsecond, hAset, hBset]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncKernel_self_integral_eq

end

end Inline_ExplicitFormula_RH79

section Inline_ExplicitFormula_RH80

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



theorem truncKernel_self_integral_eq_single {a x ε : ℝ} (hx : |x| < a)
    (hε : 0 < ε) (hεa : ε < a) :
    (∫ y in Set.Ioo (-a) a, truncKernel ε (x - y))
      = (∫ y in (-a)..(x - ε), (x - y)⁻¹) + (∫ y in (x + ε)..a, (y - x)⁻¹)
        + Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0) := by
  rw [truncKernel_self_integral_eq hx hε]
  rcases le_total 0 x with hx0 | hx0
  · have h1 : ¬ x + a < ε := by linarith
    simp only [if_neg h1, mul_zero, add_zero]
    rw [abs_of_nonneg hx0]
  · have h2 : ¬ a - x < ε := by linarith
    simp only [if_neg h2, mul_zero, add_zero, abs_of_nonpos hx0, sub_neg_eq_add]
    rw [add_comm x a]










def PositionFormEqAt (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∀ R : ℝ, 0 < R →
    (∀ u : ℝ, R < |u| → (autocorr f u).re = 0) →
    archForm a f + potentialForm a f - gammaForm a f
      = -Real.log R * (autocorr f 0).re
        - (∫ u in (0 : ℝ)..R, ((autocorr f u).re - (autocorr f 0).re) / u)
        - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re)




theorem mehlerDirichletKernelAt_of_positionForm {a : ℝ}
    (h : PositionFormEqAt a) : MehlerDirichletKernelAt a := by
  intro ha f hf
  obtain ⟨R, hR0, hR⟩ := exists_support_radius (hasCompactSupport_autocorr hf.1)
  have hR1 : 0 < R + 1 := by linarith
  have hsupp : ∀ u : ℝ, R + 1 < |u| → (autocorr f u).re = 0 := by
    intro u hu
    rw [hR u (by linarith), Complex.zero_re]
  have h1 := mehler_u_split hf.1 hR1 hsupp
  have h2 := h f hf (R + 1) hR1 hsupp
  linarith [h1, h2]


theorem digammaMatchAt_of_positionForm {a : ℝ} (h : PositionFormEqAt a) :
    DigammaArchimedeanMatchAt a :=
  digammaMatchAt_of_mehlerDirichlet (mehlerDirichletKernelAt_of_positionForm h)


theorem archimedeanMatchAt_of_positionForm {a : ℝ} (h : PositionFormEqAt a) :
    ArchimedeanMatchAt a :=
  archimedeanMatchAt_of_digammaMatch (digammaMatchAt_of_positionForm h)




theorem weilExplicitFormulaOdd_of_evenGuinandWeil_positionForm
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_evenGuinandWeil_digammaMatch hGW
    (fun a => digammaMatchAt_of_positionForm (hP a))


theorem weilExplicitFormulaOddNonneg_of_evenGuinandWeil_positionForm
    (hGW : ∀ a : ℝ, EvenGuinandWeilAt a) (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_evenGuinandWeil_digammaMatch hGW
    (fun a => digammaMatchAt_of_positionForm (hP a))

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncKernel_self_integral_eq_single
#print axioms RHLean.ExplicitFormula.mehlerDirichletKernelAt_of_positionForm
#print axioms RHLean.ExplicitFormula.digammaMatchAt_of_positionForm
#print axioms RHLean.ExplicitFormula.archimedeanMatchAt_of_positionForm
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_evenGuinandWeil_positionForm

end

end Inline_ExplicitFormula_RH80

section Inline_ExplicitFormula_RH83





























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



def AdmissibleT (T : ℕ → ℝ) : Prop :=
  Tendsto T atTop atTop ∧ (∀ n, 0 < T n) ∧
    (∀ n, ∀ p : XiZero,
      centeredZero p ∈ rectClosed (stripLeft (T n)) (stripRight (T n)) →
        centeredZero p ∈ rectOpen (stripLeft (T n)) (stripRight (T n)))









def VerticalIntegralEvalAt (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∀ T : ℕ → ℝ, AdmissibleT T →
    Tendsto (fun n => (stripRightIntegral (transf (autocorr f)) (T n)).re) atTop
      (𝓝 (Real.pi * (archimedeanBlock f + poleBlock f
            - (1 / Real.pi) * ∑ q ∈ arithSupport a, arithCoeff q * ghatAt f q)))


theorem evenGuinandWeilAt_of_growth_verticalEval {a : ℝ} (hgrowth : LogDerivStripGrowth)
    (h : VerticalIntegralEvalAt a)
    (hex : ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∃ T : ℕ → ℝ, AdmissibleT T) :
    EvenGuinandWeilAt a := by
  intro ha f hf
  obtain ⟨T, hTtop, hTpos, hbd⟩ := hex f hf
  have h1 := tendsto_right_vertical_autocorr hgrowth hf.1 hTtop hTpos hbd
  have h1re : Tendsto (fun n => (stripRightIntegral (transf (autocorr f)) (T n)).re) atTop
      (𝓝 (((Real.pi : ℂ) * ∑'
    Complex.continuous_re.continuousAt.tendsto.comp h1
  have h3 : ((Real.pi : ℂ) * ∑' p : XiZero, transf (autocorr f) (centeredZero p)).re
      = Real.pi * (∑'
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h3] at h1re
  have h2 := h f hf T ⟨hTtop, hTpos, hbd⟩
  have hEq := tendsto_nhds_unique h1re h2
  exact mul_left_cancel₀ Real.pi_ne_zero hEq




theorem weilExplicitFormulaOdd_of_growth_verticalEval_positionForm
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a)
    (hex : ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∃ T : ℕ → ℝ, AdmissibleT T)
    (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_growth_verticalEval hgrowth (hv a) (hex a)) hP


theorem weilExplicitFormulaOddNonneg_of_growth_verticalEval_positionForm
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a)
    (hex : ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∃ T : ℕ → ℝ, AdmissibleT T)
    (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_growth_verticalEval hgrowth (hv a) (hex a)) hP

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.evenGuinandWeilAt_of_growth_verticalEval
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_growth_verticalEval_positionForm

end

end Inline_ExplicitFormula_RH83

section Inline_ExplicitFormula_RH84
















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem exists_admissibleT : ∃ T : ℕ → ℝ, AdmissibleT T := by
  have hsup : (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ)).support.Countable :=
    MeromorphicOn.divisor_support_countable riemannXi (Set.univ : Set ℂ)
  set S : Set ℝ := (fun p : XiZero => |(centeredZero p).im|) '' Set.univ with hSdef
  have hS : S.Countable := by
    apply Set.Countable.mono _ (hsup.image (fun z : ℂ => |z.im|))
    rintro t ⟨p, -, rfl⟩
    refine ⟨Complex.Hadamard.divisorZeroIndex₀_val p,
      Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p, ?_⟩
    simp [centeredZero]
  have hdense : Dense Sᶜ := hS.dense_compl ℝ
  have hchoice : ∀ n : ℕ, ∃ t : ℝ, t ∈ Set.Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) ∧ t ∉ S := by
    intro n
    obtain ⟨t, htS, htU⟩ := hdense.exists_mem_open
      (U := Set.Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)) isOpen_Ioo
      ⟨(n : ℝ) + 3 / 2, by rw [Set.mem_Ioo]; constructor <;> linarith⟩
    exact ⟨t, htU, htS⟩
  choose T hTmem hTnot using hchoice
  have hTpos : ∀ n, 0 < T n := by
    intro n
    have := (hTmem n).1
    linarith
  refine ⟨T, ?_, hTpos, ?_⟩
  · rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (Nat.ceil b)] with n hn
    have h1 : (n : ℝ) + 1 ≤ T n := le_of_lt (hTmem n).1
    have h2 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
    have h3 : (Nat.ceil b : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · intro n p hp
    have hmin : min (-(T n)) (T n) = -(T n) := min_eq_left (by linarith [hTpos n])
    have hmax : max (-(T n)) (T n) = T n := max_eq_right (by linarith [hTpos n])
    have him_le : |(centeredZero p).im| ≤ T n := by
      rw [rectClosed] at hp
      simp only [stripLeft_re, stripLeft_im, stripRight_re, stripRight_im] at hp
      obtain ⟨-, -, h3, h4⟩ := hp
      rw [hmin] at h3
      rw [hmax] at h4
      rw [abs_le]
      exact ⟨h3, h4⟩
    have hne : |(centeredZero p).im| ≠ T n :=
      fun h => hTnot n ⟨p, Set.mem_univ p, h⟩
    have him_lt : |(centeredZero p).im| < T n := lt_of_le_of_ne him_le hne
    have hre := val_re_mem_Ioo p
    have hc_re : (centeredZero p).re = (Complex.Hadamard.divisorZeroIndex₀_val p).re - 1 / 2 := by
      rw [centeredZero, Complex.sub_re]
      norm_num
    rw [rectOpen]
    simp only [stripLeft_re, stripLeft_im, stripRight_re, stripRight_im]
    have hmin'
    have hmax' : max (-1 / 2 : ℝ) (1 / 2) = 1 / 2 := max_eq_right (by norm_num)
    rw [hmin', hmax', hmin, hmax]
    rw [abs_lt] at him_lt
    exact ⟨by rw [hc_re]; linarith [hre.1], by rw [hc_re]; linarith [hre.2],
      him_lt.1, him_lt.2⟩


theorem weilExplicitFormulaOdd_of_growth_verticalEval_positionForm'
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a)
    (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_growth_verticalEval_positionForm hgrowth hv
    (fun _ _ _ => exists_admissibleT) hP


theorem weilExplicitFormulaOddNonneg_of_growth_verticalEval_positionForm'
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a)
    (hP : ∀ a : ℝ, PositionFormEqAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_growth_verticalEval_positionForm hgrowth hv
    (fun _ _ _ => exists_admissibleT) hP

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_admissibleT
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_growth_verticalEval_positionForm'

end

end Inline_ExplicitFormula_RH84

section Inline_ExplicitFormula_RH99

































noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators

namespace RHLean.ExplicitFormula






def LogDerivStripGrowthAvoiding : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    (∀ p : XiZero, T ≠ |(centeredZero p).im|) → ∀ x : ℝ,
      x ∈ Set.Icc (-(1 / 2)) (1 / 2) →
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖ ≤
          C * (Real.log (1 + T)) ^ 2




def IntegratedStripPolyGrowthAvoiding : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ T : ℝ, 2 ≤ T →
    (∀ p : XiZero, T ≠ |(centeredZero p).im|) →
      IntervalIntegrable (fun x : ℝ =>
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)
        volume (-(1 / 2)) (1 / 2) ∧
      (∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)
        ≤ C * (1 + T) ^ k


theorem logDerivStripGrowthAvoiding_of_logDerivStripGrowth
    (h : LogDerivStripGrowth) : LogDerivStripGrowthAvoiding := by
  obtain ⟨C, hC0, hC⟩ := h
  exact ⟨C, hC0, fun T hT _ => hC T hT⟩







theorem admissibleT_ne_abs_im {T : ℕ → ℝ} (hT : AdmissibleT T) (n : ℕ) (p : XiZero) :
    T n ≠ |(centeredZero p).im| := by
  intro hEq
  have hpos : 0 < T n := hT.2.1 n
  have hmin : min (-(T n)) (T n) = -(T n) := min_eq_left (by linarith)
  have hmax : max (-(T n)) (T n) = T n := max_eq_right (by linarith)
  have hre := val_re_mem_Ioo p
  have hre' : (centeredZero p).re =
      (Complex.Hadamard.divisorZeroIndex₀_val p).re - 1 / 2 := by
    rw [centeredZero, Complex.sub_re]
    norm_num
  have hle : |(centeredZero p).im| ≤ T n := le_of_eq hEq.symm
  obtain ⟨him1, him2⟩ := abs_le.mp hle
  have hmin' : min (-1 / 2 : ℝ) (1 / 2) = -1 / 2 := min_eq_left (by norm_num)
  have hmax' : max (-1 / 2 : ℝ) (1 / 2) = 1 / 2 := max_eq_right (by norm_num)
  have hclosed : centeredZero p ∈ rectClosed (stripLeft (T n)) (stripRight (T n)) := by
    rw [rectClosed]
    simp only [Set.mem_ofPred_eq, stripLeft_re, stripLeft_im, stripRight_re, stripRight_im]
    rw [hmin', hmax', hmin, hmax, hre']
    exact ⟨by linarith [hre.1], by linarith [hre.2], him1, him2⟩
  have hopen := hT.2.2 n p hclosed
  rw [rectOpen] at hopen
  simp only [Set.mem_ofPred_eq, stripLeft_re, stripLeft_im, stripRight_re, stripRight_im] at hopen
  obtain ⟨-, -, h3, h4⟩ := hopen
  rw [hmin] at h3
  rw [hmax] at h4
  have hlt : |(centeredZero p).im| < T n := by
    rw [abs_lt]
    exact ⟨h3, h4⟩
  rw [hEq] at hlt
  exact lt_irrefl _ hlt




theorem measurable_logDeriv_vertical (T : ℝ) :
    Measurable (fun x : ℝ =>
      logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))) := by
  have hcont : Continuous (deriv riemannXi) :=
    continuous_iff_continuousAt.mpr fun s =>
      ((differentiable_riemannXi.analyticAt s).deriv).continuousAt
  have hlog : (fun x : ℝ => logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I)))
      = fun x : ℝ =>
          deriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))
            / riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I)) := by
    funext x
    rw [logDeriv_apply]
  rw [hlog]
  exact (hcont.measurable.comp (by fun_prop)).div
    (differentiable_riemannXi.continuous.measurable.comp (by fun_prop))



theorem intervalIntegrable_logDeriv_norm_of_bound {T M : ℝ}
    (h : ∀ x : ℝ, x ∈ Set.Icc (-(1 / 2)) (1 / 2) →
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖ ≤ M) :
    IntervalIntegrable (fun x : ℝ =>
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)
      volume (-(1 / 2)) (1 / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  refine Measure.integrableOn_of_bounded (s_finite := ?_)
    (f_mble := (measurable_logDeriv_vertical T).norm.aestronglyMeasurable) (M := M) ?_
  · rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h x ⟨(Set.mem_Ioc.mp hx).1.le, (Set.mem_Ioc.mp hx).2⟩





theorem integratedStripPolyGrowthAvoiding_of_logDerivStripGrowthAvoiding
    (h : LogDerivStripGrowthAvoiding) : IntegratedStripPolyGrowthAvoiding := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, 2, fun T hT havoid => ?_⟩
  have hb : ∀ x : ℝ, x ∈ Set.Icc (-(1 / 2)) (1 / 2) →
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖ ≤
        C * (Real.log (1 + T)) ^ 2 :=
    hC T hT havoid
  refine ⟨intervalIntegrable_logDeriv_norm_of_bound hb, ?_⟩
  have hbound : ∀ x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2),
      ‖‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖‖
        ≤ C * (Real.log (1 + T)) ^ 2 := by
    intro x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hx' : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      rw [Set.uIoc_of_le (show (-(1 / 2) : ℝ) ≤ 1 / 2 by norm_num)] at hx
      exact ⟨hx.1.le, hx.2⟩
    exact hb x hx'
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have habs : |(1 / 2 : ℝ) - (-(1 / 2))| = 1 := by norm_num
  calc (∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)
      ≤ |(∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
          ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)| :=
        le_abs_self _
    _ = ‖(∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
          ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T : ℂ) * I))‖)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ C * (Real.log (1 + T)) ^ 2 * |(1 / 2 : ℝ) - (-(1 / 2))| := hnorm
    _ = C * (Real.log (1 + T)) ^ 2 := by rw [habs]; ring
    _ ≤ C * (1 + T) ^ 2 := by
        have hlog : Real.log (1 + T) ≤ 1 + T := Real.log_le_self (by linarith)
        have hlog0 : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
        have hsq : (Real.log (1 + T)) ^ 2 ≤ (1 + T) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hsq hC0

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.logDerivStripGrowthAvoiding_of_logDerivStripGrowth
#print axioms RHLean.ExplicitFormula.admissibleT_ne_abs_im
#print axioms RHLean.ExplicitFormula.measurable_logDeriv_vertical
#print axioms RHLean.ExplicitFormula.intervalIntegrable_logDeriv_norm_of_bound
#print axioms RHLean.ExplicitFormula.integratedStripPolyGrowthAvoiding_of_logDerivStripGrowthAvoiding

end

end Inline_ExplicitFormula_RH99

section Inline_ExplicitFormula_RH85

















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



theorem truncDiagonal_rhs_potential {a x ε : ℝ} (hx : |x| < a) (hε : 0 < ε) :
    (1 / 2) * ((∫ y in (-a)..(x - ε), (x - y)⁻¹)
        + (∫ y in (x + ε)..a, (y - x)⁻¹))
      = -Real.log ε - endpointPotential a x := by
  have h := endpoint_reg_trunc hx hε
  linarith



theorem boundaryKernel_nonneg {a x ε : ℝ} (hx : |x| < a) (hε : 0 < ε) :
    0 ≤ Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0) := by
  have hpos : 0 < a - |x| := by linarith [hx]
  by_cases h : a - |x| < ε
  · rw [if_pos h, mul_one]
    apply Real.log_nonneg
    rw [le_div_iff₀ hpos]
    linarith
  · rw [if_neg h, mul_zero]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncDiagonal_rhs_potential
#print axioms RHLean.ExplicitFormula.boundaryKernel_nonneg

end

end Inline_ExplicitFormula_RH85

section Inline_ExplicitFormula_RH86















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem integral_truncKernel_mul_autocorr_eq' {a ε : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (hε : 0 < ε) :
    (∫ u : ℝ, truncKernel ε u * (autocorr f u).re)
      = ∫ p in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (p.2 - p.1) * (f p.2 * star (f p.1)).re
            ∂(volume.prod volume) := by
  have hK : (fun u : ℝ => truncKernel ε u * (autocorr f u).re)
      = fun u : ℝ => (if ε < |u| then (|u|)⁻¹ else 0) * (autocorr f u).re := by
    funext u
    simp only [truncKernel]
  rw [hK, integral_truncKernel_mul_autocorr_eq hf.1 hε]
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  have hD : MeasurableSet (D ×ˢ D) := measurableSet_Ioo.prod measurableSet_Ioo
  have hfzero : ∀ x ∉ D, f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hf.2 (Function.mem_support.mpr h))
  have hzero : ∀ p : ℝ × ℝ, p ∉ D ×ˢ D →
      (if ε < |p.2 - p.1| then (|p.2 - p.1|)⁻¹ else 0) * (f p.2 * star (f p.1)).re = 0 := by
    intro p hp
    rw [Set.mem_prod] at hp
    rcases not_and_or.mp hp with hp | hp
    · simp [hfzero p.1 hp]
    · simp [hfzero p.2 hp]
  rw [show (∫ p : ℝ × ℝ,
        (if ε < |p.2 - p.1| then (|p.2 - p.1|)⁻¹ else 0)
          * (f p.2 * star (f p.1)).re ∂(volume.prod volume))
      = ∫ p : ℝ × ℝ, (D ×ˢ D).indicator
          (fun p => (if ε < |p.2 - p.1| then (|p.2 - p.1|)⁻¹ else 0)
            * (f p.2 * star (f p.1)).re) p ∂(volume.prod volume) from
    integral_congr_ae (by
      filter_upwards with p
      by_cases hp : p ∈ D ×ˢ D
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, hzero p hp])]
  rw [integral_indicator hD]
  apply setIntegral_congr_fun hD
  intro p _
  simp only [truncKernel]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_truncKernel_mul_autocorr_eq'

end

end Inline_ExplicitFormula_RH86

section Inline_ExplicitFormula_RH87
















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem gammaForm_eq_integral_gammaKernel {a : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    gammaForm a f = ∫ u : ℝ, gammaKernel |u| * (autocorr f u).re := by
  obtain ⟨M, hM0, hM⟩ := gammaKernel_abs_le
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  have hD : MeasurableSet (D ×ˢ D) := measurableSet_Ioo.prod measurableSet_Ioo
  have hmeas : Measurable (fun z : ℝ × ℝ =>
      gammaKernel ‖z.1 - z.2‖ * (f z.1 * star (f z.2)).re) :=
    (measurable_gammaKernel.comp
      ((continuous_fst.sub continuous_snd).norm.measurable)).mul
      (Complex.continuous_re.comp
        ((hf.1.1.continuous.comp continuous_fst).mul
          (continuous_star.comp (hf.1.1.continuous.comp continuous_snd)))).measurable
  have hInt : IntegrableOn (fun z : ℝ × ℝ =>
      gammaKernel ‖z.1 - z.2‖ * (f z.1 * star (f z.2)).re) (D ×ˢ D) volume := by
    refine integrableOn_sq_of_bound (C := M * B ^ 2) (by positivity) hmeas
      (fun z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |gammaKernel ‖z.1 - z.2‖| ≤ M := hM _ (norm_nonneg _)
    have h2 : |(f z.1 * star (f z.2)).re| ≤ B ^ 2 := by
      calc |(f z.1 * star (f z.2)).re| ≤ ‖f z.1 * star (f z.2)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖f z.1‖ * ‖f z.2‖ := by rw [norm_mul, norm_star]
        _ ≤ B * B := mul_le_mul (hB z.1) (hB z.2) (norm_nonneg _) hB0
        _ = B ^ 2 := by ring
    exact mul_le_mul h1 h2 (abs_nonneg _) hM0
  unfold gammaForm
  rw [integral_gammaKernel_mul_autocorr_eq hf.1]
  rw [← setIntegral_prod _ hInt]
  rw [← setIntegral_prod_swap (μ := volume) (ν := volume) (s := D) (t := D)
    (f := fun z : ℝ × ℝ => gammaKernel ‖z.1 - z.2‖ * (f z.1 * star (f z.2)).re)]

  have hfzero : ∀ x ∉ D, f x = 0 := by
    intro x hx
    by_contra h
    exact hx (hf.2 (Function.mem_support.mpr h))
  have hzero : ∀ p : ℝ × ℝ, p ∉ D ×ˢ D →
      gammaKernel |p.2 - p.1| * (f p.2 * star (f p.1)).re = 0 := by
    intro p hp
    rw [Set.mem_prod] at hp
    rcases not_and_or.mp hp with hp | hp
    · simp [hfzero p.1 hp]
    · simp [hfzero p.2 hp]
  rw [show (∫ p : ℝ × ℝ,
        gammaKernel |p.2 - p.1| * (f p.2 * star (f p.1)).re ∂(volume.prod volume))
      = ∫ p : ℝ × ℝ, (D ×ˢ D).indicator
          (fun p => gammaKernel |p.2 - p.1| * (f p.2 * star (f p.1)).re)
          p ∂(volume.prod volume) from
    integral_congr_ae (by
      filter_upwards with p
      by_cases hp : p ∈ D ×ˢ D
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp, hzero p hp])]
  rw [integral_indicator hD]
  apply setIntegral_congr_fun hD
  intro z _
  change gammaKernel ‖z.2 - z.1‖ * (f z.2 * star (f z.1)).re
    = gammaKernel |z.2 - z.1| * (f z.2 * star (f z.1)).re
  rw [Real.norm_eq_abs]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.gammaForm_eq_integral_gammaKernel

end

end Inline_ExplicitFormula_RH87

section Inline_ExplicitFormula_RH88














noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem gammaForm_eq_two_integral {a R : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (hR : 0 < R) (hsupp : ∀ u : ℝ, R < |u| → (autocorr f u).re = 0) :
    gammaForm a f = 2 * ∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re := by
  rw [gammaForm_eq_integral_gammaKernel hf]
  obtain ⟨M, hM0, hM⟩ := gammaKernel_abs_le
  obtain ⟨B, hB0, hB⟩ := exists_autocorr_re_bound hf.1
  have hzero : ∀ u ∉ Set.Icc (-R) R, gammaKernel |u| * (autocorr f u).re = 0 := by
    intro u hu
    have hgt : R < |u| := by
      rw [Set.mem_Icc] at hu
      rcases not_and_or.mp hu with h | h
      · rw [not_le] at h
        rw [abs_of_neg (by linarith)]
        linarith
      · rw [not_le] at h
        rw [abs_of_pos (by linarith)]
        linarith
    rw [hsupp u hgt, mul_zero]
  rw [integral_eq_setIntegral_of_forall_eq_zero_of_notMem measurableSet_Icc hzero]
  have hint : ∀ {c d : ℝ}, c ≤ d → IntervalIntegrable
      (fun u : ℝ => gammaKernel |u| * (autocorr f u).re) volume c d := by
    intro c d hcd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd]
    refine Measure.integrableOn_of_bounded (s_finite := ?_) (f_mble := ?_) (M := M * B) ?_
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    · exact ((measurable_gammaKernel.comp continuous_abs.measurable).mul
        (Complex.continuous_re.measurable.comp
          (contDiff_autocorr hf.1).continuous.measurable)).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hM |u| (abs_nonneg u)) (hB u) (abs_nonneg _) hM0
  rw [integral_gammaKernel_even (autocorr_re_even hf.1) hR.le
    (hint (by linarith : -R ≤ 0)) (hint hR.le)]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.gammaForm_eq_two_integral

end

end Inline_ExplicitFormula_RH88

section Inline_ExplicitFormula_RH89
















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integral_log_div_sub (a ε : ℝ) :
    (∫ x in (a - ε)..a, Real.log (ε / (a - x)))
      = ∫ u in (0 : ℝ)..ε, Real.log (ε / u) := by
  have h := intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => Real.log (ε / u))
    (d := a) (a := a - ε) (b := a)
  rw [show a - (a - ε) = ε by ring, show a - a = 0 by ring] at h
  exact h


theorem integral_log_div_add (a ε : ℝ) :
    (∫ x in (-a)..(-a + ε), Real.log (ε / (a + x)))
      = ∫ u in (0 : ℝ)..ε, Real.log (ε / u) := by
  have h := intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => Real.log (ε / u))
    (d := -a) (a := -a) (b := -a + ε)
  rw [show -a - -a = 0 by ring, show -a + ε - -a = ε by ring] at h
  simpa only [sub_neg_eq_add, add_comm] using h


theorem integral_log_div_sub_eq (a ε : ℝ) (hε : 0 < ε) :
    (∫ x in (a - ε)..a, Real.log (ε / (a - x))) = ε := by
  rw [integral_log_div_sub, integral_log_div hε]

theorem integral_log_div_add_eq (a ε : ℝ) (hε : 0 < ε) :
    (∫ x in (-a)..(-a + ε), Real.log (ε / (a + x))) = ε := by
  rw [integral_log_div_add, integral_log_div hε]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_log_div_sub
#print axioms RHLean.ExplicitFormula.integral_log_div_add
#print axioms RHLean.ExplicitFormula.integral_log_div_sub_eq
#print axioms RHLean.ExplicitFormula.integral_log_div_add_eq

end

end Inline_ExplicitFormula_RH89

section Inline_ExplicitFormula_RH90





















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem intervalIntegrable_log_div_sub {a ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun x : ℝ => Real.log (ε / (a - x))) volume (a - ε) a := by
  have h1 : IntervalIntegrable (fun x : ℝ => Real.log (a - x)) volume (a - ε) a := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := ε)).comp_sub_left a
    simpa using h.symm
  have h2 : IntervalIntegrable (fun x : ℝ => Real.log ε - Real.log (a - x))
      volume (a - ε) a :=
    intervalIntegrable_const.sub h1
  refine h2.congr_uIoo (fun x hx => ?_)
  rw [Set.uIoo_of_le (by linarith : a - ε ≤ a), Set.mem_Ioo] at hx
  have hx' : 0 < a - x := by linarith [hx.2]
  rw [Real.log_div (ne_of_gt hε) (ne_of_gt hx')]


theorem intervalIntegrable_log_div_add {a ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun x : ℝ => Real.log (ε / (a + x))) volume (-a) (-a + ε) := by
  have h1 : IntervalIntegrable (fun x : ℝ => Real.log (a + x)) volume (-a) (-a + ε) := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := ε)).comp_sub_right (-a)
    simpa only [zero_add, add_zero, sub_neg_eq_add, add_comm] using h
  have h2 : IntervalIntegrable (fun x : ℝ => Real.log ε - Real.log (a + x))
      volume (-a) (-a + ε) :=
    intervalIntegrable_const.sub h1
  refine h2.congr_uIoo (fun x hx => ?_)
  rw [Set.uIoo_of_le (by linarith : -a ≤ -a + ε), Set.mem_Ioo] at hx
  have hx' : 0 < a + x := by linarith [hx.1]
  rw [Real.log_div (ne_of_gt hε) (ne_of_gt hx')]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.intervalIntegrable_log_div_sub
#print axioms RHLean.ExplicitFormula.intervalIntegrable_log_div_add

end

end Inline_ExplicitFormula_RH90

section Inline_ExplicitFormula_RH91



















noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integral_boundaryKernel {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    (∫ x in Set.Ioo (-a) a,
        Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)) = 2 * ε := by
  set B : ℝ → ℝ := fun x => Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
    with hB
  have hset : (∫ x in Set.Ioo (-a) a, B x) = ∫ x in (-a)..a, B x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]

  have hpt_sub : ∀ x ∈ Set.uIcc (a - ε) a, B x = Real.log (ε / (a - x)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : a - ε ≤ a), Set.mem_Icc] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    change Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
      = Real.log (ε / (a - x))
    rw [abs_of_nonneg hx0]
    by_cases h : a - x < ε
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]
      have heq : a - x = ε := le_antisymm (by linarith [hx.1]) (not_lt.mp h)
      rw [show ε / (a - x) = 1 by rw [heq, div_self (ne_of_gt hε)], Real.log_one]
  have hpt_add : ∀ x ∈ Set.uIcc (-a) (-a + ε), B x = Real.log (ε / (a + x)) := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -a ≤ -a + ε), Set.mem_Icc] at hx
    have hx0 : x ≤ 0 := by linarith [hx.2]
    change Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
      = Real.log (ε / (a + x))
    simp only [abs_of_nonpos hx0, sub_neg_eq_add]
    by_cases h : a + x < ε
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]
      have heq : a + x = ε := le_antisymm (by linarith [hx.2]) (not_lt.mp h)
      rw [show ε / (a + x) = 1 by rw [heq, div_self (ne_of_gt hε)], Real.log_one]
  have hpt_zero : ∀ x ∈ Set.uIcc (-a + ε) (a - ε), B x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith : -a + ε ≤ a - ε), Set.mem_Icc] at hx
    change Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0) = 0
    rw [if_neg, mul_zero]
    rw [not_lt]
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
      linarith [hx.2]
    · rw [abs_of_nonpos hx0]
      linarith [hx.1]

  have hB1 : IntervalIntegrable B volume (a - ε) a :=
    (intervalIntegrable_log_div_sub hε).congr_uIoo (fun x hx => by
      rw [Set.uIoo_of_le (by linarith : a - ε ≤ a), Set.mem_Ioo] at hx
      have hmem : x ∈ Set.uIcc (a - ε) a := by
        rw [Set.uIcc_of_le (by linarith : a - ε ≤ a)]
        exact ⟨by linarith [hx.1], le_of_lt hx.2⟩
      exact (hpt_sub x hmem).symm)
  have hB2 : IntervalIntegrable B volume (-a) (-a + ε) :=
    (intervalIntegrable_log_div_add hε).congr_uIoo (fun x hx => by
      rw [Set.uIoo_of_le (by linarith : -a ≤ -a + ε), Set.mem_Ioo] at hx
      have hmem : x ∈ Set.uIcc (-a) (-a + ε) := by
        rw [Set.uIcc_of_le (by linarith : -a ≤ -a + ε)]
        exact ⟨le_of_lt hx.1, by linarith [hx.2]⟩
      exact (hpt_add x hmem).symm)
  have hB0 : IntervalIntegrable B volume (-a + ε) (a - ε) :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo (fun x hx => by
      rw [Set.uIoo_of_le (by linarith : -a + ε ≤ a - ε), Set.mem_Ioo] at hx
      have hmem : x ∈ Set.uIcc (-a + ε) (a - ε) := by
        rw [Set.uIcc_of_le (by linarith : -a + ε ≤ a - ε)]
        exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
      exact (hpt_zero x hmem).symm)

  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hB2 (hB0.trans hB1)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hB0 hB1
  have e1 : (∫ x in (-a)..(-a + ε), B x) = ε := by
    rw [show (∫ x in (-a)..(-a + ε), B x)
        = ∫ x in (-a)..(-a + ε), Real.log (ε / (a + x)) from
      intervalIntegral.integral_congr hpt_add]
    exact integral_log_div_add_eq a ε hε
  have e2 : (∫ x in (-a + ε)..(a - ε), B x) = 0 := by
    rw [show (∫ x in (-a + ε)..(a - ε), B x) = ∫ x in (-a + ε)..(a - ε), (0 : ℝ) from
      intervalIntegral.integral_congr hpt_zero]
    rw [intervalIntegral.integral_zero]
  have e3 : (∫ x in (a - ε)..a, B x) = ε := by
    rw [show (∫ x in (a - ε)..a, B x) = ∫ x in (a - ε)..a, Real.log (ε / (a - x)) from
      intervalIntegral.integral_congr hpt_sub]
    exact integral_log_div_sub_eq a ε hε
  rw [hset]
  rw [← hsplit1]
  rw [← hsplit2]
  rw [e1, e2, e3]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_boundaryKernel

end

end Inline_ExplicitFormula_RH91

section Inline_ExplicitFormula_RH92













noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrableOn_log_div_sub {a ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => Real.log (ε / (a - x))) (Set.Ioo (a - ε) a) volume :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith : a - ε ≤ a)).mp (intervalIntegrable_log_div_sub hε)).mono_set
    Set.Ioo_subset_Ioc_self


theorem integrableOn_log_div_add {a ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => Real.log (ε / (a + x))) (Set.Ioo (-a) (-a + ε)) volume :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith : -a ≤ -a + ε)).mp (intervalIntegrable_log_div_add hε)).mono_set
    Set.Ioo_subset_Ioc_self

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrableOn_log_div_sub
#print axioms RHLean.ExplicitFormula.integrableOn_log_div_add

end

end Inline_ExplicitFormula_RH92

section Inline_ExplicitFormula_RH93










noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem integrableOn_boundaryKernel {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    IntegrableOn (fun x : ℝ => Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0))
      (Set.Ioo (-a) a) volume := by
  set B : ℝ → ℝ := fun x => Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
    with hB
  have h1 : IntegrableOn B (Set.Ioo (a - ε) a) volume := by
    refine (integrableOn_log_div_sub hε).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Set.mem_Ioo] at hx
    change Real.log (ε / (a - x))
      = Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [abs_of_nonneg hx0, if_pos (by linarith [hx.2]), mul_one]
  have h2 : IntegrableOn B (Set.Ioo (-a) (-a + ε)) volume := by
    refine (integrableOn_log_div_add hε).congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Set.mem_Ioo] at hx
    change Real.log (ε / (a + x))
      = Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
    have hx0 : x ≤ 0 := by linarith [hx.2]
    rw [abs_of_nonpos hx0, sub_neg_eq_add, if_pos (by linarith [hx.2]), mul_one]
  have h0 : IntegrableOn B (Set.Icc (-a + ε) (a - ε)) volume := by
    refine (integrableOn_const (s := Set.Icc (-a + ε) (a - ε)) (C := (0 : ℝ)) (hs := ?_)).congr ?_
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Set.mem_Icc] at hx
      change (0 : ℝ) = Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)
      rw [if_neg, mul_zero]
      rw [not_lt]
      rcases le_total 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0]
        linarith [hx.2]
      · rw [abs_of_nonpos hx0]
        linarith [hx.1]
  have hD : Set.Ioo (-a) a
      = Set.Ioo (-a) (-a + ε) ∪ (Set.Icc (-a + ε) (a - ε) ∪ Set.Ioo (a - ε) a) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_Ioo] at hx
      rcases lt_trichotomy x (-a + ε) with h | h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr (Or.inl (Set.mem_Icc.mpr ⟨le_of_eq h.symm, by linarith [hx.2]⟩))
      · rcases lt_trichotomy x (a - ε) with h2 | h2 | h2
        · exact Or.inr (Or.inl (Set.mem_Icc.mpr ⟨le_of_lt h, le_of_lt h2⟩))
        · exact Or.inr (Or.inl (Set.mem_Icc.mpr ⟨le_of_lt h, le_of_eq h2⟩))
        · exact Or.inr (Or.inr ⟨h2, hx.2⟩)
    · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
      · exact ⟨h1', by linarith⟩
      · exact ⟨by linarith [h1'], by linarith [h2']⟩
      · exact ⟨by linarith [h1'], h2'⟩
  rw [hD]
  exact (h2.union (h0.union h1))

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integrableOn_boundaryKernel

end

end Inline_ExplicitFormula_RH93

section Inline_ExplicitFormula_RH94




















noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula



noncomputable def boundaryKernel (a ε : ℝ) : ℝ → ℝ :=
  fun x => Real.log (ε / (a - |x|)) * (if a - |x| < ε then 1 else 0)


theorem boundaryKernel_measurable (a ε : ℝ) : Measurable (boundaryKernel a ε) := by
  unfold boundaryKernel
  have hsub : Measurable (fun x : ℝ => a - |x|) :=
    ((continuous_const : Continuous fun _ : ℝ => a).sub continuous_abs).measurable
  have hset : MeasurableSet {x : ℝ | a - |x| < ε} :=
    measurableSet_lt hsub (measurable_const : Measurable fun _ : ℝ => ε)
  exact ((measurable_const : Measurable fun _ : ℝ => ε).div hsub).log.mul
    ((measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).indicator hset)


theorem boundaryKernel_nonneg_of_abs_lt {a x ε : ℝ} (hx : |x| < a) (hε : 0 < ε) :
    0 ≤ boundaryKernel a ε x := by
  simpa only [boundaryKernel] using boundaryKernel_nonneg hx hε


theorem integrableOn_boundaryKernel_mul_sq {a ε : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (hε : 0 < ε) (hεa : ε < a) :
    IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * boundaryKernel a ε x)
      (Set.Ioo (-a) a) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hsq : ∀ x : ℝ, ‖f x‖ ^ 2 ≤ B ^ 2 := fun x => by
    nlinarith [hB x, hB0, norm_nonneg (f x)]
  have hfm : Measurable (fun x : ℝ => ‖f x‖) := (hf.1.1.continuous.norm).measurable
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ‖f x‖ ^ 2 * boundaryKernel a ε x)
      (volume.restrict (Set.Ioo (-a) a)) :=
    ((hfm.pow_const 2).mul (boundaryKernel_measurable a ε)).aestronglyMeasurable
  have hgnn : ∀ x ∈ Set.Ioo (-a) a, 0 ≤ boundaryKernel a ε x := by
    intro x hx
    refine boundaryKernel_nonneg_of_abs_lt ?_ hε
    rw [abs_lt]
    exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-a) a)),
      ‖‖f x‖ ^ 2 * boundaryKernel a ε x‖ ≤ B ^ 2 * boundaryKernel a ε x := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hgnn x hx)]
    exact mul_le_mul_of_nonneg_right (hsq x) (hgnn x hx)
  have hBint : IntegrableOn (fun x : ℝ => B ^ 2 * boundaryKernel a ε x)
      (Set.Ioo (-a) a) volume := by
    change Integrable (fun x : ℝ => B ^ 2 * boundaryKernel a ε x)
      (volume.restrict (Set.Ioo (-a) a))
    simpa only [boundaryKernel] using
      (integrableOn_boundaryKernel hε hεa).const_mul (B ^ 2)
  exact hBint.mono' hmeas hbound





theorem abs_boundaryError_le {a ε B : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (hε : 0 < ε) (hεa : ε < a)
    (hB0 : 0 ≤ B) (hB : ∀ x : ℝ, ‖f x‖ ≤ B) :
    |(1 / 2) * (∫ x in Set.Ioo (-a) a,
        ‖f x‖ ^ 2 * boundaryKernel a ε x)| ≤ B ^ 2 * ε := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  have hD : MeasurableSet D := measurableSet_Ioo
  have hsq : ∀ x : ℝ, ‖f x‖ ^ 2 ≤ B ^ 2 := fun x => by
    nlinarith [hB x, hB0, norm_nonneg (f x)]
  have hfgm : Measurable (fun x : ℝ => ‖f x‖ ^ 2 * boundaryKernel a ε x) :=
    (((hf.1.1.continuous.norm).measurable).pow_const 2).mul
      (boundaryKernel_measurable a ε)
  have hgnn : ∀ x ∈ D, 0 ≤ boundaryKernel a ε x := by
    intro x hx
    refine boundaryKernel_nonneg_of_abs_lt ?_ hε
    rw [abs_lt]
    exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
  have hbound : ∀ᵐ x ∂(volume.restrict D),
      ‖‖f x‖ ^ 2 * boundaryKernel a ε x‖ ≤ B ^ 2 * boundaryKernel a ε x := by
    filter_upwards [self_mem_ae_restrict hD] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (hgnn x hx)]
    exact mul_le_mul_of_nonneg_right (hsq x) (hgnn x hx)
  have hintfg : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * boundaryKernel a ε x) D volume := by
    rw [hDdef]
    exact integrableOn_boundaryKernel_mul_sq hf hε hεa
  have hintB : IntegrableOn (fun x : ℝ => B ^ 2 * boundaryKernel a ε x) D volume := by
    change Integrable (fun x : ℝ => B ^ 2 * boundaryKernel a ε x) (volume.restrict D)
    rw [hDdef]
    simpa only [boundaryKernel] using
      (integrableOn_boundaryKernel hε hεa).const_mul (B ^ 2)
  have h1 : |∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x|
      ≤ ∫ x in D, |‖f x‖ ^ 2 * boundaryKernel a ε x| :=
    abs_integral_le_integral_abs
  have h2 : (∫ x in D, |‖f x‖ ^ 2 * boundaryKernel a ε x|)
      = ∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x := by
    apply setIntegral_congr_fun hD
    intro x hx
    change |‖f x‖ ^ 2 * boundaryKernel a ε x| = ‖f x‖ ^ 2 * boundaryKernel a ε x
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hgnn x hx))]
  have h3 : (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x)
      ≤ ∫ x in D, B ^ 2 * boundaryKernel a ε x :=
    setIntegral_mono_on hintfg hintB hD
      (fun x hx => mul_le_mul_of_nonneg_right (hsq x) (hgnn x hx))
  have h4 : (∫ x in D, B ^ 2 * boundaryKernel a ε x) = B ^ 2 * (2 * ε) := by
    rw [integral_const_mul]
    congr 1
    have h := integral_boundaryKernel hε hεa
    simpa only [hDdef, boundaryKernel] using h
  have habs : |(1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x)|
      = (1 / 2) * |∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [habs]
  calc (1 / 2) * |∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x|
      ≤ (1 / 2) * (∫ x in D, |‖f x‖ ^ 2 * boundaryKernel a ε x|) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x) := by rw [h2]
    _ ≤ (1 / 2) * (∫ x in D, B ^ 2 * boundaryKernel a ε x) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ = (1 / 2) * (B ^ 2 * (2 * ε)) := by rw [h4]
    _ = B ^ 2 * ε := by ring



theorem tendsto_boundaryError {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (ha : 0 < a) :
    Tendsto (fun ε : ℝ => (1 / 2) * (∫ x in Set.Ioo (-a) a,
        ‖f x‖ ^ 2 * boundaryKernel a ε x)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hlim : Tendsto (fun ε : ℝ => B ^ 2 * ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun _ : ℝ => B ^ 2) (𝓝[>] 0) (𝓝 (B ^ 2)) := tendsto_const_nhds
    have h2 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    simpa only [mul_zero] using h1.mul h2
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioo ?_)
    intro x hx
    refine mul_nonneg (sq_nonneg _) ?_
    refine boundaryKernel_nonneg_of_abs_lt ?_ hε
    rw [abs_lt]
    exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ha] with ε hε hεa
    exact le_trans (le_abs_self _) (abs_boundaryError_le hf hε hεa.2 hB0 hB)

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.boundaryKernel_measurable
#print axioms RHLean.ExplicitFormula.boundaryKernel_nonneg_of_abs_lt
#print axioms RHLean.ExplicitFormula.integrableOn_boundaryKernel_mul_sq
#print axioms RHLean.ExplicitFormula.abs_boundaryError_le
#print axioms RHLean.ExplicitFormula.tendsto_boundaryError

end

end Inline_ExplicitFormula_RH94

section Inline_ExplicitFormula_RH81














noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


theorem truncKernel_fubini {a ε : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (hε : 0 < ε) :
    (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2 ∂(volume.prod volume))
      = ∫ x in Set.Ioo (-a) a,
          ‖f x‖ ^ 2 * (∫ y in Set.Ioo (-a) a, truncKernel ε (x - y)) := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hmeas : Measurable (fun z : ℝ × ℝ => truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2) :=
    ((measurable_truncKernel ε).comp (continuous_fst.sub continuous_snd).measurable).mul
      (((hf.1.1.continuous.comp continuous_fst).norm.pow 2).measurable)
  have hInt : IntegrableOn (fun z : ℝ × ℝ => truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2)
      (D ×ˢ D) volume := by
    refine integrableOn_sq_of_bound (C := (1 / ε) * B ^ 2) (by positivity) hmeas
      (fun z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |truncKernel ε (z.1 - z.2)| ≤ 1 / ε := by
      rw [← Real.norm_eq_abs]
      exact truncKernel_bound hε _
    have h2 : |‖f z.1‖ ^ 2| ≤ B ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [hB z.1, hB0, norm_nonneg (f z.1)]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  rw [setIntegral_prod _ hInt]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x _
  change (∫ y in Set.Ioo (-a) a, truncKernel ε (x - y) * ‖f x‖ ^ 2)
      = ‖f x‖ ^ 2 * ∫ y in Set.Ioo (-a) a, truncKernel ε (x - y)
  rw [integral_mul_const]
  ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncKernel_fubini

end

end Inline_ExplicitFormula_RH81

section Inline_ExplicitFormula_RH95























noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




theorem intervalIntegrable_log_sub {a : ℝ} :
    IntervalIntegrable (fun x : ℝ => Real.log (a - x)) volume (-a) a := by
  have h := ((intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 2 * a)).comp_sub_left
    a).symm
  have h1 : a - 2 * a = -a := by ring
  have h2 : a - 0 = a := by ring
  rw [h1, h2] at h
  exact h


theorem intervalIntegrable_log_add {a : ℝ} :
    IntervalIntegrable (fun x : ℝ => Real.log (a + x)) volume (-a) a := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 2 * a)).comp_sub_right (-a)
  have h1 : (fun x : ℝ => Real.log (x - -a)) = fun x : ℝ => Real.log (a + x) := by
    funext x
    rw [sub_neg_eq_add, add_comm]
  have h2 : (0 : ℝ) + -a = -a := by ring
  have h3 : 2 * a + -a = a := by ring
  rw [h1, h2, h3] at h
  exact h




theorem integrableOn_log_sub_mul_sq {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.log (a - x) * ‖f x‖ ^ 2)
      (Set.Ioo (-a) a) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hsq : ∀ x : ℝ, ‖f x‖ ^ 2 ≤ B ^ 2 := fun x => by
    nlinarith [hB x, hB0, norm_nonneg (f x)]
  have hint : IntegrableOn (fun x : ℝ => Real.log (a - x)) (Set.Ioo (-a) a) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith : -a ≤ a)).mp intervalIntegrable_log_sub).mono_set
      Set.Ioo_subset_Ioc_self
  have hmaj : IntegrableOn (fun x : ℝ => B ^ 2 * |Real.log (a - x)|)
      (Set.Ioo (-a) a) volume :=
    hint.abs.const_mul (B ^ 2)
  have hlogm : Measurable (fun x : ℝ => Real.log (a - x)) :=
    ((continuous_const : Continuous fun _ : ℝ => a).sub continuous_id).measurable.log
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.log (a - x) * ‖f x‖ ^ 2)
      (volume.restrict (Set.Ioo (-a) a)) :=
    (hlogm.mul ((((hf.1.1.continuous.norm).measurable).pow_const 2))).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-a) a)),
      ‖Real.log (a - x) * ‖f x‖ ^ 2‖ ≤ B ^ 2 * |Real.log (a - x)| := by
    filter_upwards with x
    have h2 : |‖f x‖ ^ 2| = ‖f x‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, h2]
    calc |Real.log (a - x)| * ‖f x‖ ^ 2 ≤ |Real.log (a - x)| * B ^ 2 :=
          mul_le_mul_of_nonneg_left (hsq x) (abs_nonneg _)
      _ = B ^ 2 * |Real.log (a - x)| := by ring
  exact hmaj.mono' hmeas hbound


theorem integrableOn_log_add_mul_sq {a : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.log (a + x) * ‖f x‖ ^ 2)
      (Set.Ioo (-a) a) volume := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hsq : ∀ x : ℝ, ‖f x‖ ^ 2 ≤ B ^ 2 := fun x => by
    nlinarith [hB x, hB0, norm_nonneg (f x)]
  have hint : IntegrableOn (fun x : ℝ => Real.log (a + x)) (Set.Ioo (-a) a) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith : -a ≤ a)).mp intervalIntegrable_log_add).mono_set
      Set.Ioo_subset_Ioc_self
  have hmaj : IntegrableOn (fun x : ℝ => B ^ 2 * |Real.log (a + x)|)
      (Set.Ioo (-a) a) volume :=
    hint.abs.const_mul (B ^ 2)
  have hlogm : Measurable (fun x : ℝ => Real.log (a + x)) :=
    (((continuous_const : Continuous fun _ : ℝ => a).add continuous_id)).measurable.log
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.log (a + x) * ‖f x‖ ^ 2)
      (volume.restrict (Set.Ioo (-a) a)) :=
    (hlogm.mul ((((hf.1.1.continuous.norm).measurable).pow_const 2))).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioo (-a) a)),
      ‖Real.log (a + x) * ‖f x‖ ^ 2‖ ≤ B ^ 2 * |Real.log (a + x)| := by
    filter_upwards with x
    have h2 : |‖f x‖ ^ 2| = ‖f x‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, h2]
    calc |Real.log (a + x)| * ‖f x‖ ^ 2 ≤ |Real.log (a + x)| * B ^ 2 :=
          mul_le_mul_of_nonneg_left (hsq x) (abs_nonneg _)
      _ = B ^ 2 * |Real.log (a + x)| := by ring
  exact hmaj.mono' hmeas hbound


theorem integrableOn_endpointPotential_mul_sq {a : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => endpointPotential a x * ‖f x‖ ^ 2)
      (Set.Ioo (-a) a) volume := by
  have hsub := integrableOn_log_sub_mul_sq hf ha
  have hadd := integrableOn_log_add_mul_sq hf ha
  have hsum : IntegrableOn
      (fun x : ℝ => (-(1 / 2)) *
        (Real.log (a - x) * ‖f x‖ ^ 2 + Real.log (a + x) * ‖f x‖ ^ 2))
      (Set.Ioo (-a) a) volume :=
    (hsub.add hadd).const_mul (-(1 / 2))
  refine hsum.congr_fun ?_ measurableSet_Ioo
  intro x hx
  have hx1 : 0 < a - x := by linarith [(Set.mem_Ioo.mp hx).2]
  have hx2 : 0 < a + x := by linarith [(Set.mem_Ioo.mp hx).1]
  change -(1 / 2) * (Real.log (a - x) * ‖f x‖ ^ 2 + Real.log (a + x) * ‖f x‖ ^ 2)
    = endpointPotential a x * ‖f x‖ ^ 2
  rw [endpointPotential_eq,
    show a ^ 2 - x ^ 2 = (a - x) * (a + x) by ring,
    Real.log_mul (ne_of_gt hx1) (ne_of_gt hx2)]
  ring


theorem endpointPotential_neg_eq_logSum {a x : ℝ} (hx : |x| < a) :
    -endpointPotential a x = (1 / 2) * (Real.log (a - x) + Real.log (a + x)) := by
  have hx1 : 0 < a - x := by linarith [(abs_lt.mp hx).2]
  have hx2 : 0 < a + x := by linarith [(abs_lt.mp hx).1]
  rw [endpointPotential_eq,
    show a ^ 2 - x ^ 2 = (a - x) * (a + x) by ring,
    Real.log_mul (ne_of_gt hx1) (ne_of_gt hx2)]
  ring


theorem autocorr_zero_re_eq_integral_sq {a : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    (autocorr f 0).re = ∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 := by
  rw [autocorr_zero_re hf.1]
  apply integral_eq_setIntegral_of_forall_eq_zero_of_notMem measurableSet_Ioo
  intro x hx
  have hx0 : f x = 0 := by
    by_contra h
    exact hx (hf.2 (Function.mem_support.mpr h))
  rw [hx0]
  simp








theorem truncDiagonal_eq {a ε : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (hε : 0 < ε) (hεa : ε < a) :
    (1 / 2) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2 ∂(volume.prod volume))
      = -potentialForm a f - Real.log ε * (autocorr f 0).re
        + (1 / 2) * (∫ x in Set.Ioo (-a) a,
            ‖f x‖ ^ 2 * boundaryKernel a ε x) := by
  set D : Set ℝ := Set.Ioo (-a) a with hDdef
  set I : ℝ → ℝ := fun x =>
    (∫ y in (-a)..(x - ε), (x - y)⁻¹) + (∫ y in (x + ε)..a, (y - x)⁻¹) with hIdef
  set W : ℝ → ℝ := fun x => (1 / 2) * (Real.log (a - x) + Real.log (a + x)) with hWdef
  have hD : MeasurableSet D := measurableSet_Ioo
  have ha : 0 < a := lt_trans hε hεa
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_of_localizedCore hf
  have hsq : ∀ x : ℝ, ‖f x‖ ^ 2 ≤ B ^ 2 := fun x => by
    nlinarith [hB x, hB0, norm_nonneg (f x)]
  have hfub : (∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2
        ∂(volume.prod volume))
      = ∫ x in D, ‖f x‖ ^ 2 * (∫ y in D, truncKernel ε (x - y)) :=
    truncKernel_fubini hf hε
  have hpoint : ∀ x ∈ D,
      (1 / 2) * (‖f x‖ ^ 2 * (∫ y in D, truncKernel ε (x - y)))
        = ‖f x‖ ^ 2 * (W x - Real.log ε)
          + (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x) := by
    intro x hx
    have hxA : |x| < a := by
      rw [abs_lt]
      exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
    have hSx : (∫ y in D, truncKernel ε (x - y)) = I x + boundaryKernel a ε x :=
      truncKernel_self_integral_eq_single hxA hε hεa
    have hIx : (1 / 2) * I x = W x - Real.log ε := by
      have h85 := truncDiagonal_rhs_potential hxA hε
      have hWx : W x = -endpointPotential a x := by
        change (1 / 2) * (Real.log (a - x) + Real.log (a + x)) = -endpointPotential a x
        exact (endpointPotential_neg_eq_logSum hxA).symm
      rw [hWx]
      change (1 / 2) * ((∫ y in (-a)..(x - ε), (x - y)⁻¹)
          + (∫ y in (x + ε)..a, (y - x)⁻¹)) = -endpointPotential a x - Real.log ε
      linarith [h85]
    rw [hSx, ← hIx]
    ring
  have hsq_int : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2) D volume := by
    refine Measure.integrableOn_of_bounded (s_finite := ?_) (f_mble := ?_) (M := B ^ 2) ?_
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · exact ((((hf.1.1.continuous.norm).measurable).pow_const 2)).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsq x
  have hVint : IntegrableOn (fun x : ℝ => endpointPotential a x * ‖f x‖ ^ 2) D volume := by
    rw [hDdef]
    exact integrableOn_endpointPotential_mul_sq hf ha
  have hWint : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * W x) D volume := by
    refine hVint.neg.congr_fun ?_ hD
    intro x hx
    have hxA : |x| < a := by
      rw [abs_lt]
      exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
    have hWx : W x = -endpointPotential a x := by
      change (1 / 2) * (Real.log (a - x) + Real.log (a + x)) = -endpointPotential a x
      exact (endpointPotential_neg_eq_logSum hxA).symm
    change -(endpointPotential a x * ‖f x‖ ^ 2) = ‖f x‖ ^ 2 * W x
    rw [hWx]
    ring
  have hlogint : IntegrableOn (fun x : ℝ => (-Real.log ε) * ‖f x‖ ^ 2) D volume :=
    hsq_int.const_mul (-Real.log ε)
  have hAint : IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * (W x - Real.log ε)) D volume := by
    refine (hWint.add hlogint).congr_fun ?_ hD
    intro x _
    change ‖f x‖ ^ 2 * W x + (-Real.log ε) * ‖f x‖ ^ 2
      = ‖f x‖ ^ 2 * (W x - Real.log ε)
    ring
  have hBint : IntegrableOn
      (fun x : ℝ => (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x)) D volume := by
    exact (integrableOn_boundaryKernel_mul_sq hf hε hεa).const_mul (1 / 2)
  have hsplit : (∫ x in D, (‖f x‖ ^ 2 * (W x - Real.log ε)
        + (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x)))
      = (∫ x in D, ‖f x‖ ^ 2 * (W x - Real.log ε))
        + (∫ x in D, (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x)) :=
    integral_add hAint hBint
  have hWval : (∫ x in D, ‖f x‖ ^ 2 * W x) = -potentialForm a f := by
    have hpt3 : ∀ x ∈ D, ‖f x‖ ^ 2 * W x = -(endpointPotential a x * ‖f x‖ ^ 2) := by
      intro x hx
      have hxA : |x| < a := by
        rw [abs_lt]
        exact ⟨(Set.mem_Ioo.mp hx).1, (Set.mem_Ioo.mp hx).2⟩
      have hWx : W x = -endpointPotential a x := by
        change (1 / 2) * (Real.log (a - x) + Real.log (a + x)) = -endpointPotential a x
        exact (endpointPotential_neg_eq_logSum hxA).symm
      rw [hWx]
      ring
    rw [setIntegral_congr_fun hD hpt3]
    rw [integral_neg (f := fun x : ℝ => endpointPotential a x * ‖f x‖ ^ 2)]
    have hpot : potentialForm a f = ∫ x in D, endpointPotential a x * ‖f x‖ ^ 2 := rfl
    rw [hpot]
  have hWeval : (∫ x in D, ‖f x‖ ^ 2 * (W x - Real.log ε))
      = -potentialForm a f - Real.log ε * (autocorr f 0).re := by
    have hpt2 : ∀ x ∈ D, ‖f x‖ ^ 2 * (W x - Real.log ε)
        = ‖f x‖ ^ 2 * W x + (-Real.log ε) * ‖f x‖ ^ 2 := by
      intro x _
      ring
    rw [setIntegral_congr_fun hD hpt2]
    rw [integral_add hWint hlogint]
    rw [hWval]
    rw [integral_const_mul (-Real.log ε) (fun x : ℝ => ‖f x‖ ^ 2)]
    rw [← autocorr_zero_re_eq_integral_sq hf]
    ring
  have hBeval : (∫ x in D, (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x))
      = (1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x) := by
    rw [integral_const_mul]
  calc (1 / 2) * (∫ z in D ×ˢ D, truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2
        ∂(volume.prod volume))
      = (1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * (∫ y in D, truncKernel ε (x - y))) := by
        rw [hfub]
    _ = ∫ x in D, (1 / 2) * (‖f x‖ ^ 2 * (∫ y in D, truncKernel ε (x - y))) := by
        rw [← integral_const_mul (1 / 2)
          (fun x : ℝ => ‖f x‖ ^ 2 * (∫ y in D, truncKernel ε (x - y)))]
    _ = ∫ x in D, (‖f x‖ ^ 2 * (W x - Real.log ε)
          + (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x)) :=
        setIntegral_congr_fun hD hpoint
    _ = (∫ x in D, ‖f x‖ ^ 2 * (W x - Real.log ε))
          + (∫ x in D, (1 / 2) * (‖f x‖ ^ 2 * boundaryKernel a ε x)) := hsplit
    _ = (-potentialForm a f - Real.log ε * (autocorr f 0).re)
          + (1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x) := by
        rw [hWeval, hBeval]
    _ = -potentialForm a f - Real.log ε * (autocorr f 0).re
          + (1 / 2) * (∫ x in D, ‖f x‖ ^ 2 * boundaryKernel a ε x) := by ring

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.intervalIntegrable_log_sub
#print axioms RHLean.ExplicitFormula.intervalIntegrable_log_add
#print axioms RHLean.ExplicitFormula.integrableOn_log_sub_mul_sq
#print axioms RHLean.ExplicitFormula.integrableOn_log_add_mul_sq
#print axioms RHLean.ExplicitFormula.integrableOn_endpointPotential_mul_sq
#print axioms RHLean.ExplicitFormula.endpointPotential_neg_eq_logSum
#print axioms RHLean.ExplicitFormula.autocorr_zero_re_eq_integral_sq
#print axioms RHLean.ExplicitFormula.truncDiagonal_eq

end

end Inline_ExplicitFormula_RH95

section Inline_ExplicitFormula_RH96

























noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula





theorem truncKernel_autocorr_swap {a ε : ℝ} {f : ℝ → ℂ} (hf : f ∈ localizedCore a)
    (hε : 0 < ε) :
    (∫ u : ℝ, truncKernel ε u * (autocorr f u).re)
      = ∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re := by
  rw [integral_truncKernel_mul_autocorr_eq' hf hε]
  exact (setIntegral_prod_swap (μ := volume) (ν := volume)
    (s := Set.Ioo (-a) a) (t := Set.Ioo (-a) a)
    (f := fun z : ℝ × ℝ =>
      truncKernel ε (z.2 - z.1) * (f z.2 * star (f z.1)).re)).symm





theorem integrableOn_nearDiagonal_le {a ε : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (hε : 0 < ε) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (if |p.1 - p.2| ≤ ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) volume := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := normSq_div_le_lipschitz hf
  have hfin : volume (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) ≠ ⊤ := by
    have hc : IsCompact (Set.Icc (-a) a ×ˢ Set.Icc (-a) a) :=
      (isCompact_Icc (a := -a) (b := a)).prod (isCompact_Icc (a := -a) (b := a))
    exact ne_of_lt (lt_of_le_of_lt
      (measure_mono fun p hp => Set.mem_prod.mpr
        ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
      hc.measure_lt_top)
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if |p.1 - p.2| ≤ ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0)) volume := by
    have hm1 : Measurable (fun p : ℝ × ℝ => ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2|) := by
      refine Measurable.div ?_ ?_
      · exact (((hf.1.1.continuous.comp continuous_fst).sub
          (hf.1.1.continuous.comp continuous_snd)).norm.pow 2).measurable
      · exact ((continuous_fst.sub continuous_snd).abs).measurable
    exact (Measurable.ite (((continuous_fst.sub continuous_snd).abs.measurable)
      measurableSet_Iic) hm1 measurable_const).aestronglyMeasurable
  refine Measure.integrableOn_of_bounded hfin hmeas (M := C₁ ^ 2 * ε) ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  by_cases h : |p.1 - p.2| ≤ ε
  · rw [if_pos h, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))]
    calc ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| ≤ C₁ ^ 2 * |p.1 - p.2| :=
          hC₁ p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 ⟨hp.2.1.le, hp.2.2.le⟩
      _ ≤ C₁ ^ 2 * ε := mul_le_mul_of_nonneg_left h (by positivity)
  · rw [if_neg h, norm_zero]
    positivity



theorem integrableOn_nearDiagonal_lt {a ε : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) (hε : 0 < ε) :
    IntegrableOn (fun p : ℝ × ℝ =>
        (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a) volume := by
  have hle := integrableOn_nearDiagonal_le ha hf hε
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (if |p.1 - p.2| < ε then ‖f p.1 - f p.2‖ ^ 2 / |p.1 - p.2| else 0))
      (volume.restrict (Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a)) := by
    refine (Measurable.ite (((continuous_fst.sub continuous_snd).abs.measurable)
      measurableSet_Iio) ?_ measurable_const).aestronglyMeasurable
    exact Measurable.div
      ((((hf.1.1.continuous.comp continuous_fst).sub
        (hf.1.1.continuous.comp continuous_snd)).norm.pow 2).measurable)
      (((continuous_fst.sub continuous_snd).abs).measurable)
  refine hle.mono' hmeas ?_
  filter_upwards with p
  by_cases h : |p.1 - p.2| < ε
  · rw [if_pos h, if_pos (le_of_lt h)]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (abs_nonneg _))]
  · rw [if_neg h, norm_zero]
    by_cases h2 : |p.1 - p.2| ≤ ε
    · rw [if_pos h2]
      exact div_nonneg (sq_nonneg _) (abs_nonneg _)
    · rw [if_neg h2]



theorem tendsto_nearDiagonal_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    Tendsto (fun ε : ℝ => (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h2e : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝 (2 * 0)) :=
        tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
      simpa using h0
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      exact Set.mem_Ioi.mpr (by linarith)
  have hlt : Tendsto (fun ε : ℝ => (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
      (if |z.1 - z.2| < 2 * ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_nearDiagonal ha hf).comp h2e
  refine squeeze_zero' ?_ ?_ hlt
  · filter_upwards with ε
    refine mul_nonneg (by norm_num)
      (setIntegral_nonneg (measurableSet_Ioo.prod measurableSet_Ioo) (fun z _ => ?_))
    by_cases h : |z.1 - z.2| ≤ ε
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Set.mem_Ioi] at hε
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine setIntegral_mono (integrableOn_nearDiagonal_le ha hf hε)
      (integrableOn_nearDiagonal_lt ha hf (by linarith : (0 : ℝ) < 2 * ε))
      (fun z => ?_)
    by_cases h : |z.1 - z.2| ≤ ε
    · rw [if_pos h, if_pos (by linarith : |z.1 - z.2| < 2 * ε)]
    · rw [if_neg h]
      by_cases h2 : |z.1 - z.2| < 2 * ε
      · rw [if_pos h2]
        exact div_nonneg (sq_nonneg _) (abs_nonneg _)
      · rw [if_neg h2]




theorem positionFormEqAt_of_pos {a : ℝ} (ha : 0 < a) : PositionFormEqAt a := by
  intro f hf R hR hsupp

  have h76 : Tendsto (fun ε : ℝ => ∫ u in Set.Icc (-R) R,
        truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ u in Set.Icc (-R) R,
        (|u|)⁻¹ * ((autocorr f u).re - (autocorr f 0).re))) :=
    tendsto_truncKernel_mul_autocorr_sub hf.1 R

  obtain ⟨C, hC0, hC⟩ := exists_autocorr_re_sub_bound hf.1
  obtain ⟨B', hB'0, hB'⟩ := exists_autocorr_re_bound hf.1
  have hint : ∀ {c d : ℝ}, c ≤ d → IntervalIntegrable
      (fun u : ℝ => (|u|)⁻¹ * ((autocorr f u).re - (autocorr f 0).re)) volume c d := by
    intro c d hcd
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd]
    refine Measure.integrableOn_of_bounded (s_finite := ?_) (f_mble := ?_)
      (M := max C (2 * B')) ?_
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    · exact ((continuous_abs.measurable.inv).mul
        ((Complex.continuous_re.measurable.comp
          (contDiff_autocorr hf.1).continuous.measurable).sub
            measurable_const)).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (abs_nonneg u))]
      by_cases hu : u = 0
      · rw [hu]
        simp only [sub_self, abs_zero, inv_zero, zero_mul]
        exact le_trans (by linarith [hB'0] : (0 : ℝ) ≤ 2 * B') (le_max_right _ _)
      · have hupos : 0 < |u| := abs_pos.mpr hu
        have hM : |(autocorr f u).re - (autocorr f 0).re| ≤ max C (2 * B') * |u| := by
          by_cases hle : |u| ≤ 1
          · exact le_trans (hC u hle)
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
          · have h2 : |(autocorr f u).re - (autocorr f 0).re| ≤ B' + B' := by
              have h := abs_sub_le ((autocorr f u).re) 0 ((autocorr f 0).re)
              rw [sub_zero, zero_sub, abs_neg] at h
              linarith [h, hB' u, hB' 0]
            calc |(autocorr f u).re - (autocorr f 0).re| ≤ B' + B' := h2
              _ = 2 * B' := by ring
              _ ≤ 2 * B' * |u| := by nlinarith [hle, hB'0]
              _ ≤ max C (2 * B') * |u| :=
                  mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
        rw [← div_eq_inv_mul]
        exact (div_le_iff₀ hupos).mpr hM
  have heven : ∀ u : ℝ,
      (autocorr f (-u)).re - (autocorr f 0).re = (autocorr f u).re - (autocorr f 0).re := by
    intro u
    rw [autocorr_re_even hf.1 u]
  have h78 : (∫ u in Set.Icc (-R) R,
        (|u|)⁻¹ * ((autocorr f u).re - (autocorr f 0).re))
      = 2 * ∫ u in (0 : ℝ)..R, ((autocorr f u).re - (autocorr f 0).re) / u :=
    integral_inv_abs_mul_even heven hR.le (hint (by linarith : -R ≤ 0)) (hint hR.le)

  have hT1 : Tendsto (fun ε : ℝ => -Real.log R * (autocorr f 0).re
        - (1 / 2) * (∫ u in Set.Icc (-R) R,
            truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Real.log R * (autocorr f 0).re
        - (∫ u in (0 : ℝ)..R, ((autocorr f u).re - (autocorr f 0).re) / u))) := by
    have hconstR : Tendsto (fun _ : ℝ => -Real.log R * (autocorr f 0).re)
        (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log R * (autocorr f 0).re)) := tendsto_const_nhds
    have h := hconstR.sub (h76.const_mul (1 / 2))
    rw [h78] at h
    convert h using 1
    ring

  have hE : Tendsto (fun ε : ℝ => (1 / 2) * (∫ x in Set.Ioo (-a) a,
        ‖f x‖ ^ 2 * boundaryKernel a ε x)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_boundaryError hf ha

  have hN : Tendsto (fun ε : ℝ => (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
        (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_nearDiagonal_le ha hf

  have hRHSlim : Tendsto (fun ε : ℝ =>
        (-Real.log R * (autocorr f 0).re
          - (1 / 2) * (∫ u in Set.Icc (-R) R,
              truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
          + (1 / 2) * (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 * boundaryKernel a ε x)
          + (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
              (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
                ∂(volume.prod volume))
          - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Real.log R * (autocorr f 0).re
        - (∫ u in (0 : ℝ)..R, ((autocorr f u).re - (autocorr f 0).re) / u)
        - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re))) := by
    have hG : Tendsto (fun _ : ℝ =>
          2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re))
        (𝓝[>] (0 : ℝ))
        (𝓝 (2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re))) :=
      tendsto_const_nhds
    have h := ((hT1.add hE).add hN).sub hG
    rw [Measure.volume_eq_prod] at h
    simpa only [add_zero, zero_add] using h

  have hQ_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      archForm a f + potentialForm a f - gammaForm a f
        = (-Real.log R * (autocorr f 0).re
          - (1 / 2) * (∫ u in Set.Icc (-R) R,
              truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
          + (1 / 2) * (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 * boundaryKernel a ε x)
          + (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
              (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
                ∂(volume.prod volume))
          - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re)) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min ha hR)] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεa : ε < a := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hεR : ε < R := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have h1 := archForm_trunc_split ha hf (ε := ε)
    have h2 := trunc_normSq_split ha hf hε0 (ε := ε)
    have h3a : (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
          truncKernel ε (z.1 - z.2) * (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2)
            ∂(volume.prod volume))
        = (1 / 2) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
            truncKernel ε (z.1 - z.2) * ‖f z.1‖ ^ 2 ∂(volume.prod volume)) :=
      trunc_symm hf hε0 (ε := ε)
    have h4 := truncDiagonal_eq hf hε0 hεa (ε := ε)
    have h5a : (∫ u : ℝ, truncKernel ε u * (autocorr f u).re)
        = ∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
            truncKernel ε (z.1 - z.2) * (f z.1 * star (f z.2)).re
              ∂(volume.prod volume) :=
      truncKernel_autocorr_swap hf hε0 (a := a) (ε := ε)
    have h6 := trunc_kernel_algebra hf.1 hsupp hε0 hεR
    have h7 := gammaForm_eq_two_integral hf hR hsupp
    linarith [h1, h2, h3a, h4, h5a, h6, h7]
  have hconst : Tendsto (fun _ : ℝ => archForm a f + potentialForm a f - gammaForm a f)
      (𝓝[>] (0 : ℝ)) (𝓝 (archForm a f + potentialForm a f - gammaForm a f)) :=
    tendsto_const_nhds
  have hRHSconst : Tendsto (fun ε : ℝ =>
        (-Real.log R * (autocorr f 0).re
          - (1 / 2) * (∫ u in Set.Icc (-R) R,
              truncKernel ε u * ((autocorr f u).re - (autocorr f 0).re))
          + (1 / 2) * (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 * boundaryKernel a ε x)
          + (1 / 4) * (∫ z in Set.Ioo (-a) a ×ˢ Set.Ioo (-a) a,
              (if |z.1 - z.2| ≤ ε then ‖f z.1 - f z.2‖ ^ 2 / |z.1 - z.2| else 0)
                ∂(volume.prod volume))
          - 2 * (∫ u in (0 : ℝ)..R, gammaKernel u * (autocorr f u).re)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (archForm a f + potentialForm a f - gammaForm a f)) := by
    exact hconst.congr' hQ_eq
  exact tendsto_nhds_unique hRHSconst hRHSlim


theorem positionFormEqAt (a : ℝ) : PositionFormEqAt a := by
  intro f hf R hR hsupp
  by_cases ha : 0 < a
  · exact positionFormEqAt_of_pos ha f hf R hR hsupp
  · have hempty : Set.Ioo (-a) a = ∅ := by
      rw [Set.Ioo_eq_empty_iff]
      linarith
    have hf0 : f = 0 := by
      funext x
      by_contra h
      have hx : x ∈ Set.Ioo (-a) a := hf.2 (Function.mem_support.mpr h)
      rw [hempty] at hx
      exact hx
    rw [hf0]
    simp [archForm, potentialForm, gammaForm, autocorr]







theorem weilExplicitFormulaOdd_of_growth_verticalEval
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_growth_verticalEval_positionForm' hgrowth hv
    positionFormEqAt


theorem weilExplicitFormulaOddNonneg_of_growth_verticalEval
    (hgrowth : LogDerivStripGrowth) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_growth_verticalEval_positionForm' hgrowth hv
    positionFormEqAt

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.truncKernel_autocorr_swap
#print axioms RHLean.ExplicitFormula.integrableOn_nearDiagonal_le
#print axioms RHLean.ExplicitFormula.integrableOn_nearDiagonal_lt
#print axioms RHLean.ExplicitFormula.tendsto_nearDiagonal_le
#print axioms RHLean.ExplicitFormula.positionFormEqAt_of_pos
#print axioms RHLean.ExplicitFormula.positionFormEqAt
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_growth_verticalEval

end

end Inline_ExplicitFormula_RH96

section Inline_ExplicitFormula_RH104


























noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators

namespace RHLean.ExplicitFormula






theorem tendsto_horizontal_integral_zero_quad_avoiding
    (hgrowth : LogDerivStripGrowthAvoiding) {h : ℂ → ℂ} (hdecay : StripQuadDecay h)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (havoid : ∀ n : ℕ, ∀ p : XiZero, T n ≠ |(centeredZero p).im|) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
        h ((x : ℂ) + (T n : ℂ) * I)
          * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := hgrowth
  obtain ⟨D, hD0, hD⟩ := hdecay
  have hlim : Tendsto (fun T : ℝ => D * C * (Real.log (1 + T)) ^ 2 / (1 + T) ^ 2)
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := D * C)).mul tendsto_log_sq_div_sq
    have h' : Tendsto (fun T : ℝ => D * C * (Real.log (1 + T)) ^ 2 / (1 + T) ^ 2)
        atTop (𝓝 (D * C * 0)) := by
      refine h.congr' ?_
      filter_upwards with T
      ring
    simpa using h'
  refine squeeze_zero_norm'
    (f := fun n : ℕ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
      h ((x : ℂ) + (T n : ℂ) * I)
        * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))) ?_ (hlim.comp hT)
  filter_upwards [hT.eventually (eventually_ge_atTop (2 : ℝ))] with n hTn
  have hpoint : ∀ x : ℝ, x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2) →
      ‖h ((x : ℂ) + (T n : ℂ) * I)
          * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖
        ≤ D * C * (Real.log (1 + T n)) ^ 2 / (1 + T n) ^ 2 := by
    intro x hx
    have hxI : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
      have hxb : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2) :=
        Set.uIoc_of_le (show (-(1 / 2 : ℝ)) ≤ 1 / 2 by norm_num) ▸ hx
      exact ⟨hxb.1.le, hxb.2⟩
    have hre : |(((x : ℂ) + (T n : ℂ) * I)).re| ≤ (1 : ℝ) / 2 := by
      have hxre : (((x : ℂ) + (T n : ℂ) * I)).re = x := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
      rw [hxre]
      exact abs_le.mpr ⟨hxI.1, hxI.2⟩
    have hdec := hD ((x : ℂ) + (T n : ℂ) * I) hre
    have hlog := hC (T n) hTn (havoid n) x hxI
    have him : T n ≤ ‖(x : ℂ) + (T n : ℂ) * I‖ := by
      have h := abs_im_le_norm ((x : ℂ) + (T n : ℂ) * I)
      have hz : ((x : ℂ) + (T n : ℂ) * I).im = T n := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
          Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      rw [hz, abs_of_nonneg (by linarith)] at h
      exact h
    have hden : (1 + T n) ^ 2 ≤ (1 + ‖(x : ℂ) + (T n : ℂ) * I‖) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc ‖h ((x : ℂ) + (T n : ℂ) * I)
          * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖
        = ‖h ((x : ℂ) + (T n : ℂ) * I)‖
            * ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖ := by
          rw [norm_mul]
      _ ≤ (D / (1 + T n) ^ 2) * (C * (Real.log (1 + T n)) ^ 2) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
          · exact hdec.trans (div_le_div_of_nonneg_left hD0 (by positivity) hden)
          · exact hlog
          · positivity
      _ = D * C * (Real.log (1 + T n)) ^ 2 / (1 + T n) ^ 2 := by ring
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => h ((x : ℂ) + (T n : ℂ) * I)
      * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I)))
    (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := D * C * (Real.log (1 + T n)) ^ 2 / (1 + T n) ^ 2) hpoint
  have hInt' : ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2), h ((x : ℂ) + (T n : ℂ) * I)
      * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖
      ≤ D * C * (Real.log (1 + T n)) ^ 2 / (1 + T n) ^ 2 := by
    have h := hInt
    rw [show |(1 / 2 : ℝ) - (-(1 / 2))| = 1 by norm_num, mul_one] at h
    exact h
  exact hInt'



theorem tendsto_horizontal_integral_autocorr_avoiding
    (hgrowth : LogDerivStripGrowthAvoiding) {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (havoid : ∀ n : ℕ, ∀ p : XiZero, T n ≠ |(centeredZero p).im|) :
    Tendsto (fun n : ℕ => stripTopIntegral (transf (autocorr f)) (T n)) atTop (𝓝 0) :=
  tendsto_horizontal_integral_zero_quad_avoiding hgrowth (transf_autocorr_StripQuadDecay hf)
    hT havoid






theorem tendsto_right_vertical_autocorr_avoiding
    (hgrowth : LogDerivStripGrowthAvoiding) {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hTpos : ∀ n, 0 < T n)
    (hbd : ∀ n, ∀ p : XiZero,
      centeredZero p ∈ rectClosed (stripLeft (T n)) (stripRight (T n)) →
        centeredZero p ∈ rectOpen (stripLeft (T n)) (stripRight (T n))) :
    Tendsto (fun n => stripRightIntegral (transf (autocorr f)) (T n)) atTop
      (𝓝 ((Real.pi : ℂ) * ∑' p : XiZero, transf (autocorr f) (centeredZero p))) := by
  have havoid : ∀ n : ℕ, ∀ p : XiZero, T n ≠ |(centeredZero p).im| :=
    fun n p => admissibleT_ne_abs_im ⟨hT, hTpos, hbd⟩ n p
  set S : ℂ := ∑'
  have hlim := rectangleResidueLimit_autocorr hf hT hTpos hbd
  have htop : Tendsto (fun n => stripTopIntegral (transf (autocorr f)) (T n)) atTop (𝓝 0) :=
    (tendsto_horizontal_integral_autocorr_avoiding hgrowth hf hT havoid)
  have hsum : Tendsto (fun n => rectangleBoundaryIntegral
        (xiLogIntegrand (transf (autocorr f))) (stripLeft (T n)) (stripRight (T n))
      + 2 * stripTopIntegral (transf (autocorr f)) (T n)) atTop
      (𝓝 (2 * (Real.pi : ℂ) * I * S + 2 * 0)) :=
    hlim.add ((tendsto_const_nhds (x := (2 : ℂ))).mul htop)
  have hprod : Tendsto (fun n => 2 * I * stripRightIntegral (transf (autocorr f)) (T n))
      atTop (𝓝 (2 * (Real.pi : ℂ) * I * S)) := by
    have hsum' : Tendsto (fun n => rectangleBoundaryIntegral
          (xiLogIntegrand (transf (autocorr f))) (stripLeft (T n)) (stripRight (T n))
        + 2 * stripTopIntegral (transf (autocorr f)) (T n)) atTop
        (𝓝 (2 * (Real.pi : ℂ) * I * S)) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards with n
    have hdec := stripBoundaryIntegral_autocorr_decomposition hf (T n)
    linear_combination hdec
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hR : Tendsto (fun n => (2 * I * stripRightIntegral (transf (autocorr f)) (T n))
      / (2 * I)) atTop (𝓝 ((2 * (Real.pi : ℂ) * I * S) / (2 * I))) :=
    hprod.div_const (2 * I)
  have hval : (2 * (Real.pi : ℂ) * I * S) / (2 * I) = (Real.pi : ℂ) * S := by
    field_simp
  rw [hval] at hR
  refine hR.congr' ?_
  filter_upwards with n
  field_simp




theorem evenGuinandWeilAt_of_growthAvoiding_verticalEval {a : ℝ}
    (hgrowth : LogDerivStripGrowthAvoiding) (h : VerticalIntegralEvalAt a)
    (hex : ∀ f : ℝ → ℂ, f ∈ localizedCore a → ∃ T : ℕ → ℝ, AdmissibleT T) :
    EvenGuinandWeilAt a := by
  intro ha f hf
  obtain ⟨T, hTtop, hTpos, hbd⟩ := hex f hf
  have h1 := tendsto_right_vertical_autocorr_avoiding hgrowth hf.1 hTtop hTpos hbd
  have h1re : Tendsto (fun n => (stripRightIntegral (transf (autocorr f)) (T n)).re) atTop
      (𝓝 (((Real.pi : ℂ) * ∑' p : XiZero, transf (autocorr f) (centeredZero p)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp h1
  have h3 : ((Real.pi : ℂ) * ∑'
      = Real.pi * (∑' p : XiZero, transf (autocorr f) (centeredZero p)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h3] at h1re
  have h2 := h f hf T ⟨hTtop, hTpos, hbd⟩
  have hEq := tendsto_nhds_unique h1re h2
  exact mul_left_cancel₀ Real.pi_ne_zero hEq






theorem weilExplicitFormulaOdd_of_growthAvoiding_verticalEval
    (hgrowth : LogDerivStripGrowthAvoiding) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_growthAvoiding_verticalEval hgrowth (hv a)
      (fun _ _ => exists_admissibleT))
    positionFormEqAt


theorem weilExplicitFormulaOddNonneg_of_growthAvoiding_verticalEval
    (hgrowth : LogDerivStripGrowthAvoiding) (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_growthAvoiding_verticalEval hgrowth (hv a)
      (fun _ _ => exists_admissibleT))
    positionFormEqAt

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.tendsto_horizontal_integral_zero_quad_avoiding
#print axioms RHLean.ExplicitFormula.tendsto_right_vertical_autocorr_avoiding
#print axioms RHLean.ExplicitFormula.evenGuinandWeilAt_of_growthAvoiding_verticalEval
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_growthAvoiding_verticalEval
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOddNonneg_of_growthAvoiding_verticalEval

end

end Inline_ExplicitFormula_RH104

section Inline_ExplicitFormula_RH108


































noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ContDiff

namespace RHLean.ExplicitFormula




theorem iteratedDeriv_iteratedDeriv (g : ℝ → ℂ) (m N : ℕ) :
    iteratedDeriv m (iteratedDeriv N g) = iteratedDeriv (m + N) g := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      rw [show k + 1 + N = k + N + 1 by omega]
      rw [iteratedDeriv_succ]


theorem contDiff_iteratedDeriv_of {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (N : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv N g) := by
  refine contDiff_iff_iteratedDeriv.mpr ⟨fun m _ => ?_, fun m _ => ?_⟩
  · rw [iteratedDeriv_iteratedDeriv]
    exact hg.continuous_iteratedDeriv (m + N)
      (WithTop.coe_le_coe.mpr (le_top : (((m + N : ℕ)) : ℕ∞) ≤ ⊤))
  · rw [iteratedDeriv_iteratedDeriv]
    exact hg.differentiable_iteratedDeriv (m + N)
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (m + N)))


theorem hasCompactSupport_iteratedDeriv_of {g : ℝ → ℂ} (hs : HasCompactSupport g)
    (N : ℕ) : HasCompactSupport (iteratedDeriv N g) :=
  HasCompactSupport.of_support_subset_isCompact (hs.iteratedFDeriv N).isCompact
    fun x hx => by
      by_contra hnot
      have hFx : iteratedFDeriv ℝ N g x = 0 :=
        not_not.mp fun h => hnot (subset_tsupport _ h)
      exact hx (by rw [iteratedDeriv_eq_iteratedFDeriv, hFx]; simp)



theorem z_pow_mul_transf_eq_iteratedDeriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (N : ℕ) (z : ℂ) :
    z ^ N * transf g z = (-1 : ℂ) ^ N * transf (iteratedDeriv N g) z := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hg1 : ContDiff ℝ 1 (iteratedDeriv n g) := by
        have hle : ContDiff ℝ (n + 1) g :=
          hg.of_le (WithTop.coe_le_coe.mpr (le_top : (((n + 1 : ℕ)) : ℕ∞) ≤ ⊤))
        exact (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hle).2
      have hcs : HasCompactSupport (iteratedDeriv n g) :=
        hasCompactSupport_iteratedDeriv_of hs n
      have h1 := z_mul_transf_eq_neg_transf_deriv hg1 hcs z
      calc z ^ (n + 1) * transf g z
          = z * (z ^ n * transf g z) := by ring
        _ = z * ((-1 : ℂ) ^ n * transf (iteratedDeriv n g) z) := by rw [ih]
        _ = (-1 : ℂ) ^ n * (z * transf (iteratedDeriv n g) z) := by ring
        _ = (-1 : ℂ) ^ n * (-transf (deriv (iteratedDeriv n g)) z) := by rw [h1]
        _ = (-1 : ℂ) ^ (n + 1) * transf (iteratedDeriv (n + 1) g) z := by
              rw [iteratedDeriv_succ, pow_succ]
              ring








theorem exists_transf_autocorr_superPolyDecay {f : ℝ → ℂ} (hf : f ∈ oddCore)
    (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, |z.re| ≤ 1 / 2 →
      ‖transf (autocorr f) z‖ ≤ D / (1 + ‖z‖) ^ N := by
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    exists_transf_norm_mul_le (contDiff_autocorr hf) (hasCompactSupport_autocorr hf)
  obtain ⟨CN, hCN0, hCN⟩ := exists_transf_norm_mul_le
    (contDiff_iteratedDeriv_of (contDiff_autocorr hf) N)
    (hasCompactSupport_iteratedDeriv_of (hasCompactSupport_autocorr hf) N)
  refine ⟨2 ^ N * max C₀ CN, by positivity, fun z hz => ?_⟩
  by_cases hz1 : ‖z‖ ≤ 1
  ·
    have h1 : ‖transf (autocorr f) z‖ ≤ C₀ := by
      have h0 := hC₀ z hz
      have h2 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
      nlinarith [norm_nonneg (transf (autocorr f) z)]
    have h2 : (1 + ‖z‖) ^ N ≤ 2 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    have h3 : C₀ * (1 + ‖z‖) ^ N ≤ 2 ^ N * max C₀ CN := by
      calc C₀ * (1 + ‖z‖) ^ N ≤ C₀ * 2 ^ N :=
            mul_le_mul_of_nonneg_left h2 hC₀0
        _ ≤ max C₀ CN * 2 ^ N :=
            mul_le_mul_of_nonneg_right (le_max_left C₀ CN) (by positivity)
        _ = 2 ^ N * max C₀ CN := by ring
    rw [le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans h3
  ·
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hz1)
    have hderiv := z_pow_mul_transf_eq_iteratedDeriv (contDiff_autocorr hf)
      (hasCompactSupport_autocorr hf) N z
    have hnorm : ‖z‖ ^ N * ‖transf (autocorr f) z‖
        = ‖transf (iteratedDeriv N (autocorr f)) z‖ := by
      have := congrArg (fun x : ℂ => ‖x‖) hderiv
      simpa [norm_mul, norm_pow] using this
    have h1 : ‖transf (iteratedDeriv N (autocorr f)) z‖ * (1 + ‖z‖) ≤ CN :=
      hCN z hz
    have h2 : ‖transf (autocorr f) z‖ * (‖z‖ ^ N * (1 + ‖z‖)) ≤ CN := by
      have : ‖transf (autocorr f) z‖ * ‖z‖ ^ N
          = ‖transf (iteratedDeriv N (autocorr f)) z‖ := by rw [mul_comm, hnorm]
      calc ‖transf (autocorr f) z‖ * (‖z‖ ^ N * (1 + ‖z‖))
          = (‖transf (autocorr f) z‖ * ‖z‖ ^ N) * (1 + ‖z‖) := by ring
        _ = ‖transf (iteratedDeriv N (autocorr f)) z‖ * (1 + ‖z‖) := by rw [this]
        _ ≤ CN := h1
    have h3 : ‖transf (autocorr f) z‖
        ≤ CN / ((1 + ‖z‖) * ‖z‖ ^ N) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖transf (autocorr f) z‖ * ((1 + ‖z‖) * ‖z‖ ^ N)
          = ‖transf (autocorr f) z‖ * (‖z‖ ^ N * (1 + ‖z‖)) := by ring
        _ ≤ CN := h2
    have h4 : CN * (1 + ‖z‖) ^ N ≤ (2 ^ N * max C₀ CN) * ‖z‖ ^ N := by
      have h5 : (1 + ‖z‖) ≤ 2 * ‖z‖ := by linarith
      have h6 : (1 + ‖z‖) ^ N ≤ (2 * ‖z‖) ^ N := pow_le_pow_left₀ (by positivity) h5 N
      have h7 : CN * (1 + ‖z‖) ^ N ≤ CN * (2 * ‖z‖) ^ N :=
        mul_le_mul_of_nonneg_left h6 hCN0
      have h8 : CN * (2 * ‖z‖) ^ N = CN * 2 ^ N * ‖z‖ ^ N := by
        rw [mul_pow]; ring
      have h9 : CN * 2 ^ N ≤ 2 ^ N * max C₀ CN := by
        calc CN * 2 ^ N = 2 ^ N * CN := by ring
          _ ≤ 2 ^ N * max C₀ CN :=
              mul_le_mul_of_nonneg_left (le_max_right C₀ CN) (by positivity)
      calc CN * (1 + ‖z‖) ^ N ≤ CN * 2 ^ N * ‖z‖ ^ N := by rw [← h8]; exact h7
        _ ≤ (2 ^ N * max C₀ CN) * ‖z‖ ^ N :=
            mul_le_mul_of_nonneg_right h9 (by positivity)
    have h5 : CN / ((1 + ‖z‖) * ‖z‖ ^ N)
        ≤ (2 ^ N * max C₀ CN) / (1 + ‖z‖) ^ N := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc CN * (1 + ‖z‖) ^ N ≤ (2 ^ N * max C₀ CN) * ‖z‖ ^ N := h4
        _ ≤ (2 ^ N * max C₀ CN) * ((1 + ‖z‖) * ‖z‖ ^ N) := by
            have h10 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)
            have h11 : ‖z‖ ^ N ≤ (1 + ‖z‖) * ‖z‖ ^ N :=
              le_mul_of_one_le_left (by positivity) h10
            exact mul_le_mul_of_nonneg_left h11 (by positivity)
    exact h3.trans h5









def HorizontalControl (T : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
    IntervalIntegrable (fun x : ℝ =>
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖)
      volume (-(1 / 2)) (1 / 2) ∧
    (∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖)
      ≤ C * (1 + T n) ^ k





theorem tendsto_horizontal_integral_zero_of_control {h : ℂ → ℂ}
    (hdec : ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, |z.re| ≤ 1 / 2 →
      ‖h z‖ ≤ D / (1 + ‖z‖) ^ N)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hctrl : HorizontalControl T) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
        h ((x : ℂ) + (T n : ℂ) * I)
          * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, k, hC⟩ := hctrl
  obtain ⟨D, hD0, hD⟩ := hdec (k + 1)

  have hlim : Tendsto (fun n : ℕ => D * C / (1 + T n)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (1 : ℝ) + T n) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) hT
    have hden'
      hden.inv_tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => D * C * (1 + T n)⁻¹) atTop (𝓝 (D * C * 0)) :=
      (tendsto_const_nhds (x := D * C)).mul hden'
    simpa [div_eq_mul_inv] using h2
  refine squeeze_zero_norm'
    (f := fun n : ℕ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
      h ((x : ℂ) + (T n : ℂ) * I)
        * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))) ?_ hlim
  filter_upwards [hT.eventually (eventually_ge_atTop (2 : ℝ))] with n hTn
  obtain ⟨hint, hbd⟩ := hC n
  have hmajor : IntervalIntegrable (fun x : ℝ =>
      (D / (1 + T n) ^ (k + 1)) *
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖)
      volume (-(1 / 2)) (1 / 2) :=
    hint.const_mul (D / (1 + T n) ^ (k + 1))
  have hpoint : ∀ x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2),
      ‖h ((x : ℂ) + (T n : ℂ) * I)
          * logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖
        ≤ (D / (1 + T n) ^ (k + 1)) *
          ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖ := by
    intro x hx
    have hxI : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := Set.Ioc_subset_Icc_self hx
    have hre : |(((x : ℂ) + (T n : ℂ) * I)).re| ≤ (1 : ℝ) / 2 := by
      have hxre : (((x : ℂ) + (T n : ℂ) * I)).re = x := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]
      rw [hxre]
      exact abs_le.mpr ⟨hxI.1, hxI.2⟩
    have hnorm : T n ≤ ‖((x : ℂ) + (T n : ℂ) * I)‖ := by
      have him : |(((x : ℂ) + (T n : ℂ) * I)).im| ≤
          ‖((x : ℂ) + (T n : ℂ) * I)‖ := Complex.abs_im_le_norm _
      have him' : (((x : ℂ) + (T n : ℂ) * I)).im = T n := by simp
      rwa [him', abs_of_nonneg (by linarith)] at him
    have hdec' : ‖h ((x : ℂ) + (T n : ℂ) * I)‖ ≤ D / (1 + T n) ^ (k + 1) := by
      have h1 := hD _ hre
      have h2 : (1 + T n) ^ (k + 1) ≤ (1 + ‖((x : ℂ) + (T n : ℂ) * I)‖) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) (k + 1)
      calc ‖h ((x : ℂ) + (T n : ℂ) * I)‖
          ≤ D / (1 + ‖((x : ℂ) + (T n : ℂ) * I)‖) ^ (k + 1) := h1
        _ ≤ D / (1 + T n) ^ (k + 1) :=
            div_le_div_of_nonneg_left hD0 (by positivity) h2
    rw [norm_mul]
    exact mul_le_mul hdec' le_rfl (norm_nonneg _) (div_nonneg hD0 (by positivity))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (show (-(1 / 2 : ℝ)) ≤ 1 / 2 by norm_num) (Eventually.of_forall hpoint) hmajor
  rw [intervalIntegral.integral_const_mul] at hbound
  refine hbound.trans ?_
  calc (D / (1 + T n) ^ (k + 1)) *
        (∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2),
          ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (T n : ℂ) * I))‖)
      ≤ (D / (1 + T n) ^ (k + 1)) * (C * (1 + T n) ^ k) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = D * C / (1 + T n) := by
        have h1 : (1 + T n) ≠ 0 := by positivity
        field_simp
        ring


theorem tendsto_horizontal_integral_autocorr_of_control {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hctrl : HorizontalControl T) :
    Tendsto (fun n : ℕ => stripTopIntegral (transf (autocorr f)) (T n))
      atTop (𝓝 0) := by
  have h := tendsto_horizontal_integral_zero_of_control
    (fun N => exists_transf_autocorr_superPolyDecay hf N) hT hctrl
  simpa only [stripTopIntegral, xiLogIntegrand] using h






theorem tendsto_right_vertical_autocorr_of_control {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (hTpos : ∀ n, 0 < T n)
    (hbd : ∀ n, ∀ p : XiZero,
      centeredZero p ∈ rectClosed (stripLeft (T n)) (stripRight (T n)) →
        centeredZero p ∈ rectOpen (stripLeft (T n)) (stripRight (T n)))
    (hctrl : HorizontalControl T) :
    Tendsto (fun n => stripRightIntegral (transf (autocorr f)) (T n)) atTop
      (𝓝 ((Real.pi : ℂ) * ∑' p : XiZero, transf (autocorr f) (centeredZero p))) := by
  set S : ℂ := ∑'
  have hlim := rectangleResidueLimit_autocorr hf hT hTpos hbd
  have htop : Tendsto (fun n => stripTopIntegral (transf (autocorr f)) (T n)) atTop (𝓝 0) :=
    tendsto_horizontal_integral_autocorr_of_control hf hT hctrl
  have hsum : Tendsto (fun n => rectangleBoundaryIntegral
        (xiLogIntegrand (transf (autocorr f))) (stripLeft (T n)) (stripRight (T n))
      + 2 * stripTopIntegral (transf (autocorr f)) (T n)) atTop
      (𝓝 (2 * (Real.pi : ℂ) * I * S + 2 * 0)) :=
    hlim.add ((tendsto_const_nhds (x := (2 : ℂ))).mul htop)
  have hprod : Tendsto (fun n => 2 * I * stripRightIntegral (transf (autocorr f)) (T n))
      atTop (𝓝 (2 * (Real.pi : ℂ) * I * S)) := by
    have hsum' : Tendsto (fun n => rectangleBoundaryIntegral
          (xiLogIntegrand (transf (autocorr f))) (stripLeft (T n)) (stripRight (T n))
        + 2 * stripTopIntegral (transf (autocorr f)) (T n)) atTop
        (𝓝 (2 * (Real.pi : ℂ) * I * S)) := by
      simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards with n
    have hdec := stripBoundaryIntegral_autocorr_decomposition hf (T n)
    linear_combination hdec
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hR : Tendsto (fun n => (2 * I * stripRightIntegral (transf (autocorr f)) (T n))
      / (2 * I)) atTop (𝓝 ((2 * (Real.pi : ℂ) * I * S) / (2 * I))) :=
    hprod.div_const (2 * I)
  have hval : (2 * (Real.pi : ℂ) * I * S) / (2 * I) = (Real.pi : ℂ) * S := by
    field_simp
  rw [hval] at hR
  refine hR.congr' ?_
  filter_upwards with n
  field_simp


theorem evenGuinandWeilAt_of_control_verticalEval {a : ℝ}
    (h : VerticalIntegralEvalAt a)
    (hex : ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, AdmissibleT T ∧ HorizontalControl T) :
    EvenGuinandWeilAt a := by
  intro ha f hf
  obtain ⟨T, hAdm, hctrl⟩ := hex f hf
  obtain ⟨hTtop, hTpos, hbd⟩ := hAdm
  have h1 := tendsto_right_vertical_autocorr_of_control hf.1 hTtop hTpos hbd hctrl
  have h1re : Tendsto (fun n => (stripRightIntegral (transf (autocorr f)) (T n)).re) atTop
      (𝓝 (((Real.pi : ℂ) * ∑' p : XiZero, transf (autocorr f) (centeredZero p)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp h1
  have h3 : ((Real.pi : ℂ) * ∑'
      = Real.pi * (∑' p : XiZero, transf (autocorr f) (centeredZero p)).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h3] at h1re
  have h2 := h f hf T ⟨hTtop, hTpos, hbd⟩
  have hEq := tendsto_nhds_unique h1re h2
  exact mul_left_cancel₀ Real.pi_ne_zero hEq




theorem weilExplicitFormulaOdd_of_control_verticalEval
    (hex : ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, AdmissibleT T ∧ HorizontalControl T)
    (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOdd :=
  weilExplicitFormulaOdd_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_control_verticalEval (hv a) (hex a))
    positionFormEqAt


theorem weilExplicitFormulaOddNonneg_of_control_verticalEval
    (hex : ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, AdmissibleT T ∧ HorizontalControl T)
    (hv : ∀ a : ℝ, VerticalIntegralEvalAt a) :
    WeilExplicitFormulaOddNonneg :=
  weilExplicitFormulaOddNonneg_of_evenGuinandWeil_positionForm
    (fun a => evenGuinandWeilAt_of_control_verticalEval (hv a) (hex a))
    positionFormEqAt

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.exists_transf_autocorr_superPolyDecay
#print axioms RHLean.ExplicitFormula.tendsto_horizontal_integral_zero_of_control
#print axioms RHLean.ExplicitFormula.tendsto_horizontal_integral_autocorr_of_control
#print axioms RHLean.ExplicitFormula.tendsto_right_vertical_autocorr_of_control
#print axioms RHLean.ExplicitFormula.evenGuinandWeilAt_of_control_verticalEval
#print axioms RHLean.ExplicitFormula.weilExplicitFormulaOdd_of_control_verticalEval

end

end Inline_ExplicitFormula_RH108

section Inline_wp_WP_A1











open MeasureTheory Set Filter
open scoped Real Topology BigOperators ENNReal

namespace RHLean.WP




theorem log_one_div_eq_neg_log {u : ℝ} (_hu : 0 < u) :
    Real.log (1 / u) = -Real.log u := by
  rw [one_div, Real.log_inv]


theorem log_one_div_abs_eq_neg {u : ℝ} (hu : u ≠ 0) :
    Real.log (1 / |u|) = -Real.log |u| :=
  log_one_div_eq_neg_log (abs_pos.mpr hu)


theorem integral_log_abs_zero_one : ∫ u in (0 : ℝ)..1, Real.log |u| = -1 := by
  have hcongr : ∫ u in (0 : ℝ)..1, Real.log |u| = ∫ u in (0 : ℝ)..1, Real.log u :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      (fun u hu => by rw [abs_of_pos hu.1])
  rw [hcongr, integral_log]
  norm_num


theorem integral_log_abs_neg_one_zero : ∫ u in (-1 : ℝ)..0, Real.log |u| = -1 := by
  have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
    (f := fun u : ℝ => Real.log |u|)
  rw [neg_zero, show -(1 : ℝ) = -1 by norm_num] at hcomp
  rw [← hcomp]
  have : ∫ x in (0 : ℝ)..1, Real.log |(-x)| = ∫ x in (0 : ℝ)..1, Real.log |x| := by
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) ?_
    intro x _
    simp only [abs_neg]
  rw [this, integral_log_abs_zero_one]


theorem integral_log_abs_neg_one_one : ∫ u in (-1 : ℝ)..1, Real.log |u| = -2 := by
  have hleft : IntervalIntegrable (fun u : ℝ => Real.log |u|) volume (-1) 0 :=
    IntervalIntegrable.congr_uIoo (f := Real.log) (g := fun u : ℝ => Real.log |u|)
      intervalIntegral.intervalIntegrable_log'
        have hu0 : u < 0 := by simpa using hu.2
        show Real.log u = Real.log |u|
        rw [abs_of_neg hu0, Real.log_neg_eq_log])
  have hright : IntervalIntegrable (fun u : ℝ => Real.log |u|) volume 0 1 :=
    IntervalIntegrable.congr_uIoo (f := Real.log) (g := fun u : ℝ => Real.log |u|)
      intervalIntegral.intervalIntegrable_log' (fun u hu => by
        have hu0 : 0 < u := by simpa using hu.1
        show Real.log u = Real.log |u|
        rw [abs_of_pos hu0])
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    integral_log_abs_neg_one_zero, integral_log_abs_zero_one]
  norm_num



theorem window_integral_log_inv_abs (a : ℝ) :
    ∫ t in (a - 1)..(a + 1), Real.log (1 / |t - a|) = 2 := by

  have hshift : ∫ t in (a - 1)..(a + 1), Real.log (1 / |t - a|)
      = ∫ u in (-1 : ℝ)..1, Real.log (1 / |u|) := by
    have h := intervalIntegral.integral_comp_sub_right (a := a - 1) (b := a + 1) (d := a)
      (f := fun u : ℝ => Real.log (1 / |u|))
    rw [show (a - 1) - a = -1 by ring, show (a + 1) - a = 1 by ring] at h
    exact h
  rw [hshift]

  have hcongr : ∫ u in (-1 : ℝ)..1, Real.log (1 / |u|)
      = ∫ u in (-1 : ℝ)..1, -Real.log |u| := by
    refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) ?_
    intro u hu
    rcases eq_or_ne u 0 with h | h
    · simp [h]
    · exact log_one_div_abs_eq_neg h
  rw [hcongr, intervalIntegral.integral_neg, integral_log_abs_neg_one_one]
  norm_num






theorem exists_notMem_and_le_two_mul_average {I : ℝ → ℝ} {N : Set ℝ} {a b : ℝ}
    (hab : a < b) (hI0 : ∀ x, 0 ≤ I x) (hint : IntervalIntegrable I volume a b)
    (hN : volume N = 0) :
    ∃ t ∈ Ioo a b, t ∉ N ∧ I t ≤ 2 * (∫ x in a..b, I x) / (b - a) := by
  by_contra hcon
  push Not at hcon
  set M : ℝ := ∫ x in a..b, I x with hM
  set lam : ℝ := 2 * M / (b - a) with hlam
  have hcon' : ∀ t ∈ Ioo a b, t ∉ N → lam < I t := hcon
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hM0 : 0 ≤ M := intervalIntegral.integral_nonneg hab.le (fun x _ => hI0 x)

  have hN' : ∀ᵐ x : ℝ, x ∉ N := compl_mem_ae_iff.mpr hN

  have hae : (fun _ : ℝ => lam) ≤ᵐ[volume.restrict (Ioo a b)] I := by
    change ∀ᵐ x ∂(volume.restrict (Ioo a b)), (fun _ : ℝ => lam) x ≤ I x
    simp only
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hN'] with x hx hxw
    exact (hcon' x hxw hx).le
  have hIint : IntegrableOn I (Ioo a b) := hint.1.mono_set Ioo_subset_Ioc_self
  have hconst : IntegrableOn (fun _ : ℝ => lam) (Ioo a b) volume :=
    integrableOn_const (by simp)
  have hmono : (b - a) * lam ≤ ∫ x in Ioo a b, I x := by
    have h := setIntegral_mono_ae_restrict hconst hIint hae
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (le_of_lt hba)] at h
    exact h
  have hIoc : ∫ x in Ioo a b, I x = M := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  rw [hIoc] at hmono

  have hlam2 : (b - a) * lam = 2 * M := by
    rw [hlam]
    field_simp
  rw [hlam2] at hmono
  have hMzero : M = 0 := by linarith
  have hlam0 : lam = 0 := by
    rw [hlam, hMzero]
    simp

  have hpos : ∀ᵐ x ∂(volume.restrict (Ioc a b)), 0 < I x := by
    have hb : ∀ᵐ x : ℝ, x ≠ b := by
      filter_upwards [show ({b}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) from
        compl_mem_ae_iff.mpr (by simp)] with x hx
      simpa using hx
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hN', hb] with x hxN hxb hxI
    have hxw : x ∈ Ioo a b := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
    have h := hcon' x hxw hxN
    rwa [hlam0] at h
  have hzero : ∀ᵐ x ∂(volume.restrict (Ioc a b)), I x = 0 := by
    have hle : (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[volume.restrict (Ioc a b)] I :=
      Eventually.of_forall hI0
    have hiff := intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le hle hint
    have h0 : (∫ x in a..b, I x) = 0 := by rw [← hM]; exact hMzero
    rw [h0] at hiff
    exact hiff.mp rfl
  have hfalse : ∀ᵐ x ∂(volume.restrict (Ioc a b)), False := by
    filter_upwards [hpos, hzero] with x hx1 hx2
    linarith
  have hnull : volume (Ioc a b) = 0 := by
    rw [ae_iff] at hfalse
    simpa using hfalse
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hnull
  linarith



#print axioms RHLean.WP.window_integral_log_inv_abs
#print axioms RHLean.WP.exists_notMem_and_le_two_mul_average

end RHLean.WP



end Inline_wp_WP_A1

section Inline_wp_WP_A2





















open MeasureTheory Set Filter
open scoped Real Topology BigOperators ENNReal

namespace RHLean.WP





theorem exists_sequence_of_window_bound {I : ℝ → ℝ} {Bad : Set ℝ}
    (hI0 : ∀ t, 0 ≤ I t) (hBad : volume Bad = 0)
    (hint : ∀ n : ℕ, IntervalIntegrable I volume (n : ℝ) ((n : ℝ) + 1))
    (hwin : ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∫ t in (n : ℝ)..((n : ℝ) + 1), I t ≤ K * (1 + (n : ℝ)) ^ k) :
    ∃ T : ℕ → ℝ, (∀ n : ℕ, T n ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, T n ∉ Bad) ∧ Tendsto T atTop atTop ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ, I (T n) ≤ C * (1 + T n) ^ k := by
  classical

  have hsel : ∀ n : ℕ, ∃ t ∈ Ioo (n : ℝ) ((n : ℝ) + 1), t ∉ Bad ∧
      I t ≤ 2 * (∫ x in (n : ℝ)..((n : ℝ) + 1), I x) / (((n : ℝ) + 1) - n) :=
    fun n => exists_notMem_and_le_two_mul_average (I := I) (N := Bad)
      (by linarith : (n : ℝ) < (n : ℝ) + 1) hI0 (hint n) hBad
  choose T hTmem hTbad hTle using hsel

  have hTtop : Tendsto (T : ℕ → ℝ) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => (hTmem n).1.le)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K, hK0, k, hK⟩ := hwin
  refine ⟨T, hTmem, hTbad, hTtop, ?_⟩
  refine ⟨max (2 * K) (I (T 0) / (1 + T 0) ^ k), ?_, k, fun n => ?_⟩
  · exact le_trans (by linarith : (0 : ℝ) ≤ 2 * K) (le_max_left _ _)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hpos : (0 : ℝ) < 1 + T 0 := by linarith [(hTmem 0).1]
      have hC0 : I (T 0) = (I (T 0) / (1 + T 0) ^ k) * (1 + T 0) ^ k := by
        field_simp
      calc I (T 0) = (I (T 0) / (1 + T 0) ^ k) * (1 + T 0) ^ k := hC0
        _ ≤ max (2 * K) (I (T 0) / (1 + T 0) ^ k) * (1 + T 0) ^ k :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · have hdiv : (((n : ℝ) + 1) - n) = 1 := by ring
      have hb := hTle n
      rw [hdiv, div_one] at hb
      have hKn := hK n hn
      have hpos : (0 : ℝ) ≤ 1 + T n := by linarith [(hTmem n).1]
      have hmono : (1 + (n : ℝ)) ^ k ≤ (1 + T n) ^ k :=
        pow_le_pow_left₀ (by positivity) (by linarith [(hTmem n).1]) k
      have hnn : (0 : ℝ) ≤ (1 + T n) ^ k := pow_nonneg hpos k
      have h2K : 2 * K ≤ max (2 * K) (I (T 0) / (1 + T 0) ^ k) := le_max_left _ _
      calc I (T n) ≤ 2 * (∫ x in (n : ℝ)..((n : ℝ) + 1), I x) := hb
        _ ≤ 2 * (K * (1 + (n : ℝ)) ^ k) := by linarith
        _ = (2 * K) * (1 + (n : ℝ)) ^ k := by ring
        _ ≤ (2 * K) * (1 + T n) ^ k := by
            exact mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ max (2 * K) (I (T 0) / (1 + T 0) ^ k) * (1 + T n) ^ k :=
            mul_le_mul_of_nonneg_right h2K hnn

end RHLean.WP



#print axioms RHLean.WP.exists_sequence_of_window_bound



end Inline_wp_WP_A2

section Inline_wp_WP_A3
















open MeasureTheory Set Filter
open scoped Real Topology BigOperators
open RHLean.ExplicitFormula Complex

namespace RHLean.WP



noncomputable def sectionInt (t : ℝ) : ℝ :=
  ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
    ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (t : ℂ) * I))‖


noncomputable def sectionFun (t : ℝ) (x : ℝ) : ℝ :=
  ‖logDeriv riemannXi ((1 / 2 : ℂ) + ((x : ℂ) + (t : ℂ) * I))‖

theorem sectionInt_eq (t : ℝ) : sectionInt t = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), sectionFun t x := by
  unfold sectionInt sectionFun
  rfl

theorem sectionInt_nonneg (t : ℝ) : 0 ≤ sectionInt t := by
  unfold sectionInt
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)





theorem horizontalControl_of_window_bound {Bad : Set ℝ}
    (hBad : volume Bad = 0)
    (hintWin : ∀ n : ℕ, IntervalIntegrable sectionInt volume (n : ℝ) ((n : ℝ) + 1))
    (hsec : ∀ t : ℝ, t ∉ Bad → IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2))
    (hwin : ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∫ t in (n : ℝ)..((n : ℝ) + 1), sectionInt t ≤ K * (1 + (n : ℝ)) ^ k) :
    ∃ T : ℕ → ℝ, (∀ n, T n ∉ Bad) ∧ (∀ n, 0 < T n) ∧ Tendsto T atTop atTop ∧
      HorizontalControl T := by
  obtain ⟨T, hTmem, hTbad, hTtop, C, hC0, k, hCk⟩ :=
    exists_sequence_of_window_bound (I := sectionInt) (Bad := Bad)
      sectionInt_nonneg hBad hintWin hwin
  refine ⟨T, hTbad, fun n => ?_, hTtop, C, hC0, k, fun n => ?_⟩
  · have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [(hTmem n).1]
  · exact ⟨hsec (T n) (hTbad n), hCk n⟩

end RHLean.WP



#print axioms RHLean.WP.sectionInt_nonneg
#print axioms RHLean.WP.horizontalControl_of_window_bound



end Inline_wp_WP_A3

section Inline_wp_WP_B3_nearband


















open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula


noncomputable def hadamardSec (μ : ℂ) (T : ℝ) (x : ℝ) : ℝ :=
  ‖((x : ℂ) + (T : ℂ) * I) / (((x : ℂ) + (T : ℂ) * I) ^ 2 - μ ^ 2)‖


private theorem hadamard_den_ne__wp_WP_B3_nearband {T : ℝ} {μ : ℂ} (hsep1 : T ≠ μ.im) (hsep2 : T ≠ -μ.im)
    (x : ℝ) : ((x : ℂ) + (T : ℂ) * I) ^ 2 - μ ^ 2 ≠ 0 := by
  have hne1 : ((x : ℂ) + (T : ℂ) * I) - μ ≠ 0 := by
    intro hzero
    have him : (((x : ℂ) + (T : ℂ) * I) - μ).im = 0 := by rw [hzero]; simp
    simp at him
    exact hsep1 (by linarith)
  have hne2 : ((x : ℂ) + (T : ℂ) * I) + μ ≠ 0 := by
    intro hzero
    have him : (((x : ℂ) + (T : ℂ) * I) + μ).im = 0 := by rw [hzero]; simp
    simp at him
    exact hsep2 (by linarith)
  rw [show ((x : ℂ) + (T : ℂ) * I) ^ 2 - μ ^ 2
      = (((x : ℂ) + (T : ℂ) * I) - μ) * (((x : ℂ) + (T : ℂ) * I) + μ) by ring]
  exact mul_ne_zero hne1 hne2


theorem integral_norm_hadamardTerm_le_log {T : ℝ} {μ : ℂ} (hre : |μ.re| ≤ 1 / 2)
    (hsep1 : T ≠ μ.im) (hsep2 : T ≠ -μ.im) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), hadamardSec μ T x)
      ≤ 2 + |Real.log (|T - μ.im|)| + |Real.log (|T + μ.im|)| := by

  have hcont1 : Continuous fun x : ℝ => 1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖ := by
    have hne : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) - μ ≠ 0 := by
      intro x hzero
      have him : (((x : ℂ) + (T : ℂ) * I) - μ).im = 0 := by rw [hzero]; simp
      simp at him
      exact hsep1 (by linarith)
    have hg : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) - μ := by fun_prop
    exact Continuous.div continuous_const hg.norm (fun x => norm_ne_zero_iff.mpr (hne x))
  have hcont2 : Continuous fun x : ℝ => 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖ := by
    have hne : ∀ x : ℝ, ((x : ℂ) + (T : ℂ) * I) + μ ≠ 0 := by
      intro x hzero
      have him : (((x : ℂ) + (T : ℂ) * I) + μ).im = 0 := by rw [hzero]; simp
      simp at him
      exact hsep2 (by linarith)
    have hg : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) + μ := by fun_prop
    exact Continuous.div continuous_const hg.norm (fun x => norm_ne_zero_iff.mpr (hne x))
  have hcontH : Continuous (hadamardSec μ T) := by
    unfold hadamardSec
    have hgW : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) := by fun_prop
    have hgD : Continuous fun x : ℝ => ((x : ℂ) + (T : ℂ) * I) ^ 2 - μ ^ 2 := by fun_prop
    exact Continuous.norm (Continuous.div hgW hgD (fun x => hadamard_den_ne__wp_WP_B3_nearband hsep1 hsep2 x))
  have hIntL : IntervalIntegrable (hadamardSec μ T) volume (-(1 / 2) : ℝ) (1 / 2) :=
    hcontH.intervalIntegrable _ _
  have hInt : IntervalIntegrable (fun x : ℝ => (1 / 2) *
      (1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖ + 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖))
      volume (-(1 / 2) : ℝ) (1 / 2) :=
    ((hcont1.add hcont2).const_mul (1 / 2)).intervalIntegrable _ _

  have hpt : ∀ᵐ x ∂(volume.restrict (Set.Icc (-(1 / 2) : ℝ) (1 / 2))),
      hadamardSec μ T x
        ≤ (1 / 2) * (1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖
            + 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖) := by
    filter_upwards with x
    exact norm_hadamardTerm_le _ _
  have hmono : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), hadamardSec μ T x)
      ≤ ∫ x in (-(1 / 2) : ℝ)..(1 / 2), (1 / 2) *
          (1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖ + 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖) :=
    intervalIntegral.integral_mono_ae_restrict (by norm_num) hIntL hInt hpt

  have hsplit : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), (1 / 2) *
        (1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖ + 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖))
      = (1 / 2) * ((∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖)
          + ∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _)]

  have hb1 := integral_inv_norm_le (T := T) (μ := μ) hre hsep1
  have hre' : |(-μ).re| ≤ 1 / 2 := by simpa using hre
  have him' : T ≠ (-μ).im := by simpa using hsep2
  have hb2 := integral_inv_norm_le (T := T) (μ := -μ) hre' him'
  have hb2' : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖)
      ≤ 2 + 2 * |Real.log (|T + μ.im|)| := by
    simpa [sub_eq_add_neg, neg_im, add_comm, add_left_comm, add_assoc] using hb2
  have hsum : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖)
      + (∫ x in (-(1 / 2) : ℝ)..(1 / 2), 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖)
      ≤ (2 + 2 * |Real.log (|T - μ.im|)|) + (2 + 2 * |Real.log (|T + μ.im|)|) :=
    add_le_add hb1 hb2'
  have hstep : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), (1 / 2) *
        (1 / ‖((x : ℂ) + (T : ℂ) * I) - μ‖ + 1 / ‖((x : ℂ) + (T : ℂ) * I) + μ‖))
      ≤ 2 + |Real.log (|T - μ.im|)| + |Real.log (|T + μ.im|)| := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have harith : (1 / 2) * ((2 + 2 * |Real.log (|T - μ.im|)|)
        + (2 + 2 * |Real.log (|T + μ.im|)|))
        = 2 + |Real.log (|T - μ.im|)| + |Real.log (|T + μ.im|)| := by ring
    linarith
  exact hmono.trans hstep

end RHLean.ExplicitFormula

#print axioms RHLean.ExplicitFormula.integral_norm_hadamardTerm_le_log



end Inline_wp_WP_B3_nearband

section Inline_wp_WP_A4











open MeasureTheory Set
open scoped Real Topology BigOperators

namespace RHLean.WP

theorem intervalIntegrable_log_abs (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => |Real.log u|) volume a b := by
  simpa only [Real.norm_eq_abs] using
    (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).abs


theorem integral_log_abs_le (M : ℝ) (hM : 0 ≤ M) :
    ∫ u in (0 : ℝ)..M, |Real.log u| ≤ M * (|Real.log M| + 1) := by
  by_cases h1 : M ≤ 1
  ·
    have hcongr : ∫ u in (0 : ℝ)..M, |Real.log u| = ∫ u in (0 : ℝ)..M, -Real.log u :=
      intervalIntegral.integral_congr_Ioo_of_le hM (fun u hu => by
        have hpos : 0 < u := hu.1
        have hu1 : u < 1 := lt_of_lt_of_le hu.2 h1
        exact abs_of_neg (Real.log_neg hpos hu1))
    rw [hcongr, intervalIntegral.integral_neg, integral_log]
    have hlogM : Real.log M ≤ 0 := Real.log_nonpos hM h1
    rw [abs_of_nonpos hlogM]
    nlinarith
  ·
    push Not at h1
    have hsplit : ∫ u in (0 : ℝ)..M, |Real.log u|
        = (∫ u in (0 : ℝ)..1, |Real.log u|) + ∫ u in (1 : ℝ)..M, |Real.log u| := by
      rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_log_abs 0 1)
        (intervalIntegrable_log_abs 1 M)]
    have hfirst : ∫ u in (0 : ℝ)..1, |Real.log u| = 1 := by
      have hc : ∫ u in (0 : ℝ)..1, |Real.log u| = ∫ u in (0 : ℝ)..1, -Real.log u :=
        intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun u hu =>
          abs_of_neg (Real.log_neg hu.1 hu.2))
      rw [hc, intervalIntegral.integral_neg, integral_log]
      norm_num
    have hsecond : ∫ u in (1 : ℝ)..M, |Real.log u| = M * Real.log M - M + 1 := by
      have hc : ∫ u in (1 : ℝ)..M, |Real.log u| = ∫ u in (1 : ℝ)..M, Real.log u :=
        intervalIntegral.integral_congr_Ioo_of_le h1.le
          (fun u hu => abs_of_pos (Real.log_pos hu.1))
      rw [hc, integral_log, Real.log_one]
      ring
    rw [hsplit, hfirst, hsecond, abs_of_pos (Real.log_pos h1)]
    nlinarith



theorem integral_log_abs_abs_symm (M : ℝ) (hM : 0 ≤ M) :
    ∫ t in (-M)..M, |Real.log (|t|)| ≤ 2 * (M * (|Real.log M| + 1)) := by
  have hIntL : IntervalIntegrable (fun t : ℝ => |Real.log (|t|)|) volume (-M) 0 :=
    IntervalIntegrable.congr_uIoo (f := fun t : ℝ => |Real.log t|)
      (intervalIntegrable_log_abs (-M) 0) (fun t ht => by
        have ht0 : t < 0 := by
          have h := ht.2
          rwa [max_eq_right (by linarith : -M ≤ 0)] at h
        show |Real.log t| = |Real.log (|t|)|
        rw [abs_of_neg ht0, Real.log_neg_eq_log])
  have hIntR : IntervalIntegrable (fun t : ℝ => |Real.log (|t|)|) volume 0 M :=
    IntervalIntegrable.congr_uIoo (f := fun t : ℝ => |Real.log t|)
      (intervalIntegrable_log_abs 0 M) (fun t ht => by
        have ht0 : 0 < t := by
          have h := ht.1
          rwa [min_eq_left hM] at h
        show |Real.log t| = |Real.log (|t|)|
        rw [abs_of_pos ht0])
  have hleft : ∫ t in (-M)..0, |Real.log (|t|)| = ∫ u in (0 : ℝ)..M, |Real.log u| := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := M)
      (f := fun t : ℝ => |Real.log (|t|)|)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr_Ioo_of_le hM (fun u hu => ?_)
    have hu0 : 0 < u := hu.1
    show |Real.log (|(-u)|)| = |Real.log u|
    rw [abs_neg, abs_of_pos hu0]
  have hright : ∫ t in (0 : ℝ)..M, |Real.log (|t|)| = ∫ u in (0 : ℝ)..M, |Real.log u| := by
    refine intervalIntegral.integral_congr_Ioo_of_le hM (fun u hu => ?_)
    show |Real.log (|u|)| = |Real.log u|
    rw [abs_of_pos hu.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals hIntL hIntR, hleft, hright]
  have h := integral_log_abs_le M hM
  linarith



theorem integral_log_abs_abs_window_le {n b M : ℝ}
    (hM : 1 ≤ M) (hb : |n - b| + 1 ≤ M) :
    ∫ t in n..(n + 1), |Real.log (|t - b|)| ≤ 2 * (M * (|Real.log M| + 1)) := by
  have hM0 : 0 ≤ M := by linarith
  rw [intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => |Real.log (|u|)|) b]
  have habs : |n - b| ≤ M - 1 := by linarith
  have hleft : -M ≤ n - b := by
    have h := (abs_le.mp habs).1
    linarith
  have hright : n + 1 - b ≤ M := by
    have h := (abs_le.mp habs).2
    linarith
  have hmid : n - b ≤ n + 1 - b := by linarith
  have hint : IntervalIntegrable (fun u : ℝ => |Real.log (|u|)|) volume (-M) M :=
    IntervalIntegrable.congr_uIoo (f := fun u : ℝ => |Real.log u|)
      (intervalIntegrable_log_abs (-M) M) (fun u hu => by
        show |Real.log u| = |Real.log (|u|)|
        rcases lt_trichotomy u 0 with h | h | h
        · rw [abs_of_neg h, Real.log_neg_eq_log]
        · subst h; simp
        · rw [abs_of_pos h])
  have hmono := intervalIntegral.integral_mono_interval
    (f := fun u : ℝ => |Real.log (|u|)|) (μ := volume)
    (a := n - b) (b := n + 1 - b) (c := -M) (d := M) hleft hmid hright
    (by filter_upwards with u using abs_nonneg (Real.log (|u|))) hint
  exact hmono.trans (integral_log_abs_abs_symm M hM0)



theorem intervalIntegrable_log_abs_sub (b n n' : ℝ) :
    IntervalIntegrable (fun t : ℝ => |Real.log (|t - b|)|) volume n n' := by
  have h := (intervalIntegrable_log_abs (n - b) (n' - b)).comp_sub_right b
  simpa using h




theorem integral_two_add_log_window_le {n b M : ℝ}
    (hM : 1 ≤ M) (hb : |n - b| + 1 ≤ M) :
    ∫ t in n..(n + 1), (2 + 2 * |Real.log (|t - b|)|)
      ≤ 2 + 2 * (2 * (M * (|Real.log M| + 1))) := by
  have hIntLog := intervalIntegrable_log_abs_sub b n (n + 1)
  have hInt2 : IntervalIntegrable (fun t : ℝ => (2 : ℝ)) volume n (n + 1) :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add hInt2 (hIntLog.const_mul 2),
    intervalIntegral.integral_const]
  have hwin := integral_log_abs_abs_window_le (n := n) (b := b) (M := M) hM hb
  have hconst : (n + 1 - n) • (2 : ℝ) = 2 := by ring
  rw [hconst]
  rw [intervalIntegral.integral_const_mul]
  linarith

end RHLean.WP

#print axioms RHLean.WP.integral_log_abs_le
#print axioms RHLean.WP.integral_log_abs_abs_symm
#print axioms RHLean.WP.integral_log_abs_abs_window_le
#print axioms RHLean.WP.intervalIntegrable_log_abs_sub
#print axioms RHLean.WP.integral_two_add_log_window_le



end Inline_wp_WP_A4

section Inline_wp_WP_B3_section



















open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval

namespace RHLean.ExplicitFormula




private noncomputable def hadamardJoint__wp_WP_B3_section (μ : ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖((p.2 : ℂ) + (p.1 : ℂ) * I) / (((p.2 : ℂ) + (p.1 : ℂ) * I) ^ 2 - μ ^ 2)‖


private theorem measurable_hadamardJoint__wp_WP_B3_section (μ : ℂ) : Measurable (hadamardJoint__wp_WP_B3_section μ) := by
  have hW : Continuous fun p : ℝ × ℝ => ((p.2 : ℂ) + (p.1 : ℂ) * I) := by fun_prop
  have hD : Continuous fun p : ℝ × ℝ => ((p.2 : ℂ) + (p.1 : ℂ) * I) ^ 2 - μ ^ 2 := by fun_prop
  have hAn : Measurable fun p : ℝ × ℝ => ‖((p.2 : ℂ) + (p.1 : ℂ) * I)‖ :=
    hW.norm.measurable
  have hBn : Measurable fun p : ℝ × ℝ => ‖((p.2 : ℂ) + (p.1 : ℂ) * I) ^ 2 - μ ^ 2‖ :=
    hD.norm.measurable
  have hEq : hadamardJoint__wp_WP_B3_section μ = (fun p : ℝ × ℝ => ‖((p.2 : ℂ) + (p.1 : ℂ) * I)‖)
      / (fun p : ℝ × ℝ => ‖((p.2 : ℂ) + (p.1 : ℂ) * I) ^ 2 - μ ^ 2‖) := by
    funext p
    exact norm_div _ _
  rw [hEq]
  exact hAn.div hBn



theorem aestronglyMeasurable_hadamardSection (μ : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => ∫ x, hadamardJoint__wp_WP_B3_section μ (t, x)
      ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))) volume := by
  have hjoint : AEStronglyMeasurable (hadamardJoint__wp_WP_B3_section μ)
      (volume.prod (volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))) :=
    (measurable_hadamardJoint__wp_WP_B3_section μ).aestronglyMeasurable.mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  exact hjoint.integral_prod_right' (μ := volume)




theorem intervalIntegrable_hadamardMajorant (b n n' : ℝ) :
    IntervalIntegrable (fun t : ℝ => 2 + |Real.log (|t - b|)| + |Real.log (|t + b|)|)
      volume n n' := by
  have h1 : IntervalIntegrable (fun t : ℝ => |Real.log (|t - b|)|) volume n n' :=
    RHLean.WP.intervalIntegrable_log_abs_sub b n n'
  have h2 : IntervalIntegrable (fun t : ℝ => |Real.log (|t + b|)|) volume n n' := by
    have h := RHLean.WP.intervalIntegrable_log_abs_sub (-b) n n'
    simpa [sub_eq_add_neg] using h
  have h3 : IntervalIntegrable (fun t : ℝ => (2 : ℝ)) volume n n' :=
    intervalIntegrable_const
  simpa [add_assoc] using h3.add (h1.add h2)




theorem integral_norm_hadamardTerm_window_le {n : ℝ} {μ : ℂ} {M : ℝ}
    (hre : |μ.re| ≤ 1 / 2) (hM : 1 ≤ M)
    (hb : |n - μ.im| + 1 ≤ M) (hb' : |n + μ.im| + 1 ≤ M) :
    (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2), hadamardSec μ t x))
      ≤ 2 + 4 * (M * (|Real.log M| + 1)) := by
  rw [intervalIntegral.integral_of_le (by linarith : n ≤ n + 1)]
  have hnn1 : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hsec_eq : ∀ t : ℝ, (∫ x in (-(1 / 2) : ℝ)..(1 / 2), hadamardSec μ t x)
      = ∫ x, hadamardJoint__wp_WP_B3_section μ (t, x) ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))) := by
    intro t
    unfold hadamardSec hadamardJoint__wp_WP_B3_section
    rw [intervalIntegral.integral_of_le hnn1, uIoc_of_le hnn1]

  have hnn : ∀ t : ℝ, 0 ≤ ∫ x, hadamardJoint__wp_WP_B3_section μ (t, x)
      ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))) := by
    intro t
    rw [← hsec_eq t, intervalIntegral.integral_of_le hnn1]
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    exact norm_nonneg _

  have hpt : ∀ᵐ t ∂(volume : Measure ℝ),
      (∫ x, hadamardJoint__wp_WP_B3_section μ (t, x) ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))))
        ≤ 2 + |Real.log (|t - μ.im|)| + |Real.log (|t + μ.im|)| := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ μ.im := by
      refine MeasureTheory.ae_iff.mpr ?_
      simp
    have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ -μ.im := by
      refine MeasureTheory.ae_iff.mpr ?_
      simp
    filter_upwards [h1, h2] with t ht1 ht2
    rw [← hsec_eq t]
    exact integral_norm_hadamardTerm_le_log hre ht1 ht2

  have hmaj : IntervalIntegrable
      (fun t : ℝ => 2 + |Real.log (|t - μ.im|)| + |Real.log (|t + μ.im|)|) volume n (n + 1) :=
    intervalIntegrable_hadamardMajorant μ.im n (n + 1)

  have hmajI : Integrable
      (fun t : ℝ => 2 + |Real.log (|t - μ.im|)| + |Real.log (|t + μ.im|)|)
      (volume.restrict (Ioc n (n + 1))) := hmaj.1
  have hf : Integrable (fun t : ℝ => ∫ x, hadamardJoint__wp_WP_B3_section μ (t, x)
      ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))) (volume.restrict (Ioc n (n + 1))) := by
    refine hmajI.mono (aestronglyMeasurable_hadamardSection μ).restrict ?_
    filter_upwards [ae_restrict_of_ae hpt] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t), Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ht

  have hle := MeasureTheory.integral_mono_ae hf hmajI (ae_restrict_of_ae hpt)

  have hval : (∫ t in Ioc n (n + 1),
      (2 + |Real.log (|t - μ.im|)| + |Real.log (|t + μ.im|)|))
      ≤ 2 + 4 * (M * (|Real.log M| + 1)) := by
    rw [← intervalIntegral.integral_of_le (by linarith : n ≤ n + 1)]
    have hlog1 : IntervalIntegrable (fun t : ℝ => |Real.log (|t - μ.im|)|) volume n (n + 1) :=
      RHLean.WP.intervalIntegrable_log_abs_sub μ.im n (n + 1)
    have hlog2 : IntervalIntegrable (fun t : ℝ => |Real.log (|t + μ.im|)|) volume n (n + 1) := by
      have h := RHLean.WP.intervalIntegrable_log_abs_sub (-μ.im) n (n + 1)
      simpa [sub_eq_add_neg] using h
    have hc : IntervalIntegrable (fun t : ℝ => (2 : ℝ)) volume n (n + 1) := intervalIntegrable_const
    rw [intervalIntegral.integral_add (hc.add hlog1) hlog2,
      intervalIntegral.integral_add hc hlog1, intervalIntegral.integral_const]
    have hI1 : (∫ t in n..(n + 1), |Real.log (|t - μ.im|)|)
        ≤ 2 * (M * (|Real.log M| + 1)) :=
      RHLean.WP.integral_log_abs_abs_window_le hM hb
    have hI2 : (∫ t in n..(n + 1), |Real.log (|t + μ.im|)|)
        ≤ 2 * (M * (|Real.log M| + 1)) := by
      have h := RHLean.WP.integral_log_abs_abs_window_le (b := -μ.im) hM (by simpa using hb')
      simpa [sub_eq_add_neg] using h
    have hconst : (n + 1 - n) • (2 : ℝ) = 2 := by ring
    rw [hconst]
    linarith

  have hEqint : (∫ t in Ioc n (n + 1), (∫ x, hadamardJoint__wp_WP_B3_section μ (t, x)
      ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))))
      = ∫ t in Ioc n (n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2), hadamardSec μ t x) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    exact (hsec_eq t).symm
  rw [hEqint] at hle
  exact hle.trans hval

end RHLean.ExplicitFormula

#print axioms RHLean.ExplicitFormula.aestronglyMeasurable_hadamardSection
#print axioms RHLean.ExplicitFormula.integral_norm_hadamardTerm_window_le



end Inline_wp_WP_B3_section

section Inline_wp_WP_B3_nearfar






















open scoped Real BigOperators

namespace RHLean.WP


theorem log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]
    ring
  rw [hlog]
  have hle : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs0
  nlinarith


theorem abs_log_le {y : ℝ} (hy : 1 ≤ y) : |Real.log y| ≤ 2 * Real.sqrt y := by
  rw [abs_of_nonneg (Real.log_nonneg hy)]
  exact log_le_two_sqrt hy




theorem near_cost_bound {n : ℝ} (hn : 1 ≤ n) :
    2 + 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1)
      ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) := by
  have hn2 : 1 ≤ n + 2 := by linarith
  have hM1 : 1 ≤ 2 + 2 * (n + 2) := by linarith
  have hMpos : (0 : ℝ) < 2 + 2 * (n + 2) := by linarith

  have hMle : 2 + 2 * (n + 2) ≤ 6 * (n + 2) := by linarith

  have hlogM : Real.log (2 + 2 * (n + 2)) ≤ Real.log 6 + 2 * Real.sqrt (n + 2) := by
    have h1 : Real.log (2 + 2 * (n + 2)) ≤ Real.log (6 * (n + 2)) :=
      Real.log_le_log hMpos hMle
    have h2 : Real.log (6 * (n + 2)) = Real.log 6 + Real.log (n + 2) :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log (n + 2) ≤ 2 * Real.sqrt (n + 2) := log_le_two_sqrt hn2
    rw [h2] at h1
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt (n + 2) := Real.one_le_sqrt.mpr hn2

  have hbd : |Real.log (2 + 2 * (n + 2))| + 1
      ≤ (Real.log 6 + 3) * Real.sqrt (n + 2) := by
    rw [abs_of_nonneg (Real.log_nonneg hM1)]
    have hsum : Real.log (2 + 2 * (n + 2)) + 1
        ≤ (Real.log 6 + 2 * Real.sqrt (n + 2)) + 1 := by linarith
    have h6 : (0 : ℝ) ≤ Real.log 6 + 1 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 6)
      linarith
    have hmul : Real.log 6 + 1 ≤ (Real.log 6 + 1) * Real.sqrt (n + 2) := by
      have := mul_le_mul_of_nonneg_left hsqrt1 h6
      simpa using this
    nlinarith [hmul]

  have hstep : 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1)
      ≤ 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2)) := by
    have hb0 : 0 ≤ |Real.log (2 + 2 * (n + 2))| + 1 := by positivity
    have h1 : 4 * (2 + 2 * (n + 2)) ≤ 4 * (6 * (n + 2)) := by linarith
    have h2 : 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1)
        ≤ 4 * (6 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1) := by
      apply mul_le_mul_of_nonneg_right h1
      positivity
    have h3 : 4 * (6 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1)
        ≤ 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2)) := by
      apply mul_le_mul_of_nonneg_left hbd
      linarith
    linarith

  have hpow : (n + 2) * Real.sqrt (n + 2) = (n + 2) ^ ((3 : ℝ) / 2) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith)]
    rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hcost : 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2))
      = 24 * (Real.log 6 + 3) * ((n + 2) * Real.sqrt (n + 2)) := by ring
  rw [hcost, hpow] at hstep
  have hpow1 : (1 : ℝ) ≤ (n + 2) ^ ((3 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ (n + 2) := by linarith
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 2) := by simp
      _ ≤ (n + 2) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hn2 (by norm_num)
  nlinarith



theorem window_bound_k3 {Cfar Cnear : ℝ} (hfar0 : 0 ≤ Cfar) (hCnear : 0 ≤ Cnear) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℝ, 1 ≤ n →
      Cfar * Real.sqrt (1 + n)
        + Cnear * (n + 2) ^ ((3 : ℝ) / 2)
            * (2 + 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1))
      ≤ K * (1 + n) ^ 3 := by
  refine ⟨Cfar + (8 * Cnear + 1) * (74 + 24 * Real.log 6), ?_, ?_⟩
  · have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
    nlinarith
  · intro n hn
    have hn1 : (0 : ℝ) < 1 + n := by linarith
    have hn2 : 1 ≤ n + 2 := by linarith
    have hnear := near_cost_bound hn
    have hCnear0 : 0 ≤ Cnear * (n + 2) ^ ((3 : ℝ) / 2) := by positivity

    have hpow3 : (n + 2) ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2) = (n + 2) ^ 3 := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have hnear2 : Cnear * (n + 2) ^ ((3 : ℝ) / 2)
        * (2 + 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1))
        ≤ Cnear * (74 + 24 * Real.log 6) * (n + 2) ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hnear hCnear0
      calc Cnear * (n + 2) ^ ((3 : ℝ) / 2)
          * (2 + 4 * (2 + 2 * (n + 2)) * (|Real.log (2 + 2 * (n + 2))| + 1))
          ≤ Cnear * (n + 2) ^ ((3 : ℝ) / 2)
            * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := h
        _ = Cnear * (74 + 24 * Real.log 6)
            * ((n + 2) ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)) := by ring
        _ = Cnear * (74 + 24 * Real.log 6) * (n + 2) ^ 3 := by rw [hpow3]

    have hsqrt : Real.sqrt (1 + n) ≤ (1 + n) ^ 3 := by
      have h1 : Real.sqrt (1 + n) ≤ 1 + n := by
        have := Real.sq_sqrt (le_of_lt hn1) ▸ (Real.sqrt_nonneg (1 + n))
        nlinarith [Real.sq_sqrt (le_of_lt hn1), Real.sqrt_nonneg (1 + n), hn1]
      have h2 : (1 + n) ≤ (1 + n) ^ 3 := by nlinarith
      linarith
    have hfar2 : Cfar * Real.sqrt (1 + n) ≤ Cfar * (1 + n) ^ 3 :=
      mul_le_mul_of_nonneg_left hsqrt hfar0

    have hshift : (n + 2) ^ 3 ≤ (27 / 8) * (1 + n) ^ 3 := by
      have h1 : n + 2 ≤ (3 / 2) * (1 + n) := by linarith
      have h0 : (0 : ℝ) ≤ n + 2 := by linarith
      calc (n + 2) ^ 3 ≤ ((3 / 2) * (1 + n)) ^ 3 := by
            apply pow_le_pow_left₀ h0 h1
        _ = (27 / 8) * (1 + n) ^ 3 := by ring
    have hcoef : (0 : ℝ) ≤ Cnear * (74 + 24 * Real.log 6) := by
      have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
      exact mul_nonneg hCnear (by linarith)
    have hnear3 : Cnear * (74 + 24 * Real.log 6) * (n + 2) ^ 3
        ≤ Cnear * (74 + 24 * Real.log 6) * ((27 / 8) * (1 + n) ^ 3) :=
      mul_le_mul_of_nonneg_left hshift hcoef
    have hK : Cfar * (1 + n) ^ 3 + Cnear * (74 + 24 * Real.log 6) * ((27 / 8) * (1 + n) ^ 3)
        ≤ (Cfar + (8 * Cnear + 1) * (74 + 24 * Real.log 6)) * (1 + n) ^ 3 := by
      have hcube : 0 ≤ (1 + n) ^ 3 := by positivity
      have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
      nlinarith
    linarith

end RHLean.WP

#print axioms RHLean.WP.log_le_two_sqrt
#print axioms RHLean.WP.near_cost_bound
#print axioms RHLean.WP.window_bound_k3



end Inline_wp_WP_B3_nearfar

section Inline_wp_WP_B3_zerosum
















open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval

namespace RHLean.WP



theorem near_cost_bound_M {n M : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M) (hMle : M ≤ 6 * (n + 2)) :
    2 + 4 * M * (|Real.log M| + 1)
      ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) := by
  have hn2 : 1 ≤ n + 2 := by linarith
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : Real.log M ≤ Real.log 6 + 2 * Real.sqrt (n + 2) := by
    have h1 : Real.log M ≤ Real.log (6 * (n + 2)) := Real.log_le_log hMpos hMle
    have h2 : Real.log (6 * (n + 2)) = Real.log 6 + Real.log (n + 2) :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log (n + 2) ≤ 2 * Real.sqrt (n + 2) := log_le_two_sqrt hn2
    rw [h2] at h1
    linarith
  have hsqrt1 : 1 ≤ Real.sqrt (n + 2) := Real.one_le_sqrt.mpr hn2
  have hbd : |Real.log M| + 1 ≤ (Real.log 6 + 3) * Real.sqrt (n + 2) := by
    rw [abs_of_nonneg (Real.log_nonneg hM)]
    have h6 : (0 : ℝ) ≤ Real.log 6 + 1 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 6)
      linarith
    have hmul : Real.log 6 + 1 ≤ (Real.log 6 + 1) * Real.sqrt (n + 2) := by
      have := mul_le_mul_of_nonneg_left hsqrt1 h6
      simpa using this
    nlinarith [hlogM, hmul]
  have hstep : 4 * M * (|Real.log M| + 1) ≤ 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2)) := by
    have h1 : 4 * M ≤ 4 * (6 * (n + 2)) := by linarith
    have hb0 : (0 : ℝ) ≤ |Real.log M| + 1 := by positivity
    have h2 : 4 * M * (|Real.log M| + 1) ≤ 4 * (6 * (n + 2)) * (|Real.log M| + 1) :=
      mul_le_mul_of_nonneg_right h1 hb0
    have h3 : 4 * (6 * (n + 2)) * (|Real.log M| + 1)
        ≤ 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2)) :=
      mul_le_mul_of_nonneg_left hbd (by linarith)
    linarith
  have hpow : (n + 2) * Real.sqrt (n + 2) = (n + 2) ^ ((3 : ℝ) / 2) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith)]
    rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hcost : 4 * (6 * (n + 2)) * ((Real.log 6 + 3) * Real.sqrt (n + 2))
      = 24 * (Real.log 6 + 3) * ((n + 2) * Real.sqrt (n + 2)) := by ring
  rw [hcost, hpow] at hstep
  have hpow1 : (1 : ℝ) ≤ (n + 2) ^ ((3 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ (n + 2) := by linarith
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 2) := by simp
      _ ≤ (n + 2) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hn2 (by norm_num)
  nlinarith




theorem near_zero_window_cost {n R : ℝ} (hn : 1 ≤ n) {μ : ℂ}
    (hre : |μ.re| ≤ 1 / 2) (hμ : ‖μ‖ ≤ R) (hR : R ≤ 3 * (n + 2)) :
    (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x))
      ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) := by
  have hnpos : (0 : ℝ) ≤ n := by linarith
  have hn2 : (0 : ℝ) < n + 2 := by linarith

  have him : |μ.im| ≤ 3 * (n + 2) := by
    have h1 : |μ.im| ≤ ‖μ‖ := Complex.abs_im_le_norm μ
    linarith

  have hM : (1 : ℝ) ≤ 6 * (n + 2) := by linarith
  have hb1 : |n - μ.im| + 1 ≤ 6 * (n + 2) := by
    have h1 : |n - μ.im| ≤ n + |μ.im| := by
      calc |n - μ.im| ≤ |n| + |μ.im| := abs_sub _ _
        _ = n + |μ.im| := by rw [abs_of_nonneg hnpos]
    linarith
  have hb2 : |n + μ.im| + 1 ≤ 6 * (n + 2) := by
    have h1 : |n + μ.im| ≤ n + |μ.im| := by
      calc |n + μ.im| ≤ |n| + |μ.im| := abs_add_le _ _
        _ = n + |μ.im| := by rw [abs_of_nonneg hnpos]
    linarith
  have hcost := RHLean.ExplicitFormula.integral_norm_hadamardTerm_window_le
    (n := n) (μ := μ) (M := 6 * (n + 2)) hre hM hb1 hb2
  have hgrowth := near_cost_bound_M hn hM (le_refl (6 * (n + 2)))
  linarith






theorem sum_near_window_cost {n R : ℝ} (hn : 1 ≤ n) (s : Finset ℂ)
    (hre : ∀ μ ∈ s, |μ.re| ≤ 1 / 2)
    (hμ : ∀ μ ∈ s, ‖μ‖ ≤ R) (hR : R ≤ 3 * (n + 2)) :
    (∑ μ ∈ s, (∫ t in n..(n + 1),
        (∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x)))
      ≤ (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := by
  have hper : ∀ μ ∈ s, (∫ t in n..(n + 1),
      (∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x))
      ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) :=
    fun μ hμs => near_zero_window_cost hn (hre μ hμs) (hμ μ hμs) hR
  calc (∑ μ ∈ s, (∫ t in n..(n + 1),
        (∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x)))
      ≤ ∑ _μ ∈ s, ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) :=
        Finset.sum_le_sum hper
    _ = (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]




theorem near_band_total_le {Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcount : ∀ T : ℝ, 2 ≤ T →
      ((RHLean.ExplicitFormula.zeroBall (2 * (1 + T))).card : ℝ)
        ≤ Ccard * (1 + T) ^ ((3 : ℝ) / 2))
    {n : ℝ} (hn : 1 ≤ n) :
    (∑ μ ∈ (RHLean.ExplicitFormula.zeroBall (2 * (1 + (n + 1)))).image centeredZero,
        (∫ t in n..(n + 1),
          (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            RHLean.ExplicitFormula.hadamardSec μ t x)))
      ≤ (Ccard * 3 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
  set B := RHLean.ExplicitFormula.zeroBall (2 * (1 + (n + 1))) with hB
  set X : ℝ := (n + 2) ^ ((3 : ℝ) / 2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hre : ∀ μ ∈ B.image centeredZero, |μ.re| ≤ 1 / 2 := by
    intro μ hμ
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hμ
    exact RHLean.ExplicitFormula.abs_re_centeredZero_le p
  have hμ : ∀ μ ∈ B.image centeredZero, ‖μ‖ ≤ 3 * (n + 2) := by
    intro μ hμ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hμ
    have h := RHLean.ExplicitFormula.zeroBall_mem.mp hp
    have h2 : 2 * (1 + (n + 1)) = 2 * (n + 2) := by ring
    rw [h2] at h

    have hle : ‖centeredZero p‖ ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by
      unfold centeredZero
      calc ‖Complex.Hadamard.divisorZeroIndex₀_val p - 1 / 2‖
          ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by norm_num
    linarith
  have hsum := sum_near_window_cost hn (B.image centeredZero) hre hμ (by linarith)

  have hT : (2 : ℝ) ≤ n + 1 := by linarith
  have hcard := hcount (n + 1) hT
  have hcard_img : ((B.image centeredZero).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_image_le

  have hpow : (1 + (n + 1)) ^ ((3 : ℝ) / 2) ≤ 3 ^ ((3 : ℝ) / 2) * X := by
    have hle : 1 + (n + 1) ≤ 3 * (n + 2) := by linarith
    have h0 : (0 : ℝ) ≤ 1 + (n + 1) := by linarith
    calc (1 + (n + 1)) ^ ((3 : ℝ) / 2) ≤ (3 * (n + 2)) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow h0 hle (by norm_num)
      _ = 3 ^ ((3 : ℝ) / 2) * X := by
          rw [Real.mul_rpow (by norm_num) (by linarith), hX]
  have hcard2 : ((B.image centeredZero).card : ℝ) ≤ Ccard * (3 ^ ((3 : ℝ) / 2) * X) := by
    refine hcard_img.trans ?_
    exact hcard.trans (mul_le_mul_of_nonneg_left hpow hCcard)

  have hconst0 : (0 : ℝ) ≤ (74 + 24 * Real.log 6) * X := by
    have : 0 < Real.log 6 := Real.log_pos (by norm_num)
    positivity
  have hcube : X * X = (n + 2) ^ 3 := by
    rw [hX]
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < n + 2)]
    norm_num
  have hstep : ((B.image centeredZero).card : ℝ) * ((74 + 24 * Real.log 6) * X)
      ≤ (Ccard * (3 ^ ((3 : ℝ) / 2) * X)) * ((74 + 24 * Real.log 6) * X) :=
    mul_le_mul_of_nonneg_right hcard2 hconst0
  refine hsum.trans (hstep.trans (le_of_eq ?_))
  calc (Ccard * (3 ^ ((3 : ℝ) / 2) * X)) * ((74 + 24 * Real.log 6) * X)
      = (Ccard * 3 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (X * X) := by ring
    _ = (Ccard * 3 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
        rw [hcube]


set_option maxHeartbeats 600000 in






theorem near_band_total_le_shift {Ccard : ℝ} (hCcard : 0 ≤ Ccard)
    (hcount : ∀ T : ℝ, 2 ≤ T →
      ((RHLean.ExplicitFormula.zeroBall (2 * (1 + T))).card : ℝ)
        ≤ Ccard * (1 + T) ^ ((3 : ℝ) / 2))
    {n : ℝ} (hn : 1 ≤ n) :
    (∑ μ ∈ (RHLean.ExplicitFormula.zeroBall (2 * (n + 2) + 1)).image centeredZero,
        (∫ t in n..(n + 1),
          (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            RHLean.ExplicitFormula.hadamardSec μ t x)))
      ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
  set B := RHLean.ExplicitFormula.zeroBall (2 * (n + 2) + 1) with hB
  set X : ℝ := (n + 2) ^ ((3 : ℝ) / 2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hre : ∀ μ ∈ B.image centeredZero, |μ.re| ≤ 1 / 2 := by
    intro μ hμ
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hμ
    exact RHLean.ExplicitFormula.abs_re_centeredZero_le p
  have hμ : ∀ μ ∈ B.image centeredZero, ‖μ‖ ≤ 3 * (n + 2) := by
    intro μ hμ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hμ
    have h := RHLean.ExplicitFormula.zeroBall_mem.mp hp
    have hle : ‖centeredZero p‖ ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by
      unfold centeredZero
      calc ‖Complex.Hadamard.divisorZeroIndex₀_val p - 1 / 2‖
          ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by norm_num
    linarith
  have hsum := sum_near_window_cost hn (B.image centeredZero) hre hμ (by linarith)

  have hT : (2 : ℝ) ≤ n + 3 / 2 := by linarith
  have hBeq : 2 * (1 + (n + 3 / 2)) = 2 * (n + 2) + 1 := by ring
  have hcard : ((B.card : ℝ)) ≤ Ccard * (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2) := by
    have := hcount (n + 3 / 2) hT
    rwa [hBeq] at this
  have hcard_img : ((B.image centeredZero).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_image_le

  have hpow : (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2) ≤ 2 ^ ((3 : ℝ) / 2) * X := by
    have hle : 1 + (n + 3 / 2) ≤ 2 * (n + 2) := by linarith
    have h0 : (0 : ℝ) ≤ 1 + (n + 3 / 2) := by linarith
    calc (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2) ≤ (2 * (n + 2)) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow h0 hle (by norm_num)
      _ = 2 ^ ((3 : ℝ) / 2) * X := by
          rw [Real.mul_rpow (by norm_num) (by linarith), hX]
  have hcard2 : ((B.image centeredZero).card : ℝ) ≤ Ccard * (2 ^ ((3 : ℝ) / 2) * X) := by
    refine hcard_img.trans ?_
    exact hcard.trans (mul_le_mul_of_nonneg_left hpow hCcard)
  have hconst0 : (0 : ℝ) ≤ (74 + 24 * Real.log 6) * X := by
    have : 0 < Real.log 6 := Real.log_pos (by norm_num)
    positivity
  have hcube : X * X = (n + 2) ^ 3 := by
    rw [hX]
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < n + 2)]
    norm_num
  have hstep : ((B.image centeredZero).card : ℝ) * ((74 + 24 * Real.log 6) * X)
      ≤ (Ccard * (2 ^ ((3 : ℝ) / 2) * X)) * ((74 + 24 * Real.log 6) * X) :=
    mul_le_mul_of_nonneg_right hcard2 hconst0
  refine hsum.trans (hstep.trans (le_of_eq ?_))
  calc (Ccard * (2 ^ ((3 : ℝ) / 2) * X)) * ((74 + 24 * Real.log 6) * X)
      = (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (X * X) := by ring
    _ = (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
        rw [hcube]






theorem far_zero_window_cost {n : ℝ} (hn : 0 ≤ n) {μ : ℂ}
    (hμ : 2 * (1 + (n + 1)) ≤ ‖μ‖) :
    (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        RHLean.ExplicitFormula.hadamardSec μ t x))
      ≤ 4 * (1 + (n + 1)) / ‖μ‖ ^ 2 := by
  set C : ℝ := 4 * (1 + (n + 1)) / ‖μ‖ ^ 2 with hC
  have hμpos : (0 : ℝ) < ‖μ‖ := by linarith
  refine le_trans (le_abs_self _) ?_
  rw [← Real.norm_eq_abs]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := n) (b := n + 1)
    (f := fun t => ∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x)
    (C := C) ?_
  · rw [show |n + 1 - n| = 1 from by norm_num, mul_one] at h
    exact h
  · intro t ht
    rw [uIoc_of_le (by linarith : n ≤ n + 1)] at ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hn ht.1.le
    have htle : t ≤ n + 1 := ht.2

    have hfar : 2 * (1 + t) ≤ ‖μ‖ := by linarith
    have hb := RHLean.ExplicitFormula.integral_norm_hadamardTerm_far (T := t) ht0 (μ := μ) hfar

    have hb' : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x)
        ≤ 4 * (1 + t) / ‖μ‖ ^ 2 := hb
    have hmono : 4 * (1 + t) / ‖μ‖ ^ 2 ≤ C := by
      rw [hC]
      have h1 : 1 + t ≤ 1 + (n + 1) := by linarith
      have h2 : (0 : ℝ) < ‖μ‖ ^ 2 := by positivity
      exact div_le_div_of_nonneg_right (by linarith) h2.le
    have hnn : (0 : ℝ) ≤ ∫ x in (-(1 / 2) : ℝ)..(1 / 2), RHLean.ExplicitFormula.hadamardSec μ t x := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
      refine integral_nonneg_of_ae ?_
      filter_upwards with x
      exact norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hb'.trans hmono






private abbrev XZ__wp_WP_B3_zerosum := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)






theorem far_band_total_le {C n : ℝ} (hn : 1 ≤ n)
    (hfar : 4 * (1 + (n + 1)) *
        (∑' p : XZ__wp_WP_B3_zerosum,
          (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ C * Real.sqrt (1 + (n + 1))) :
    (∑'
        (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
          (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            RHLean.ExplicitFormula.hadamardSec
              (Complex.Hadamard.divisorZeroIndex₀_val p) t x))
        else 0))
      ≤ C * Real.sqrt (1 + (n + 1)) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := by linarith
  set a : ℝ := 4 * (1 + (n + 1)) with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith

  have hsumm0 : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

  have hnorm : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm0
    · split_ifs <;> positivity
    · split_ifs with h
      · rw [one_div, inv_pow]
      · positivity
  have hmaj : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      a * (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    hnorm.mul_left a

  have hterm : ∀ p : XZ__wp_WP_B3_zerosum,
      (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
        (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          RHLean.ExplicitFormula.hadamardSec
            (Complex.Hadamard.divisorZeroIndex₀_val p) t x))
      else 0)
      ≤ a * (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0) := by
    intro p
    by_cases hp : 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
    · rw [if_pos hp, if_pos hp]
      have hcost := far_zero_window_cost (n := n) hn0
        (μ := Complex.Hadamard.divisorZeroIndex₀_val p) (le_of_lt hp)
      have hpos : (0 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by linarith
      calc (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
              RHLean.ExplicitFormula.hadamardSec
                (Complex.Hadamard.divisorZeroIndex₀_val p) t x))
          ≤ 4 * (1 + (n + 1)) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := hcost
        _ = a * (1 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by
            rw [ha]; ring
    · rw [if_neg hp, if_neg hp, mul_zero]

  have hL : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
        (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          RHLean.ExplicitFormula.hadamardSec
            (Complex.Hadamard.divisorZeroIndex₀_val p) t x))
      else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) hterm hmaj
    by_cases hp : 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
    · rw [if_pos hp]
      rw [intervalIntegral.integral_of_le (by norm_num : n ≤ n + 1)]
      refine integral_nonneg_of_ae ?_
      filter_upwards with t
      rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
      refine integral_nonneg_of_ae ?_
      filter_upwards with x
      exact norm_nonneg _
    · rw [if_neg hp]
  refine le_trans (hL.tsum_le_tsum hterm hmaj) ?_
  have hfac : (∑' p : XZ__wp_WP_B3_zerosum,
      a * (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
      = a * (∑'
        (if 2 * (1 + (n + 1)) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    tsum_mul_left
  rw [hfac, ha]
  exact hfar





private theorem norm_centeredZero_ge__wp_WP_B3_zerosum (p : XZ__wp_WP_B3_zerosum) :
    ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ - 1 / 2 ≤ ‖RHLean.centeredZero p‖ := by
  have h : RHLean.centeredZero p + (1 / 2 : ℂ) =
      Complex.Hadamard.divisorZeroIndex₀_val p := by
    rw [RHLean.centeredZero]; ring
  have h2 := norm_add_le (RHLean.centeredZero p) (1 / 2 : ℂ)
  rw [h] at h2
  simpa using h2

set_option maxHeartbeats 600000 in





theorem far_band_total_le_centered {C n : ℝ} (hn : 1 ≤ n)
    (hfar : 16 * (n + 2) *
        (∑' p : XZ__wp_WP_B3_zerosum,
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ C * Real.sqrt (n + 2)) :
    (∑'
        (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
          (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x))
        else 0))
      ≤ C * Real.sqrt (n + 2) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn2 : (0 : ℝ) < n + 2 := by linarith
  have hsumm0 : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
  have hnorm : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm0
    · split_ifs <;> positivity
    · split_ifs with h
      · rw [one_div, inv_pow]
      · positivity
  have hmaj : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    hnorm.mul_left _
  have hterm : ∀ p : XZ__wp_WP_B3_zerosum,
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
        (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x))
      else 0)
      ≤ 16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0) := by
    intro p
    by_cases hp : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
    · rw [if_pos hp, if_pos hp]
      have hval : (0 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by linarith
      have hlam : 2 * (1 + (n + 1)) ≤ ‖RHLean.centeredZero p‖ := by
        have := norm_centeredZero_ge__wp_WP_B3_zerosum p
        linarith
      have hcost := far_zero_window_cost (n := n) hn0
        (μ := RHLean.centeredZero p) hlam
      have hlam0 : (0 : ℝ) < ‖RHLean.centeredZero p‖ := by linarith
      have hlt : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2 ≤ ‖RHLean.centeredZero p‖ := by
        linarith [norm_centeredZero_ge__wp_WP_B3_zerosum p]
      have hinv : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
          ≤ 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
        have h3 : (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            ≤ ‖RHLean.centeredZero p‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlt 2
        have h4 : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
            ≤ 1 / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) h3
        have h5 : (1 : ℝ) / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            = 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
          field_simp
          try ring
        rw [h5] at h4
        exact h4
      calc (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
              RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x))
          ≤ 4 * (1 + (n + 1)) / ‖RHLean.centeredZero p‖ ^ 2 := hcost
        _ = 4 * (n + 2) * (1 / ‖RHLean.centeredZero p‖ ^ 2) := by
            field_simp
            ring
        _ ≤ 4 * (n + 2) * (4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 16 * (n + 2) * (1 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by ring
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hL : Summable (fun p : XZ__wp_WP_B3_zerosum =>
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ then
        (∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x))
      else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) hterm hmaj
    by_cases hp : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
    · rw [if_pos hp]
      rw [intervalIntegral.integral_of_le (by linarith : n ≤ n + 1)]
      refine integral_nonneg_of_ae ?_
      filter_upwards with t
      rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
      refine integral_nonneg_of_ae ?_
      filter_upwards with x
      exact norm_nonneg _
    · rw [if_neg hp]
  refine le_trans (hL.tsum_le_tsum hterm hmaj) ?_
  have hfac : (∑' p : XZ__wp_WP_B3_zerosum,
      16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
      = 16 * (n + 2) * (∑'
        (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    tsum_mul_left
  rw [hfac]
  exact hfar

end RHLean.WP

#print axioms RHLean.WP.near_band_total_le_shift
#print axioms RHLean.WP.near_cost_bound_M
#print axioms RHLean.WP.near_zero_window_cost
#print axioms RHLean.WP.sum_near_window_cost
#print axioms RHLean.WP.near_band_total_le
#print axioms RHLean.WP.far_zero_window_cost
#print axioms RHLean.WP.far_band_total_le
#print axioms RHLean.WP.far_band_total_le_centered



end Inline_wp_WP_B3_zerosum

section Inline_wp_WP_B3_split










open MeasureTheory
open scoped BigOperators

namespace RHLean.WP

private abbrev XZ__wp_WP_B3_split := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)

set_option maxHeartbeats 400000 in


theorem tsum_split_finset [DecidableEq XZ__wp_WP_B3_split] {f : XZ__wp_WP_B3_split → ℝ} (s : Finset XZ__wp_WP_B3_split)
    (hsumm : Summable f) :
    (∑' p : XZ__wp_WP_B3_split, f p) = (∑ p ∈ s, f p) + (∑' p : XZ__wp_WP_B3_split, if p ∈ s then 0 else f p) := by
  classical
  have h := hsumm.sum_add_tsum_compl (s := s)
  rw [← h]
  congr 1
  rw [tsum_subtype]
  refine tsum_congr ?_
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

end RHLean.WP

#print axioms RHLean.WP.tsum_split_finset



end Inline_wp_WP_B3_split

section Inline_wp_WP_B3_bands














open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval

namespace RHLean.WP

private abbrev XZ__wp_WP_B3_bands := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)


noncomputable def wcost (n : ℝ) (p : XZ__wp_WP_B3_bands) : ℝ :=
  ∫ t in n..(n + 1), (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
    RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x)

theorem wcost_nonneg {n : ℝ} (p : XZ__wp_WP_B3_bands) : 0 ≤ wcost n p := by
  unfold wcost
  rw [intervalIntegral.integral_of_le (by linarith : n ≤ n + 1)]
  refine integral_nonneg_of_ae ?_
  filter_upwards with t
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  refine integral_nonneg_of_ae ?_
  filter_upwards with x
  exact norm_nonneg _

set_option maxHeartbeats 600000 in


theorem summable_wcost {n : ℝ} (hn : 0 ≤ n) : Summable (fun p : XZ__wp_WP_B3_bands => wcost n p) := by
  classical
  set s : Finset XZ__wp_WP_B3_bands := RHLean.ExplicitFormula.zeroBall (2 * (n + 2) + 1) with hs
  have hnorm : Summable (fun p : XZ__wp_WP_B3_bands =>
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    have hsumm0 : Summable (fun p : XZ__wp_WP_B3_bands =>
        (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
      summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm0
    · split_ifs <;> positivity
    · split_ifs with h
      · rw [one_div, inv_pow]
      · positivity
  have hmaj : Summable (fun p : XZ__wp_WP_B3_bands =>
      16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    hnorm.mul_left _
  have htail_per : ∀ p : XZ__wp_WP_B3_bands, (if p ∈ s then 0 else wcost n p)
      ≤ 16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0) := by
    intro p
    by_cases hp : p ∈ s
    · rw [if_pos hp]
      have hn2 : (0 : ℝ) ≤ n + 2 := by linarith
      split_ifs <;> positivity
    · have hgt : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by
        by_contra hcon
        exact hp (by rw [hs]; exact RHLean.ExplicitFormula.zeroBall_mem.mpr (not_lt.mp hcon))
      rw [if_neg hp, if_pos hgt]
      have hval : (0 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by linarith
      have hge : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ - 1 / 2
          ≤ ‖RHLean.centeredZero p‖ := by
        have heq : RHLean.centeredZero p + (1 / 2 : ℂ) =
            Complex.Hadamard.divisorZeroIndex₀_val p := by
          unfold RHLean.centeredZero; ring
        have h2 := norm_add_le (RHLean.centeredZero p) (1 / 2 : ℂ)
        rw [heq] at h2
        simpa using h2
      have hlam : 2 * (1 + (n + 1)) ≤ ‖RHLean.centeredZero p‖ := by linarith
      have hcost := far_zero_window_cost (n := n) hn (μ := RHLean.centeredZero p) hlam
      have hlt : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2 ≤ ‖RHLean.centeredZero p‖ := by
        linarith
      have hinv : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
          ≤ 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
        have h3 : (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            ≤ ‖RHLean.centeredZero p‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlt 2
        have h4 : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
            ≤ 1 / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) h3
        have h5 : (1 : ℝ) / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            = 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
          field_simp
          try ring
        rw [h5] at h4
        exact h4
      calc wcost n p
          ≤ 4 * (1 + (n + 1)) / ‖RHLean.centeredZero p‖ ^ 2 := hcost
        _ = 4 * (n + 2) * (1 / ‖RHLean.centeredZero p‖ ^ 2) := by
            field_simp
            try ring
        _ ≤ 4 * (n + 2) * (4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 16 * (n + 2) * (1 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by ring
  have hL : Summable (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then 0 else wcost n p)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) htail_per hmaj
    by_cases hp : p ∈ s <;> simp [hp, wcost_nonneg]
  have hfin : Summable (fun p : XZ__wp_WP_B3_bands => if p ∈ s then wcost n p else 0) :=
    summable_of_ne_finset_zero (s := s) (fun p hp => by simp [hp])
  have hsum : Summable (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then wcost n p else 0)
      + (if p ∈ s then 0 else wcost n p)) := hfin.add hL
  have hcongr : (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then wcost n p else 0)
      + (if p ∈ s then 0 else wcost n p)) = wcost n := by
    funext p
    by_cases hp : p ∈ s <;> simp [hp]
  exact hcongr ▸ hsum

set_option maxHeartbeats 1200000 in

theorem tsum_window_cost_le_bands {Ccard Cfar n : ℝ} (hCcard : 0 ≤ Ccard)
    (hcount : ∀ T : ℝ, 2 ≤ T →
      ((RHLean.ExplicitFormula.zeroBall (2 * (1 + T))).card : ℝ)
        ≤ Ccard * (1 + T) ^ ((3 : ℝ) / 2))
    (hfar : 16 * (n + 2) *
        (∑'
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ Cfar * Real.sqrt (n + 2))
    (hn : 1 ≤ n) :
    (∑' p : XZ__wp_WP_B3_bands, wcost n p)
      ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3
          + Cfar * Real.sqrt (n + 2) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn2 : (0 : ℝ) < n + 2 := by linarith
  set s : Finset XZ__wp_WP_B3_bands := RHLean.ExplicitFormula.zeroBall (2 * (n + 2) + 1) with hs

  have hnear_per : ∀ p ∈ s, wcost n p ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) := by
    intro p hp
    have hb := RHLean.ExplicitFormula.zeroBall_mem.mp (hs ▸ hp : p ∈ RHLean.ExplicitFormula.zeroBall (2 * (n + 2) + 1))
    have hle : ‖RHLean.centeredZero p‖ ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by
      unfold RHLean.centeredZero
      calc ‖Complex.Hadamard.divisorZeroIndex₀_val p - 1 / 2‖
          ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ + 1 / 2 := by norm_num
    exact near_zero_window_cost hn (RHLean.ExplicitFormula.abs_re_centeredZero_le p)
      (by linarith) (le_refl _)
  have hnear_sum : (∑ p ∈ s, wcost n p)
      ≤ (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := by
    calc (∑ p ∈ s, wcost n p)
        ≤ ∑ _p ∈ s, ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) :=
          Finset.sum_le_sum hnear_per
      _ = (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_le : (s.card : ℝ) ≤ Ccard * (2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)) := by
    have hT : (2 : ℝ) ≤ n + 3 / 2 := by linarith
    have hBeq : 2 * (1 + (n + 3 / 2)) = 2 * (n + 2) + 1 := by ring
    have h1 : ((RHLean.ExplicitFormula.zeroBall (2 * (1 + (n + 3 / 2)))).card : ℝ)
        ≤ Ccard * (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2) := hcount (n + 3 / 2) hT
    rw [hBeq] at h1
    have h2 : (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2)
        ≤ 2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2) := by
      have hle : 1 + (n + 3 / 2) ≤ 2 * (n + 2) := by linarith
      have h0 : (0 : ℝ) ≤ 1 + (n + 3 / 2) := by linarith
      calc (1 + (n + 3 / 2)) ^ ((3 : ℝ) / 2) ≤ (2 * (n + 2)) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow h0 hle (by norm_num)
        _ = 2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2) := by
            rw [Real.mul_rpow (by norm_num) (le_of_lt hn2)]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hCcard)
  have hnear : (∑ p ∈ s, wcost n p)
      ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
    have hK0 : (0 : ℝ) ≤ (74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2) := by
      have : 0 < Real.log 6 := Real.log_pos (by norm_num)
      positivity
    have h1 : (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2))
        ≤ (Ccard * (2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)))
            * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hcard_le hK0
    have hid : (Ccard * (2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)))
        * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2))
        = (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6))
            * ((n + 2) ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)) := by ring
    have hpow : (n + 2) ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2) = (n + 2) ^ 3 := by
      rw [← Real.rpow_add hn2]
      norm_num
    calc (∑ p ∈ s, wcost n p)
        ≤ (s.card : ℝ) * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := hnear_sum
      _ ≤ (Ccard * (2 ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)))
            * ((74 + 24 * Real.log 6) * (n + 2) ^ ((3 : ℝ) / 2)) := h1
      _ = (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6))
            * ((n + 2) ^ ((3 : ℝ) / 2) * (n + 2) ^ ((3 : ℝ) / 2)) := hid
      _ = (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3 := by
          rw [hpow]

  have hnorm : Summable (fun p : XZ__wp_WP_B3_bands =>
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    have hsumm0 : Summable (fun p : XZ__wp_WP_B3_bands =>
        (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
      summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm0
    · split_ifs <;> positivity
    · split_ifs with h
      · rw [one_div, inv_pow]
      · positivity
  have hmaj : Summable (fun p : XZ__wp_WP_B3_bands =>
      16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
    hnorm.mul_left _
  have htail_per : ∀ p : XZ__wp_WP_B3_bands, (if p ∈ s then 0 else wcost n p)
      ≤ 16 * (n + 2) * (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0) := by
    intro p
    by_cases hp : p ∈ s
    · rw [if_pos hp]
      have h0 : (0 : ℝ) ≤ 16 * (n + 2) *
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [if_neg hp]
      have hgt : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by
        by_contra hcon
        exact hp (by rw [hs]; exact RHLean.ExplicitFormula.zeroBall_mem.mpr (not_lt.mp hcon))
      rw [if_pos hgt]
      have hval : (0 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by linarith

      have hge : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ - 1 / 2
          ≤ ‖RHLean.centeredZero p‖ := by
        have heq : RHLean.centeredZero p + (1 / 2 : ℂ) =
            Complex.Hadamard.divisorZeroIndex₀_val p := by
          unfold RHLean.centeredZero; ring
        have h2 := norm_add_le (RHLean.centeredZero p) (1 / 2 : ℂ)
        rw [heq] at h2
        simpa using h2
      have hlam : 2 * (1 + (n + 1)) ≤ ‖RHLean.centeredZero p‖ := by linarith
      have hcost := far_zero_window_cost (n := n) hn0 (μ := RHLean.centeredZero p) hlam
      have hlt : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2 ≤ ‖RHLean.centeredZero p‖ := by
        linarith
      have hinv : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
          ≤ 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
        have h3 : (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            ≤ ‖RHLean.centeredZero p‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlt 2
        have h4 : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
            ≤ 1 / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) h3
        have h5 : (1 : ℝ) / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
            = 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
          field_simp
          try ring
        rw [h5] at h4
        exact h4
      calc wcost n p
          ≤ 4 * (1 + (n + 1)) / ‖RHLean.centeredZero p‖ ^ 2 := hcost
        _ = 4 * (n + 2) * (1 / ‖RHLean.centeredZero p‖ ^ 2) := by
            field_simp
            try ring
        _ ≤ 4 * (n + 2) * (4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 16 * (n + 2) * (1 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by ring
  have hL : Summable (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then 0 else wcost n p)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) htail_per hmaj
    by_cases hp : p ∈ s <;> simp [hp, wcost_nonneg]
  have htail : (∑'
    refine le_trans (hL.tsum_le_tsum htail_per hmaj) ?_
    have hfac : (∑' p : XZ__wp_WP_B3_bands, 16 * (n + 2) *
        (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        = 16 * (n + 2) * (∑'
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) :=
      tsum_mul_left
    rw [hfac]
    exact hfar

  have hfin : Summable (fun p : XZ__wp_WP_B3_bands => if p ∈ s then wcost n p else 0) :=
    summable_of_ne_finset_zero (s := s) (fun p hp => by simp [hp])
  have hsum : Summable (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then wcost n p else 0)
      + (if p ∈ s then 0 else wcost n p)) := hfin.add hL
  have hcongr : (fun p : XZ__wp_WP_B3_bands => (if p ∈ s then wcost n p else 0)
      + (if p ∈ s then 0 else wcost n p)) = wcost n := by
    funext p
    by_cases hp : p ∈ s <;> simp [hp]
  have hcost : Summable (fun p : XZ__wp_WP_B3_bands => wcost n p) := hcongr ▸ hsum
  rw [tsum_split_finset s hcost]
  linarith [hnear, htail]

end RHLean.WP

#print axioms RHLean.WP.summable_wcost
#print axioms RHLean.WP.tsum_window_cost_le_bands



end Inline_wp_WP_B3_bands

section Inline_wp_WP_B3_domination













open MeasureTheory Complex Set
open scoped Real Topology BigOperators

namespace RHLean.WP

private abbrev XZ__wp_WP_B3_domination := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)

set_option maxHeartbeats 800000 in

private theorem far_bound__wp_WP_B3_domination {w : ℂ} {p : XZ__wp_WP_B3_domination}
    (hv : max 1 (2 * ‖w‖ + 1 / 2) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖) :
    ‖w / (w ^ 2 - RHLean.centeredZero p ^ 2)‖
      ≤ (16 / 3) * ‖w‖ * ((‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) := by
  have hB1 : (1 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ :=
    lt_of_le_of_lt (le_max_left _ _) hv
  have hB2 : 2 * ‖w‖ + 1 / 2 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ :=
    lt_of_le_of_lt (le_max_right _ _) hv
  have hval0 : (0 : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by linarith

  have hlam_eq : RHLean.centeredZero p + (1 / 2 : ℂ) =
      Complex.Hadamard.divisorZeroIndex₀_val p := by
    rw [RHLean.centeredZero]; ring
  have h1 : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
      ≤ ‖RHLean.centeredZero p‖ + 1 / 2 := by
    have h := norm_add_le (RHLean.centeredZero p) (1 / 2 : ℂ)
    rw [hlam_eq] at h
    simpa using h
  have hlam : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2 ≤ ‖RHLean.centeredZero p‖ := by
    linarith
  have hlam0 : (0 : ℝ) < ‖RHLean.centeredZero p‖ := by linarith
  have hwlam : ‖w‖ ≤ ‖RHLean.centeredZero p‖ / 2 := by linarith

  have hden : (3 / 4) * ‖RHLean.centeredZero p‖ ^ 2
      ≤ ‖w ^ 2 - RHLean.centeredZero p ^ 2‖ := by
    have h1 : ‖RHLean.centeredZero p ^ 2‖
        ≤ ‖w ^ 2 - RHLean.centeredZero p ^ 2‖ + ‖w ^ 2‖ := by
      have hsplit : RHLean.centeredZero p ^ 2
          = (RHLean.centeredZero p ^ 2 - w ^ 2) + w ^ 2 := by ring
      calc ‖RHLean.centeredZero p ^ 2‖
          = ‖(RHLean.centeredZero p ^ 2 - w ^ 2) + w ^ 2‖ := by
            conv_lhs => rw [hsplit]
        _ ≤ ‖RHLean.centeredZero p ^ 2 - w ^ 2‖ + ‖w ^ 2‖ := norm_add_le _ _
        _ = ‖w ^ 2 - RHLean.centeredZero p ^ 2‖ + ‖w ^ 2‖ := by rw [norm_sub_rev]
    rw [norm_pow, norm_pow] at h1
    nlinarith [h1, hwlam, hlam0, norm_nonneg w]
  have hden0 : (0 : ℝ) < (3 / 4) * ‖RHLean.centeredZero p‖ ^ 2 := by positivity

  have hinv : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
      ≤ 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
    have h3 : (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
        ≤ ‖RHLean.centeredZero p‖ ^ 2 := pow_le_pow_left₀ (by linarith) hlam 2
    have h4 : (1 : ℝ) / ‖RHLean.centeredZero p‖ ^ 2
        ≤ 1 / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) h3
    have h5 : (1 : ℝ) / (‖Complex.Hadamard.divisorZeroIndex₀_val p‖ / 2) ^ 2
        = 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
      field_simp
      try ring
    linarith [h4, h5.symm ▸ h4]
  have hnum : ‖w / (w ^ 2 - RHLean.centeredZero p ^ 2)‖
      = ‖w‖ / ‖w ^ 2 - RHLean.centeredZero p ^ 2‖ := norm_div _ _
  rw [hnum]
  have step1 : ‖w‖ / ‖w ^ 2 - RHLean.centeredZero p ^ 2‖
      ≤ ‖w‖ / ((3 / 4) * ‖RHLean.centeredZero p‖ ^ 2) :=
    div_le_div_of_nonneg_left (norm_nonneg w) hden0 hden
  refine step1.trans ?_
  have hfac : ‖w‖ / ((3 / 4) * ‖RHLean.centeredZero p‖ ^ 2)
      = ‖w‖ * (4 / 3) * (1 / ‖RHLean.centeredZero p‖ ^ 2) := by
    field_simp
    try ring
  rw [hfac]
  have hw43 : (0 : ℝ) ≤ ‖w‖ * (4 / 3) := by positivity
  have hstep2 : ‖w‖ * (4 / 3) * (1 / ‖RHLean.centeredZero p‖ ^ 2)
      ≤ ‖w‖ * (4 / 3) * (4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hinv hw43
  refine hstep2.trans (le_of_eq ?_)
  rw [inv_pow]
  field_simp
  try ring

set_option maxHeartbeats 800000 in



theorem summable_norm_centered_hadamard {w : ℂ} (hw0 : w ≠ 0)
    (hne : ∀ p : XZ__wp_WP_B3_domination, w ^ 2 - RHLean.centeredZero p ^ 2 ≠ 0) :
    Summable (fun p : XZ__wp_WP_B3_domination => ‖w / (w ^ 2 - RHLean.centeredZero p ^ 2)‖) := by
  classical
  have hsumm0 : Summable (fun p : XZ__wp_WP_B3_domination =>
      (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
  refine Summable.of_norm_bounded_eventually (hsumm0.mul_left ((16 / 3) * ‖w‖)) ?_
  have hfin : ({p : XZ__wp_WP_B3_domination | ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
      ≤ max 1 (2 * ‖w‖ + 1 / 2)}).Finite :=
    Complex.Hadamard.divisorZeroIndex₀_norm_le_finite (f := Complex.riemannXi)
      (U := Set.univ) (max 1 (2 * ‖w‖ + 1 / 2)) (by simp)
  refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
  intro p hp
  simpa only [Set.mem_setOf_eq, norm_norm] using far_bound__wp_WP_B3_domination (not_le.mp hp)

set_option maxHeartbeats 800000 in


theorem norm_logDeriv_le_tsum_hadamardSec {w : ℂ} (hw0 : w ≠ 0)
    (hne : ∀ p : XZ__wp_WP_B3_domination, w ^ 2 - RHLean.centeredZero p ^ 2 ≠ 0) :
    ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + w)‖
      ≤ ∑' p : XZ__wp_WP_B3_domination,
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) w.im w.re := by
  classical
  have hw1 : ∀ p : XZ__wp_WP_B3_domination, w ≠ RHLean.centeredZero p := by
    intro p h
    exact hne p (by rw [h]; ring)
  have hw2 : ∀ p : XZ__wp_WP_B3_domination, w ≠ -RHLean.centeredZero p := by
    intro p h
    exact hne p (by rw [h]; ring)
  rw [ExplicitFormula.hadamardDensityCentered w hw1 hw2]
  have hsumm := summable_norm_centered_hadamard hw0 hne
  have hEq : (fun p : XZ__wp_WP_B3_domination => ‖w / (w ^ 2 - RHLean.centeredZero p ^ 2)‖)
      = fun p : XZ__wp_WP_B3_domination =>
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) w.im w.re := by
    funext p
    rw [RHLean.ExplicitFormula.hadamardSec]
    have hw : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w := Complex.re_add_im w
    rw [hw]
  rw [← hEq]
  exact norm_tsum_le_tsum_norm hsumm

end RHLean.WP

#print axioms RHLean.WP.summable_norm_centered_hadamard
#print axioms RHLean.WP.norm_logDeriv_le_tsum_hadamardSec



end Inline_wp_WP_B3_domination

section Inline_wp_WP_B3_tonelli













open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval ENNReal



namespace RHLean.WP


private abbrev XZ__wp_WP_B3_tonelli := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)


private noncomputable def hJ__wp_WP_B3_tonelli (μ : ℂ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec μ q.1 q.2)


private theorem measurable_hJ__wp_WP_B3_tonelli (μ : ℂ) : Measurable (hJ__wp_WP_B3_tonelli μ) := by
  have hW : Measurable fun q : ℝ × ℝ => ((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) := by fun_prop
  have hD : Measurable fun q : ℝ × ℝ =>
      (((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2) := by fun_prop
  have hEq : hJ__wp_WP_B3_tonelli μ = fun q : ℝ × ℝ => ENNReal.ofReal
      (‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I)‖
        / ‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2‖) := by
    funext q
    rw [hJ__wp_WP_B3_tonelli, RHLean.ExplicitFormula.hadamardSec, norm_div]
  rw [hEq]
  exact ENNReal.measurable_ofReal.comp (hW.norm.div hD.norm)



private theorem measurable_hSec_fixed__wp_WP_B3_tonelli (μ : ℂ) (t : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec μ t x) := by
  have hEq : (fun x : ℝ => ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec μ t x))
      = fun x : ℝ => ENNReal.ofReal
          (‖((x : ℂ) + (t : ℂ) * Complex.I)‖
            / ‖((x : ℂ) + (t : ℂ) * Complex.I) ^ 2 - μ ^ 2‖) := by
    funext x
    rw [RHLean.ExplicitFormula.hadamardSec, norm_div]
  rw [hEq]
  refine ENNReal.measurable_ofReal.comp ?_
  have hW : Measurable fun x : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hD : Measurable fun x : ℝ => (((x : ℂ) + (t : ℂ) * Complex.I) ^ 2 - μ ^ 2) := by
    fun_prop
  exact hW.norm.div hD.norm



theorem lintegral_lintegral_tsum_hadamardSec (a b : ℝ) :
    (∫⁻ t in Ι a b, ∫⁻ x in Ι (-(1 / 2) : ℝ) (1 / 2),
        (∑'
          ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
            (Complex.Hadamard.divisorZeroIndex₀_val p) t x)))
      = ∑' p : XZ__wp_WP_B3_tonelli, (∫⁻ t in Ι a b, ∫⁻ x in Ι (-(1 / 2) : ℝ) (1 / 2),
          ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
            (Complex.Hadamard.divisorZeroIndex₀_val p) t x)) := by
  classical

  have hpt : ∀ t : ℝ,
      (∫⁻ x in Ι (-(1 / 2) : ℝ) (1 / 2),
          (∑'
            ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
              (Complex.Hadamard.divisorZeroIndex₀_val p) t x)))
        = ∑' p : XZ__wp_WP_B3_tonelli, (∫⁻ x in Ι (-(1 / 2) : ℝ) (1 / 2),
            ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
              (Complex.Hadamard.divisorZeroIndex₀_val p) t x)) := by
    intro t
    refine lintegral_tsum (μ := volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))
      (f := fun (p : XZ__wp_WP_B3_tonelli) (x : ℝ) =>
        ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
          (Complex.Hadamard.divisorZeroIndex₀_val p) t x)) (fun p => ?_)
    exact ((measurable_hSec_fixed__wp_WP_B3_tonelli (Complex.Hadamard.divisorZeroIndex₀_val p)
      t).aemeasurable).mono_measure Measure.restrict_le_self

  refine (lintegral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
  refine lintegral_tsum (μ := volume.restrict (Ι a b))
    (f := fun (p : XZ__wp_WP_B3_tonelli) (t : ℝ) => ∫⁻ x in Ι (-(1 / 2) : ℝ) (1 / 2),
      ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec
        (Complex.Hadamard.divisorZeroIndex₀_val p) t x)) (fun p => ?_)
  have hjoint : AEMeasurable (hJ__wp_WP_B3_tonelli (Complex.Hadamard.divisorZeroIndex₀_val p))
      ((volume.restrict (Ι a b)).prod (volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))) :=
    (measurable_hJ__wp_WP_B3_tonelli _).aemeasurable.mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  exact hjoint.lintegral_prod_right'

end RHLean.WP

#print axioms RHLean.WP.lintegral_lintegral_tsum_hadamardSec



end Inline_wp_WP_B3_tonelli

section Inline_wp_WP_B3_transfer
















open MeasureTheory Complex Set
open scoped Real Topology BigOperators Interval ENNReal

namespace RHLean.WP

abbrev XZ := Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)


noncomputable def W (q : ℝ × ℝ) : ℂ := (q.2 : ℂ) + (q.1 : ℂ) * Complex.I

private theorem W_re__wp_WP_B3_transfer {q : ℝ × ℝ} : (W q).re = q.2 := by simp [W]

private theorem W_im__wp_WP_B3_transfer {q : ℝ × ℝ} : (W q).im = q.1 := by simp [W]


private theorem eq_of_W_eq__wp_WP_B3_transfer {q : ℝ × ℝ} {z : ℂ} (h : W q = z) : q = (z.im, z.re) := by
  have h1 : q.1 = z.im := by rw [← W_im__wp_WP_B3_transfer (q := q), h]
  have h2 : q.2 = z.re := by rw [← W_re__wp_WP_B3_transfer (q := q), h]
  exact Prod.ext h1 h2


private def badSet__wp_WP_B3_transfer : Set (ℝ × ℝ) :=
  {q | (∃ p : XZ, W q = RHLean.centeredZero p ∨ W q = -RHLean.centeredZero p)
    ∨ W q = 0}

private theorem countable_badSet__wp_WP_B3_transfer : badSet__wp_WP_B3_transfer.Countable := by
  have hsub : ∀ z : ℂ, ({q : ℝ × ℝ | W q = z} : Set (ℝ × ℝ)).Subsingleton := by
    intro z a ha b hb
    rw [eq_of_W_eq__wp_WP_B3_transfer ha, eq_of_W_eq__wp_WP_B3_transfer hb]
  have h1 : ({q : ℝ × ℝ | ∃ p : XZ, W q = RHLean.centeredZero p
      ∨ W q = -RHLean.centeredZero p}).Countable := by
    have hfam : ∀ p : XZ, (({q : ℝ × ℝ | W q = RHLean.centeredZero p}
        ∪ {q : ℝ × ℝ | W q = -RHLean.centeredZero p}) : Set (ℝ × ℝ)).Countable :=
      fun p => Set.Countable.union (Set.Subsingleton.countable (hsub _))
        (Set.Subsingleton.countable (hsub _))
    refine Set.Countable.mono ?_ (Set.countable_iUnion hfam)
    intro q hq
    obtain ⟨p, hp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p, by rcases hp with h | h <;> simp [h]⟩
  refine Set.Countable.mono (s₂ := (({q : ℝ × ℝ | ∃ p : XZ, W q = RHLean.centeredZero p
      ∨ W q = -RHLean.centeredZero p} ∪ {q : ℝ × ℝ | W q = 0}) : Set (ℝ × ℝ))) ?_
    (Set.Countable.union h1 (Set.Subsingleton.countable (hsub 0)))
  intro q hq
  rcases hq with h | h
  · exact Or.inl h
  · exact Or.inr h


noncomputable def muwin (n : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ι n (n + 1))).prod (volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))

private theorem muwin_badSet__wp_WP_B3_transfer (n : ℝ) : muwin n badSet__wp_WP_B3_transfer = 0 := by
  have hbad0 : (volume.prod volume) badSet__wp_WP_B3_transfer = 0 :=
    countable_badSet__wp_WP_B3_transfer.measure_zero (volume.prod volume)
  have hle : muwin n ≤ volume.prod volume :=
    Measure.prod_mono (Measure.restrict_le_self (s := Ι n (n + 1)))
      (Measure.restrict_le_self (s := Ι (-(1 / 2) : ℝ) (1 / 2)))
  exact le_antisymm (le_trans (hle badSet__wp_WP_B3_transfer) (le_of_eq hbad0)) (by simp)


private theorem domination_of_not_bad__wp_WP_B3_transfer {q : ℝ × ℝ} (hq : q ∉ badSet__wp_WP_B3_transfer) :
    ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖
      ≤ ∑' p : XZ,
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2 := by
  have hw0 : W q ≠ 0 := fun h => hq (Or.inr h)
  have hne : ∀ p : XZ, W q ^ 2 - RHLean.centeredZero p ^ 2 ≠ 0 := by
    intro p h
    have hfac : W q ^ 2 - RHLean.centeredZero p ^ 2
        = (W q - RHLean.centeredZero p) * (W q + RHLean.centeredZero p) := by ring
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact hq (Or.inl ⟨p, Or.inl (sub_eq_zero.mp h1)⟩)
    · exact hq (Or.inl ⟨p, Or.inr (by linear_combination h1)⟩)
  have h := norm_logDeriv_le_tsum_hadamardSec hw0 hne
  simpa [W_re__wp_WP_B3_transfer, W_im__wp_WP_B3_transfer] using h

private theorem W_ne_zero_of_not_bad__wp_WP_B3_transfer {q : ℝ × ℝ} (hq : q ∉ badSet__wp_WP_B3_transfer) : W q ≠ 0 :=
  fun h => hq (Or.inr h)

private theorem summable_hSec_of_not_bad__wp_WP_B3_transfer {q : ℝ × ℝ} (hq : q ∉ badSet__wp_WP_B3_transfer) :
    Summable (fun p : XZ =>
      RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2) := by
  have hw0 : W q ≠ 0 := W_ne_zero_of_not_bad__wp_WP_B3_transfer hq
  have hne : ∀ p : XZ, W q ^ 2 - RHLean.centeredZero p ^ 2 ≠ 0 := by
    intro p h
    have hfac : W q ^ 2 - RHLean.centeredZero p ^ 2
        = (W q - RHLean.centeredZero p) * (W q + RHLean.centeredZero p) := by ring
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact hq (Or.inl ⟨p, Or.inl (sub_eq_zero.mp h1)⟩)
    · exact hq (Or.inl ⟨p, Or.inr (by linear_combination h1)⟩)
  have h := summable_norm_centered_hadamard hw0 hne
  refine h.congr fun p => ?_
  simp [RHLean.ExplicitFormula.hadamardSec, W]


theorem ae_domination_and_summable (n : ℝ) :
    ∀ᵐ q ∂(muwin n),
      (‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖
          ≤ ∑'
              RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
      ∧ Summable (fun p : XZ =>
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2) := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun q hq => ?_) (muwin_badSet__wp_WP_B3_transfer n)
  by_contra hq'
  exact hq ⟨domination_of_not_bad__wp_WP_B3_transfer hq', summable_hSec_of_not_bad__wp_WP_B3_transfer hq'⟩


private theorem measurable_hSec_ofReal__wp_WP_B3_transfer (μ : ℂ) :
    Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec μ q.1 q.2) := by
  have hEq : (fun q : ℝ × ℝ =>
        ENNReal.ofReal (RHLean.ExplicitFormula.hadamardSec μ q.1 q.2))
      = fun q : ℝ × ℝ => ENNReal.ofReal
          (‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I)‖
            / ‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2‖) := by
    funext q
    rw [RHLean.ExplicitFormula.hadamardSec, norm_div]
  rw [hEq]
  refine ENNReal.measurable_ofReal.comp ?_
  have hW : Measurable fun q : ℝ × ℝ => ((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) := by
    fun_prop
  have hD : Measurable fun q : ℝ × ℝ =>
      (((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2) := by fun_prop
  exact hW.norm.div hD.norm

set_option maxHeartbeats 800000 in

theorem lintegral_window_le_tsum (n : ℝ) :
    (∫⁻ q, ENNReal.ofReal
        ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
      ≤ ∑' p : XZ, ∫⁻ q, ENNReal.ofReal
          (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
          ∂(muwin n) := by
  have hae : (fun q => ENNReal.ofReal
        ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖)
      ≤ᵐ[muwin n] (fun q => ∑'
          (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)) := by
    filter_upwards [ae_domination_and_summable n] with q hq
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun p : XZ =>
      RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
      (fun p => norm_nonneg _) hq.2]
    exact ENNReal.ofReal_le_ofReal hq.1
  refine le_trans (lintegral_mono_ae hae) (le_of_eq ?_)
  refine lintegral_tsum (μ := muwin n)
    (f := fun (p : XZ) (q : ℝ × ℝ) => ENNReal.ofReal
      (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)) (fun p => ?_)
  exact (measurable_hSec_ofReal__wp_WP_B3_transfer _).aemeasurable




noncomputable def prcost (n : ℝ) (p : XZ) : ℝ :=
  ∫ q, RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2 ∂(muwin n)

theorem prcost_nonneg (n : ℝ) (p : XZ) : 0 ≤ prcost n p := by
  refine integral_nonneg ?_
  intro q
  exact norm_nonneg _

set_option maxHeartbeats 800000 in

theorem integral_window_le_tsum_of {n : ℝ} {c : XZ → ℝ} (hc : ∀ p, 0 ≤ c p)
    (hmeas : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n))
    (hfin : ∀ p : XZ, (∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = ENNReal.ofReal (c p))
    (hsumm : Summable c) :
    (∫ q, ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
      ≤ ∑' p : XZ, c p := by
  have hnonneg : (0 : ℝ × ℝ → ℝ) ≤ fun q =>
      ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ := fun q => norm_nonneg _
  have hEq : (∫ q, ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
      = (∫⁻ q, ENNReal.ofReal
          ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg) hmeas
  have htoReal : (∑'
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = ENNReal.ofReal (∑' p : XZ, c p) := by
    have h1 : (fun p : XZ => ∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = fun p : XZ => ENNReal.ofReal (c p) := by
      funext p
      exact hfin p
    rw [h1, ENNReal.ofReal_tsum_of_nonneg hc hsumm]
  rw [hEq]
  have hstep := lintegral_window_le_tsum n
  refine le_trans (ENNReal.toReal_mono ?_ hstep) ?_
  · rw [htoReal]
    exact ENNReal.ofReal_ne_top
  · rw [htoReal, ENNReal.toReal_ofReal (tsum_nonneg hc)]


theorem integral_window_le_tsum {n : ℝ}
    (hmeas : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n))
    (hfin : ∀ p : XZ, (∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = ENNReal.ofReal (prcost n p))
    (hsumm : Summable (fun p : XZ => prcost n p)) :
    (∫ q, ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
      ≤ ∑'
  integral_window_le_tsum_of (c := fun p => prcost n p) (prcost_nonneg n) hmeas hfin hsumm

end RHLean.WP

#print axioms RHLean.WP.integral_window_le_tsum_of
#print axioms RHLean.WP.ae_domination_and_summable
#print axioms RHLean.WP.lintegral_window_le_tsum
#print axioms RHLean.WP.prcost_nonneg
#print axioms RHLean.WP.integral_window_le_tsum



end Inline_wp_WP_B3_transfer

section Inline_wp_WP_B3_window











open MeasureTheory Complex Set
open scoped Real Topology BigOperators

namespace RHLean.WP

set_option maxHeartbeats 400000 in



theorem exists_poly_window_bound {g : ℝ → ℝ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : ∀ n : ℝ, 1 ≤ n → g n ≤ A * (n + 2) ^ 3 + C * Real.sqrt (n + 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℝ, 1 ≤ n → g n ≤ K * (1 + n) ^ 3 := by
  refine ⟨27 * (A + C), by positivity, fun n hn => ?_⟩
  have h2 : (1 : ℝ) ≤ n + 2 := by linarith

  have hsqrt : Real.sqrt (n + 2) ≤ (n + 2) ^ 3 := by
    have h1 : Real.sqrt (n + 2) ≤ n + 2 := by
      conv_rhs => rw [← Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ n + 2)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hnon : (0 : ℝ) ≤ (n + 2) * ((n + 2) - 1) * ((n + 2) + 1) := by
      have hx : (0 : ℝ) ≤ n + 2 := by linarith
      have hy : (0 : ℝ) ≤ (n + 2) - 1 := by linarith
      have hz : (0 : ℝ) ≤ (n + 2) + 1 := by linarith
      positivity
    have hfac : (n + 2) ^ 3 - (n + 2)
        = (n + 2) * ((n + 2) - 1) * ((n + 2) + 1) := by ring
    linarith [h1, hnon, hfac.symm.le, hfac.le]

  have hcube : (n + 2) ^ 3 ≤ 27 * (1 + n) ^ 3 := by
    have hle : n + 2 ≤ 3 * (1 + n) := by linarith
    have h3 : (n + 2) ^ 3 ≤ (3 * (1 + n)) ^ 3 := pow_le_pow_left₀ (by linarith) hle 3
    have h4 : (3 * (1 + n)) ^ 3 = 27 * (1 + n) ^ 3 := by ring
    linarith [h3, h4.symm.le, h4.le]
  have hAc : 0 ≤ A + C := by linarith
  calc g n ≤ A * (n + 2) ^ 3 + C * Real.sqrt (n + 2) := h n hn
    _ ≤ A * (n + 2) ^ 3 + C * (n + 2) ^ 3 := by
        have hC' : C * Real.sqrt (n + 2) ≤ C * (n + 2) ^ 3 :=
          mul_le_mul_of_nonneg_left hsqrt hC
        linarith
    _ = (A + C) * (n + 2) ^ 3 := by ring
    _ ≤ (A + C) * (27 * (1 + n) ^ 3) := mul_le_mul_of_nonneg_left hcube hAc
    _ = 27 * (A + C) * (1 + n) ^ 3 := by ring

end RHLean.WP

#print axioms RHLean.WP.exists_poly_window_bound



end Inline_wp_WP_B3_window

section Inline_wp_WP_hwin















open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval ENNReal

namespace RHLean.WP

set_option maxHeartbeats 1200000 in


theorem hwin_of_transfer
    (hCcard : 0 ≤ Ccard) (hCfar : 0 ≤ Cfar)
    (sectionInt : ℝ → ℝ)
    (hbridge : ∀ n : ℝ, (∫ t in n..(n + 1), sectionInt t)
      = ∫ q, ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
    (hmeas : ∀ n : ℝ, AEStronglyMeasurable
      (fun q : ℝ × ℝ => ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n))
    (hfin : ∀ (n : ℝ) (p : XZ), (∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = ENNReal.ofReal (RHLean.WP.wcost n p))
    (hcount : ∀ T : ℝ, 2 ≤ T →
      ((RHLean.ExplicitFormula.zeroBall (2 * (1 + T))).card : ℝ)
        ≤ Ccard * (1 + T) ^ ((3 : ℝ) / 2))
    (hfar : ∀ n : ℝ, 1 ≤ n → 16 * (n + 2) *
        (∑' p : XZ,
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ Cfar * Real.sqrt (n + 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℝ, 1 ≤ n →
      (∫ t in n..(n + 1), sectionInt t) ≤ K * (1 + n) ^ k := by
  classical

  have hstep : ∀ n : ℝ, 1 ≤ n →
      (∫ t in n..(n + 1), sectionInt t)
        ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3
            + Cfar * Real.sqrt (n + 2) := by
    intro n hn
    rw [hbridge n]
    calc (∫ q, ‖logDeriv Complex.riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
        ≤ ∑'
          integral_window_le_tsum_of (c := fun p => RHLean.WP.wcost n p)
            (fun p => RHLean.WP.wcost_nonneg p) (hmeas n) (hfin n)
            (RHLean.WP.summable_wcost (by linarith))
      _ ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3
            + Cfar * Real.sqrt (n + 2) :=
          RHLean.WP.tsum_window_cost_le_bands hCcard hcount (hfar n hn) hn
  obtain ⟨K, hK0, hKn⟩ := exists_poly_window_bound (g := fun n => ∫ t in n..(n + 1), sectionInt t)
    (A := Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) (C := Cfar)
    (by positivity) hCfar hstep
  exact ⟨K, hK0, 3, fun n hn => hKn n hn⟩

end RHLean.WP

#print axioms RHLean.WP.hwin_of_transfer



end Inline_wp_WP_hwin

section Inline_wp_WP_A3_hex














open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval ENNReal

namespace RHLean.WP

set_option maxHeartbeats 800000 in

theorem admissibleT_of_avoid {T : ℕ → ℝ}
    (hTend : Tendsto T atTop atTop) (hpos : ∀ n, 0 < T n)
    (havoid : ∀ n (p : ExplicitFormula.XiZero), T n ≠ (RHLean.centeredZero p).im
      ∧ T n ≠ -((RHLean.centeredZero p).im)) :
    ExplicitFormula.AdmissibleT T := by
  refine ⟨hTend, hpos, ?_⟩
  intro n p hp
  have hτ : (0 : ℝ) < T n := hpos n
  have hre : -(1 / 2 : ℝ) < (RHLean.centeredZero p).re
      ∧ (RHLean.centeredZero p).re < 1 / 2 := by
    have hval := val_re_mem_Ioo p
    have h : (RHLean.centeredZero p).re =
        (Complex.Hadamard.divisorZeroIndex₀_val p).re - 1 / 2 := by
      rw [RHLean.centeredZero, Complex.sub_re]
      norm_num
    rw [h]
    exact ⟨by linarith [hval.1], by linarith [hval.2]⟩
  have him : -(T n) ≤ (RHLean.centeredZero p).im ∧ (RHLean.centeredZero p).im ≤ T n := by
    rw [ExplicitFormula.rectClosed, ExplicitFormula.stripLeft_re, ExplicitFormula.stripLeft_im,
      ExplicitFormula.stripRight_re, ExplicitFormula.stripRight_im] at hp
    constructor
    · have := hp.2.2.1
      rwa [min_eq_left (by linarith : -(T n) ≤ T n)] at this
    · have := hp.2.2.2
      rwa [max_eq_right (by linarith : -(T n) ≤ T n)] at this
  have hne := havoid n p
  rw [ExplicitFormula.rectOpen, ExplicitFormula.stripLeft_re, ExplicitFormula.stripLeft_im,
    ExplicitFormula.stripRight_re, ExplicitFormula.stripRight_im]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmin := min_le_left (-(1 / 2) : ℝ) (1 / 2)
    linarith [hre.1]
  · have hmax := le_max_right (-(1 / 2) : ℝ) (1 / 2)
    linarith [hre.2]
  · have hmin := min_le_left (-(T n)) (T n)
    refine lt_of_le_of_ne (by linarith [him.1]) ?_
    intro h
    exact hne.2 (by linarith [h])
  · have hmax := le_max_right (-(T n)) (T n)
    refine lt_of_le_of_ne (by linarith [him.2]) ?_
    intro h
    exact hne.1 (by linarith [h])

set_option maxHeartbeats 800000 in

theorem hex_at_of_side_facts (a : ℝ) {Bad : Set ℝ}
    (hBadtot : volume Bad = 0)
    (hBadsub : ∀ p : ExplicitFormula.XiZero,
      (RHLean.centeredZero p).im ∈ Bad ∧ -((RHLean.centeredZero p).im) ∈ Bad)
    (hintWin : ∀ n : ℕ, IntervalIntegrable sectionInt volume (n : ℝ) ((n : ℝ) + 1))
    (hsec : ∀ t : ℝ, t ∉ Bad → IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2))
    (hwin : ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∫ t in (n : ℝ)..((n : ℝ) + 1), sectionInt t ≤ K * (1 + (n : ℝ)) ^ k) :
    ∃ T : ℕ → ℝ, ExplicitFormula.AdmissibleT T ∧ ExplicitFormula.HorizontalControl T := by
  obtain ⟨T, hTbad, hTpos, hTtop, hctrl⟩ :=
    horizontalControl_of_window_bound hBadtot hintWin hsec hwin
  refine ⟨T, ?_, hctrl⟩

  have havoid : ∀ n (p : ExplicitFormula.XiZero), T n ≠ (RHLean.centeredZero p).im
      ∧ T n ≠ -((RHLean.centeredZero p).im) := by
    intro n p
    constructor
    · intro h
      exact hTbad n (h ▸ (hBadsub p).1)
    · intro h
      exact hTbad n (h ▸ (hBadsub p).2)
  exact admissibleT_of_avoid hTtop hTpos havoid


def badOrd : Set ℝ := {t | ∃ p : ExplicitFormula.XiZero,
  t = (RHLean.centeredZero p).im ∨ t = -((RHLean.centeredZero p).im)}

theorem badOrd_mem (p : ExplicitFormula.XiZero) :
    (RHLean.centeredZero p).im ∈ badOrd ∧ -((RHLean.centeredZero p).im) ∈ badOrd :=
  ⟨⟨p, Or.inl rfl⟩, ⟨p, Or.inr rfl⟩⟩

theorem badOrd_countable : badOrd.Countable := by
  have h1 : ({t : ℝ | ∃ p : ExplicitFormula.XiZero,
      t = (RHLean.centeredZero p).im}).Countable :=
    Set.Countable.mono (fun t ht => by
        obtain ⟨p, h⟩ := ht
        exact ⟨p, h.symm⟩) (Set.countable_range _)
  have h2 : ({t : ℝ | ∃ p : ExplicitFormula.XiZero,
      t = -((RHLean.centeredZero p).im)}).Countable :=
    Set.Countable.mono (fun t ht => by
        obtain ⟨p, h⟩ := ht
        exact ⟨p, h.symm⟩) (Set.countable_range _)
  refine Set.Countable.mono ?_
    (Set.Countable.union h1 h2)
  intro t ht
  obtain ⟨p, h | h⟩ := ht
  · exact Or.inl ⟨p, h⟩
  · exact Or.inr ⟨p, h⟩

theorem badOrd_null : volume badOrd = 0 :=
  badOrd_countable.measure_zero volume

set_option maxHeartbeats 800000 in



theorem hex_of_side_facts
    (hintWin : ∀ n : ℕ, IntervalIntegrable sectionInt volume (n : ℝ) ((n : ℝ) + 1))
    (hsec : ∀ t : ℝ, t ∉ badOrd → IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2))
    (hwin : ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∫ t in (n : ℝ)..((n : ℝ) + 1), sectionInt t ≤ K * (1 + (n : ℝ)) ^ k) :
    ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, ExplicitFormula.AdmissibleT T ∧ ExplicitFormula.HorizontalControl T :=
  fun a f _hf => hex_at_of_side_facts a badOrd_null badOrd_mem hintWin hsec hwin




theorem weilExplicitFormulaOdd_of_side_facts_and_verticalEval
    (hintWin : ∀ n : ℕ, IntervalIntegrable sectionInt volume (n : ℝ) ((n : ℝ) + 1))
    (hsec : ∀ t : ℝ, t ∉ badOrd → IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2))
    (hwin : ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∫ t in (n : ℝ)..((n : ℝ) + 1), sectionInt t ≤ K * (1 + (n : ℝ)) ^ k)
    (hv : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalAt a) :
    ExplicitFormula.WeilExplicitFormulaOdd :=
  ExplicitFormula.weilExplicitFormulaOdd_of_control_verticalEval
    (hex_of_side_facts hintWin hsec hwin) hv

end RHLean.WP

#print axioms RHLean.WP.admissibleT_of_avoid
#print axioms RHLean.WP.hex_at_of_side_facts
#print axioms RHLean.WP.badOrd_null
#print axioms RHLean.WP.hex_of_side_facts
#print axioms RHLean.WP.weilExplicitFormulaOdd_of_side_facts_and_verticalEval



end Inline_wp_WP_A3_hex

section Inline_ExplicitFormula_RH105

















noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ComplexConjugate

namespace RHLean.ExplicitFormula






theorem integral_LSeries_trunc_eq_tsum_Ioc {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    (∫ y : ℝ, bridgeLine f y * LSeries vonMangoldtComplex (bridgeSpectralArgument ε y)
        ∂(volume.restrict (Set.Ioc (-T) T)))
      = ∑' n : ℕ,
          ∫ y : ℝ, bridgePrimeIntegrand f ε n y ∂(volume.restrict (Set.Ioc (-T) T)) := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (-T) T) with hμ
  have hg_int : Integrable (bridgeLine f) μ := (integrable_bridgeLine hf).restrict
  have hg_norm_int : Integrable (fun y => ‖bridgeLine f y‖) μ := hg_int.norm
  set G : ℝ := ∫ y, ‖bridgeLine f y‖ ∂μ with hG
  have hK_summable : Summable (primeLSeriesWeight ε) := summable_primeLSeriesWeight hε
  have hG_summable : Summable (fun n : ℕ => primeLSeriesWeight ε n * G) :=
    hK_summable.mul_right G
  have hF_int : ∀ n : ℕ, Integrable (bridgePrimeIntegrand f ε n) μ := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hzero : bridgePrimeIntegrand f ε 0 = fun _ => 0 := by
        funext y
        simp [bridgePrimeIntegrand, vonMangoldtComplex]
      rw [hzero]
      exact integrable_zero ℝ ℂ μ
    · have hcont : Continuous (bridgePrimeIntegrand f ε n) :=
        (continuous_bridgeLine hf).mul (continuous_const.mul
          (continuous_primeLSeriesKernel (ε := ε) hn))
      refine Integrable.mono'
        hcont.aestronglyMeasurable ?_
      filter_upwards with y
      rw [norm_bridgePrimeIntegrand]
  have hF_sum : Summable (fun n : ℕ => ∫ y, ‖bridgePrimeIntegrand f ε n y‖ ∂μ) := by
    refine hG_summable.congr fun n => ?_
    rw [integral_congr_ae (Eventually.of_forall
        (fun y => norm_bridgePrimeIntegrand f ε n y)),
      integral_mul_const, ← hG]
    ring
  have hhas : HasSum (fun n : ℕ => ∫ y, bridgePrimeIntegrand f ε n y ∂μ)
      (∫ y, ∑' n : ℕ, bridgePrimeIntegrand f ε n y ∂μ) :=
    hasSum_integral_of_summable_integral_norm hF_int hF_sum
  have hLHS : (∫ y : ℝ,
        bridgeLine f y * LSeries vonMangoldtComplex (bridgeSpectralArgument ε y) ∂μ)
      = ∫ y : ℝ, ∑'
    integral_congr_ae (Eventually.of_forall fun y =>
      (tsum_bridgePrimeIntegrand f ε y).symm)
  rw [hLHS, ← hhas.tsum_eq]


theorem integral_LSeries_trunc_eq_tsum {f : ℝ → ℂ} (hf : f ∈ oddCore)
    {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T) :
    (∫ y in (-T)..T, bridgeLine f y * LSeries vonMangoldtComplex (bridgeSpectralArgument ε y))
      = ∑' n : ℕ, ∫ y in (-T)..T, bridgePrimeIntegrand f ε n y := by
  simp_rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact integral_LSeries_trunc_eq_tsum_Ioc hf hε T

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.integral_LSeries_trunc_eq_tsum_Ioc
#print axioms RHLean.ExplicitFormula.integral_LSeries_trunc_eq_tsum

end

end Inline_ExplicitFormula_RH105

section Inline_ExplicitFormula_RH106
















noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators ComplexConjugate

namespace RHLean.ExplicitFormula


theorem tendsto_intervalIntegral_atTop {g : ℝ → ℂ} (hg : Integrable g volume) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, g y) atTop (𝓝 (∫ y : ℝ, g y)) := by
  have hmain : Tendsto (fun T : ℝ => ∫ y : ℝ, (Set.Ioc (-T) T).indicator g y)
      atTop (𝓝 (∫ y : ℝ, g y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y : ℝ => ‖g y‖)
      ?_ ?_ hg.norm ?_
    · filter_upwards with T
      exact hg.aestronglyMeasurable.indicator measurableSet_Ioc
    · filter_upwards with T
      filter_upwards with y
      by_cases hy : y ∈ Set.Ioc (-T) T
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, norm_zero]
        positivity
    · filter_upwards with y
      have hev : ∀ᶠ T : ℝ in atTop, y ∈ Set.Ioc (-T) T := by
        filter_upwards [eventually_ge_atTop (|y| + 1)] with T hT
        rw [Set.mem_Ioc]
        constructor <;> linarith [neg_abs_le y, le_abs_self y]
      refine Tendsto.congr'
      change g y = (Set.Ioc (-T) T).indicator g y
      rw [Set.indicator_of_mem hT]
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← integral_indicator measurableSet_Ioc]

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.tendsto_intervalIntegral_atTop

end

end Inline_ExplicitFormula_RH106

section Inline_ExplicitFormula_RH109























noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 800000

namespace RHLean.ExplicitFormula









def VerticalIntegralEvalFull (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, f ∈ localizedCore a →
    Integrable (fun y : ℝ =>
      bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)) ∧
    (∫ y : ℝ,
      bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)).re
      = Real.pi * (archimedeanBlock f + poleBlock f) - primeSideComb f a




theorem verticalIntegralEvalAt_of_full {a : ℝ}
    (h : VerticalIntegralEvalFull a) : VerticalIntegralEvalAt a := by
  intro f hf T hT
  obtain ⟨hint, hval⟩ := h f hf
  have hTend : Tendsto (fun n : ℕ =>
      ∫ y : ℝ in (-(T n))..(T n),
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I))
      atTop (𝓝 (∫ y : ℝ,
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I))) :=
    (tendsto_intervalIntegral_atTop hint).comp hT.1
  have hre : Tendsto (fun n : ℕ =>
      (∫ y : ℝ in (-(T n))..(T n),
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)).re)
      atTop (𝓝 ((∫ y : ℝ,
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hTend
  have hstrip : ∀ n : ℕ,
      stripRightIntegral (transf (autocorr f)) (T n)
        = ∫ y : ℝ in (-(T n))..(T n),
            bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I) := by
    intro n
    simp only [stripRightIntegral, xiLogIntegrand, bridgeLine]
    apply intervalIntegral.integral_congr
    intro y _hy
    dsimp only
    have harg : ((1 / 2 : ℂ) + (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
        = (1 : ℂ) + (y : ℂ) * I := by
      norm_num
      ring
    rw [harg]
    norm_num
  have hfinal : (∫ y : ℝ,
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)).re
      = Real.pi * (archimedeanBlock f + poleBlock f
          - (1 / Real.pi) * ∑ q ∈ arithSupport a, arithCoeff q * ghatAt f q) := by
    rw [hval]
    simp only [primeSideComb]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  have hmain : Tendsto (fun n : ℕ =>
        (stripRightIntegral (transf (autocorr f)) (T n)).re)
      atTop (𝓝 ((∫ y : ℝ,
        bridgeLine f y * logDeriv riemannXi ((1 : ℂ) + (y : ℂ) * I)).re)) :=
    hre.congr' (Eventually.of_forall fun n =>
      congrArg Complex.re (hstrip n).symm)
  rw [hfinal] at hmain
  exact hmain

end RHLean.ExplicitFormula



#print axioms RHLean.ExplicitFormula.verticalIntegralEvalAt_of_full

end

end Inline_ExplicitFormula_RH109

section Inline_wp_WP_A3_close






















open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval ENNReal

namespace RHLean.WP




theorem ofReal_iterated_intervalIntegral_eq_lintegral
    {a b c d : ℝ} (hab : a ≤ b) (_hcd : c ≤ d)
    {f : ℝ → ℝ → ℝ}
    (hmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (f q.1 q.2))
      ((volume.restrict (Set.Ioc c d)).prod (volume.restrict (Set.Ioc a b))))
    (hnonneg : ∀ t x, 0 ≤ f t x)
    (hinner : ∀ᵐ t ∂(volume.restrict (Set.Ioc c d)),
      Integrable (f t) (volume.restrict (Set.Ioc a b)))
    (houter : Integrable (fun t => ∫ x, f t x ∂(volume.restrict (Set.Ioc a b)))
      (volume.restrict (Set.Ioc c d))) :
    ENNReal.ofReal (∫ t in c..d, ∫ x in a..b, f t x)
      = ∫⁻ q, ENNReal.ofReal (f q.1 q.2)
          ∂((volume.restrict (Set.Ioc c d)).prod (volume.restrict (Set.Ioc a b))) := by
  rw [intervalIntegral.integral_of_le _hcd]
  simp_rw [intervalIntegral.integral_of_le hab]
  have hcongr : (fun t => ENNReal.ofReal
        (∫ x, f t x ∂(volume.restrict (Set.Ioc a b))))
      =ᵐ[volume.restrict (Set.Ioc c d)]
        (fun t => ∫⁻ x, ENNReal.ofReal (f t x) ∂(volume.restrict (Set.Ioc a b))) := by
    filter_upwards [hinner] with t ht
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal ht
      (Eventually.of_forall (fun x => hnonneg t x))
  calc
    ENNReal.ofReal (∫ t, (∫ x, f t x ∂(volume.restrict (Set.Ioc a b)))
        ∂(volume.restrict (Set.Ioc c d)))
        = ∫⁻ t, ENNReal.ofReal
            (∫ x, f t x ∂(volume.restrict (Set.Ioc a b)))
            ∂(volume.restrict (Set.Ioc c d)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal houter
            (Eventually.of_forall (fun t =>
              integral_nonneg (fun x => hnonneg t x)))
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (f t x)
          ∂(volume.restrict (Set.Ioc a b)) ∂(volume.restrict (Set.Ioc c d)) :=
          lintegral_congr_ae hcongr
    _ = ∫⁻ q, ENNReal.ofReal (f q.1 q.2)
          ∂((volume.restrict (Set.Ioc c d)).prod
            (volume.restrict (Set.Ioc a b))) :=
          (MeasureTheory.lintegral_prod _ hmeas).symm


theorem measurable_hadamardSec_joint (μ : ℂ) :
    Measurable (fun q : ℝ × ℝ =>
      RHLean.ExplicitFormula.hadamardSec μ q.1 q.2) := by
  have hW : Measurable fun q : ℝ × ℝ =>
      ((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) := by fun_prop
  have hD : Measurable fun q : ℝ × ℝ =>
      (((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2) := by fun_prop
  have hEq : (fun q : ℝ × ℝ =>
        RHLean.ExplicitFormula.hadamardSec μ q.1 q.2)
      = fun q : ℝ × ℝ =>
          ‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I)‖
            / ‖((q.2 : ℂ) + (q.1 : ℂ) * Complex.I) ^ 2 - μ ^ 2‖ := by
    funext q
    rw [RHLean.ExplicitFormula.hadamardSec, norm_div]
  rw [hEq]
  exact hW.norm.div hD.norm


theorem integrable_hadamardSec_section {μ : ℂ} {t : ℝ}
    (ht1 : t ≠ μ.im) (ht2 : t ≠ -μ.im) :
    Integrable (fun x : ℝ => RHLean.ExplicitFormula.hadamardSec μ t x)
      (volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))) := by
  have hne : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I) ^ 2 - μ ^ 2 ≠ 0 := by
    intro x hzero
    have hfac : ((x : ℂ) + (t : ℂ) * Complex.I) ^ 2 - μ ^ 2
        = (((x : ℂ) + (t : ℂ) * Complex.I) - μ)
          * (((x : ℂ) + (t : ℂ) * Complex.I) + μ) := by ring
    rw [hfac] at hzero
    rcases mul_eq_zero.mp hzero with h1 | h1
    · have him : (((x : ℂ) + (t : ℂ) * Complex.I) - μ).im = 0 := by rw [h1]; simp
      simp at him
      exact ht1 (by linarith)
    · have him : (((x : ℂ) + (t : ℂ) * Complex.I) + μ).im = 0 := by rw [h1]; simp
      simp at him
      exact ht2 (by linarith)
  have hcont : Continuous (fun x : ℝ => RHLean.ExplicitFormula.hadamardSec μ t x) := by
    unfold RHLean.ExplicitFormula.hadamardSec
    have hgW : Continuous fun x : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hgD : Continuous fun x : ℝ =>
        ((x : ℂ) + (t : ℂ) * Complex.I) ^ 2 - μ ^ 2 := by fun_prop
    exact Continuous.norm (Continuous.div hgW hgD (fun x => hne x))
  have hOn : IntegrableOn (fun x : ℝ => RHLean.ExplicitFormula.hadamardSec μ t x)
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) volume :=
    hcont.integrableOn_Icc
  have hsub : Ι (-(1 / 2) : ℝ) (1 / 2) ⊆ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  simpa only [MeasureTheory.IntegrableOn] using hOn.mono_set hsub


theorem integrable_hadamardSec_outer {μ : ℂ} (hre : |μ.re| ≤ 1 / 2) (n : ℝ) :
    Integrable (fun t : ℝ => ∫ x, RHLean.ExplicitFormula.hadamardSec μ t x
      ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))))
      (volume.restrict (Ι n (n + 1))) := by
  have hjoint' : AEStronglyMeasurable (fun q : ℝ × ℝ =>
      RHLean.ExplicitFormula.hadamardSec μ q.1 q.2)
      (volume.prod (volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2)))) :=
    (measurable_hadamardSec_joint μ).aestronglyMeasurable.mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hsec_meas : AEStronglyMeasurable
      (fun t : ℝ => ∫ x, RHLean.ExplicitFormula.hadamardSec μ t x
        ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))))
      (volume.restrict (Ι n (n + 1))) :=
    (MeasureTheory.AEStronglyMeasurable.integral_prod_right' hjoint').mono_measure
      Measure.restrict_le_self
  have hmaj_int : Integrable
      (fun t : ℝ => 2 + |Real.log (|t - μ.im|)| + |Real.log (|t + μ.im|)|)
      (volume.restrict (Ι n (n + 1))) := by
    have h := RHLean.ExplicitFormula.intervalIntegrable_hadamardMajorant μ.im n (n + 1)
    have hn : n ≤ n + 1 := by linarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hn] at h
    simpa [MeasureTheory.IntegrableOn, Set.uIoc_of_le hn] using h
  refine Integrable.mono' hmaj_int hsec_meas ?_
  have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ μ.im := by
    rw [MeasureTheory.ae_iff]
    simp
  have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ -μ.im := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [MeasureTheory.ae_restrict_of_ae hae1,
    MeasureTheory.ae_restrict_of_ae hae2] with t ht1 ht2
  have hnonneg : 0 ≤ ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
      RHLean.ExplicitFormula.hadamardSec μ t x :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => norm_nonneg _)
  have hEq : (∫ x, RHLean.ExplicitFormula.hadamardSec μ t x
        ∂(volume.restrict (Ι (-(1 / 2) : ℝ) (1 / 2))))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          RHLean.ExplicitFormula.hadamardSec μ t x := by
    rw [show Ι (-(1 / 2) : ℝ) (1 / 2) = Set.Ioc (-(1 / 2) : ℝ) (1 / 2) from
      Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hEq]; exact hnonneg), hEq]
  exact RHLean.ExplicitFormula.integral_norm_hadamardTerm_le_log hre ht1 ht2



theorem hfin (n : ℝ) (p : XZ) :
    (∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = ENNReal.ofReal (wcost n p) := by
  have hab : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hcd : n ≤ n + 1 := by linarith
  have hinner : ∀ᵐ t ∂(volume.restrict (Set.Ioc n (n + 1))),
      Integrable (fun x : ℝ =>
        RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x)
        (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) := by
    have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (RHLean.centeredZero p).im := by
      rw [MeasureTheory.ae_iff]; simp
    have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ -(RHLean.centeredZero p).im := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [MeasureTheory.ae_restrict_of_ae hae1,
      MeasureTheory.ae_restrict_of_ae hae2] with t ht1 ht2
    simpa [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] using
      integrable_hadamardSec_section (μ := RHLean.centeredZero p) ht1 ht2
  have houter : Integrable (fun t : ℝ => ∫ x,
        RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x
        ∂(volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))))
      (volume.restrict (Set.Ioc n (n + 1))) := by
    simpa [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2),
      Set.uIoc_of_le hcd] using
      integrable_hadamardSec_outer (μ := RHLean.centeredZero p)
        (RHLean.ExplicitFormula.abs_re_centeredZero_le p) n
  have hmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2))
      ((volume.restrict (Set.Ioc n (n + 1))).prod
        (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)))) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_hadamardSec_joint (RHLean.centeredZero p))).aemeasurable
  have hmain := ofReal_iterated_intervalIntegral_eq_lintegral
    (a := (-(1 / 2) : ℝ)) (b := 1 / 2) (c := n) (d := n + 1)
    hab hcd (f := fun t x => RHLean.ExplicitFormula.hadamardSec
      (RHLean.centeredZero p) t x) hmeas
    (fun t x => norm_nonneg _) hinner houter
  have hmu : muwin n = (volume.restrict (Set.Ioc n (n + 1))).prod
      (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) := by
    simp [muwin, Set.uIoc_of_le hcd, Set.uIoc_of_le hab]
  rw [hmu]
  simpa [wcost] using hmain.symm



theorem measurable_logDeriv_riemannXi : Measurable (logDeriv riemannXi) := by
  have hderiv_cont : Continuous (deriv riemannXi) :=
    continuous_iff_continuousAt.mpr fun s =>
      ((differentiable_riemannXi.analyticAt s).deriv).continuousAt
  rw [show logDeriv riemannXi = fun z => deriv riemannXi z / riemannXi z from
    funext fun z => logDeriv_apply riemannXi z]
  exact hderiv_cont.measurable.div differentiable_riemannXi.continuous.measurable


theorem measurable_W : Measurable (fun q : ℝ × ℝ => W q) := by
  unfold W
  fun_prop



theorem hmeas (n : ℝ) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ => ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n) :=
  (measurable_logDeriv_riemannXi.comp
    (measurable_const.add measurable_W)).norm.aestronglyMeasurable


theorem lintegral_window_lt_top {n : ℝ} (hn : 0 ≤ n) :
    (∫⁻ q, ENNReal.ofReal
        ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n)) < ∞ := by
  have hle := lintegral_window_le_tsum n
  have hcongr : (fun p : XZ => ∫⁻ q, ENNReal.ofReal
        (RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) q.1 q.2)
        ∂(muwin n)) = fun p : XZ => ENNReal.ofReal (wcost n p) := by
    funext p
    exact hfin n p
  rw [hcongr] at hle
  have hsumm : Summable (fun p : XZ => wcost n p) := summable_wcost hn
  have htsum : (∑' p : XZ, ENNReal.ofReal (wcost n p))
      = ENNReal.ofReal (∑'
    (ENNReal.ofReal_tsum_of_nonneg (fun p => wcost_nonneg p) hsumm).symm
  rw [htsum] at hle
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top


theorem integrable_logDeriv_muwin {n : ℝ} (hn : 0 ≤ n) :
    Integrable (fun q : ℝ × ℝ =>
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n) := by
  refine ⟨(measurable_logDeriv_riemannXi.comp
    (measurable_const.add measurable_W)).norm.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun q => norm_nonneg _))]
  exact lintegral_window_lt_top hn



theorem hbridge {n : ℝ} (hn : 1 ≤ n) :
    (∫ t in n..(n + 1), sectionInt t)
      = ∫ q, ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n) := by
  have hn0 : 0 ≤ n := by linarith
  have hcd : n ≤ n + 1 := by linarith
  have hx : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hjoint : Integrable (fun q : ℝ × ℝ =>
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖) (muwin n) :=
    integrable_logDeriv_muwin hn0
  have hmu : muwin n = (volume.restrict (Set.Ioc n (n + 1))).prod
      (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2))) := by
    simp [muwin, Set.uIoc_of_le hcd, Set.uIoc_of_le hx]
  have hjoint' : Integrable (fun q : ℝ × ℝ =>
      ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖)
      ((volume.restrict (Set.Ioc n (n + 1))).prod
        (volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)))) := by
    simpa [hmu] using hjoint
  rw [hmu]
  rw [intervalIntegral.integral_of_le hcd]
  unfold sectionInt
  conv_lhs =>
    arg 2
    ext x
    rw [intervalIntegral.integral_of_le hx]
  exact (MeasureTheory.integral_prod _ hjoint').symm



theorem hintWin (n : ℕ) :
    IntervalIntegrable sectionInt volume (n : ℝ) ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hjoint := integrable_logDeriv_muwin hn
  have houter := hjoint.integral_prod_left
  have hsec : Integrable (fun t : ℝ => sectionInt t)
      (volume.restrict (Ι (n : ℝ) ((n : ℝ) + 1))) := by
    convert houter using 1
    funext t
    rw [sectionInt_eq]
    rw [intervalIntegral.integral_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
    rw [show Ι (-(1 / 2) : ℝ) (1 / 2) = Set.Ioc (-(1 / 2) : ℝ) (1 / 2) from
      Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)]
    rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast Nat.le_succ n)]
  change Integrable sectionInt (volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1)))
  have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hEqset : volume.restrict (Ι (n : ℝ) ((n : ℝ) + 1))
      = volume.restrict (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
    rw [Set.uIoc_of_le hnle]
  rw [← hEqset]
  exact hsec



theorem exists_Ccard :
    ∃ Ccard : ℝ, 0 ≤ Ccard ∧ ∀ T : ℝ, 2 ≤ T →
      ((RHLean.ExplicitFormula.zeroBall (2 * (1 + T))).card : ℝ)
        ≤ Ccard * (1 + T) ^ ((3 : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := RHLean.ExplicitFormula.zeroBall_card_le_three_halves
  refine ⟨C * 2 ^ ((3 : ℝ) / 2), by positivity, fun T hT => ?_⟩
  have hR : (1 : ℝ) ≤ 2 * (1 + T) := by linarith
  have h := hC (2 * (1 + T)) hR
  refine h.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ 1 + T)]
  ring



theorem exists_Cfar :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧ ∀ n : ℝ, 1 ≤ n →
      16 * (n + 2) *
        (∑' p : XZ,
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
        ≤ Cfar * Real.sqrt (n + 2) := by
  obtain ⟨C, hC0, hC⟩ := RHLean.ExplicitFormula.far_band_sum_le
  refine ⟨4 * C, by positivity, fun n hn => ?_⟩
  have hT : (2 : ℝ) ≤ n + 1 := by linarith
  have h := hC (n + 1) hT
  have hsumm0 : Summable (fun p : XZ =>
      (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
  have hsumm2 : Summable (fun p : XZ =>
      (if 2 * (n + 2) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm0
    · split_ifs <;> positivity
    · split_ifs with hp
      · rw [one_div, inv_pow]
      · positivity
  have hsumm1 : Summable (fun p : XZ =>
      (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
        then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsumm2
    · split_ifs <;> positivity
    · by_cases hp : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
      · rw [if_pos hp, if_pos (by linarith)]
      · rw [if_neg hp]
        split_ifs <;> positivity
  have hle : (∑'
        (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
      ≤ (∑' p : XZ,
        (if 2 * (n + 2) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0)) := by
    refine hsumm1.tsum_le_tsum (fun p => ?_) hsumm2
    by_cases hp : 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
    · rw [if_pos hp, if_pos (by linarith)]
    · rw [if_neg hp]
      split_ifs <;> positivity
  have hbase : 4 * (n + 2) *
      (∑'
        (if 2 * (n + 2) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
          then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
      ≤ C * Real.sqrt (n + 2) := by
    simpa [show (1 : ℝ) + (n + 1) = n + 2 by ring] using h
  calc 16 * (n + 2) *
        (∑' p : XZ,
          (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
            then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))
      = 4 * (4 * (n + 2) *
          (∑'
            (if 2 * (n + 2) + 1 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
              then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))) := by ring
    _ ≤ 4 * (4 * (n + 2) *
          (∑' p : XZ,
            (if 2 * (n + 2) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖
              then (1 : ℝ) / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 else 0))) := by
        gcongr
    _ ≤ 4 * (C * Real.sqrt (n + 2)) := by gcongr
    _ = (4 * C) * Real.sqrt (n + 2) := by ring


theorem hwin_closed :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℝ, 1 ≤ n →
      (∫ t in n..(n + 1), sectionInt t) ≤ K * (1 + n) ^ k := by
  obtain ⟨Ccard, hCcard, hcount⟩ := exists_Ccard
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_Cfar
  have hstep : ∀ n : ℝ, 1 ≤ n →
      (∫ t in n..(n + 1), sectionInt t)
        ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3
            + Cfar * Real.sqrt (n + 2) := by
    intro n hn
    rw [hbridge hn]
    calc (∫ q, ‖logDeriv riemannXi ((1 / 2 : ℂ) + W q)‖ ∂(muwin n))
        ≤ ∑'
          integral_window_le_tsum_of (c := fun p => wcost n p)
            (fun p => wcost_nonneg p) (hmeas n) (hfin n)
            (summable_wcost (by linarith))
      _ ≤ (Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) * (n + 2) ^ 3
            + Cfar * Real.sqrt (n + 2) :=
          tsum_window_cost_le_bands hCcard hcount (hfar n hn) hn
  obtain ⟨K, hK0, hKn⟩ := RHLean.WP.exists_poly_window_bound
    (g := fun n => ∫ t in n..(n + 1), sectionInt t)
    (A := Ccard * 2 ^ ((3 : ℝ) / 2) * (74 + 24 * Real.log 6)) (C := Cfar)
    (by positivity) hCfar hstep
  exact ⟨K, hK0, 3, fun n hn => hKn n hn⟩


theorem hwin_nat :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k : ℕ, ∀ n : ℕ, 1 ≤ n →
      (∫ t in (n : ℝ)..((n : ℝ) + 1), sectionInt t) ≤ K * (1 + (n : ℝ)) ^ k := by
  obtain ⟨K, hK0, k, hK⟩ := hwin_closed
  exact ⟨K, hK0, k, fun n hn => hK n (by exact_mod_cast hn)⟩


theorem hex_closed (hsec : ∀ t : ℝ, t ∉ badOrd →
    IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2)) :
    ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, ExplicitFormula.AdmissibleT T ∧ ExplicitFormula.HorizontalControl T :=
  hex_of_side_facts hintWin hsec hwin_nat




theorem weilBridge_of_verticalEvalFull
    (hV : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalFull a)
    (hsec : ∀ t : ℝ, t ∉ badOrd →
      IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2)) :
    WeilBridge := by
  have hv : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalAt a :=
    fun a => ExplicitFormula.verticalIntegralEvalAt_of_full (hV a)
  have hodd := weilExplicitFormulaOdd_of_side_facts_and_verticalEval
    hintWin hsec hwin_nat hv
  intro a ha f hf
  exact hodd a ha f hf

end RHLean.WP

#print axioms RHLean.WP.ofReal_iterated_intervalIntegral_eq_lintegral
#print axioms RHLean.WP.hfin



end Inline_wp_WP_A3_close

section Inline_wp_WP_A3_hsec

















open MeasureTheory Complex Set Filter
open scoped Real Topology BigOperators Interval ENNReal

namespace RHLean.WP



theorem norm_hadamardTerm_far_abs {t : ℝ} {μ : ℂ}
    (hμ : 2 * (1 + |t|) ≤ ‖μ‖) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    ‖((x : ℂ) + (t : ℂ) * I) / (((x : ℂ) + (t : ℂ) * I) ^ 2 - μ ^ 2)‖
      ≤ 4 * (1 + |t|) / ‖μ‖ ^ 2 := by
  set w : ℂ := (x : ℂ) + (t : ℂ) * I with hwdef
  have ht1 : (0 : ℝ) < 1 + |t| := by positivity
  have hμ0 : 0 < ‖μ‖ := by linarith
  have hw : ‖w‖ ≤ 1 + |t| := by
    have h2 : ‖w‖ ^ 2 ≤ (1 + |t|) ^ 2 := by
      rw [hwdef, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_one, mul_zero,
        add_zero]
      have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        have := abs_le.mp hx
        nlinarith [this.1, this.2]
      have ht2 : t ^ 2 = |t| ^ 2 := by rw [sq_abs]
      nlinarith [hx2, ht2, abs_nonneg t]
    nlinarith [norm_nonneg w, abs_nonneg t]
  have h1 : ‖μ‖ / 2 ≤ ‖w - μ‖ := by
    have htri := norm_add_le (μ - w) w
    rw [sub_add_cancel, norm_sub_rev] at htri
    linarith
  have h2 : ‖μ‖ / 2 ≤ ‖w + μ‖ := by
    have htri := norm_add_le (μ + w) (-w)
    rw [show μ + w + -w = μ by ring, norm_neg, add_comm μ w] at htri
    linarith
  have hden : (‖μ‖ / 2) * (‖μ‖ / 2) ≤ ‖w - μ‖ * ‖w + μ‖ :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  rcases eq_or_ne (w ^ 2 - μ ^ 2) 0 with hzero | hne
  · rw [hzero, div_zero, norm_zero]
    positivity
  · have hfac : w ^ 2 - μ ^ 2 = (w - μ) * (w + μ) := by ring
    have hwμ : w - μ ≠ 0 := by intro h; exact hne (by rw [hfac, h, zero_mul])
    have hwμ' : w + μ ≠ 0 := by intro h; exact hne (by rw [hfac, h, mul_zero])
    rw [hfac, norm_div, norm_mul]
    rw [div_le_iff₀ (mul_pos (norm_pos_iff.mpr hwμ) (norm_pos_iff.mpr hwμ'))]
    calc ‖w‖ ≤ 1 + |t| := hw
      _ = (4 * (1 + |t|) / ‖μ‖ ^ 2) * ((‖μ‖ / 2) * (‖μ‖ / 2)) := by
          rw [show (4 * (1 + |t|) / ‖μ‖ ^ 2) * ((‖μ‖ / 2) * (‖μ‖ / 2))
              = (4 * (1 + |t|) * ((‖μ‖ / 2) * (‖μ‖ / 2))) / ‖μ‖ ^ 2 by ring]
          rw [eq_div_iff (pow_ne_zero 2 hμ0.ne')]
          ring
      _ ≤ (4 * (1 + |t|) / ‖μ‖ ^ 2) * (‖w - μ‖ * ‖w + μ‖) :=
          mul_le_mul_of_nonneg_left hden (by positivity)


theorem hadamardSec_le_sep {t : ℝ} {μ : ℂ}
    (hsep1 : t ≠ μ.im) (hsep2 : t ≠ -μ.im) (x : ℝ) :
    RHLean.ExplicitFormula.hadamardSec μ t x
      ≤ (1 / 2) * (1 / |t - μ.im| + 1 / |t + μ.im|) := by
  rw [RHLean.ExplicitFormula.hadamardSec]
  exact RHLean.ExplicitFormula.norm_hadamardTerm_sep hsep1 hsep2



theorem hsec {t : ℝ} (ht : t ∉ badOrd) :
    IntervalIntegrable (sectionFun t) volume (-(1 / 2)) (1 / 2) := by
  classical
  have hnot : ∀ p : XZ,
      t ≠ (RHLean.centeredZero p).im ∧ t ≠ -((RHLean.centeredZero p).im) := by
    intro p
    constructor
    · intro h
      exact ht ⟨p, Or.inl h⟩
    · intro h
      exact ht ⟨p, Or.inr h⟩
  let R : ℝ := 2 * (1 + |t|) + 1
  have hfin : ({p : XZ | ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R}).Finite :=
    Complex.Hadamard.divisorZeroIndex₀_norm_le_finite (f := Complex.riemannXi)
      (U := Set.univ) R (by simp)
  let s : Finset XZ := hfin.toFinset
  have hmem : ∀ p : XZ, p ∈ s ↔ ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R :=
    fun p => hfin.mem_toFinset
  let sep : XZ → ℝ := fun p => (1 / 2) *
    (1 / |t - (RHLean.centeredZero p).im| + 1 / |t + (RHLean.centeredZero p).im|)
  let far : XZ → ℝ := fun p =>
    16 * (1 + |t|) * (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2
  have hsep_nonneg : ∀ p : XZ, 0 ≤ sep p := by
    intro p
    have h1 : 0 ≤ |t - (RHLean.centeredZero p).im| := abs_nonneg _
    have h2 : 0 ≤ |t + (RHLean.centeredZero p).im| := abs_nonneg _
    have h3 : 0 ≤ 1 / |t - (RHLean.centeredZero p).im| := by positivity
    have h4 : 0 ≤ 1 / |t + (RHLean.centeredZero p).im| := by positivity
    exact mul_nonneg (by norm_num) (add_nonneg h3 h4)
  have hfar_nonneg : ∀ p : XZ, 0 ≤ far p := by
    intro p
    exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (sq_nonneg _)
  have hfar_summ : Summable far := by
    have h := summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.mul_left (16 * (1 + |t|))
    simpa [far] using h
  let M : ℝ := max ((∑ p ∈ s, sep p) + ∑' p : XZ, far p)
    ‖logDeriv riemannXi ((1 / 2 : ℂ))‖
  have hfx : ∀ x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), sectionFun t x ≤ M := by
    intro x hxI
    have hx : |x| ≤ 1 / 2 := by
      rw [abs_le]
      exact ⟨hxI.1, hxI.2⟩
    set w : ℂ := (x : ℂ) + (t : ℂ) * I with hwdef
    by_cases hw0 : w = 0
    ·
      have hx0 : x = 0 := by
        have := congrArg Complex.re hw0
        simpa [hwdef] using this
      have ht0 : t = 0 := by
        have := congrArg Complex.im hw0
        simpa [hwdef] using this
      subst x
      subst t
      have hval : sectionFun 0 0 = ‖logDeriv riemannXi ((1 / 2 : ℂ))‖ := by
        simp [sectionFun]
      rw [hval]
      exact le_max_right _ _
    · have hne : ∀ p : XZ, w ^ 2 - RHLean.centeredZero p ^ 2 ≠ 0 := by
        intro p hzero
        have hfac : w ^ 2 - RHLean.centeredZero p ^ 2
            = (w - RHLean.centeredZero p) * (w + RHLean.centeredZero p) := by ring
        rw [hfac] at hzero
        rcases mul_eq_zero.mp hzero with h1 | h1
        · have him : (w - RHLean.centeredZero p).im = 0 := by rw [h1]; simp
          simp [hwdef] at him
          exact (hnot p).1 (by linarith)
        · have him : (w + RHLean.centeredZero p).im = 0 := by rw [h1]; simp
          simp [hwdef] at him
          exact (hnot p).2 (by linarith)
      have hdom := norm_logDeriv_le_tsum_hadamardSec (w := w) hw0 hne
      have hdom'
          ∑' p : XZ, RHLean.ExplicitFormula.hadamardSec
            (RHLean.centeredZero p) t x := by
        simpa [hwdef] using hdom
      have hsumm_f : Summable (fun p : XZ =>
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x) := by
        have h := summable_norm_centered_hadamard (w := w) hw0 hne
        simpa [hwdef, RHLean.ExplicitFormula.hadamardSec] using h
      have hnear : (∑ p ∈ s,
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x)
          ≤ ∑ p ∈ s, sep p := by
        refine Finset.sum_le_sum (fun p _hp => ?_)
        exact hadamardSec_le_sep (hnot p).1 (hnot p).2 x
      have htail : (∑'
          RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p.1) t x)
          ≤ ∑' p : {p : XZ // p ∉ s}, far p.1 := by
        refine Summable.tsum_le_tsum (fun p => ?_) (hsumm_f.subtype _)
          (hfar_summ.subtype _)
        have hgt : R < ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ := by
          by_contra hle
          exact p.2 ((hmem p.1).mpr (not_lt.mp hle))
        have hnorm : ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖
            ≤ ‖RHLean.centeredZero p.1‖ + 1 / 2 := by
          have heq : RHLean.centeredZero p.1 + (1 / 2 : ℂ) =
              Complex.Hadamard.divisorZeroIndex₀_val p.1 := by
            unfold RHLean.centeredZero; ring
          have h := norm_add_le (RHLean.centeredZero p.1) (1 / 2 : ℂ)
          rw [heq] at h
          simpa using h
        have hμ : 2 * (1 + |t|) ≤ ‖RHLean.centeredZero p.1‖ := by
          have hR : R = 2 * (1 + |t|) + 1 := rfl
          linarith
        have hfar := norm_hadamardTerm_far_abs (t := t)
          (μ := RHLean.centeredZero p.1) (x := x) hμ hx
        have hρ3 : 3 ≤ ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ := by
          have hR3 : 3 ≤ R := by
            dsimp [R]
            have : 0 ≤ |t| := abs_nonneg t
            linarith
          linarith
        have hhalf : ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ / 2
            ≤ ‖RHLean.centeredZero p.1‖ := by
          linarith
        have hsq : (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ / 2) ^ 2
            ≤ ‖RHLean.centeredZero p.1‖ ^ 2 :=
          pow_le_pow_left₀ (by linarith) hhalf 2
        have hinv : (1 : ℝ) / ‖RHLean.centeredZero p.1‖ ^ 2
            ≤ 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ ^ 2 := by
          have h4 : (1 : ℝ) / ‖RHLean.centeredZero p.1‖ ^ 2
              ≤ 1 / (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ / 2) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) hsq
          have h5 : (1 : ℝ) / (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ / 2) ^ 2
              = 4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ ^ 2 := by
            field_simp
            ring
          linarith [h4, h5.symm ▸ h4]
        have hfar_le_far : 4 * (1 + |t|) / ‖RHLean.centeredZero p.1‖ ^ 2 ≤ far p.1 := by
          dsimp [far]
          calc 4 * (1 + |t|) / ‖RHLean.centeredZero p.1‖ ^ 2
              = 4 * (1 + |t|) * (1 / ‖RHLean.centeredZero p.1‖ ^ 2) := by ring
            _ ≤ 4 * (1 + |t|) * (4 / ‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
            _ = 16 * (1 + |t|) *
                (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹) ^ 2 := by
                rw [inv_pow]
                ring
        simpa [RHLean.ExplicitFormula.hadamardSec, hwdef] using hfar.trans hfar_le_far
      have hsplit := hsumm_f.sum_add_tsum_compl (s := s)
      have hfar_split := hfar_summ.sum_add_tsum_compl (s := s)
      have hnear_le : (∑ p ∈ s, sep p) ≤ M := by
        dsimp [M]
        exact le_trans (le_add_of_nonneg_right (tsum_nonneg (fun p => hfar_nonneg p)))
          (le_max_left _ _)
      have htail_le : (∑'
        have hfinite : 0 ≤ ∑ p ∈ s, far p := Finset.sum_nonneg (fun p _ => hfar_nonneg p)
        calc (∑' p : {p : XZ // p ∉ s}, far p.1)
            ≤ (∑ p ∈ s, far p) + ∑'
              le_add_of_nonneg_left hfinite
          _ = ∑' p : XZ, far p := hfar_split
      calc sectionFun t x
          = ‖logDeriv riemannXi ((1 / 2 : ℂ) + w)‖ := by simp [sectionFun, hwdef]
        _ ≤ ∑'
              RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x := hdom'
        _ = (∑ p ∈ s, RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p) t x)
              + ∑' p : {p : XZ // p ∉ s},
                  RHLean.ExplicitFormula.hadamardSec (RHLean.centeredZero p.1) t x :=
              hsplit.symm
        _ ≤ (∑ p ∈ s, sep p) + ∑'
              add_le_add hnear htail
        _ ≤ (∑ p ∈ s, sep p) + ∑' p : XZ, far p := by
              gcongr
        _ ≤ M := le_max_left _ _
  refine RHLean.ExplicitFormula.intervalIntegrable_logDeriv_norm_of_bound
    (T := t) (M := M) ?_
  intro x hxI
  exact hfx x hxI



theorem hex_complete :
    ∀ a : ℝ, ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      ∃ T : ℕ → ℝ, ExplicitFormula.AdmissibleT T ∧ ExplicitFormula.HorizontalControl T :=
  hex_closed (fun t ht => hsec ht)


theorem weilBridge_of_verticalEvalFull_closed
    (hV : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalFull a) : WeilBridge :=
  weilBridge_of_verticalEvalFull hV (fun t ht => hsec ht)

end RHLean.WP

#print axioms RHLean.WP.hex_complete
#print axioms RHLean.WP.weilBridge_of_verticalEvalFull_closed

#print axioms RHLean.WP.norm_hadamardTerm_far_abs
#print axioms RHLean.WP.hadamardSec_le_sep
#print axioms RHLean.WP.hsec



end Inline_wp_WP_A3_hsec








namespace RHLean




theorem weilBridge_of_verticalEvalFull
    (hV : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalFull a) : WeilBridge :=
  WP.weilBridge_of_verticalEvalFull_closed hV


theorem rh_full_proof_of_verticalEvalFull
    (hV : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalFull a)
    (hY7 : Y7OperatorTarget) (hII : GateIIOperatorStep) : RiemannHypothesis :=
  rh_full_proof (weilBridge_of_verticalEvalFull hV) hY7 hII


theorem riemannHypothesis_of_zhu_verticalEvalFull
    (hV : ∀ a : ℝ, ExplicitFormula.VerticalIntegralEvalFull a)
    (hzhu : ZhuBase.ZhuWindowPositivity)
    (hII : ZhuBase.GateIIOperatorStepFour) : RiemannHypothesis :=
  ZhuBase.riemannHypothesis_of_zhu (weilBridge_of_verticalEvalFull hV) hzhu hII

end RHLean

#print axioms RHLean.weilBridge_of_verticalEvalFull
#print axioms RHLean.rh_full_proof_of_verticalEvalFull
#print axioms RHLean.riemannHypothesis_of_zhu_verticalEvalFull



section Inline_GateII_Chain







































namespace RHLean.GateII.Chain

open Finset
open MeasureTheory
open Filter
open scoped Topology




noncomputable def Lambda (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n





noncomputable def Nset (k m : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0 ∧ ¬ n ∣ k ∧ k / n = m)



noncomputable def V (k m : ℕ) : ℝ :=
  (∑ n ∈ Nset k m, (Lambda n) ^ 2 / (n : ℝ))
    - (∑ n ∈ Nset k m, Lambda n) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ))

theorem mem_Nset {k m n : ℕ} :
    n ∈ Nset k m ↔ n ≤ k ∧ Lambda n ≠ 0 ∧ ¬ n ∣ k ∧ k / n = m := by
  simp [Nset, Finset.mem_filter]


theorem Nset_pos {k m : ℕ} {n : ℕ} (hn : n ∈ Nset k m) : 0 < (n : ℝ) := by
  have hΛ : Lambda n ≠ 0 := (mem_Nset.mp hn).2.1
  have hn0 : n ≠ 0 := by
    intro h0
    exact hΛ (by simp [Lambda, h0, ArithmeticFunction.map_zero])
  exact_mod_cast Nat.pos_of_ne_zero hn0



theorem V_nonneg (k m : ℕ) : 0 ≤ V k m := by
  have hcs := Finset.sq_sum_div_le_sum_sq_div (s := Nset k m)
    (f := Lambda) (g := fun n : ℕ => (n : ℝ))
    (fun n hn => Nset_pos hn)
  unfold V
  linarith


theorem V_le_weighted (k m : ℕ) :
    V k m ≤ ∑ n ∈ Nset k m, (Lambda n) ^ 2 / (n : ℝ) := by
  unfold V
  have hsq : 0 ≤ (∑ n ∈ Nset k m, Lambda n) ^ 2 := sq_nonneg _
  have hden : 0 ≤ (∑ n ∈ Nset k m, (n : ℝ)) :=
    sum_nonneg fun n _ => Nat.cast_nonneg n
  have hdiv : 0 ≤ (∑ n ∈ Nset k m, Lambda n) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ)) :=
    div_nonneg hsq hden
  linarith



noncomputable def Vsum (k : ℕ) : ℝ := ∑ m ∈ Finset.range (k + 1), V k m


theorem Vsum_le_weighted (k : ℕ) :
    Vsum k ≤ ∑ m ∈ Finset.range (k + 1), ∑ n ∈ Nset k m, (Lambda n) ^ 2 / (n : ℝ) := by
  unfold Vsum
  exact Finset.sum_le_sum (fun m _ => V_le_weighted k m)




noncomputable def wNat (j : ℕ) : ℝ := Real.log (1 + 1 / (j : ℝ))


noncomputable def beta0 : ℝ := Real.log 2 + 1 / 2

theorem beta0_pos : 0 < beta0 := by
  unfold beta0
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]



noncomputable def Lkn (k n : ℕ) : ℝ :=
  1 / 2 + Real.log (wNat (k / n) / wNat k)


noncomputable def activeN (k : ℕ) : Finset ℕ :=
  (Finset.range (k + 1)).filter (fun n => Lambda n ≠ 0 ∧ ¬ n ∣ k)


noncomputable def sigmaTilde (k : ℕ) : ℝ :=
  ∑ n ∈ activeN k, (Lambda n) ^ 2 / ((n : ℝ) * (Real.log n + beta0))


noncomputable def sigma (k : ℕ) : ℝ :=
  ∑ n ∈ activeN k, (Lambda n) ^ 2 / ((n : ℝ) * Lkn k n)






theorem sigmaTilde_le_sigma_of_L_bound {k : ℕ}
    (hpos : ∀ n ∈ activeN k, 0 < Lkn k n)
    (hL : ∀ n ∈ activeN k, Lkn k n ≤ Real.log n + beta0)
    (hlog : ∀ n ∈ activeN k, 0 < Real.log n + beta0) :
    sigmaTilde k ≤ sigma k := by
  unfold sigmaTilde sigma
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hΛ : Lambda n ≠ 0 := (Finset.mem_filter.mp hn).2.1
    have hn0 : n ≠ 0 := by
      intro h0
      exact hΛ (by simp [Lambda, h0, ArithmeticFunction.map_zero])
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hdn : 0 < (n : ℝ) * Lkn k n := mul_pos hnpos (hpos n hn)
  have hle : (n : ℝ) * Lkn k n ≤ (n : ℝ) * (Real.log n + beta0) :=
    mul_le_mul_of_nonneg_left (hL n hn) hnpos.le
  have hΛ2 : 0 ≤ (Lambda n) ^ 2 := sq_nonneg _
  exact div_le_div_of_nonneg_left hΛ2 hdn hle




def AWGC (k : ℕ) : Prop :=
  (1 / Real.log 2) * Vsum k ≤ sigmaTilde k




noncomputable def w (k : ℕ) : ℝ := Real.log (1 + 1 / (k : ℝ))

theorem w_pos {k : ℕ} (hk : 1 ≤ k) : 0 < w k := by
  unfold w
  apply Real.log_pos
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  linarith [one_div_pos.mpr hk0]


theorem w_lt_inv {k : ℕ} (hk : 1 ≤ k) : w k < 1 / (k : ℝ) := by
  unfold w
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx : 0 < 1 + 1 / (k : ℝ) := by positivity
  have hx1 : 1 + 1 / (k : ℝ) ≠ 1 := by
    have : 0 < 1 / (k : ℝ) := one_div_pos.mpr hk0
    linarith
  have h := Real.log_lt_sub_one_of_pos hx hx1
  linarith


theorem wNat_eq_w (k : ℕ) : wNat k = w k := rfl


theorem w_sq_div_48_lt {k : ℕ} (hk : 1 ≤ k) :
    (w k) ^ 2 / 48 < 1 / (48 * (k : ℝ) ^ 2) := by
  have hw := w_lt_inv hk
  have hwpos := w_pos hk
  have hinvpos : 0 < 1 / (k : ℝ) := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact one_div_pos.mpr hk0
  have hsq : (w k) ^ 2 < (1 / (k : ℝ)) ^ 2 := by nlinarith
  have hdiv : (w k) ^ 2 / 48 < (1 / (k : ℝ)) ^ 2 / 48 :=
    div_lt_div_of_pos_right hsq (by norm_num)
  have heq : (1 / (k : ℝ)) ^ 2 / 48 = 1 / (48 * (k : ℝ) ^ 2) := by
    field_simp
  linarith







noncomputable def masterGap (k : ℕ) (W : ℝ) : ℝ :=
  1 / 2 + Real.log k - (439 / (250 * Real.log 2)) * Vsum k - (5 / 2) * W






theorem master_scalar_reduction {k : ℕ} {W : ℝ}
    (hS : Vsum k ≤ (14736 / 100000) * Real.log k + (2904 / 1000))
    (hW : W ≤ (47 / 1000) * Real.log k)
    (hX : 15 ≤ Real.log k) :
    0 < masterGap k W := by
  unfold masterGap
  set L := Real.log k with hL
  set C := 439 / (250 * Real.log 2) with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hCub : C < 2.533373 := by
    rw [hC, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9]
  have hL0 : 0 ≤ L := by linarith
  have hCL : C * ((14736 / 100000) * L) ≤ 2.533373 * ((14736 / 100000) * L) := by
    apply mul_le_mul_of_nonneg_right hCub.le
    positivity
  have hC2 : C * (2904 / 1000) ≤ 2.533373 * (2904 / 1000) := by
    apply mul_le_mul_of_nonneg_right hCub.le
    norm_num
  have hcore : C * ((14736 / 100000) * L + (2904 / 1000))
      + (5 / 2) * ((47 / 1000) * L) < 1 / 2 + L := by
    nlinarith [hCL, hC2, hX, hL0]
  have hCS : C * Vsum k ≤ C * ((14736 / 100000) * L + (2904 / 1000)) :=
    mul_le_mul_of_nonneg_left hS hCpos.le
  have hCW : (5 / 2) * W ≤ (5 / 2) * ((47 / 1000) * L) :=
    mul_le_mul_of_nonneg_left hW (by norm_num)
  linarith





theorem master_scalar_audited {k : ℕ} {W : ℝ}
    (hS : Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000))
    (hW : W ≤ (47 / 1000) * Real.log k)
    (hX : 15 ≤ Real.log k) :
    0 < (5785 / 10000) * Real.log k - (6778 / 1000) ∧ 0 < masterGap k W := by
  unfold masterGap
  set L := Real.log k with hL
  set C := 439 / (250 * Real.log 2) with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by positivity
  have hCub : C < 2.533373 := by
    rw [hC, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9]
  have hL0 : 0 ≤ L := by linarith
  have hCL : C * ((12 / 100) * L) ≤ 2.533373 * ((12 / 100) * L) := by
    apply mul_le_mul_of_nonneg_right hCub.le
    positivity
  have hC2 : C * (2873 / 1000) ≤ 2.533373 * (2873 / 1000) := by
    apply mul_le_mul_of_nonneg_right hCub.le
    norm_num
  have hSbound : C * Vsum k ≤ 2.533373 * ((12 / 100) * L + (2873 / 1000)) := by
    calc C * Vsum k ≤ C * ((12 / 100) * L + (2873 / 1000)) :=
          mul_le_mul_of_nonneg_left hS hCpos.le
      _ ≤ 2.533373 * ((12 / 100) * L + (2873 / 1000)) := by
          apply mul_le_mul_of_nonneg_right hCub.le
          positivity
  have hWbound : (5 / 2) * W ≤ (5 / 2) * ((47 / 1000) * L) :=
    mul_le_mul_of_nonneg_left hW (by norm_num)
  have hlin : 0 < (5785 / 10000 : ℝ) * L - (6778 / 1000) := by
    nlinarith [hX, hL0, hCL, hC2]
  refine ⟨hlin, ?_⟩
  nlinarith [hSbound, hWbound, hX, hL0]




theorem master_scalar_positive {k : ℕ} {W : ℝ}
    (hS : Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000))
    (hW : W ≤ (47 / 1000) * Real.log k)
    (hX : 15 ≤ Real.log k) :
    0 < 1 / 2 + Real.log k - (439 / (250 * Real.log 2)) * Vsum k - (5 / 2) * W :=
  (master_scalar_audited hS hW hX).2





















theorem wNat_pos {k : ℕ} (hk : 1 ≤ k) : 0 < wNat k := by
  simpa [wNat_eq_w] using w_pos hk


theorem wNat_lt_inv {k : ℕ} (hk : 1 ≤ k) : wNat k < 1 / (k : ℝ) := by
  simpa [wNat_eq_w] using w_lt_inv hk



theorem wNat_gt_inv_succ {k : ℕ} (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) < wNat k := by
  rw [wNat_eq_w, w]
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 / (k : ℝ) by positivity)
  have heq : 2 * (1 / (k : ℝ)) / ((1 / (k : ℝ)) + 2) = 2 / (1 + 2 * (k : ℝ)) := by
    field_simp
  rw [heq] at h
  have hmid : 1 / ((k : ℝ) + 1) < 1 / ((k : ℝ) + 1 / 2) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  have heq2 : 1 / ((k : ℝ) + 1 / 2) = 2 / (1 + 2 * (k : ℝ)) := by
    field_simp
    ring
  rw [heq2] at hmid
  linarith


theorem wNat_lt_wNat {m k : ℕ} (hm : 1 ≤ m) (hmk : m < k) :
    wNat k < wNat m := by
  unfold wNat
  apply Real.log_lt_log
  · positivity
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have : (1 : ℝ) / (k : ℝ) < 1 / (m : ℝ) :=
      one_div_lt_one_div_of_lt hm0 (by exact_mod_cast hmk)
    linarith






theorem Lkn_lt_log_add_beta0 {k n : ℕ} (hn : n ∈ activeN k) :
    Lkn k n < Real.log n + beta0 := by
  have hn'
  have hΛ : Lambda n ≠ 0 := hn'.2.1
  have hnle : n ≤ k := by
    have := Finset.mem_range.mp hn'.1
    omega
  have hpp : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
  have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  have hm1 : 1 ≤ k / n := Nat.div_pos hnle hnpos
  have hmk : k / n < k := Nat.div_lt_self hkpos (by omega : 1 < n)

  have hk_lt : k < n * (k / n + 1) := by
    have hmod : k % n < n := Nat.mod_lt k hnpos
    have h := Nat.div_add_mod k n
    have hmul : n * (k / n + 1) = n * (k / n) + n := by
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have hk1' : k + 1 ≤ n * (k / n + 1) := Nat.succ_le_of_lt hk_lt

  have hwm : wNat (k / n) < 1 / ((k / n : ℕ) : ℝ) := wNat_lt_inv hm1
  have hwk : 1 / ((k : ℝ) + 1) < wNat k := wNat_gt_inv_succ hk1
  have hwkpos : 0 < wNat k := wNat_pos hk1
  have hratio : wNat (k / n) / wNat k < ((k : ℝ) + 1) / ((k / n : ℕ) : ℝ) := by
    calc wNat (k / n) / wNat k
        < (1 / ((k / n : ℕ) : ℝ)) / wNat k :=
          div_lt_div_of_pos_right hwm hwkpos
      _ < (1 / ((k / n : ℕ) : ℝ)) / (1 / ((k : ℝ) + 1)) :=
          div_lt_div_of_pos_left (div_pos one_pos (by exact_mod_cast hm1))
            (div_pos one_pos (by positivity)) hwk
      _ = ((k : ℝ) + 1) / ((k / n : ℕ) : ℝ) := by field_simp
  have hm0 : (0 : ℝ) < ((k / n : ℕ) : ℝ) := by exact_mod_cast hm1
  have hcast : ((k : ℝ) + 1) ≤ (n : ℝ) * (((k / n : ℕ) : ℝ) + 1) := by
    exact_mod_cast hk1'
  have hbound : ((k : ℝ) + 1) / ((k / n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    have hdiv : ((k : ℝ) + 1) / ((k / n : ℕ) : ℝ)
        ≤ ((n : ℝ) * (((k / n : ℕ) : ℝ) + 1)) / ((k / n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hcast hm0.le
    have hle2 : ((n : ℝ) * (((k / n : ℕ) : ℝ) + 1)) / ((k / n : ℕ) : ℝ)
        ≤ 2 * (n : ℝ) := by
      rw [mul_div_assoc]
      have hm1' : (1 : ℝ) ≤ ((k / n : ℕ) : ℝ) := by exact_mod_cast hm1
      have hfac : (((k / n : ℕ) : ℝ) + 1) / ((k / n : ℕ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hm0]
        linarith
      calc (n : ℝ) * ((((k / n : ℕ) : ℝ) + 1) / ((k / n : ℕ) : ℝ)) ≤ (n : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg n)
        _ = 2 * (n : ℝ) := by ring
    exact le_trans hdiv hle2
  have hlogratio : Real.log (wNat (k / n) / wNat k)
      < Real.log (((k : ℝ) + 1) / ((k / n : ℕ) : ℝ)) :=
    Real.log_lt_log (div_pos (wNat_pos hm1) hwkpos) hratio
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
  have hlog2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnne
  calc Lkn k n = 1 / 2 + Real.log (wNat (k / n) / wNat k) := rfl
    _ < 1 / 2 + Real.log (((k : ℝ) + 1) / ((k / n : ℕ) : ℝ)) := by linarith
    _ ≤ 1 / 2 + Real.log (2 * (n : ℝ)) := by
          have hp : 0 < ((k : ℝ) + 1) / ((k / n : ℕ) : ℝ) := by positivity
          have := Real.log_le_log hp hbound
          linarith
    _ = Real.log n + beta0 := by
          rw [hlog2n]
          unfold beta0
          ring



theorem sigmaTilde_le_sigma (k : ℕ) : sigmaTilde k ≤ sigma k := by
  apply sigmaTilde_le_sigma_of_L_bound
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hΛ : Lambda n ≠ 0 := hn'.2.1
    have hnle : n ≤ k := by
      have := Finset.mem_range.mp hn'.1
      omega
    have hpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
    have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
    have hk1 : 1 ≤ k := by omega
    have hm1 : 1 ≤ k / n := Nat.div_pos hnle (by omega : 0 < n)
    have hmk : k / n < k := Nat.div_lt_self (by omega : 0 < k) (by omega : 1 < n)
    have hwlt : wNat k < wNat (k / n) := wNat_lt_wNat hm1 hmk
    have hratio1 : 1 < wNat (k / n) / wNat k :=
      (lt_div_iff₀ (wNat_pos hk1)).mpr (by simpa using hwlt)
    have hlogpos : 0 < Real.log (wNat (k / n) / wNat k) := Real.log_pos hratio1
    unfold Lkn
    linarith
  · intro n hn
    exact (Lkn_lt_log_add_beta0 hn).le
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hΛ : Lambda n ≠ 0 := hn'.2.1
    have hpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
    have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
    have hlog : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hb : 0 < beta0 := beta0_pos
    linarith







theorem AWGC_of_V_bound {k : ℕ} {chihat : ℕ → ℝ}
    (hchi : ∀ m, chihat m ≤ V k m / Real.log 2) :
    ∑ m ∈ Finset.range (k + 1), chihat m ≤ (1 / Real.log 2) * Vsum k := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ m ∈ Finset.range (k + 1), chihat m
      ≤ ∑ m ∈ Finset.range (k + 1), V k m / Real.log 2 :=
        Finset.sum_le_sum (fun m _ => hchi m)
    _ = (∑ m ∈ Finset.range (k + 1), V k m) / Real.log 2 := by
        rw [Finset.sum_div]
    _ = (1 / Real.log 2) * Vsum k := by
        rw [Vsum]
        ring




theorem mismatch_debit_le_sigma {k : ℕ} (hAWGC : AWGC k) {chihat : ℕ → ℝ}
    (hchi : ∀ m, chihat m ≤ V k m / Real.log 2) :
    ∑ m ∈ Finset.range (k + 1), chihat m ≤ sigma k :=
  le_trans (AWGC_of_V_bound hchi) (le_trans hAWGC (sigmaTilde_le_sigma k))






def FiniteSweep : Prop :=
  ∀ k : ℕ, 2 ≤ k → k ≤ 3594641 → (1 / Real.log 2) * Vsum k ≤ sigmaTilde k



def AWGCTail : Prop :=
  ∀ k : ℕ, 3594642 ≤ k → (1 / Real.log 2) * Vsum k ≤ sigmaTilde k



theorem AWGC_of_sweep_tail (hsweep : FiniteSweep) (htail : AWGCTail) :
    ∀ k : ℕ, 2 ≤ k → AWGC k := by
  intro k hk
  by_cases h : k ≤ 3594641
  · exact hsweep k hk h
  · exact htail k (by omega)




theorem exp_15_le_3594642 : Real.exp 15 ≤ (3594642 : ℝ) := by
  have h1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have h2 : (Real.exp 1) ^ 15 < (2.7182818286 : ℝ) ^ 15 :=
    pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num : (15 : ℕ) ≠ 0)
  have h3 : Real.exp 15 = (Real.exp 1) ^ 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3]
  have h4 : (2.7182818286 : ℝ) ^ 15 < (3594642 : ℝ) := by norm_num
  linarith


theorem log_3594642_ge_15 : (15 : ℝ) ≤ Real.log 3594642 :=
  (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3594642)).mpr exp_15_le_3594642








theorem awgc_tail_assembly {primePart hpp L : ℝ}
    (hprime : primePart ≤ 0.100317302 * L + 0.259330618)
    (hhpp : hpp ≤ 2.871496589970) (hL : 15 ≤ L) :
    primePart + hpp < 0.12 * L + 2.873 := by
  nlinarith







theorem W_tail_assembly {L k C W1 W2 : ℝ}
    (hC : C ≤ 1.018232801063381479)
    (hlog2 : 0 < Real.log 2)
    (hb1 : (Real.log 2 / 24) * (C + L / k) ≤ 0.029409)
    (hb2 : 9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)) ≤ 0.017216)
    (hW1 : W1 ≤ L * ((Real.log 2 / 24) * (C + L / k)))
    (hW2 : W2 ≤ L * (9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k))))
    (hLpos : 0 < L) :
    W1 + W2 < 0.047 * L := by
  have hb : (Real.log 2 / 24) * (C + L / k)
      + 9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)) ≤ 0.046625 := by
    have := add_le_add hb1 hb2
    norm_num at this
    linarith
  have hsum : W1 + W2 ≤ L * ((Real.log 2 / 24) * (C + L / k))
      + L * (9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k))) :=
    add_le_add hW1 hW2
  have hfac : L * ((Real.log 2 / 24) * (C + L / k))
      + L * (9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)))
      = L * ((Real.log 2 / 24) * (C + L / k)
        + 9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k))) := by ring
  rw [hfac] at hsum
  nlinarith [hsum, hb, hLpos]





theorem W_tail_branch_bounds {L k C : ℝ}
    (hC : C ≤ 1.018232801063381479) (hCpos : 0 ≤ C)
    (hlog2 : 0 < Real.log 2) (hlog2ub : Real.log 2 ≤ 0.6931471808)
    (hk : 2 * 10 ^ 6 ≤ k) (hL : L = Real.log k) (hLub : L ≤ 14.52) :
    (Real.log 2 / 24) * (C + L / k) ≤ 0.029409 ∧
      9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)) ≤ 0.017216 := by
  have hkpos : (0 : ℝ) < k := by linarith
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  have hlogk2 : Real.log (k / 2) ≤ L := by
    rw [hL]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlk : L / k ≤ 14.52 / (2 * 10 ^ 6 : ℝ) := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]
    nlinarith [hLub, hk]
  have hk2 : Real.log (k / 2) / (2 * k) ≤ 14.52 / (2 * (2 * 10 ^ 6 : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlogk2, hk, hLub]
  have hc1 : Real.log 2 / 24 ≤ 0.028882 := by
    have h := div_le_div_of_nonneg_right hlog2ub (by norm_num : (0 : ℝ) ≤ 24)
    have h2 : (0.6931471808 : ℝ) / 24 ≤ 0.028882 := by norm_num
    linarith
  have hb1 : (Real.log 2 / 24) * (C + L / k) ≤ 0.029409 := by
    have hsum : C + L / k ≤ 1.01824007 := by
      have hk6 : (14.52 : ℝ) / (2 * 10 ^ 6) = 0.00000726 := by norm_num
      linarith
    have hcl : 0 ≤ C + L / k := by
      have hLk : 0 ≤ L / k := div_nonneg hLpos.le hkpos.le
      linarith
    calc (Real.log 2 / 24) * (C + L / k) ≤ 0.028882 * 1.01824007 :=
          mul_le_mul hc1 hsum hcl (by norm_num)
      _ ≤ 0.029409 := by norm_num
  have hden : 192 * (0.6931471803 : ℝ) ≤ 192 * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num)
  have hc2 : 9 / (192 * Real.log 2) ≤ 0.067627 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 9)
      (by norm_num : (0 : ℝ) < 192 * 0.6931471803) hden
    have h2 : 9 / (192 * (0.6931471803 : ℝ)) ≤ 0.067627 := by norm_num
    linarith
  have hb2 : 9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)) ≤ 0.017216 := by
    have hsum : C / 4 + Real.log (k / 2) / (2 * k) ≤ 0.25456184 := by
      have h14 : (14.52 : ℝ) / (4 * 10 ^ 6) = 0.00000363 := by norm_num
      nlinarith [hC, hk2, hk]
    have hcl : 0 ≤ C / 4 + Real.log (k / 2) / (2 * k) := by
      have hlognn : 0 ≤ Real.log (k / 2) :=
        Real.log_nonneg (by linarith : (1 : ℝ) ≤ k / 2)
      have hkk : 0 < 2 * k := by linarith
      have hdivnn : 0 ≤ Real.log (k / 2) / (2 * k) := div_nonneg hlognn hkk.le
      have hC4 : 0 ≤ C / 4 := by positivity
      linarith
    calc 9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k))
        ≤ 0.067627 * 0.25456184 := mul_le_mul hc2 hsum hcl (by norm_num)
      _ ≤ 0.017216 := by norm_num
  exact ⟨hb1, hb2⟩









theorem W_tail {L k C W1 W2 : ℝ}
    (hC : C ≤ 1.018232801063381479) (hCpos : 0 ≤ C)
    (hlog2 : 0 < Real.log 2) (hlog2ub : Real.log 2 ≤ 0.6931471808)
    (hk : 2 * 10 ^ 6 ≤ k) (hL : L = Real.log k) (hLub : L ≤ 14.52)
    (hW1 : W1 ≤ L * ((Real.log 2 / 24) * (C + L / k)))
    (hW2 : W2 ≤ L * (9 / (192 * Real.log 2) * (C / 4 + Real.log (k / 2) / (2 * k)))) :
    W1 + W2 < 0.047 * L := by
  obtain ⟨hb1, hb2⟩ := W_tail_branch_bounds hC hCpos hlog2 hlog2ub hk hL hLub
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos (by linarith)
  exact W_tail_assembly hC hlog2 hb1 hb2 hW1 hW2 hLpos





theorem exp_852_gt_5000 : (5000 : ℝ) < Real.exp 8.52 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 8 < (Real.exp 1) ^ 8 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num : (8 : ℕ) ≠ 0)
  have h3 : Real.exp 8 = (Real.exp 1) ^ 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 : (∑ i ∈ Finset.range 5, ((0.52 : ℝ) ^ i) / (i.factorial : ℝ)) ≤ Real.exp 0.52 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 5
  have h5 : (1.68168 : ℝ) ≤ ∑ i ∈ Finset.range 5, ((0.52 : ℝ) ^ i) / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have h6 : (5000 : ℝ) < (2.7182818283 : ℝ) ^ 8 * (1.68168 : ℝ) := by norm_num
  rw [show (8.52 : ℝ) = 8 + 0.52 by norm_num, Real.exp_add, h3]
  nlinarith [h2, h4, h5, h6, Real.exp_pos (0.52 : ℝ)]


theorem log_5000_lt_852 : Real.log 5000 < 8.52 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5000)).mpr exp_852_gt_5000





theorem leakage_bound_of_log {k : ℕ} (hk : 5000 ≤ k) (hlog : Real.log k ≤ 8.52) :
    (Real.log k) ^ 2 / (48 * Real.log 2 * (k : ℝ) ^ 2) < 9 / 10 ^ 8 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h5000 : (5000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlogpos : 0 ≤ Real.log k :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hnum : (Real.log k) ^ 2 ≤ (8.52 : ℝ) ^ 2 := by nlinarith
  have hden : (5000 : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hdenle : 48 * Real.log 2 * (5000 : ℝ) ^ 2 ≤ 48 * Real.log 2 * (k : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hden (by positivity)
  have hstep1 : (Real.log k) ^ 2 / (48 * Real.log 2 * (k : ℝ) ^ 2)
      ≤ (Real.log k) ^ 2 / (48 * Real.log 2 * (5000 : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdenle
  have hstep2 : (Real.log k) ^ 2 / (48 * Real.log 2 * (5000 : ℝ) ^ 2)
      ≤ (8.52 : ℝ) ^ 2 / (48 * Real.log 2 * (5000 : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hfinal : (8.52 : ℝ) ^ 2 / (48 * Real.log 2 * (5000 : ℝ) ^ 2) < 9 / 10 ^ 8 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hlog2]
  linarith




theorem reserve_scalar {k : ℕ} (hk : 1 ≤ k) :
    (8 / 1000 : ℝ) < 1 / 2 - Real.log ((k : ℝ) * w k) - 492 / 1000 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hwpos : 0 < w k := w_pos hk
  have hlt : (k : ℝ) * w k < 1 := by
    have h := w_lt_inv hk
    have h2 := mul_lt_mul_of_pos_left h hk0
    rwa [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp] at h2
  have hloglt : Real.log ((k : ℝ) * w k) < 0 := by
    have h := Real.log_lt_log (mul_pos hk0 hwpos) hlt
    rwa [Real.log_one] at h
  linarith




theorem reserve_corrected {E leak : ℝ} (hE : (8 / 1000 : ℝ) < E)
    (hleak : leak < 9 / 10 ^ 8) :
    (79999 / 10000000 : ℝ) < E - leak := by
  norm_num at *
  linarith








theorem master_scalar_uniform_all {W : ℕ → ℝ}
    (hsweep : ∀ k : ℕ, 7 ≤ k → k ≤ 3594641 → 0 < masterGap k (W k))
    (htail : ∀ k : ℕ, 3594642 ≤ k →
      Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000) ∧
        W k ≤ (47 / 1000) * Real.log k) :
    ∀ k : ℕ, 7 ≤ k → 0 < masterGap k (W k) := by
  intro k hk
  by_cases h : k ≤ 3594641
  · exact hsweep k hk h
  · have hk' : 3594642 ≤ k := by omega
    have hlog : 15 ≤ Real.log k :=
      le_trans log_3594642_ge_15
        (Real.log_le_log (by norm_num) (by exact_mod_cast hk'))
    exact (master_scalar_audited (htail k hk').1 (htail k hk').2 hlog).2




noncomputable def Bk (k : ℕ) : ℝ := 1 / 2 + Real.log (1 / wNat k)


theorem wNat_le_log2 {k : ℕ} (hk : 1 ≤ k) : wNat k ≤ Real.log 2 := by
  rcases eq_or_lt_of_le hk with h | h
  · subst h
    norm_num [wNat]
  · have hlt := wNat_lt_wNat (m := 1) (k := k) (by norm_num) h
    have h1 : wNat 1 = Real.log 2 := by norm_num [wNat]
    rw [h1] at hlt
    exact hlt.le




theorem Lkn_gt_log {k n : ℕ} (hn : n ∈ activeN k) : Real.log n < Lkn k n := by
  have hn' := Finset.mem_filter.mp hn
  have hΛ : Lambda n ≠ 0 := hn'.2.1
  have hndvd : ¬ n ∣ k := hn'.2.2
  have hnle : n ≤ k := by
    have := Finset.mem_range.mp hn'.1
    omega
  have hpp : IsPrimePow n :=
    ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
  have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  have hm1 : 1 ≤ k / n := Nat.div_pos hnle hnpos
  have hm0 : (0 : ℝ) < ((k / n : ℕ) : ℝ) := by exact_mod_cast hm1
  have hne : n ≠ k := by
    intro hkn
    exact hndvd (hkn ▸ dvd_rfl)
  have hnlt : n < k := lt_of_le_of_ne hnle hne

  have hwm_lb : 2 / (1 + 2 * ((k / n : ℕ) : ℝ)) < wNat (k / n) := by
    have hmpos : (0 : ℝ) < 1 / ((k / n : ℕ) : ℝ) := one_div_pos.mpr hm0
    have h := Real.lt_log_one_add_of_pos hmpos
    have heq : 2 * (1 / ((k / n : ℕ) : ℝ)) / ((1 / ((k / n : ℕ) : ℝ)) + 2)
        = 2 / (1 + 2 * ((k / n : ℕ) : ℝ)) := by
      field_simp
    rw [heq] at h
    simpa [wNat] using h
  have hwk_ub : wNat k < 1 / (k : ℝ) := wNat_lt_inv hk1
  have hwk_pos : 0 < wNat k := wNat_pos hk1
  have hratio_lb : 2 * (k : ℝ) / (1 + 2 * ((k / n : ℕ) : ℝ))
      < wNat (k / n) / wNat k := by
    have ha : 0 < 2 / (1 + 2 * ((k / n : ℕ) : ℝ)) := by positivity
    calc 2 * (k : ℝ) / (1 + 2 * ((k / n : ℕ) : ℝ))
        = (2 / (1 + 2 * ((k / n : ℕ) : ℝ))) / (1 / (k : ℝ)) := by
          field_simp
      _ < (2 / (1 + 2 * ((k / n : ℕ) : ℝ))) / wNat k :=
          div_lt_div_of_pos_left ha hwk_pos hwk_ub
      _ < wNat (k / n) / wNat k :=
          div_lt_div_of_pos_right hwm_lb hwk_pos

  have hml : (((k / n : ℕ) : ℝ)) ≤ (k : ℝ) / (n : ℝ) := Nat.cast_div_le
  have hnle' : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnle
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hfrac : 2 * (n : ℝ) / 3 < 2 * (k : ℝ) / (1 + 2 * ((k / n : ℕ) : ℝ)) := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)
      (by linarith [hm0] : (0 : ℝ) < 1 + 2 * ((k / n : ℕ) : ℝ))]
    have hmod : 0 < k % n := by
      rcases Nat.eq_zero_or_pos (k % n) with h0 | h0
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hndvd
      · exact h0
    have hnm : (n : ℝ) * ((k / n : ℕ) : ℝ) < (k : ℝ) := by
      have hnat : n * (k / n) + k % n = k := Nat.div_add_mod k n
      have hcast : ((n * (k / n) + k % n : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      have hmodpos : (0 : ℝ) < ((k % n : ℕ) : ℝ) := by exact_mod_cast hmod
      linarith
    nlinarith [hnm, hnle']

  have hlog_lb : Real.log (2 * (n : ℝ) / 3)
      ≤ Real.log (2 * (k : ℝ) / (1 + 2 * ((k / n : ℕ) : ℝ))) :=
    Real.log_le_log (div_pos (mul_pos (by norm_num) hn0) (by norm_num)) hfrac.le
  have hlog_ub : Real.log (2 * (k : ℝ) / (1 + 2 * ((k / n : ℕ) : ℝ)))
      < Real.log (wNat (k / n) / wNat k) :=
    Real.log_lt_log (div_pos (mul_pos (by norm_num) hk0) (by linarith [hm0])) hratio_lb
  have hsplit : Real.log (2 * (n : ℝ) / 3) = Real.log n + Real.log (2 / 3) := by
    rw [Real.log_div (mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hnpos)))
      (by norm_num : (3 : ℝ) ≠ 0)]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast (ne_of_gt hnpos))]
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have h23 : 0 < 1 / 2 + Real.log (2 / 3) := by
    have hlt := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      (by norm_num : (3 / 2 : ℝ) ≠ 1)
    have hinv : Real.log (2 / 3) = -Real.log (3 / 2) := by
      rw [show (2 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
    rw [hinv]
    linarith
  unfold Lkn
  linarith [hlog_lb, hlog_ub, hsplit, h23]





def MertensActive (k : ℕ) : Prop :=
  ∑ n ∈ activeN k, Lambda n / (n : ℝ) ≤ Real.log k




theorem sigma_lt_of_mertens {k : ℕ} (hk : 2 ≤ k) (hM : MertensActive k) :
    sigma k < Real.log k := by
  have hterm : ∀ n ∈ activeN k,
      (Lambda n) ^ 2 / ((n : ℝ) * Lkn k n) < Lambda n / (n : ℝ) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hΛ : Lambda n ≠ 0 := hn'.2.1
    have hnle : n ≤ k := by
      have := Finset.mem_range.mp hn'.1
      omega
    have hpp : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (by simpa [Lambda] using hΛ)
    have hn2 : 2 ≤ n := IsPrimePow.two_le hpp
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hΛnonneg : 0 ≤ Lambda n :=
      by simpa [Lambda] using ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛpos : 0 < Lambda n := lt_of_le_of_ne hΛnonneg (Ne.symm hΛ)
    have hLgt : Lambda n < Lkn k n :=
      lt_of_le_of_lt (by simpa [Lambda] using ArithmeticFunction.vonMangoldt_le_log (n := n))
        (Lkn_gt_log hn)
    have hLpos : 0 < Lkn k n :=
      lt_trans (Real.log_pos (by exact_mod_cast (show 1 < n by omega))) (Lkn_gt_log hn)
    rw [div_lt_div_iff₀ (mul_pos hnpos hLpos) hnpos]
    have hcalc : (n : ℝ) * (Lambda n) ^ 2 < (n : ℝ) * Lambda n * Lkn k n := by
      have hpos : 0 < (n : ℝ) * Lambda n := mul_pos hnpos hΛpos
      calc (n : ℝ) * (Lambda n) ^ 2 = ((n : ℝ) * Lambda n) * Lambda n := by ring
        _ < ((n : ℝ) * Lambda n) * Lkn k n := mul_lt_mul_of_pos_left hLgt hpos
        _ = (n : ℝ) * Lambda n * Lkn k n := by ring
    nlinarith [hcalc]
  unfold MertensActive at hM
  rcases Finset.eq_empty_or_nonempty (activeN k) with hem | hne
  · have hs : sigma k = 0 := by simp [sigma, hem]
    rw [hs]
    exact Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  · exact (Finset.sum_lt_sum_of_nonempty hne hterm).trans_le hM




theorem feshbach_reserve_of_mertens {k : ℕ} (hk : 2 ≤ k) (hM : MertensActive k) :
    (1 / 2 : ℝ) < Bk k - sigma k := by
  have hk1 : 1 ≤ k := by omega
  have hsigma : sigma k < Real.log k := sigma_lt_of_mertens hk hM
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hw : 0 < wNat k := wNat_pos hk1
  have hkw : (k : ℝ) * wNat k < 1 := by
    have h := wNat_lt_inv hk1
    have h2 := mul_lt_mul_of_pos_left h hk0
    rwa [show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp] at h2
  have hlogkw : Real.log ((k : ℝ) * wNat k) < 0 := by
    have h := Real.log_lt_log (mul_pos hk0 hw) hkw
    rwa [Real.log_one] at h
  have hlogmul : Real.log ((k : ℝ) * wNat k) = Real.log k + Real.log (wNat k) :=
    Real.log_mul (ne_of_gt hk0) (ne_of_gt hw)
  have hloginv : Real.log (1 / wNat k) = -Real.log (wNat k) := by
    rw [one_div, Real.log_inv]
  unfold Bk
  rw [hloginv]
  linarith




















theorem gateII_arithmetic_budget {W : ℕ → ℝ} {chihat : ℕ → ℕ → ℝ}
    (hSweep : FiniteSweep) (hTail : AWGCTail)
    (hMert : ∀ k : ℕ, 7 ≤ k → MertensActive k)
    (hVtail : ∀ k : ℕ, 3594642 ≤ k →
      Vsum k ≤ (12 / 100) * Real.log k + (2873 / 1000))
    (hWtail : ∀ k : ℕ, 3594642 ≤ k → W k ≤ (47 / 1000) * Real.log k)
    (hWsweep : ∀ k : ℕ, 7 ≤ k → k ≤ 3594641 → 0 < masterGap k (W k))
    (hchi : ∀ k m, chihat k m ≤ V k m / Real.log 2) :
    (∀ k : ℕ, 7 ≤ k → AWGC k) ∧
      (∀ k : ℕ, 7 ≤ k → ∑ m ∈ Finset.range (k + 1), chihat k m ≤ sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → (1 / 2 : ℝ) < Bk k - sigma k) ∧
      (∀ k : ℕ, 7 ≤ k → 0 < masterGap k (W k)) := by
  have hAWGC : ∀ k : ℕ, 7 ≤ k → AWGC k := fun k hk =>
    AWGC_of_sweep_tail hSweep hTail k (by omega)
  refine ⟨hAWGC, ?_, ?_, ?_⟩
  · intro k hk
    exact mismatch_debit_le_sigma (hAWGC k hk) (hchi k)
  · intro k hk
    exact feshbach_reserve_of_mertens (by omega) (hMert k hk)
  · intro k hk
    exact master_scalar_uniform_all hWsweep
      (fun j hj => ⟨hVtail j hj, hWtail j hj⟩) k hk








theorem V_le_shifted (k m : ℕ) (c : ℝ) :
    V k m ≤ ∑ n ∈ Nset k m, (Lambda n - c * (n : ℝ)) ^ 2 / (n : ℝ) := by
  have hterm : ∀ n ∈ Nset k m,
      (Lambda n - c * (n : ℝ)) ^ 2 / (n : ℝ)
        = (Lambda n) ^ 2 / (n : ℝ) - 2 * c * Lambda n + c ^ 2 * (n : ℝ) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nset_pos hn)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  have hsum1 : ∑ n ∈ Nset k m,
        ((Lambda n) ^ 2 / (n : ℝ) - 2 * c * Lambda n + c ^ 2 * (n : ℝ))
      = (∑ n ∈ Nset k m, (Lambda n) ^ 2 / (n : ℝ))
        - 2 * c * (∑ n ∈ Nset k m, Lambda n)
        + c ^ 2 * (∑ n ∈ Nset k m, (n : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsum1]
  unfold V
  rcases Finset.eq_empty_or_nonempty (Nset k m) with hem | hne
  · rw [hem]
    simp
  · have hden : 0 < ∑ n ∈ Nset k m, (n : ℝ) :=
      Finset.sum_pos (fun n hn => Nset_pos hn) hne
    have hsq : 0 ≤ (c * (∑ n ∈ Nset k m, (n : ℝ)) - ∑ n ∈ Nset k m, Lambda n) ^ 2
        / (∑ n ∈ Nset k m, (n : ℝ)) :=
      div_nonneg (sq_nonneg _) hden.le
    have hkey : (c * (∑ n ∈ Nset k m, (n : ℝ)) - ∑ n ∈ Nset k m, Lambda n) ^ 2
          / (∑ n ∈ Nset k m, (n : ℝ))
        = c ^ 2 * (∑ n ∈ Nset k m, (n : ℝ)) - 2 * c * (∑ n ∈ Nset k m, Lambda n)
          + (∑ n ∈ Nset k m, Lambda n) ^ 2 / (∑ n ∈ Nset k m, (n : ℝ)) := by
      field_simp
      ring
    linarith




noncomputable def Jm (m : ℕ) : ℝ :=
  ∫ u in (m : ℝ) / ((m : ℝ) + 1)..1, (1 - u) ^ 2 / u


noncomputable def Jprim (u : ℝ) : ℝ := Real.log u - 2 * u + u ^ 2 / 2

theorem hasDerivAt_Jprim {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt Jprim ((1 - u) ^ 2 / u) u := by
  unfold Jprim
  have h1 : HasDerivAt (fun u : ℝ => Real.log u) u⁻¹ u := Real.hasDerivAt_log hu
  have h2 : HasDerivAt (fun u : ℝ => -2 * u) (-2) u := by
    simpa using (hasDerivAt_id u).const_mul (-2)
  have h3 : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
    have h := (hasDerivAt_pow 2 u).div_const 2
    simpa using h
  have h := (h1.add h2).add h3
  convert h using 1
  · funext x
    simp only [Pi.add_apply]
    ring
  · field_simp
    ring



theorem Jm_closed {m : ℕ} (hm : 1 ≤ m) :
    Jm m = -1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1) ^ 2)
      - Real.log ((m : ℝ) / ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have ha0 : 0 < (m : ℝ) / ((m : ℝ) + 1) := div_pos hm0 hden
  have ha1 : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hint : IntervalIntegrable (fun u : ℝ => (1 - u) ^ 2 / u) volume
      ((m : ℝ) / ((m : ℝ) + 1)) 1 := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div ?_ continuousOn_id ?_
    · fun_prop
    · intro u hu
      rw [Set.uIcc_of_le ha1] at hu
      exact ne_of_gt (lt_of_lt_of_le ha0 hu.1)
  have hderiv : ∀ u ∈ Set.uIcc ((m : ℝ) / ((m : ℝ) + 1)) 1,
      HasDerivAt Jprim ((1 - u) ^ 2 / u) u := by
    intro u hu
    rw [Set.uIcc_of_le ha1] at hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hu.1)
    exact hasDerivAt_Jprim hu0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [Jm, hFTC]
  unfold Jprim
  rw [Real.log_one]
  rw [div_pow]
  field_simp
  ring



theorem sum_log_telescope_quot (N : ℕ) :
    ∑ m ∈ Finset.range N, Real.log (((m : ℝ) + 1) / ((m : ℝ) + 2))
      = -Real.log ((N : ℝ) + 1) := by
  have h : ∀ m : ℕ, Real.log (((m : ℝ) + 1) / ((m : ℝ) + 2))
      = Real.log ((m : ℝ) + 1) - Real.log ((m : ℝ) + 2) := by
    intro m
    rw [Real.log_div (ne_of_gt (by positivity : (0 : ℝ) < (m : ℝ) + 1))
      (ne_of_gt (by positivity : (0 : ℝ) < (m : ℝ) + 2))]
  simp_rw [h]
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring


theorem sum_shifted_harmonic (N : ℕ) :
    ∑ m ∈ Finset.range N, 1 / ((m : ℝ) + 2) = (harmonic (N + 1) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [harmonic]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hsucc : (harmonic (n + 2) : ℝ)
          = (harmonic (n + 1) : ℝ) + 1 / ((n : ℝ) + 2) := by
        rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
        push_cast
        rw [one_div]
        ring
      rw [hsucc]
      ring



theorem Jm_partial_sum (N : ℕ) :
    ∑ m ∈ Finset.range N, Jm (m + 1)
      = 1 - (harmonic (N + 1) : ℝ)
        - (∑ m ∈ Finset.range N, 1 / (2 * ((m : ℝ) + 2) ^ 2))
        + Real.log ((N : ℝ) + 1) := by
  have hJ : ∀ m ∈ Finset.range N,
      Jm (m + 1) = -1 / ((m : ℝ) + 2) - 1 / (2 * ((m : ℝ) + 2) ^ 2)
        - Real.log (((m : ℝ) + 1) / ((m : ℝ) + 2)) := by
    intro m _hm
    have h := Jm_closed (m := m + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring_nf
  rw [Finset.sum_congr rfl hJ]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [neg_div]
  rw [Finset.sum_neg_distrib, sum_shifted_harmonic N, sum_log_telescope_quot N]
  ring




theorem Jm_succ_nonneg (m : ℕ) : 0 ≤ Jm (m + 1) := by
  unfold Jm
  apply intervalIntegral.integral_nonneg
  · have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) + 1 := by positivity
    rw [div_le_one hpos]
    linarith
  · intro u hu
    have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) := by positivity
    have hu0 : 0 < u := lt_of_lt_of_le hm0 hu.1
    exact div_nonneg (sq_nonneg _) hu0.le


theorem sum_shifted_inv_sq (N : ℕ) :
    (∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2))
      = (∑ n ∈ Finset.range (N + 2), 1 / ((n : ℝ) ^ 2)) - 1 := by
  have h := Finset.sum_range_add (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 2 N
  have h2 : (∑ k ∈ Finset.range 2, 1 / ((k : ℝ) ^ 2)) = 1 := by
    norm_num [Finset.sum_range_succ]
  rw [show N + 2 = 2 + N by omega, h, h2]
  have hrew : (∑ k ∈ Finset.range N, 1 / (((2 + k : ℕ) : ℝ) ^ 2))
      = ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2) := by
    apply Finset.sum_congr rfl
    intro m _
    push_cast
    ring
  rw [hrew]
  ring



theorem hasSum_Jm :
    HasSum (fun m : ℕ => Jm (m + 1))
      (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12) := by
  have hpartial : (fun N : ℕ => ∑ m ∈ Finset.range N, Jm (m + 1))
      = fun N : ℕ =>
          1 - ((harmonic (N + 1) : ℝ) - Real.log ((N : ℝ) + 1))
            - (∑ m ∈ Finset.range N, 1 / (2 * ((m : ℝ) + 2) ^ 2)) := by
    funext N
    rw [Jm_partial_sum N]
    ring
  have hH : Tendsto (fun N : ℕ => (harmonic (N + 1) : ℝ) - Real.log ((N : ℝ) + 1))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
  have hZ : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2))
      atTop (𝓝 (Real.pi ^ 2 / 6 - 1)) := by
    have hZ' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 2), 1 / ((n : ℝ) ^ 2))
        atTop (𝓝 (Real.pi ^ 2 / 6)) :=
      hasSum_zeta_two.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    have h : (fun N : ℕ => ∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2))
        = fun N : ℕ => (∑ n ∈ Finset.range (N + 2), 1 / ((n : ℝ) ^ 2)) - 1 :=
      funext sum_shifted_inv_sq
    rw [h]
    exact hZ'.sub tendsto_const_nhds
  have hQ : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, 1 / (2 * ((m : ℝ) + 2) ^ 2))
      atTop (𝓝 ((1 / 2) * (Real.pi ^ 2 / 6 - 1))) := by
    have h : (fun N : ℕ => ∑ m ∈ Finset.range N, 1 / (2 * ((m : ℝ) + 2) ^ 2))
        = fun N : ℕ =>
            (1 / 2) * (∑ m ∈ Finset.range N, 1 / (((m : ℝ) + 2) ^ 2)) := by
      funext N
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
    rw [h]
    exact hZ.const_mul (1 / 2)
  have hlim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, Jm (m + 1)) atTop
      (𝓝 (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12)) := by
    rw [hpartial]
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hcomb := (h1.sub hH).sub hQ
    convert hcomb using 1
    ring
  exact (hasSum_iff_tendsto_nat_of_nonneg (f := fun m : ℕ => Jm (m + 1))
    (fun m => Jm_succ_nonneg m)
    (3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12)).mpr hlim


theorem tsum_Jm :
    ∑' m : ℕ, Jm (m + 1)
      = 3 / 2 - Real.eulerMascheroniConstant - Real.pi ^ 2 / 12 :=
  hasSum_Jm.tsum_eq




theorem sq_sub_le_sq_add {A D : ℝ} (h : 0 ≤ A * D) : (A - D) ^ 2 ≤ A ^ 2 + D ^ 2 :=
  by nlinarith







theorem vonMangoldt_sub_sq_le {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ ≠ 0) (c : ℝ)
    (hAD : 0 ≤ (Real.log ((p ^ ℓ : ℕ) : ℝ) - c * ((p ^ ℓ : ℕ) : ℝ))
      * (((ℓ : ℝ) - 1) * Real.log p)) :
    (ArithmeticFunction.vonMangoldt (p ^ ℓ) - c * ((p ^ ℓ : ℕ) : ℝ)) ^ 2
      ≤ (Real.log ((p ^ ℓ : ℕ) : ℝ) - c * ((p ^ ℓ : ℕ) : ℝ)) ^ 2
        + (((ℓ : ℝ) - 1) * Real.log p) ^ 2 := by
  have hΛ : ArithmeticFunction.vonMangoldt (p ^ ℓ) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hℓ,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogq : Real.log ((p ^ ℓ : ℕ) : ℝ) = (ℓ : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hsub : Real.log p - c * ((p ^ ℓ : ℕ) : ℝ)
      = (Real.log ((p ^ ℓ : ℕ) : ℝ) - c * ((p ^ ℓ : ℕ) : ℝ))
        - (((ℓ : ℝ) - 1) * Real.log p) := by
    rw [hlogq]
    ring
  rw [hΛ, hsub]
  exact sq_sub_le_sq_add hAD




noncomputable def Apar (c t : ℝ) : ℝ := Real.log t - c * t



noncomputable def gpar (c t : ℝ) : ℝ := (Apar c t) ^ 2 / (t * Real.log t)



theorem hasDerivAt_gpar {c t : ℝ} (ht : t ≠ 0) (hlog : Real.log t ≠ 0) :
    HasDerivAt (gpar c)
      (Apar c t * (1 - Real.log t) * (Real.log t + c * t) / (t * Real.log t) ^ 2) t := by
  have hA : HasDerivAt (Apar c) (t⁻¹ - c) t := by
    have h1 : HasDerivAt (fun u : ℝ => Real.log u) t⁻¹ t := Real.hasDerivAt_log ht
    have h2 : HasDerivAt (fun u : ℝ => c * u) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have h := h1.sub h2
    have hfun : (fun u : ℝ => Real.log u) - (fun u : ℝ => c * u) = Apar c := by
      funext u
      simp [Apar]
    rw [hfun] at h
    exact h
  have hden : HasDerivAt (fun u : ℝ => u * Real.log u) (Real.log t + 1) t := by
    have h := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht)
    simp only [Pi.mul_apply, id_eq] at h
    rw [show (1 : ℝ) * Real.log t + t * t⁻¹ = Real.log t + 1 by
      rw [one_mul, mul_inv_cancel₀ ht, add_comm]] at h
    exact h
  have h := (hA.pow 2).div hden (mul_ne_zero ht hlog)
  convert h using 1
  · ext u
    simp only [Pi.div_apply, Pi.pow_apply]
    unfold gpar
    ring
  · simp only [Pi.pow_apply, Pi.div_apply]
    unfold Apar
    field_simp
    ring




theorem gpar_deriv_nonpos {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hlog1 : 1 ≤ Real.log t) (hA : 0 ≤ Apar c t) :
    Apar c t * (1 - Real.log t) * (Real.log t + c * t) ≤ 0 := by
  have h1 : 1 - Real.log t ≤ 0 := by linarith
  have h2 : 0 < Real.log t + c * t := add_pos (by linarith) (mul_pos hc ht)
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA h1) h2.le




theorem gpar_antitoneOn_Icc {c a b : ℝ} (hc : 0 < c) (ha : Real.exp 1 ≤ a)
    (hab : a ≤ b) (hA : ∀ t ∈ Set.Icc a b, 0 ≤ Apar c t) :
    AntitoneOn (gpar c) (Set.Icc a b) := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hlog1 : ∀ t ∈ Set.Icc a b, 1 ≤ Real.log t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    exact (Real.le_log_iff_exp_le ht0).mpr (le_trans ha ht.1)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · have hsub : Set.Icc a b ⊆ {0}ᶜ :=
      fun t ht => ne_of_gt (lt_of_lt_of_le ha0 ht.1)
    have hnum : ContinuousOn (fun t : ℝ => Apar c t ^ 2) (Set.Icc a b) := by
      have h : ContinuousOn (fun t : ℝ => Real.log t - c * t) (Set.Icc a b) :=
        (Real.continuousOn_log.mono hsub).sub (continuousOn_const.mul continuousOn_id)
      convert h.mul h using 1
      ext t
      simp only [Pi.mul_apply]
      unfold Apar
      ring
    have hden : ContinuousOn (fun t : ℝ => t * Real.log t) (Set.Icc a b) :=
      continuousOn_id.mul (Real.continuousOn_log.mono hsub)
    have hne : ∀ t ∈ Set.Icc a b, t * Real.log t ≠ 0 := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
      have hl0 : 0 < Real.log t := lt_of_lt_of_le one_pos (hlog1 t ht)
      exact mul_ne_zero (ne_of_gt ht0) (ne_of_gt hl0)
    convert hnum.div hden hne using 1
    ext t
    simp only [Pi.div_apply, Pi.pow_apply]
    unfold gpar
    ring
  · intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hl0 : 0 < Real.log t :=
      lt_of_lt_of_le one_pos (hlog1 t (Set.Ioo_subset_Icc_self ht))
    exact (hasDerivAt_gpar (ne_of_gt ht0) (ne_of_gt hl0)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0 < t := lt_trans ha0 ht.1
    have hlt : 1 ≤ Real.log t := hlog1 t (Set.Ioo_subset_Icc_self ht)
    have hl0 : 0 < Real.log t := lt_of_lt_of_le one_pos hlt
    rw [(hasDerivAt_gpar (ne_of_gt ht0) (ne_of_gt hl0)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg
      (gpar_deriv_nonpos hc ht0 hlt (hA t (Set.Ioo_subset_Icc_self ht))) (sq_nonneg _)





theorem Apar_nonneg {b t : ℝ} (hb : Real.exp 1 ≤ b) (ht : Real.exp 1 ≤ t)
    (htb : t ≤ b) : 0 ≤ Apar (Real.log b / b) t := by
  unfold Apar
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hanti : Real.log b / b ≤ Real.log t / t :=
    Real.log_div_self_antitoneOn ht hb htb
  have hmul := mul_le_mul_of_nonneg_right hanti ht0.le
  have h1 : Real.log t / t * t = Real.log t := by field_simp
  linarith




theorem stirlingSecond_two_zero : Nat.stirlingSecond 2 0 = 0 := by decide

theorem stirlingSecond_two_one : Nat.stirlingSecond 2 1 = 1 := by decide

theorem stirlingSecond_two_two : Nat.stirlingSecond 2 2 = 1 := by decide



theorem hpp_rational_identity (x : ℝ) (hx : x ≠ 1) :
    2 * x ^ 2 / (1 - x) ^ 3 + 3 * x / (1 - x) ^ 2 + 1 / (1 - x)
      = (1 + x) / (1 - x) ^ 3 := by
  field_simp
  ring




theorem hasSum_hpp_series {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * x ^ (j + 2))
      (x ^ 2 * (1 + x) / (1 - x) ^ 3) := by
  have hnorm : ‖x‖ < 1 := by rwa [Real.norm_eq_abs]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h] at hx
    norm_num at hx
  have h0 : HasSum (fun n : ℕ => x ^ n) (1 / (1 - x)) := by
    have h := hasSum_geometric_of_norm_lt_one (ξ := x) hnorm
    simpa [one_div] using h
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm
  have h2 : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * x ^ n)
      (x * (1 + x) / (1 - x) ^ 3) := by
    have h := hasSum_pow_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
    have hval : (∑ j ∈ Finset.range (2 + 1),
        (Nat.stirlingSecond 2 j : ℝ) * (Nat.factorial j : ℝ) * x ^ j
          / (1 - x) ^ (j + 1))
        = x * (1 + x) / (1 - x) ^ 3 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      simp only [stirlingSecond_two_zero, stirlingSecond_two_one, stirlingSecond_two_two,
        Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]
      norm_num
      field_simp
      ring
    rw [hval] at h
    simpa only [Nat.cast_pow] using h
  have hcomb := (h2.add (h1.mul_left 2)).add h0
  have hcomb'
      (fun n : ℕ => (n : ℝ) ^ 2 * x ^ n + 2 * ((n : ℝ) * x ^ n) + x ^ n)
      (x * (1 + x) / (1 - x) ^ 3 + 2 * (x / (1 - x) ^ 2) + 1 / (1 - x)) :=
    by simpa only [Pi.add_apply] using hcomb
  have hfun : (fun n : ℕ => (n : ℝ) ^ 2 * x ^ n + 2 * ((n : ℝ) * x ^ n) + x ^ n)
      = fun n : ℕ => ((n : ℝ) + 1) ^ 2 * x ^ n := by
    funext n
    ring
  have hval : x * (1 + x) / (1 - x) ^ 3 + 2 * (x / (1 - x) ^ 2) + 1 / (1 - x)
      = (1 + x) / (1 - x) ^ 3 := by
    field_simp
    ring
  rw [hfun, hval] at hcomb'
  have hfinal := hcomb'.mul_left (x ^ 2)
  have hfinal' : HasSum (fun n : ℕ => x ^ 2 * (((n : ℝ) + 1) ^ 2 * x ^ n))
      (x ^ 2 * ((1 + x) / (1 - x) ^ 3)) :=
    by simpa only [Pi.smul_apply, smul_eq_mul] using hfinal
  have hfun3 : (fun n : ℕ => x ^ 2 * (((n : ℝ) + 1) ^ 2 * x ^ n))
      = fun n : ℕ => ((n : ℝ) + 1) ^ 2 * x ^ (n + 2) := by
    funext n
    rw [pow_add]
    ring
  have hval3 : x ^ 2 * ((1 + x) / (1 - x) ^ 3) = x ^ 2 * (1 + x) / (1 - x) ^ 3 :=
    by ring
  rwa [hfun3, hval3] at hfinal'






theorem hpp_prime_series {p : ℝ} (hp : 1 < p) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) ^ 2 / p ^ (j + 2))
      ((p + 1) / (p - 1) ^ 3) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hx : |1 / p| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hp0), div_lt_one hp0]
    exact hp
  have h := hasSum_hpp_series hx
  have hfun : (fun j : ℕ => ((j : ℝ) + 1) ^ 2 * (1 / p) ^ (j + 2))
      = fun j : ℕ => ((j : ℝ) + 1) ^ 2 / p ^ (j + 2) := by
    funext j
    rw [one_div, inv_pow, div_eq_mul_inv]
  have hval : (1 / p) ^ 2 * (1 + 1 / p) / (1 - 1 / p) ^ 3
      = (p + 1) / (p - 1) ^ 3 := by
    field_simp
  rwa [hfun, hval] at h












noncomputable def tailPrim (x : ℝ) : ℝ :=
  -((Real.log x) ^ 2 + 2 * Real.log x + 2) / x


theorem hasDerivAt_tailPrim {x : ℝ} (hx : 0 < x) :
    HasDerivAt tailPrim ((Real.log x) ^ 2 / x ^ 2) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hnum := ((hlog.pow 2).add (hlog.const_mul 2)).add (hasDerivAt_const x 2)
  have h := hnum.neg.div (hasDerivAt_id x) hx.ne'
  refine h.congr_deriv ?_
  simp only [id_eq]
  field_simp [hx.ne']
  simp


theorem tendsto_tailPrim_atTop : Tendsto tailPrim atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 2 one_ne_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 one_ne_zero
  have h0 : Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h := ((h2.add (h1.const_mul 2)).add (h0.const_mul 2)).neg
  have hfun : tailPrim = fun x : ℝ =>
      -((Real.log x) ^ 2 / x + 2 * (Real.log x / x) + 2 * (1 / x)) := by
    funext x
    unfold tailPrim
    ring
  rw [hfun]
  simpa using h



theorem hasDerivAt_log_sq_div_sq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / t ^ 2)
      (2 * Real.log x * (1 - Real.log x) / x ^ 3) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h := (hlog.pow 2).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx.ne')
  refine h.congr_deriv ?_
  field_simp [hx.ne']
  simp only [Pi.pow_apply]
  ring



theorem integral_log_sq_div_sq {P N : ℝ} (hP : 0 < P) (hPN : P ≤ N) :
    ∫ x in P..N, (Real.log x) ^ 2 / x ^ 2 = tailPrim N - tailPrim P := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  · intro x hx
    rw [Set.uIcc_of_le hPN] at hx
    exact hasDerivAt_tailPrim (lt_of_lt_of_le hP hx.1)
  · have hsub : Set.uIcc P N ⊆ {0}ᶜ := by
      intro x hx
      rw [Set.uIcc_of_le hPN] at hx
      exact ne_of_gt (lt_of_lt_of_le hP hx.1)
    have hnum : ContinuousOn (fun x : ℝ => (Real.log x) ^ 2) (Set.uIcc P N) :=
      (Real.continuousOn_log.mono hsub).pow 2
    have hden : ContinuousOn (fun x : ℝ => x ^ 2) (Set.uIcc P N) :=
      continuousOn_id.pow 2
    exact (hnum.div hden (fun x hx => pow_ne_zero 2 (hsub hx))).intervalIntegrable


theorem antitoneOn_log_sq_div_sq {P : ℝ} (hP : Real.exp 1 ≤ P) :
    AntitoneOn (fun t : ℝ => (Real.log t) ^ 2 / t ^ 2) (Set.Ici P) := by
  have hP0 : 0 < P := lt_of_lt_of_le (Real.exp_pos 1) hP
  apply antitoneOn_of_deriv_nonpos (convex_Ici P)
  · have hsub : Set.Ici P ⊆ {0}ᶜ := fun t ht => ne_of_gt (lt_of_lt_of_le hP0 ht)
    have hnum : ContinuousOn (fun t : ℝ => (Real.log t) ^ 2) (Set.Ici P) :=
      (Real.continuousOn_log.mono hsub).pow 2
    have hden : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Ici P) :=
      continuousOn_id.pow 2
    exact hnum.div hden (fun t ht => pow_ne_zero 2 (hsub ht))
  · intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hP0 ht.le
    exact (hasDerivAt_log_sq_div_sq ht0).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hP0 ht.le
    have hlog1 : 1 ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht0).mpr (le_trans hP ht.le)
    rw [(hasDerivAt_log_sq_div_sq ht0).deriv]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (by linarith))
      (by linarith)



theorem log_sq_div_sq_partial_le (P : ℕ) (hP : Real.exp 1 ≤ (P : ℝ)) (M : ℕ) :
    ∑ i ∈ Finset.range M,
        (Real.log ((i + P + 1 : ℕ) : ℝ)) ^ 2 / ((i + P + 1 : ℕ) : ℝ) ^ 2
      ≤ ((Real.log (P : ℝ)) ^ 2 + 2 * Real.log (P : ℝ) + 2) / (P : ℝ) := by
  have hP0 : (0 : ℝ) < P := lt_of_lt_of_le (Real.exp_pos 1) hP
  have hanti : AntitoneOn (fun t : ℝ => (Real.log t) ^ 2 / t ^ 2)
      (Set.Icc (P : ℝ) ((P : ℝ) + M)) :=
    (antitoneOn_log_sq_div_sq hP).mono Set.Icc_subset_Ici_self
  have hsum := hanti.sum_le_integral (x₀ := (P : ℝ)) (a := M)
  have hftp : ∫ x in (P : ℝ)..(P : ℝ) + M, (Real.log x) ^ 2 / x ^ 2
      = tailPrim ((P : ℝ) + M) - tailPrim (P : ℝ) :=
    integral_log_sq_div_sq hP0 (le_add_of_nonneg_right (Nat.cast_nonneg M))
  have hFnp : tailPrim ((P : ℝ) + M) ≤ 0 := by
    unfold tailPrim
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by nlinarith [sq_nonneg (Real.log ((P : ℝ) + M) + 1)]))
      (add_nonneg hP0.le (Nat.cast_nonneg M))
  calc
    ∑ i ∈ Finset.range M,
        (Real.log ((i + P + 1 : ℕ) : ℝ)) ^ 2 / ((i + P + 1 : ℕ) : ℝ) ^ 2
        = ∑ i ∈ Finset.range M,
            (fun t : ℝ => (Real.log t) ^ 2 / t ^ 2) ((P : ℝ) + (i + 1 : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          have harg : (P : ℝ) + (i + 1 : ℕ) = ((i + P + 1 : ℕ) : ℝ) := by
            push_cast
            ring
          rw [harg]
    _ ≤ ∫ x in (P : ℝ)..(P : ℝ) + M, (Real.log x) ^ 2 / x ^ 2 := hsum
    _ = tailPrim ((P : ℝ) + M) - tailPrim (P : ℝ) := hftp
    _ ≤ -tailPrim (P : ℝ) := by linarith
    _ = ((Real.log (P : ℝ)) ^ 2 + 2 * Real.log (P : ℝ) + 2) / (P : ℝ) := by
      unfold tailPrim
      ring




theorem tsum_log_sq_div_sq_tail_le (P : ℕ) (hP : Real.exp 1 ≤ (P : ℝ)) :
    ∑' i : ℕ, (Real.log ((i + P + 1 : ℕ) : ℝ)) ^ 2 / ((i + P + 1 : ℕ) : ℝ) ^ 2
      ≤ ((Real.log (P : ℝ)) ^ 2 + 2 * Real.log (P : ℝ) + 2) / (P : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun i => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (log_sq_div_sq_partial_le P hP)



theorem summable_log_sq_div_sq_tail (P : ℕ) (hP : Real.exp 1 ≤ (P : ℝ)) :
    Summable (fun i : ℕ =>
      (Real.log ((i + P + 1 : ℕ) : ℝ)) ^ 2 / ((i + P + 1 : ℕ) : ℝ) ^ 2) :=
  summable_of_sum_range_le (fun i => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (log_sq_div_sq_partial_le P hP)

noncomputable def hppRatio (x : ℝ) : ℝ := (1 + x) / (1 - x) ^ 3

noncomputable def hppTerm (n : ℕ) : ℝ :=
  if Nat.Prime n then
    (Real.log (n : ℝ)) ^ 2 * (((n : ℝ) + 1) / ((n : ℝ) - 1) ^ 3)
  else 0

noncomputable def Hpp : ℝ := ∑'

theorem hasDerivAt_hppRatio {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt hppRatio ((4 + 2 * x) / (1 - x) ^ 4) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
    convert h using 1
    · ext t
      simp only [Pi.add_apply, Pi.one_apply, id_eq]
    · ring
  have h2 : HasDerivAt (fun t : ℝ => (1 - t) ^ 3) (3 * (1 - x) ^ 2 * (-1)) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 3
    convert h using 1
    · ext t
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq, zero_sub]
      norm_num
  have h := h1.div h2 (pow_ne_zero 3 (sub_ne_zero.mpr (Ne.symm hx)))
  refine h.congr_deriv ?_
  field_simp <;> ring

theorem hppRatio_monotoneOn : MonotoneOn hppRatio (Set.Icc 0 (1 / 2 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2 : ℝ))
  · have hsub : Set.Icc (0 : ℝ) (1 / 2) ⊆ {1}ᶜ := by
      intro t ht
      exact ne_of_lt (lt_of_le_of_lt ht.2 (by norm_num))
    have h1 : ContinuousOn (fun t : ℝ => 1 + t) (Set.Icc 0 (1 / 2)) :=
      continuousOn_const.add continuousOn_id
    have h2 : ContinuousOn (fun t : ℝ => (1 - t) ^ 3) (Set.Icc 0 (1 / 2)) :=
      (continuousOn_const.sub continuousOn_id).pow 3
    exact h1.div h2 (fun t ht => pow_ne_zero 3 (sub_ne_zero.mpr (Ne.symm (hsub ht))))
  · intro t ht
    rw [interior_Icc] at ht
    have ht1 : t ≠ 1 := ne_of_lt (lt_of_lt_of_le ht.2 (by norm_num))
    exact (hasDerivAt_hppRatio ht1).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht1 : t < 1 := lt_of_lt_of_le ht.2 (by norm_num)
    rw [(hasDerivAt_hppRatio (ne_of_lt ht1)).deriv]
    exact div_nonneg (by linarith [ht.1]) (by positivity)

theorem hppRatio_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ hppRatio x := by
  unfold hppRatio
  exact div_nonneg (by linarith) (pow_nonneg (by linarith) 3)

theorem hpp_term_eq {n : ℕ} (hn : 1 < n) :
    (Real.log (n : ℝ)) ^ 2 * (((n : ℝ) + 1) / ((n : ℝ) - 1) ^ 3)
      = hppRatio (1 / (n : ℝ)) * ((Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  unfold hppRatio
  field_simp <;> ring


theorem hppTerm_le_ratio_mul (P : ℕ) (hP : 4 ≤ P) {n : ℕ} (hn : P < n) :
    hppTerm n ≤ hppRatio (1 / (P : ℝ)) * ((Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hratio : hppRatio (1 / (n : ℝ)) ≤ hppRatio (1 / (P : ℝ)) := by
    refine hppRatio_monotoneOn ?_ ?_ ?_
    · exact ⟨by positivity, by
        rw [div_le_iff₀ hn0]
        have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (by omega : 4 ≤ n)
        linarith⟩
    · exact ⟨by positivity, by
        rw [div_le_iff₀ hP0]
        have hP4 : (4 : ℝ) ≤ P := by exact_mod_cast hP
        linarith⟩
    · exact div_le_div_of_nonneg_left zero_le_one hP0 (by exact_mod_cast (le_of_lt hn))
  have hfn : 0 ≤ (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hp : Nat.Prime n
  · rw [hppTerm, if_pos hp, hpp_term_eq (Nat.Prime.one_lt hp)]
    exact mul_le_mul_of_nonneg_right hratio hfn
  · rw [hppTerm, if_neg hp]
    exact mul_nonneg (hppRatio_nonneg (by positivity) (by
      rw [div_le_iff₀ hP0]
      have hP4 : (4 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)) hfn

theorem Hpp_lt_of_certificate (P : ℕ) (hP : 4 ≤ P)
    (u : ℕ → ℚ) (uP : ℚ)
    (hu : ∀ p, Nat.Prime p → p ≤ P → Real.log (p : ℝ) ≤ (u p : ℝ))
    (huP : Real.log (P : ℝ) ≤ (uP : ℝ))
    (hnum : (∑ p ∈ Finset.range (P + 1),
                if Nat.Prime p then
                  ((u p : ℝ)) ^ 2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3)
                else 0)
              + hppRatio (1 / (P : ℝ)) * ((((uP : ℝ)) ^ 2 + 2 * (uP : ℝ) + 2) / (P : ℝ))
            < 2.798806594208) :
    Hpp < 2.798806594208 := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hPexp : Real.exp 1 ≤ (P : ℝ) := by
    have h3P : (3 : ℝ) ≤ P := by exact_mod_cast (by omega : 3 ≤ P)
    linarith [Real.exp_one_lt_three]
  set C : ℝ := hppRatio (1 / (P : ℝ)) with hCdef
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    exact hppRatio_nonneg (by positivity) (by
      rw [div_le_iff₀ hP0]
      have hP4 : (4 : ℝ) ≤ P := by exact_mod_cast hP
      linarith)
  set B : ℝ := ((Real.log (P : ℝ)) ^ 2 + 2 * Real.log (P : ℝ) + 2) / (P : ℝ) with hBdef
  set Bu : ℝ := (((uP : ℝ)) ^ 2 + 2 * (uP : ℝ) + 2) / (P : ℝ) with hBudef
  have hlogP0 : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have hBle : B ≤ Bu := by
    rw [hBdef, hBudef]
    apply div_le_div_of_nonneg_right _ hP0.le
    have hsq : (Real.log (P : ℝ)) ^ 2 ≤ (uP : ℝ) ^ 2 :=
      pow_le_pow_left₀ hlogP0 huP 2
    linarith
  have hpartial' : ∀ M : ℕ,
      ∑ k ∈ Finset.range M, hppTerm (k + P + 1) ≤ C * Bu := by
    intro M
    calc
      ∑ k ∈ Finset.range M, hppTerm (k + P + 1)
          ≤ ∑ k ∈ Finset.range M,
              C * ((Real.log ((k + P + 1 : ℕ) : ℝ)) ^ 2
                    / ((k + P + 1 : ℕ) : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro k _
            rw [hCdef]
            exact hppTerm_le_ratio_mul P hP (by omega)
      _ = C * ∑ k ∈ Finset.range M,
              (Real.log ((k + P + 1 : ℕ) : ℝ)) ^ 2
                / ((k + P + 1 : ℕ) : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ C * B := by
            exact mul_le_mul_of_nonneg_left (log_sq_div_sq_partial_le P hPexp M) hCnonneg
      _ ≤ C * Bu := mul_le_mul_of_nonneg_left hBle hCnonneg
  have hpartial : ∀ M : ℕ,
      ∑ k ∈ Finset.range M, hppTerm (k + (P + 1)) ≤ C * Bu := by
    intro M
    simpa only [Nat.add_assoc] using hpartial' M
  have hnonneg : ∀ k : ℕ, 0 ≤ hppTerm (k + (P + 1)) := by
    intro k
    rw [hppTerm]
    split_ifs with hk
    · apply mul_nonneg (sq_nonneg _)
      apply div_nonneg
      · positivity
      · have : (1 : ℝ) < (k + (P + 1) : ℕ) := by
          exact_mod_cast (by omega : 1 < k + (P + 1))
        positivity
    · rfl
  have hshift_summ : Summable (fun k : ℕ => hppTerm (k + (P + 1))) :=
    summable_of_sum_range_le hnonneg hpartial
  have hshift_bound : ∑' k : ℕ, hppTerm (k + (P + 1)) ≤ C * Bu :=
    Real.tsum_le_of_sum_range_le hnonneg hpartial
  have hsumm : Summable hppTerm := (summable_nat_add_iff (P + 1)).mp hshift_summ
  have hsplit := hsumm.sum_add_tsum_nat_add (P + 1)
  have hfinite : ∑ p ∈ Finset.range (P + 1), hppTerm p
      ≤ ∑ p ∈ Finset.range (P + 1),
          (if Nat.Prime p then
            ((u p : ℝ)) ^ 2 * (((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3)
           else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mem_range] at hp
    by_cases hprime : Nat.Prime p
    · rw [if_pos hprime, hppTerm, if_pos hprime]
      have hlog0 : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hprime.one_le)
      have hlogu : Real.log (p : ℝ) ≤ (u p : ℝ) := hu p hprime (Nat.le_of_lt_succ hp)
      have hsq : (Real.log (p : ℝ)) ^ 2 ≤ ((u p : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlog0 hlogu 2
      have hc : 0 ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1) ^ 3 := by
        apply div_nonneg
        · positivity
        · have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
          positivity
      exact mul_le_mul_of_nonneg_right hsq hc
    · rw [if_neg hprime, hppTerm, if_neg hprime]
  rw [Hpp, ← hsplit]
  linarith [hfinite, hshift_bound, hnum]













theorem log_le_of_taylor {p N : ℕ} {u : ℚ} (hp : 0 < p) (hu : 0 ≤ u)
    (h : (p : ℚ) ≤ ∑ k ∈ Finset.range N, u ^ k / (Nat.factorial k : ℚ)) :
    Real.log (p : ℝ) ≤ (u : ℝ) := by
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hp)]
  have hcast : (((∑ k ∈ Finset.range N, u ^ k / (Nat.factorial k : ℚ)) : ℚ) : ℝ)
      = ∑ k ∈ Finset.range N, ((u : ℝ)) ^ k / (Nat.factorial k : ℝ) := by
    push_cast
    ring
  calc (p : ℝ) = ((p : ℚ) : ℝ) := by simp
    _ ≤ ((∑ k ∈ Finset.range N, u ^ k / (Nat.factorial k : ℚ) : ℚ) : ℝ) := by
          exact_mod_cast h
    _ = ∑ k ∈ Finset.range N, ((u : ℝ)) ^ k / (Nat.factorial k : ℝ) := hcast
    _ ≤ Real.exp (u : ℝ) := Real.sum_le_exp_of_nonneg (by exact_mod_cast hu) N



structure LogUpper where
  p : ℕ
  u : ℚ
  N : ℕ
  hp : 0 < p
  hu : 0 ≤ u
  htaylor : (p : ℚ) ≤ ∑ k ∈ Finset.range N, u ^ k / (Nat.factorial k : ℚ)


theorem LogUpper.sound (b : LogUpper) : Real.log (b.p : ℝ) ≤ (b.u : ℝ) :=
  log_le_of_taylor b.hp b.hu b.htaylor

end RHLean.GateII.Chain



end Inline_GateII_Chain
