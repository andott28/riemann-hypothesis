import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber
import PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorSupport
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.Polynomial
import PrimeNumberTheoremAnd.EulerMascheroniBounds
import Architect
import LeanCert.CertifiedBounds.Chebyshev
import LeanCert.Tactic.IntervalAuto
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.NormNum.BigOperators
import PrimeNumberTheoremAnd.IEANTN.LogTables
import ChebyshevPsiKernel
import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import PrimeNumberTheoremAnd.StrongPNT
import Zeta23.WeilEF.Main
namespace KernelLog
theorem log_2_gt : (0.693147 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]
theorem log_2_lt : Real.log 2 < (0.693148 : ℝ) := by
  linarith [Real.log_two_lt_d9]
theorem log_3_gt : (1.098612 : ℝ) < Real.log 3 := by
  linarith [Real.log_three_gt_d9]
theorem log_3_lt : Real.log 3 < (1.098613 : ℝ) := by
  linarith [Real.log_three_lt_d9]
theorem log_5_gt : (1.609437 : ℝ) < Real.log 5 := by
  linarith [Real.log_five_gt_d9]
theorem log_5_lt : Real.log 5 < (1.609438 : ℝ) := by
  linarith [Real.log_five_lt_d9]
theorem log_30_gt : (3.401197 : ℝ) < Real.log 30 := by
  have h30 : (30 : ℝ) = 2 * 3 * 5 := by norm_num
  rw [h30, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
theorem log_10_eq : Real.log 10 = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
theorem log_1_1723_lt : Real.log (1 + 1723 / 10000 : ℝ) < (0.1589677 : ℝ) := by
  have hx : |(-(1723 / 10000) : ℝ)| < 1 := by norm_num
  have h := Real.abs_log_sub_add_sum_range_le (x := -(1723 / 10000 : ℝ)) hx 12
  have hrhs : |(-(1723 / 10000) : ℝ)| ^ (12 + 1)
        / (1 - |(-(1723 / 10000) : ℝ)|)
      = (1723 / 10000) ^ 13 / (1 - 1723 / 10000) := by norm_num
  have harg : (1 : ℝ) - (-(1723 / 10000)) = 1 + 1723 / 10000 := by norm_num
  rw [hrhs, harg] at h
  have h2 : (∑ i ∈ Finset.range 12, (-(1723 / 10000 : ℝ)) ^ (i + 1) / (i + 1))
      + Real.log (1 + 1723 / 10000)
      ≤ (1723 / 10000) ^ 13 / (1 - 1723 / 10000) := (abs_le.mp h).2
  have hnum : -(∑ i ∈ Finset.range 12, (-(1723 / 10000 : ℝ)) ^ (i + 1) / (i + 1))
      + (1723 / 10000) ^ 13 / (1 - 1723 / 10000) < (0.1589677 : ℝ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
      Nat.cast_one, zero_add]
    norm_num
  linarith
theorem log_11723_lt : Real.log (11723 : ℝ) ≤ 937 / 100 := by
  have hfac : (11723 : ℝ) = (1 + 1723 / 10000) * 10 ^ 4 := by norm_num
  have hsplit : Real.log (11723 : ℝ)
      = Real.log (1 + 1723 / 10000) + 4 * Real.log 10 := by
    rw [hfac, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  have h10 := log_10_eq
  have h11723 := log_1_1723_lt
  nlinarith [hsplit, h10, h2, h5, h11723]
end KernelLog
namespace RHLean
open Matrix
section WeilOddCore
open MeasureTheory Complex Set Filter
open scoped ContDiff Topology
def IsOddTest (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ (∀ x, f (-x) = - f x)
def oddCore : Set (ℝ → ℂ) := {f | IsOddTest f}
def weilCore : Set (ℝ → ℂ) :=
  {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
private noncomputable def evenBump : ContDiffBump (0 : ℝ) :=
  { rIn := 2
    rOut := 3
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
noncomputable def nonzeroOddTest (x : ℝ) : ℂ :=
  ((x * evenBump x : ℝ) : ℂ)
theorem nonzeroOddTest_smooth : ContDiff ℝ ∞ nonzeroOddTest := by
  have hreal : ContDiff ℝ ∞ (fun x : ℝ => (x * evenBump x : ℝ)) :=
    contDiff_id.mul evenBump.contDiff
  have hcomplex : ContDiff ℝ ∞ (fun x : ℝ => ((x * evenBump x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  change ContDiff ℝ ∞ (fun x : ℝ => ((x * evenBump x : ℝ) : ℂ))
  exact hcomplex
theorem nonzeroOddTest_compact : HasCompactSupport nonzeroOddTest := by
  have hreal : HasCompactSupport (fun x : ℝ => x * evenBump x) :=
    evenBump.hasCompactSupport.mul_left
  have hcomplex : HasCompactSupport (fun x : ℝ => ((x * evenBump x : ℝ) : ℂ)) :=
    hreal.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  change HasCompactSupport (fun x : ℝ => ((x * evenBump x : ℝ) : ℂ))
  exact hcomplex
theorem nonzeroOddTest_odd (x : ℝ) :
    nonzeroOddTest (-x) = -nonzeroOddTest x := by
  simp [nonzeroOddTest, evenBump.neg x]
theorem nonzeroOddTest_real (x : ℝ) :
    star (nonzeroOddTest x) = nonzeroOddTest x := by
  simp [nonzeroOddTest]
theorem nonzeroOddTest_at_one : nonzeroOddTest 1 = 1 := by
  have hb : evenBump (1 : ℝ) = 1 := by
    apply evenBump.one_of_mem_closedBall
    change dist (1 : ℝ) 0 ≤ 2
    norm_num [Real.dist_eq]
  simp [nonzeroOddTest, hb]
theorem nonzeroOddTest_ne_zero : nonzeroOddTest ≠ 0 := by
  intro h
  have hz : nonzeroOddTest 1 = 0 := congrFun h 1
  rw [nonzeroOddTest_at_one] at hz
  exact (one_ne_zero : (1 : ℂ) ≠ 0) hz
theorem nonzeroOddTest_mem_oddCore : nonzeroOddTest ∈ oddCore :=
  ⟨nonzeroOddTest_smooth, nonzeroOddTest_compact, nonzeroOddTest_odd⟩
theorem exists_nonzero_mem_oddCore :
    ∃ f : ℝ → ℂ, f ∈ oddCore ∧ f ≠ 0 :=
  ⟨nonzeroOddTest, nonzeroOddTest_mem_oddCore, nonzeroOddTest_ne_zero⟩
noncomputable def transf (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, f y * Complex.exp (z * (y : ℂ))
@[simp]
theorem transf_zero (z : ℂ) : transf 0 z = 0 := by
  simp [transf]
@[simp]
theorem transf_neg (f : ℝ → ℂ) (z : ℂ) : transf (-f) z = -transf f z := by
  rw [transf, transf, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Pi.neg_apply]
  ring
theorem integrable_transf_kernel_of_continuous {f : ℝ → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (z : ℂ) :
    Integrable (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))) := by
  have hcont : Continuous (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))) :=
    hf.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  exact hcont.integrable_of_hasCompactSupport (μ := volume) (hs.mul_right)
theorem integrable_transf_kernel_of_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (z : ℂ) :
    Integrable (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))) :=
  integrable_transf_kernel_of_continuous hf.continuous hs z
theorem integrable_transf_kernel_of_mem {f : ℝ → ℂ} (hf : f ∈ oddCore) (z : ℂ) :
    Integrable (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))) :=
  integrable_transf_kernel_of_contDiff hf.1 hf.2.1 z
theorem transf_add {f g : ℝ → ℂ} {z : ℂ}
    (hf : Integrable (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))))
    (hg : Integrable (fun y : ℝ => g y * Complex.exp (z * (y : ℂ)))) :
    transf (f + g) z = transf f z + transf g z := by
  rw [transf, transf, transf, ← integral_add hf hg]
  apply integral_congr_ae
  filter_upwards with y
  change (f y + g y) * Complex.exp (z * (y : ℂ))
    = f y * Complex.exp (z * (y : ℂ)) + g y * Complex.exp (z * (y : ℂ))
  ring
theorem transf_smul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    transf (c • f) z = c * transf f z := by
  rw [transf, transf]
  have h : (fun y : ℝ => (c • f) y * Complex.exp (z * (y : ℂ)))
      = fun y : ℝ => c • (f y * Complex.exp (z * (y : ℂ))) := by
    funext y
    change c * f y * Complex.exp (z * (y : ℂ))
      = c * (f y * Complex.exp (z * (y : ℂ)))
    ring
  rw [h, integral_smul, smul_eq_mul]
theorem transf_add_of_mem {f g : ℝ → ℂ} (hf : f ∈ oddCore) (hg : g ∈ oddCore) (z : ℂ) :
    transf (f + g) z = transf f z + transf g z :=
  transf_add (integrable_transf_kernel_of_mem hf z) (integrable_transf_kernel_of_mem hg z)
theorem transf_neg_arg {f : ℝ → ℂ} (hf : ∀ x, f (-x) = -f x) (z : ℂ) :
    transf f (-z) = -transf f z := by
  rw [transf, transf]
  have hsub : ∫ y : ℝ, f y * Complex.exp ((-z) * (y : ℂ))
      = ∫ y : ℝ, f (-y) * Complex.exp (z * (y : ℂ)) := by
    rw [← integral_neg_eq_self (f := fun y : ℝ => f y * Complex.exp ((-z) * (y : ℂ)))]
    apply integral_congr_ae
    filter_upwards with y
    have : ((-z) * ((-y : ℝ) : ℂ)) = z * (y : ℂ) := by
      push_cast
      ring
    rw [this]
  rw [hsub, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [hf y]
  ring
theorem transf_conj {f : ℝ → ℂ} (hf : ∀ x, star (f x) = f x) (z : ℂ) :
    transf f (star z) = star (transf f z) := by
  rw [transf, transf]
  rw [show star (∫ y : ℝ, f y * Complex.exp (z * (y : ℂ)))
      = (starRingEnd ℂ) (∫ y : ℝ, f y * Complex.exp (z * (y : ℂ)))
      from starRingEnd_apply _]
  rw [← integral_conj (μ := volume) (𝕜 := ℂ)]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_mul, starRingEnd_apply, hf y]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul]
  simp
theorem hasDerivAt_transf {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (z : ℂ) :
    HasDerivAt (transf f)
      (∫ y : ℝ, f y * ((y : ℂ) * Complex.exp (z * (y : ℂ)))) z := by
  let F : ℂ → ℝ → ℂ := fun w y => f y * Complex.exp (w * (y : ℂ))
  let F' : ℂ → ℝ → ℂ := fun w y => f y * ((y : ℂ) * Complex.exp (w * (y : ℂ)))
  let bound : ℝ → ℝ := fun y => ‖f y‖ * |y| * Real.exp ((‖z‖ + 1) * |y|)
  have hbound_int : Integrable bound := by
    have hcont : Continuous bound := by
      dsimp [bound]
      fun_prop
    have hnorm : HasCompactSupport (fun y : ℝ => ‖f y‖) :=
      hs.comp_left (g := fun r : ℂ => ‖r‖) (by simp)
    have hsupp : HasCompactSupport bound := by
      refine hnorm.mono (fun y hy => ?_)
      have hne : ‖f y‖ * (|y| * Real.exp ((‖z‖ + 1) * |y|)) ≠ 0 := by
        simpa [bound] using hy
      exact (mul_ne_zero_iff.mp hne).1
    exact hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  have hF_meas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) volume := by
    refine Eventually.of_forall fun w => ?_
    exact (hf.continuous.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hF_int : Integrable (F z) volume :=
    integrable_transf_kernel_of_contDiff hf hs z
  have hF'_meas : AEStronglyMeasurable (F' z) volume := by
    have hcont : Continuous (F' z) := by
      dsimp [F']
      fun_prop
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ w ∈ Metric.ball z 1, ‖F' w y‖ ≤ bound y := by
    filter_upwards with y
    intro w hw
    have hw1 : ‖w‖ ≤ ‖z‖ + 1 := by
      have hdist : dist w z < 1 := Metric.mem_ball.mp hw
      have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := norm_le_norm_sub_add w z
      rw [dist_eq_norm] at hdist
      linarith [h1, hdist]
    have hrew : ‖F' w y‖ = ‖f y‖ * (|y| * Real.exp (w.re * y)) := by
      dsimp [F']
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have hre : (w * (y : ℂ)).re = w.re * y := by
        simp [Complex.mul_re]
      rw [hre]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hrew]
    have hexp_le : Real.exp (w.re * y) ≤ Real.exp ((‖z‖ + 1) * |y|) := by
      apply Real.exp_le_exp.2
      calc w.re * y ≤ |w.re * y| := le_abs_self _
        _ = |w.re| * |y| := abs_mul _ _
        _ ≤ ‖w‖ * |y| := by gcongr; exact Complex.abs_re_le_norm w
        _ ≤ (‖z‖ + 1) * |y| := by gcongr
    calc ‖f y‖ * (|y| * Real.exp (w.re * y))
        ≤ ‖f y‖ * (|y| * Real.exp ((‖z‖ + 1) * |y|)) := by
          gcongr
      _ = ‖f y‖ * |y| * Real.exp ((‖z‖ + 1) * |y|) := by ring
  have h_diff : ∀ᵐ y ∂volume, ∀ w ∈ Metric.ball z 1,
      HasDerivAt (F · y) (F' w y) w := by
    filter_upwards with y
    intro w hw
    have hlin : HasDerivAt (fun w : ℂ => w * (y : ℂ)) (y : ℂ) w := by
      simpa using (hasDerivAt_id w).mul_const (y : ℂ)
    have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * (y : ℂ)))
        (Complex.exp (w * (y : ℂ)) * (y : ℂ)) w :=
      (Complex.hasDerivAt_exp (w * (y : ℂ))).comp w hlin
    have h := hexp.const_mul (f y)
    dsimp [F, F']
    convert h using 1
    ring
  obtain ⟨-, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z) (s := Metric.ball z 1) (bound := bound)
    (Metric.ball_mem_nhds z zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  convert hderiv using 1
  ext n
  rfl
theorem z_mul_transf_eq_neg_transf_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) (z : ℂ) :
    z * transf f z = -transf (deriv f) z := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hs.isCompact.isBounded
  let M : ℝ := |R| + 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMsub : tsupport f ⊆ Set.Ioo (-M) M := by
    intro y hy
    have hy' : ‖y‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
    have hyB : |y| ≤ |R| := by
      rw [← Real.norm_eq_abs]
      exact le_trans hy' (le_abs_self R)
    have hMval : M = |R| + 1 := rfl
    constructor
    · have h1 : -|y| ≤ y := neg_abs_le y
      rw [hMval]
      linarith
    · have h1 : y ≤ |y| := le_abs_self y
      rw [hMval]
      linarith
  let E : ℝ → ℂ := fun y => Complex.exp (z * (y : ℂ))
  let g : ℝ → ℂ := fun y => f y * E y
  let g' : ℝ → ℂ := fun y => deriv f y * E y + z * (f y * E y)
  have hE : ∀ y : ℝ, HasDerivAt E (z * E y) y := by
    intro y
    have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    have hmul : HasDerivAt (fun y : ℝ => z * (y : ℂ)) (z * 1) y := hof.const_mul z
    have hexp := (Complex.hasDerivAt_exp (z * (y : ℂ))).comp y hmul
    have hval : z * 1 = z := by ring
    rw [hval] at hexp
    dsimp [E]
    simpa only [Function.comp_def, mul_comm] using hexp
  have hg_deriv : ∀ y : ℝ, HasDerivAt g (g' y) y := by
    intro y
    have hfd : HasDerivAt f (deriv f y) y := (hf.differentiable_one y).hasDerivAt
    have hg := hfd.mul (hE y)
    dsimp only [g, g']
    convert hg using 1
    ring
  have hg'_cont : Continuous g' := by
    have h1 : Continuous (fun y : ℝ => deriv f y * E y) :=
      (hf.continuous_deriv_one.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).congr
        (fun y => by rfl)
    have h2 : Continuous (fun y : ℝ => z * (f y * E y)) :=
      continuous_const.mul (hf.continuous.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))
    exact h1.add h2
  have hg'_int : IntervalIntegrable g' volume (-M) M := hg'_cont.intervalIntegrable _ _
  have hftc : ∫ y in (-M)..M, g' y = g M - g (-M) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg_deriv y) hg'_int
  have hM_notMem : M ∉ tsupport f := fun h => (lt_irrefl M) (hMsub h).2
  have hM_neg_notMem : -M ∉ tsupport f := fun h => (lt_irrefl (-M)) (hMsub h).1
  have h_endM : g M = 0 := by
    have : f M = 0 := by
      by_contra h
      exact hM_notMem (subset_tsupport f h)
    simp [g, this]
  have h_endneg : g (-M) = 0 := by
    have : f (-M) = 0 := by
      by_contra h
      exact hM_neg_notMem (subset_tsupport f h)
    simp [g, this]
  have hzero_out : ∀ y : ℝ, y ∉ Set.Ioc (-M) M → g' y = 0 := by
    intro y hy
    have hyts : y ∉ tsupport f := by
      intro hyt
      have := hMsub hyt
      exact hy ⟨this.1, this.2.le⟩
    have hf0 : f y = 0 := by
      by_contra h
      exact hyts (subset_tsupport f h)
    have hdf0 : deriv f y = 0 := deriv_of_notMem_tsupport hyts
    simp [g', hf0, hdf0]
  have hglobal : ∫ y, g' y = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-M) M) hzero_out]
    rw [← intervalIntegral.integral_of_le (show -M ≤ M by linarith)]
    rw [hftc, h_endM, h_endneg]
    ring
  have h1 : Integrable (fun y : ℝ => deriv f y * E y) := by
    have hc : Continuous (fun y : ℝ => deriv f y * E y) :=
      hf.continuous_deriv_one.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have hsupp : HasCompactSupport (fun y : ℝ => deriv f y * E y) :=
      hs.deriv.mono (fun y hy => by
        have hne : deriv f y * E y ≠ 0 := hy
        exact (mul_ne_zero_iff.mp hne).1)
    exact hc.integrable_of_hasCompactSupport (μ := volume) hsupp
  have h2 : Integrable (fun y : ℝ => z * (f y * E y)) :=
    (integrable_transf_kernel_of_continuous hf.continuous hs z).const_mul z
  have hsplit : (∫ y : ℝ, deriv f y * E y) + ∫ y : ℝ, z * (f y * E y) = 0 := by
    rw [← integral_add h1 h2, ← hglobal]
  rw [integral_const_mul] at hsplit
  have hA : (∫ y : ℝ, deriv f y * E y) = transf (deriv f) z := rfl
  have hB : (∫ y : ℝ, f y * E y) = transf f z := rfl
  rw [hA, hB] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit
lemma exists_pos_tsupport_subset_Ioo {f : ℝ → ℂ} (hs : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ tsupport f ⊆ Set.Ioo (-M) M := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hs.isCompact.isBounded
  refine ⟨|R| + 1, by positivity, ?_⟩
  intro y hy
  have hy' : ‖y‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
  have hyB : |y| ≤ |R| := by
    rw [← Real.norm_eq_abs]
    exact le_trans hy' (le_abs_self R)
  constructor
  · have h1 : -|y| ≤ y := neg_abs_le y
    linarith
  · have h1 : y ≤ |y| := le_abs_self y
    linarith
theorem exists_transf_norm_mul_le {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖transf f z‖ * (1 + ‖z‖) ≤ C := by
  obtain ⟨M, hMpos, hMsub⟩ := exists_pos_tsupport_subset_Ioo hs
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hderiv_cont : Continuous (fun y : ℝ => ‖deriv f y‖) := hf1.continuous_deriv_one.norm
  have hderiv_int : Integrable (fun y : ℝ => ‖deriv f y‖) :=
    hderiv_cont.integrable_of_hasCompactSupport (μ := volume) hs.deriv.norm
  have hf_int : Integrable (fun y : ℝ => ‖f y‖) :=
    hf.continuous.norm.integrable_of_hasCompactSupport (μ := volume) hs.norm
  let C₁ : ℝ := Real.exp (M / 2) * ∫ y : ℝ, ‖deriv f y‖
  let M₁ : ℝ := Real.exp (M / 2) * ∫ y : ℝ, ‖f y‖
  have hC₁ : 0 ≤ C₁ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun y => norm_nonneg _)
  have hM₁ : 0 ≤ M₁ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun y => norm_nonneg _)
  have hbound_deriv : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖transf (deriv f) z‖ ≤ C₁ := by
    intro z hz
    rw [transf]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ y : ℝ, ‖deriv f y * Complex.exp (z * (y : ℂ))‖
        ≤ ‖deriv f y‖ * Real.exp (M / 2) := by
      intro y
      by_cases hy : y ∈ tsupport f
      · have hyM : |y| < M := by
          have h := hMsub hy
          rw [abs_lt]
          exact ⟨h.1, h.2⟩
        rw [norm_mul, Complex.norm_exp]
        have hre : (z * (y : ℂ)).re = z.re * y := by simp [Complex.mul_re]
        rw [hre]
        have hexp : Real.exp (z.re * y) ≤ Real.exp (M / 2) := by
          apply Real.exp_le_exp.2
          calc z.re * y ≤ |z.re * y| := le_abs_self _
            _ = |z.re| * |y| := abs_mul _ _
            _ ≤ (1 / 2) * |y| := by gcongr
            _ ≤ M / 2 := by linarith
        exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      · have h0 : deriv f y = 0 := deriv_of_notMem_tsupport hy
        simp [h0]
    have hprod_int : Integrable (fun y : ℝ => deriv f y * Complex.exp (z * (y : ℂ))) := by
      have hcont : Continuous (fun y : ℝ => deriv f y * Complex.exp (z * (y : ℂ))) :=
        hf1.continuous_deriv_one.mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
      have hsupp : HasCompactSupport (fun y : ℝ => deriv f y * Complex.exp (z * (y : ℂ))) :=
        hs.deriv.mono (fun y hy => (mul_ne_zero_iff.mp hy).1)
      exact hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
    have hint2 : Integrable (fun y : ℝ => ‖deriv f y‖ * Real.exp (M / 2)) := by
      simpa only [mul_comm] using hderiv_int.mul_const (Real.exp (M / 2))
    calc ∫ y : ℝ, ‖deriv f y * Complex.exp (z * (y : ℂ))‖
        ≤ ∫ y : ℝ, ‖deriv f y‖ * Real.exp (M / 2) :=
          integral_mono hprod_int.norm hint2 hpt
      _ = C₁ := by
          rw [integral_mul_const, mul_comm]
  have hbound_f : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖transf f z‖ ≤ M₁ := by
    intro z hz
    rw [transf]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ y : ℝ, ‖f y * Complex.exp (z * (y : ℂ))‖
        ≤ ‖f y‖ * Real.exp (M / 2) := by
      intro y
      by_cases hy : y ∈ tsupport f
      · have hyM : |y| < M := by
          have h := hMsub hy
          rw [abs_lt]
          exact ⟨h.1, h.2⟩
        rw [norm_mul, Complex.norm_exp]
        have hre : (z * (y : ℂ)).re = z.re * y := by simp [Complex.mul_re]
        rw [hre]
        have hexp : Real.exp (z.re * y) ≤ Real.exp (M / 2) := by
          apply Real.exp_le_exp.2
          calc z.re * y ≤ |z.re * y| := le_abs_self _
            _ = |z.re| * |y| := abs_mul _ _
            _ ≤ (1 / 2) * |y| := by gcongr
            _ ≤ M / 2 := by linarith
        exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      · have h0 : f y = 0 := by
          by_contra h
          exact hy (subset_tsupport f h)
        simp [h0]
    have hprod_int : Integrable (fun y : ℝ => f y * Complex.exp (z * (y : ℂ))) :=
      integrable_transf_kernel_of_continuous hf.continuous hs z
    have hint2 : Integrable (fun y : ℝ => ‖f y‖ * Real.exp (M / 2)) := by
      simpa only [mul_comm] using hf_int.mul_const (Real.exp (M / 2))
    calc ∫ y : ℝ, ‖f y * Complex.exp (z * (y : ℂ))‖
        ≤ ∫ y : ℝ, ‖f y‖ * Real.exp (M / 2) :=
          integral_mono hprod_int.norm hint2 hpt
      _ = M₁ := by
          rw [integral_mul_const, mul_comm]
  refine ⟨2 * max C₁ M₁, by positivity, ?_⟩
  intro z hz
  rcases le_or_gt 1 ‖z‖ with hz1 | hz1
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz1
      norm_num at hz1
    have hibp := z_mul_transf_eq_neg_transf_deriv hf1 hs z
    have hnorm : ‖z‖ * ‖transf f z‖ = ‖transf (deriv f) z‖ := by
      rw [← norm_mul, hibp, norm_neg]
    have hb := hbound_deriv z hz
    calc ‖transf f z‖ * (1 + ‖z‖)
        ≤ ‖transf f z‖ * (2 * ‖z‖) := by
          gcongr
          linarith
      _ = 2 * (‖z‖ * ‖transf f z‖) := by ring
      _ = 2 * ‖transf (deriv f) z‖ := by rw [hnorm]
      _ ≤ 2 * max C₁ M₁ := by
          gcongr
          exact le_trans hb (le_max_left _ _)
  · have hb := hbound_f z hz
    have h1z : 1 + ‖z‖ ≤ 2 := by linarith
    have h2 : ‖transf f z‖ * (1 + ‖z‖) ≤ M₁ * 2 := by
      nlinarith [norm_nonneg (transf f z), hM₁, hb, h1z]
    have h3 : M₁ * 2 ≤ 2 * max C₁ M₁ := by
      have : M₁ ≤ max C₁ M₁ := le_max_right _ _
      linarith
    linarith
theorem differentiable_transf {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Differentiable ℂ (transf f) :=
  fun z => (hasDerivAt_transf hf hs z).differentiableAt
open scoped ContDiff
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hre : 1 ≤ s.re) (hs1 : s ≠ 1) :
    riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hG : Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (lt_of_lt_of_le zero_lt_one hre)
  have hcz : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero (s := s) hs0]
    field_simp
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hcz]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
      (mul_ne_zero hG (riemannZeta_ne_zero_of_one_le_re hre)))
    (by norm_num)
theorem riemannXi_one_ne_zero : riemannXi (1 : ℂ) ≠ 0 := by
  have h : riemannXi (1 : ℂ) = riemannXi 0 := by
    have := riemannXi_one_sub (1 : ℂ)
    simpa using this.symm
  rw [h, riemannXi_zero]
  norm_num
theorem riemannXi_zero_re_mem_Ioo {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    have hle : s.re ≤ 0 := le_of_not_gt h
    have h1s : riemannXi (1 - s) = 0 := by
      rw [riemannXi_one_sub]
      exact hs
    have hre1 : 1 ≤ (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    by_cases h1 : (1 : ℂ) - s = 1
    · have hs0 : s = 0 := by
        linear_combination -h1
      rw [hs0] at hs
      rw [riemannXi_zero] at hs
      norm_num at hs
    · exact riemannXi_ne_zero_of_one_le_re hre1 h1 h1s
  · by_contra h
    have hge : 1 ≤ s.re := le_of_not_gt h
    by_cases hs1 : s = 1
    · rw [hs1] at hs
      exact riemannXi_one_ne_zero hs
    · exact riemannXi_ne_zero_of_one_le_re hge hs1 hs
theorem val_re_mem_Ioo
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).re ∈ Set.Ioo (0 : ℝ) 1 := by
  refine riemannXi_zero_re_mem_Ioo ?_
  have hdiv := Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support (p := p)
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi] at hdiv
  have hnat : analyticOrderNatAt Complex.riemannXi
      (Complex.Hadamard.divisorZeroIndex₀_val p) ≠ 0 := by
    simpa using hdiv
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hnat
theorem finite_divisorSupport_im_le (T : ℝ) :
    ((MeromorphicOn.divisor Complex.riemannXi (Set.univ : Set ℂ)).support ∩
      {z : ℂ | |z.im| ≤ T}).Finite := by
  have hfin : (Metric.closedBall (0 : ℂ) (1 + T) ∩
      (MeromorphicOn.divisor Complex.riemannXi (Set.univ : Set ℂ)).support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := Complex.riemannXi)
      (U := Set.univ) (K := Metric.closedBall (0 : ℂ) (1 + T))
      (isCompact_closedBall (0 : ℂ) (1 + T)) (Set.subset_univ _)
  refine hfin.subset ?_
  rintro z ⟨hzsupp, hzim⟩
  have hzimT : |z.im| ≤ T := hzim
  have hzero : Complex.riemannXi z = 0 := by
    have hdiv : MeromorphicOn.divisor Complex.riemannXi (Set.univ : Set ℂ) z ≠ 0 := by
      simpa [Function.mem_support] using hzsupp
    have hcast : ((analyticOrderNatAt Complex.riemannXi z : ℤ)) ≠ 0 := by
      rwa [← Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
        differentiable_riemannXi]
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (Nat.cast_ne_zero.mp hcast)
  have hstrip := riemannXi_zero_re_mem_Ioo hzero
  have hTnonneg : 0 ≤ T := le_trans (abs_nonneg z.im) hzimT
  refine ⟨?_, hzsupp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq : ‖z‖ ^ 2 ≤ (1 + T) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have him : z.im ^ 2 ≤ T ^ 2 := by
      have h := abs_le.mp hzimT
      nlinarith [h.1, h.2]
    nlinarith [hstrip.1, hstrip.2, him, hTnonneg]
  have h2 : |‖z‖| ≤ |1 + T| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg (by linarith)] at h2
theorem analyticOrderAt_riemannXi_ne_top (z : ℂ) : analyticOrderAt Complex.riemannXi z ≠ ⊤ := by
  intro htop
  have hloc : ∀ᶠ w in 𝓝 z, Complex.riemannXi w = 0 := analyticOrderAt_eq_top.mp htop
  have hfreq : ∃ᶠ w in 𝓝[≠] z, Complex.riemannXi w = 0 :=
    (hloc.filter_mono nhdsWithin_le_nhds).frequently
  have hzero : Complex.riemannXi = 0 :=
    AnalyticOnNhd.eq_of_frequently_eq (f := Complex.riemannXi) (g := fun _ : ℂ => 0)
      (differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ)
      analyticOnNhd_const hfreq
  have h0 := congrFun hzero 0
  rw [Complex.riemannXi_zero] at h0
  norm_num at h0
theorem exists_index_of_riemannXi_eq_zero {s : ℂ} (hs : s ≠ 0)
    (hξ : Complex.riemannXi s = 0) :
    ∃ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = s := by
  have han : AnalyticAt ℂ Complex.riemannXi s := differentiable_riemannXi.analyticAt s
  have hord : analyticOrderAt Complex.riemannXi s ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨han, hξ⟩
  have hnat : analyticOrderNatAt Complex.riemannXi s ≠ 0 := by
    intro h0
    apply hord
    rw [← Nat.cast_analyticOrderNatAt (f := Complex.riemannXi) (z₀ := s)
      (analyticOrderAt_riemannXi_ne_top s), h0]
    rfl
  have hcard := Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (f := Complex.riemannXi) differentiable_riemannXi (z₀ := s) hs
  have hne : (Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      (f := Complex.riemannXi) s).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.card_empty] at hcard
    exact hnat hcard.symm
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
    (f := Complex.riemannXi) (z₀ := s) p).mp hp⟩
noncomputable def centeredZero
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) : ℂ :=
  Complex.Hadamard.divisorZeroIndex₀_val p - 1 / 2
theorem finite_indexSet_im_le (T : ℝ) :
    ({p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) |
      |(centeredZero p).im| ≤ T} : Set _).Finite := by
  have hfin := finite_divisorSupport_im_le T
  have hunion :
      (⋃ z ∈ (MeromorphicOn.divisor Complex.riemannXi (Set.univ : Set ℂ)).support ∩
          {z : ℂ | |z.im| ≤ T},
        {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) |
          Complex.Hadamard.divisorZeroIndex₀_val p = z}).Finite :=
    hfin.biUnion (fun z _ => Complex.Hadamard.divisorZeroIndex₀_fiber_finite Complex.riemannXi z)
  refine hunion.subset ?_
  intro p hp
  refine Set.mem_iUnion.mpr ⟨Complex.Hadamard.divisorZeroIndex₀_val p, ?_⟩
  refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
  · refine ⟨Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support (p := p), ?_⟩
    have him : (centeredZero p).im = (Complex.Hadamard.divisorZeroIndex₀_val p).im := by
      rw [centeredZero, Complex.sub_im]
      norm_num
    simpa [him] using hp
  · rfl
noncomputable def weilOdd (f : ℝ → ℂ) : ℝ :=
  (∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
    transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))).re
theorem weilOdd_summand_eq_neg_sq {f : ℝ → ℂ}
    (hodd : ∀ x, f (-x) = -f x) (hreal : ∀ x, star (f x) = f x)
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))
      = -(transf f (centeredZero p)) ^ 2 := by
  have h1 : transf f (-(star (centeredZero p))) = -transf f (star (centeredZero p)) :=
    transf_neg_arg hodd (star (centeredZero p))
  rw [h1, star_neg, transf_conj hreal (centeredZero p), star_star]
  ring
theorem weilOdd_eq_tsum_neg_sq {f : ℝ → ℂ}
    (hodd : ∀ x, f (-x) = -f x) (hreal : ∀ x, star (f x) = f x) :
    weilOdd f = (∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      -(transf f (centeredZero p)) ^ 2).re := by
  rw [weilOdd]
  congr 1
  exact tsum_congr fun p => weilOdd_summand_eq_neg_sq hodd hreal p
theorem weilOdd_smul (c : ℝ) (f : ℝ → ℂ) :
    weilOdd (c • f) = c ^ 2 * weilOdd f := by
  have hfun : (c • f : ℝ → ℂ) = (c : ℂ) • f := by
    funext x
    simp [Complex.real_smul]
  have hterm : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      transf ((c : ℂ) • f) (centeredZero p)
          * star (transf ((c : ℂ) • f) (-(star (centeredZero p))))
        = (c : ℂ) ^ 2 *
          (transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))) := by
    intro p
    rw [transf_smul, transf_smul, star_mul]
    have hc : star (c : ℂ) = (c : ℂ) := by simp
    rw [hc]
    ring
  rw [weilOdd, weilOdd, hfun, tsum_congr hterm, tsum_mul_left]
  rw [Complex.mul_re]
  have hc2 : (c : ℂ) ^ 2 = ((c ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc2]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring
private lemma inv_one_add_sq_le_nine_quarters_div_sq {x r : ℝ} (hr : 0 < r)
    (h : r ≤ (3 / 2) * (1 + x)) :
    1 / (1 + x) ^ 2 ≤ (9 / 4) / r ^ 2 := by
  have hx : 0 < 1 + x := by nlinarith
  have h1 : 0 < (1 + x) ^ 2 := by positivity
  have h2 : 0 < r ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 h2]
  nlinarith
theorem summable_weil_summand {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) =>
      transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))) := by
  obtain ⟨C, hC0, hC⟩ := exists_transf_norm_mul_le hf.1 hf.2.1
  have hbound : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      ‖transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))‖
        ≤ (9 / 4) * C ^ 2 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2 := by
    intro p
    set ρ : ℂ := Complex.Hadamard.divisorZeroIndex₀_val p with hρ
    set l : ℂ := centeredZero p with hl
    have hρre := val_re_mem_Ioo p
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
    have hlre : |l.re| ≤ 1 / 2 := by
      have hre : l.re = ρ.re - 1 / 2 := by
        rw [hl, centeredZero, hρ, Complex.sub_re]
        norm_num
      rw [hre, abs_le]
      exact ⟨by linarith [hρre.1], by linarith [hρre.2]⟩
    have hl're : |(-(star l)).re| ≤ 1 / 2 := by
      have hre : (-(star l)).re = -l.re := by simp
      rw [hre, abs_neg]
      exact hlre
    have h1 := hC l hlre
    have h2 := hC (-(star l)) hl're
    have hden : 0 < 1 + ‖l‖ := by positivity
    have hF1 : ‖transf f l‖ ≤ C / (1 + ‖l‖) := by
      rw [le_div_iff₀ hden]
      exact h1
    have hnorml' : ‖-(star l)‖ = ‖l‖ := by simp
    have hF2 : ‖transf f (-(star l))‖ ≤ C / (1 + ‖l‖) := by
      have h2' : ‖transf f (-(star l))‖ * (1 + ‖l‖) ≤ C := by
        simpa [hnorml'] using h2
      rw [le_div_iff₀ hden]
      exact h2'
    have hρle : ‖ρ‖ ≤ (3 / 2) * (1 + ‖l‖) := by
      have htri : ‖ρ‖ ≤ ‖l‖ + ‖(1 / 2 : ℂ)‖ := by
        have hsum : ρ = l + 1 / 2 := by
          rw [hl, hρ, centeredZero]
          ring
        rw [hsum]
        exact norm_add_le _ _
      have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [hhalf] at htri
      nlinarith [norm_nonneg l]
    have hineq : 1 / (1 + ‖l‖) ^ 2 ≤ (9 / 4) / ‖ρ‖ ^ 2 :=
      inv_one_add_sq_le_nine_quarters_div_sq hρpos hρle
    calc ‖transf f l * star (transf f (-(star l)))‖
        = ‖transf f l‖ * ‖transf f (-(star l))‖ := by rw [norm_mul, norm_star]
      _ ≤ (C / (1 + ‖l‖)) * (C / (1 + ‖l‖)) :=
          mul_le_mul hF1 hF2 (norm_nonneg _) (div_nonneg hC0 hden.le)
      _ = C ^ 2 / (1 + ‖l‖) ^ 2 := by field_simp
      _ ≤ (9 / 4) * C ^ 2 / ‖ρ‖ ^ 2 := by
          have hmul := mul_le_mul_of_nonneg_left hineq (sq_nonneg C)
          calc C ^ 2 / (1 + ‖l‖) ^ 2 = C ^ 2 * (1 / (1 + ‖l‖) ^ 2) := by
                rw [mul_one_div]
            _ ≤ C ^ 2 * ((9 / 4) / ‖ρ‖ ^ 2) := hmul
            _ = (9 / 4) * C ^ 2 / ‖ρ‖ ^ 2 := by ring
  have hsumm_maj :
      Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) =>
        (9 / 4) * C ^ 2 / ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ^ 2) := by
    have hbase := summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
    have hbase' : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) => ((9 / 4) * C ^ 2) * (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ (2 : ℕ)) :=
      hbase.mul_left _
    refine hbase'.congr ?_
    intro p
    rw [div_eq_mul_inv, inv_pow]
    ring
  exact Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hsumm_maj)
theorem summable_weil_summand_of_odd_real {f : ℝ → ℂ}
    (hodd : ∀ x, f (-x) = -f x) (hreal : ∀ x, star (f x) = f x) (hf : f ∈ oddCore) :
    Summable (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) =>
      -(transf f (centeredZero p)) ^ 2) := by
  refine (summable_weil_summand hf).congr ?_
  intro p
  exact weilOdd_summand_eq_neg_sq hodd hreal p
theorem nonzeroOddTest_weil_summand
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    transf nonzeroOddTest (centeredZero p)
        * star (transf nonzeroOddTest (-(star (centeredZero p))))
      = -(transf nonzeroOddTest (centeredZero p)) ^ 2 :=
  weilOdd_summand_eq_neg_sq nonzeroOddTest_odd nonzeroOddTest_real p
theorem weilOdd_zero : weilOdd (0 : ℝ → ℂ) = 0 := by
  simp [weilOdd, transf]
noncomputable def bump0 : ℝ → ℝ := evenBump.normed volume
theorem bump0_smooth : ContDiff ℝ ∞ bump0 := evenBump.contDiff_normed (μ := volume)
theorem bump0_compact : HasCompactSupport bump0 :=
  evenBump.hasCompactSupport_normed (μ := volume)
theorem bump0_even (x : ℝ) : bump0 (-x) = bump0 x := evenBump.normed_neg (μ := volume) x
theorem bump0_integral : (∫ x : ℝ, bump0 x) = 1 := evenBump.integral_normed (μ := volume)
theorem transf_bump0_zero :
    transf (fun y : ℝ => (bump0 y : ℂ)) 0 = 1 := by
  rw [transf]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  calc ∫ y : ℝ, (bump0 y : ℂ) = ((∫ y : ℝ, bump0 y : ℝ) : ℂ) :=
        integral_ofReal (f := bump0) (μ := volume)
    _ = ((1 : ℝ) : ℂ) := by rw [bump0_integral]
    _ = 1 := by norm_num
noncomputable def bumpScale (a : ℝ) (y : ℝ) : ℂ :=
  ((a * bump0 (a * y) : ℝ) : ℂ)
theorem ofReal_smul_eq_mul (r : ℝ) (x : ℂ) : r • x = (r : ℂ) * x :=
  RCLike.real_smul_eq_coe_mul r x
theorem bumpScale_smooth (a : ℝ) : ContDiff ℝ ∞ (bumpScale a) := by
  have hreal : ContDiff ℝ ∞ (fun y : ℝ => a * bump0 (a * y)) :=
    contDiff_const.mul (bump0_smooth.comp (contDiff_const.mul contDiff_id))
  exact Complex.ofRealCLM.contDiff.comp hreal
theorem bumpScale_even (a : ℝ) (y : ℝ) : bumpScale a (-y) = bumpScale a y := by
  have h : a * (-y) = -(a * y) := by ring
  simp [bumpScale, h, bump0_even]
theorem bumpScale_real (a : ℝ) (y : ℝ) : star (bumpScale a y) = bumpScale a y := by
  rw [bumpScale, RCLike.star_def]
  exact Complex.conj_ofReal _
theorem bumpScale_compact {a : ℝ} (ha : 0 < a) : HasCompactSupport (bumpScale a) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (3 / a)) ?_
  intro y hy
  have hsupport : bump0 (a * y) ≠ 0 := by
    intro h0
    exact hy (by simp [bumpScale, h0])
  have hts : tsupport bump0 = Metric.closedBall (0 : ℝ) 3 := by
    rw [bump0, evenBump.tsupport_normed_eq (μ := volume)]
    rfl
  have hball : a * y ∈ Metric.closedBall (0 : ℝ) 3 := by
    have hmem := subset_tsupport bump0 (Function.mem_support.mpr hsupport)
    rwa [hts] at hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hball ⊢
  simp only [Real.norm_eq_abs] at hball ⊢
  rw [abs_mul, abs_of_pos ha] at hball
  rw [le_div_iff₀ ha]
  nlinarith [hball]
theorem transf_bumpScale (a : ℝ) (ha : 0 < a) (z : ℂ) :
    transf (bumpScale a) z
      = transf (fun y : ℝ => (bump0 y : ℂ)) (z / a) := by
  rw [transf, transf]
  have hpt : ∀ y : ℝ,
      bumpScale a y * Complex.exp (z * (y : ℂ))
        = (a : ℂ) • ((bump0 (a * y) : ℂ)
            * Complex.exp ((z / a) * ((a * y : ℝ) : ℂ))) := by
    intro y
    have hexp : Complex.exp ((z / a) * ((a * y : ℝ) : ℂ))
        = Complex.exp (z * (y : ℂ)) := by
      congr 1
      push_cast
      field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha.ne']
    rw [hexp]
    simp only [bumpScale, Complex.ofReal_mul]
    rw [smul_eq_mul]
    ring
  calc ∫ y : ℝ, bumpScale a y * Complex.exp (z * (y : ℂ))
      = ∫ y : ℝ, (a : ℂ) • ((bump0 (a * y) : ℂ)
          * Complex.exp ((z / a) * ((a * y : ℝ) : ℂ))) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (a : ℂ) • ∫ y : ℝ, (bump0 (a * y) : ℂ)
          * Complex.exp ((z / a) * ((a * y : ℝ) : ℂ)) := by
        rw [integral_smul]
    _ = (a : ℂ) • (|a⁻¹| • ∫ y : ℝ, (bump0 y : ℂ)
          * Complex.exp ((z / a) * (y : ℂ))) := by
        rw [MeasureTheory.Measure.integral_comp_mul_left
          (fun u : ℝ => (bump0 u : ℂ) * Complex.exp ((z / a) * (u : ℂ))) a]
    _ = ∫ y : ℝ, (bump0 y : ℂ) * Complex.exp ((z / a) * (y : ℂ)) := by
        rw [abs_of_pos (inv_pos.mpr ha), ofReal_smul_eq_mul, smul_eq_mul]
        have h1 : (a : ℂ) * ((a⁻¹ : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one]
        rw [← mul_assoc, h1, one_mul]
theorem exists_bumpScale_transf_ne_zero (lam : ℂ) :
    ∃ a : ℝ, 0 < a ∧ transf (bumpScale a) lam ≠ 0 := by
  have hbump_smooth : ContDiff ℝ ∞ (fun y : ℝ => (bump0 y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp bump0_smooth
  have hbump_compact : HasCompactSupport (fun y : ℝ => (bump0 y : ℂ)) :=
    bump0_compact.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hcont : ContinuousAt (fun w : ℂ => transf (fun y : ℝ => (bump0 y : ℂ)) w) 0 :=
    (differentiable_transf hbump_smooth hbump_compact).continuous.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (1 / 2) (by norm_num)
  let a : ℝ := max 1 (2 * ‖lam‖ / δ) + 1
  have ha : 0 < a := by
    have h1 : (1 : ℝ) ≤ max 1 (2 * ‖lam‖ / δ) := le_max_left _ _
    linarith
  refine ⟨a, ha, ?_⟩
  rw [transf_bumpScale a ha lam]
  intro hz
  have hdist : dist (lam / a) 0 < δ := by
    rw [dist_zero_right, norm_div]
    rw [show ‖((a : ℝ) : ℂ)‖ = a by simp [abs_of_pos ha]]
    rw [div_lt_iff₀ ha]
    have h2 : 2 * ‖lam‖ / δ < a := by
      have hle : 2 * ‖lam‖ / δ ≤ max 1 (2 * ‖lam‖ / δ) := le_max_right _ _
      linarith
    have h3 : 2 * ‖lam‖ < a * δ := (div_lt_iff₀ hδpos).mp h2
    nlinarith [norm_nonneg lam]
  have hnear := hδ hdist
  rw [transf_bump0_zero, hz] at hnear
  norm_num at hnear
theorem exists_orbit_test (lam : ℂ) :
    ∃ ψ : ℝ → ℂ,
      (∀ x, star (ψ x) = ψ x) ∧ (∀ x, ψ (-x) = ψ x) ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ‖transf ψ lam‖ = 1 ∧
      ∃ T : ℝ, |lam.im| < T ∧
        ∀ z : ℂ, |z.re| ≤ 1 / 2 → T ≤ |z.im| → ‖transf ψ z‖ ≤ 1 / 2 := by
  obtain ⟨a, ha, hne⟩ := exists_bumpScale_transf_ne_zero lam
  let c : ℝ := ‖transf (bumpScale a) lam‖⁻¹
  have hcpos : 0 < c := inv_pos.mpr (norm_pos_iff.mpr hne)
  let ψ : ℝ → ℂ := fun y => (c : ℂ) * bumpScale a y
  have hsmul : ψ = (c : ℂ) • bumpScale a := rfl
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    rw [hsmul]
    exact (bumpScale_smooth a).const_smul (c : ℂ)
  have hψ_compact : HasCompactSupport ψ := by
    rw [hsmul]
    exact (bumpScale_compact ha).smul_left
  have hψ_real : ∀ x, star (ψ x) = ψ x := by
    intro x
    rw [show ψ x = (c : ℂ) * bumpScale a x from rfl, star_mul, bumpScale_real a x]
    simp [mul_comm]
  have hψ_even : ∀ x, ψ (-x) = ψ x := by
    intro x
    simp [ψ, bumpScale_even a x]
  have hψ_norm : ‖transf ψ lam‖ = 1 := by
    rw [hsmul, transf_smul, norm_mul]
    have hcn : ‖(c : ℂ)‖ = c := by
      simp [abs_of_pos hcpos]
    rw [hcn]
    have hc1 : c * ‖transf (bumpScale a) lam‖ = 1 := by
      dsimp [c]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
    linarith
  obtain ⟨C, hCnonneg, hC⟩ := exists_transf_norm_mul_le hψ_smooth hψ_compact
  refine ⟨ψ, hψ_real, hψ_even, hψ_smooth, hψ_compact, hψ_norm,
    max |lam.im| (2 * C) + 1, ?_, ?_⟩
  · have hle : |lam.im| ≤ max |lam.im| (2 * C) := le_max_left _ _
    linarith
  · intro z hzre hzim
    have hzC := hC z hzre
    have hznorm : max |lam.im| (2 * C) + 1 ≤ ‖z‖ := by
      have h := Complex.abs_im_le_norm z
      linarith
    have h1 : ‖transf ψ z‖ ≤ C / (1 + ‖z‖) := by
      rw [le_div_iff₀ (by linarith [norm_nonneg z] : (0 : ℝ) < 1 + ‖z‖)]
      linarith [hzC]
    have hpos : 0 < 1 + (max |lam.im| (2 * C) + 1) := by
      have h0 : 0 ≤ max |lam.im| (2 * C) := le_trans (abs_nonneg _) (le_max_left _ _)
      linarith
    have h2 : C / (1 + ‖z‖) ≤ C / (1 + (max |lam.im| (2 * C) + 1)) := by
      have hden : 1 + (max |lam.im| (2 * C) + 1) ≤ 1 + ‖z‖ := by linarith [hznorm]
      exact div_le_div_of_nonneg_left hCnonneg hpos hden
    have h3 : C / (1 + (max |lam.im| (2 * C) + 1)) ≤ 1 / 2 := by
      have hT : 2 * C ≤ max |lam.im| (2 * C) + 1 := by
        have hle : 2 * C ≤ max |lam.im| (2 * C) := le_max_right _ _
        linarith
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith
theorem exists_even_polynomial_killing (S : Finset ℂ) (lam : ℂ)
    (hS : ∀ z ∈ S, z ≠ lam ∧ z ≠ -lam ∧ z ≠ star lam ∧ z ≠ -star lam) :
    ∃ P : Polynomial ℂ,
      (∀ z : ℂ, P.eval (-z) = P.eval z) ∧
      (∀ z ∈ S, P.eval z = 0) ∧
      P.eval lam ≠ 0 ∧ P.eval (star lam) ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, fun z => by simp, fun z hz => by simp at hz, by simp, by simp⟩
  | insert a S ha ih =>
      obtain ⟨P, hPeven, hPkill, hPne, hPne'⟩ :=
        ih (fun z hz => hS z (Finset.mem_insert_of_mem hz))
      have haS := hS a (Finset.mem_insert_self a S)
      have hne : lam ^ 2 - a ^ 2 ≠ 0 := by
        intro h
        have hfac : (lam - a) * (lam + a) = 0 := by linear_combination h
        rcases mul_eq_zero.mp hfac with h1 | h1
        · exact haS.1 (sub_eq_zero.mp h1).symm
        · have h2 : a = -lam := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact h1
          exact haS.2.1 h2
      have hne' : (star lam) ^ 2 - a ^ 2 ≠ 0 := by
        intro h
        have hfac : (star lam - a) * (star lam + a) = 0 := by linear_combination h
        rcases mul_eq_zero.mp hfac with h1 | h1
        · exact haS.2.2.1 (sub_eq_zero.mp h1).symm
        · have h2 : a = -star lam := by
            rw [eq_neg_iff_add_eq_zero, add_comm]
            exact h1
          exact haS.2.2.2 h2
      refine ⟨P * (Polynomial.X ^ 2 - Polynomial.C (a ^ 2)), ?_, ?_, ?_, ?_⟩
      · intro z
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, hPeven z]
        ring
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · rw [Polynomial.eval_mul]
          exact mul_eq_zero.mpr (Or.inr (by
            simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
              Polynomial.eval_C]
            ring))
        · rw [Polynomial.eval_mul]
          exact mul_eq_zero.mpr (Or.inl (hPkill z hz))
      · rw [Polynomial.eval_mul]
        exact mul_ne_zero hPne (by
          simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C] using hne)
      · rw [Polynomial.eval_mul]
        exact mul_ne_zero hPne' (by
          simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C] using hne')
theorem orbit_quartet_summands {F : ℂ → ℂ} {lam : ℂ}
    (hodd : ∀ z, F (-z) = -F z) (hconj : ∀ z, F (star z) = star (F z))
    (h1 : F lam = 1) :
    F lam * star (F (-(star lam))) = -1 ∧
    F (star lam) * star (F (-(star (star lam)))) = -1 ∧
    F (-lam) * star (F (-(star (-lam)))) = -1 ∧
    F (-(star lam)) * star (F (-(star (-(star lam))))) = -1 := by
  have hstar : F (star lam) = 1 := by rw [hconj, h1]; simp
  have hneg : F (-lam) = -1 := by rw [hodd, h1]
  have hnegstar : F (-(star lam)) = -1 := by rw [hodd, hstar]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnegstar, h1]; simp
  · rw [star_star, hneg, hstar]; simp
  · rw [star_neg, neg_neg, hstar, hneg]; simp
  · rw [star_neg, star_star, neg_neg, h1, hnegstar]; simp
noncomputable def realFactor (z : ℂ) : Polynomial ℂ :=
  (Polynomial.X ^ 2 - Polynomial.C (((z ^ 2).re : ℝ) : ℂ)) ^ 2 +
    Polynomial.C ((((z ^ 2).im : ℝ) ^ 2 : ℝ) : ℂ)
theorem realFactor_eval (z w : ℂ) :
    (realFactor z).eval w = (w ^ 2 - z ^ 2) * (w ^ 2 - star (z ^ 2)) := by
  set a : ℂ := (((z ^ 2).re : ℝ) : ℂ) with ha
  set b : ℂ := (((z ^ 2).im : ℝ) : ℂ) with hb
  have hz : z ^ 2 = a + b * Complex.I := by
    rw [ha, hb]
    exact (RCLike.re_add_im (z ^ 2)).symm
  have hstar2 : star (a + b * Complex.I) = a - b * Complex.I := by
    apply Complex.ext
    · rw [RCLike.star_def, Complex.conj_re, Complex.add_re, Complex.sub_re, Complex.mul_re]
      simp [ha, hb, Complex.I_re, Complex.I_im]
    · rw [RCLike.star_def, Complex.conj_im, Complex.add_im, Complex.sub_im, Complex.mul_im]
      simp [ha, hb, Complex.I_re, Complex.I_im]
  have hrf : realFactor z = (Polynomial.X ^ 2 - Polynomial.C a) ^ 2 +
      Polynomial.C (b ^ 2) := by
    simp only [realFactor, ← ha, Complex.ofReal_pow, ← hb]
  rw [hrf]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  have key : (w ^ 2 - a) ^ 2 + b ^ 2 =
      (w ^ 2 - (a + b * Complex.I)) * (w ^ 2 - (a - b * Complex.I)) := by
    ring_nf
    rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]
    ring
  rw [key, ← hstar2, ← hz]
theorem exists_even_conj_polynomial_killing (S : Finset ℂ) (lam : ℂ)
    (hS : ∀ z ∈ S, z ≠ lam ∧ z ≠ -lam ∧ z ≠ star lam ∧ z ≠ -star lam) :
    ∃ P : Polynomial ℂ,
      (∀ z : ℂ, P.eval (-z) = P.eval z) ∧
      (∀ z : ℂ, P.eval (star z) = star (P.eval z)) ∧
      (∀ z ∈ S, P.eval z = 0) ∧
      P.eval lam ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨1, by intro z; simp, by intro z; simp, by intro z hz; simp at hz, by simp⟩
  | insert a S ha ih =>
      obtain ⟨P, hPeven, hPconj, hPkill, hPne⟩ :=
        ih (fun z hz => hS z (Finset.mem_insert_of_mem hz))
      have haS := hS a (Finset.mem_insert_self a S)
      refine ⟨P * realFactor a, ?_, ?_, ?_, ?_⟩
      · intro z
        simp only [Polynomial.eval_mul, hPeven z]
        congr 1
        rw [realFactor_eval, realFactor_eval]
        ring
      · intro z
        simp only [Polynomial.eval_mul, hPconj z, star_mul']
        congr 1
        rw [realFactor_eval, realFactor_eval]
        simp only [star_mul', star_sub, star_pow, star_star]
        ring
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · rw [Polynomial.eval_mul, realFactor_eval]
          simp
        · rw [Polynomial.eval_mul]
          exact mul_eq_zero.mpr (Or.inl (hPkill z hz))
      · rw [Polynomial.eval_mul, realFactor_eval]
        refine mul_ne_zero hPne (mul_ne_zero ?_ ?_)
        · intro h
          have h2 : lam ^ 2 = a ^ 2 := sub_eq_zero.mp h
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h1 | h1
          · exact haS.1 h1.symm
          · exact haS.2.1 (by rw [h1]; ring)
        · intro h
          have h2 : lam ^ 2 = (star a) ^ 2 := by
            rw [sub_eq_zero.mp h, star_pow]
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h1 | h1
          · refine haS.2.2.1 ?_
            rw [h1, star_star]
          · refine haS.2.2.2 ?_
            rw [h1]
            simp
theorem orbit_quartet_summands_of_values {F : ℂ → ℂ} {lam : ℂ}
    (hodd : ∀ z, F (-z) = -F z) (h1 : F lam = 1) (hstar : F (star lam) = 1) :
    F lam * star (F (-(star lam))) = -1 ∧
    F (star lam) * star (F (-(star (star lam)))) = -1 ∧
    F (-lam) * star (F (-(star (-lam)))) = -1 ∧
    F (-(star lam)) * star (F (-(star (-(star lam))))) = -1 := by
  have hneg : F (-lam) = -1 := by rw [hodd, h1]
  have hnegstar : F (-(star lam)) = -1 := by rw [hodd, hstar]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnegstar, h1]; simp
  · rw [star_star, hneg, hstar]; simp
  · rw [star_neg, neg_neg, hstar, hneg]; simp
  · rw [star_neg, star_star, neg_neg, h1, hnegstar]; simp
theorem exists_even_constant_normalization {lam H : ℂ} (hH : H ≠ 0) :
    ∃ R : Polynomial ℂ, (∀ z : ℂ, R.eval (-z) = R.eval z) ∧ R.eval lam * H = 1 := by
  refine ⟨Polynomial.C H⁻¹, ?_, ?_⟩
  · intro z; simp
  · simp [one_div, inv_mul_cancel₀ hH]
theorem exists_even_quadratic_normalization {lam H H' : ℂ} (hH : H ≠ 0) (hH' : H' ≠ 0)
    (hne : lam ^ 2 ≠ star (lam ^ 2)) :
    ∃ a b : ℂ, (a + b * lam ^ 2) * H = 1 ∧ (a + b * star (lam ^ 2)) * H' = 1 := by
  set b : ℂ := (1 / H - 1 / H') / (lam ^ 2 - star (lam ^ 2)) with hb
  refine ⟨1 / H - b * lam ^ 2, b, ?_, ?_⟩
  · rw [sub_add_cancel]
    simpa [one_div] using inv_mul_cancel₀ hH
  · have hb' : b * (lam ^ 2 - star (lam ^ 2)) = 1 / H - 1 / H' := by
      rw [hb]
      field_simp
    calc (1 / H - b * lam ^ 2 + b * star (lam ^ 2)) * H'
        = (1 / H - b * (lam ^ 2 - star (lam ^ 2))) * H' := by ring
      _ = (1 / H - (1 / H - 1 / H')) * H' := by rw [hb']
      _ = (1 / H') * H' := by ring
      _ = 1 := by simpa [one_div] using inv_mul_cancel₀ hH'
lemma even_quadratic_eval (a b : ℂ) (z : ℂ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2).eval (-z) =
      (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2).eval z := by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  ring
theorem exists_transf_norm_mul_pow_le :
    ∀ (N : ℕ) (f : ℝ → ℂ), ContDiff ℝ ∞ f → HasCompactSupport f →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.re| ≤ 1 / 2 →
        ‖transf f z‖ * (1 + ‖z‖) ^ N ≤ C := by
  intro N
  induction N with
  | zero =>
      intro f hf hs
      obtain ⟨C0, hC0nn, hC0⟩ := exists_transf_norm_mul_le hf hs
      refine ⟨C0, hC0nn, fun z hz => ?_⟩
      have h := hC0 z hz
      have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have hle : ‖transf f z‖ ≤ C0 := by
        calc ‖transf f z‖ = ‖transf f z‖ * 1 := (mul_one _).symm
          _ ≤ ‖transf f z‖ * (1 + ‖z‖) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ ≤ C0 := h
      simpa using hle
  | succ N ih =>
      intro f hf hs
      obtain ⟨C0, hC0nn, hC0⟩ := exists_transf_norm_mul_le hf hs
      have hf' : ContDiff ℝ ∞ (deriv f) := by
        simpa using ContDiff.iterate_deriv 1 hf
      obtain ⟨C1, hC1nn, hC1⟩ := ih (deriv f) hf' hs.deriv
      refine ⟨max (C0 * 2 ^ (N + 1)) (2 * C1), by positivity, fun z hz => ?_⟩
      by_cases hz1 : ‖z‖ ≤ 1
      · have hle : ‖transf f z‖ ≤ C0 := by
          have h := hC0 z hz
          have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
          calc ‖transf f z‖ = ‖transf f z‖ * 1 := (mul_one _).symm
            _ ≤ ‖transf f z‖ * (1 + ‖z‖) :=
                mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
            _ ≤ C0 := h
        have hpow : (1 + ‖z‖) ^ (N + 1) ≤ 2 ^ (N + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg z]) _
        calc ‖transf f z‖ * (1 + ‖z‖) ^ (N + 1)
            ≤ C0 * 2 ^ (N + 1) :=
              mul_le_mul hle hpow (by positivity) hC0nn
          _ ≤ max (C0 * 2 ^ (N + 1)) (2 * C1) := le_max_left _ _
      · push_neg at hz1
        have hzpos : 0 < ‖z‖ := lt_trans one_pos hz1
        have hid := z_mul_transf_eq_neg_transf_deriv
          (hf.of_le (by simp : (1 : ℕ∞) ≤ ∞)) hs z
        have hnorm : ‖z‖ * ‖transf f z‖ = ‖transf (deriv f) z‖ := by
          have h := congrArg norm hid
          rwa [norm_mul, norm_neg] at h
        have hval : ‖transf f z‖ = ‖transf (deriv f) z‖ / ‖z‖ := by
          rw [eq_div_iff hzpos.ne']
          rw [mul_comm]
          exact hnorm
        have hrw : ‖transf (deriv f) z‖ / ‖z‖ * (1 + ‖z‖) ^ (N + 1)
            = (‖transf (deriv f) z‖ * (1 + ‖z‖) ^ N) * ((1 + ‖z‖) / ‖z‖) := by
          rw [pow_succ]
          field_simp
        rw [hval, hrw]
        have hb := hC1 z hz
        have hratio : (1 + ‖z‖) / ‖z‖ ≤ 2 := by
          rw [div_le_iff₀ hzpos]
          linarith
        have hratio_nonneg : 0 ≤ (1 + ‖z‖) / ‖z‖ :=
          div_nonneg (by positivity) hzpos.le
        calc (‖transf (deriv f) z‖ * (1 + ‖z‖) ^ N) * ((1 + ‖z‖) / ‖z‖)
            ≤ C1 * 2 := mul_le_mul hb hratio hratio_nonneg hC1nn
          _ ≤ max (C0 * 2 ^ (N + 1)) (2 * C1) := by
              rw [mul_comm C1 2]
              exact le_max_right _ _
theorem exists_polynomial_eval_bound (P : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖P.eval z‖ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
  classical
  set C : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun k hk => norm_nonneg _
  refine ⟨C, hCnn, fun z => ?_⟩
  rw [Polynomial.eval_eq_sum_range z]
  calc ‖∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * z ^ k‖
      ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k * z ^ k‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ * ‖z‖ ^ k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1),
          ‖P.coeff k‖ * (1 + ‖z‖) ^ P.natDegree := by
        refine Finset.sum_le_sum fun k hk => ?_
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hk' : k ≤ P.natDegree := by
          have := Finset.mem_range.mp hk
          omega
        have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
        calc ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k :=
              pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) k
          _ ≤ (1 + ‖z‖) ^ P.natDegree := pow_le_pow_right₀ h1 hk'
    _ = C * (1 + ‖z‖) ^ P.natDegree := by
        rw [hC, ← Finset.sum_mul]
theorem transf_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (z : ℂ) :
    transf (deriv f) z = -z * transf f z := by
  have h := z_mul_transf_eq_neg_transf_deriv hf hs z
  have h' := congrArg Neg.neg h
  simpa [neg_mul] using h'.symm
theorem contDiff_iteratedDeriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n hf
theorem hasCompactSupport_iteratedDeriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ∀ n, HasCompactSupport (iteratedDeriv n f) := by
  intro n
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hs
  | succ k ihk =>
      rw [iteratedDeriv_succ]
      exact HasCompactSupport.deriv ihk
theorem transf_iteratedDeriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∀ (n : ℕ) (z : ℂ),
      transf (iteratedDeriv n f) z = (-1) ^ n * z ^ n * transf f z := by
  intro n
  induction n with
  | zero =>
      intro z
      simp [iteratedDeriv_zero]
  | succ n ih =>
      intro z
      have hcd : ContDiff ℝ ∞ (iteratedDeriv n f) := contDiff_iteratedDeriv f hf n
      have hcs : HasCompactSupport (iteratedDeriv n f) :=
        hasCompactSupport_iteratedDeriv f hf hs n
      have h1 : ContDiff ℝ 1 (iteratedDeriv n f) :=
        hcd.of_le (by simp : (1 : ℕ∞) ≤ ∞)
      rw [iteratedDeriv_succ, transf_deriv h1 hcs, ih z, pow_succ, pow_succ]
      ring
theorem exists_transf_mul_polynomial :
    ∀ (Q : Polynomial ℂ) (h : ℝ → ℂ), ContDiff ℝ ∞ h → HasCompactSupport h →
      ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
        ∀ z : ℂ, transf g z = Q.eval z * transf h z := by
  intro Q
  refine Polynomial.induction_on Q ?hC ?hadd ?hmonomial
  · intro c h hh hs
    exact ⟨c • h, hh.const_smul c, HasCompactSupport.smul_left hs, fun z => by
      rw [transf_smul, Polynomial.eval_C]⟩
  · intro p q hp hq h hh hs
    obtain ⟨gp, hgp_s, hgp_c, hgp⟩ := hp h hh hs
    obtain ⟨gq, hgq_s, hgq_c, hgq⟩ := hq h hh hs
    refine ⟨gp + gq, hgp_s.add hgq_s, HasCompactSupport.add hgp_c hgq_c, fun z => ?_⟩
    rw [transf_add (integrable_transf_kernel_of_contDiff hgp_s hgp_c z)
        (integrable_transf_kernel_of_contDiff hgq_s hgq_c z),
      hgp z, hgq z, Polynomial.eval_add]
    ring
  · intro n a hp h hh hs
    obtain ⟨gp, hgp_s, hgp_c, hgp⟩ := hp h hh hs
    have hdg_s : ContDiff ℝ ∞ (deriv gp) := by
      simpa using ContDiff.iterate_deriv 1 hgp_s
    have hdg_c : HasCompactSupport (deriv gp) := HasCompactSupport.deriv hgp_c
    refine ⟨-deriv gp, hdg_s.neg, HasCompactSupport.neg hdg_c, fun z => ?_⟩
    have h1 : ContDiff ℝ 1 gp := hgp_s.of_le (by simp : (1 : ℕ∞) ≤ ∞)
    rw [transf_neg, transf_deriv h1 hgp_c z, hgp z,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_X, pow_succ]
    ring
theorem transf_reflect (g : ℝ → ℂ) (z : ℂ) :
    transf (fun y => g (-y)) z = transf g (-z) := by
  rw [transf, transf]
  have h : (fun y : ℝ => g (-y) * Complex.exp (z * (y : ℂ)))
      = fun y : ℝ => (fun u : ℝ => g u * Complex.exp ((-z) * (u : ℂ))) (-y) := by
    funext y
    simp only
    rw [show ((-z : ℂ) * (((-y : ℝ) : ℂ))) = z * ((y : ℝ) : ℂ) by
      push_cast
      ring]
  rw [h]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    (fun u : ℝ => g u * Complex.exp ((-z) * (u : ℂ)))
noncomputable def oddPart (g : ℝ → ℂ) : ℝ → ℂ := fun y => (g y - g (-y)) / 2
theorem oddPart_odd (g : ℝ → ℂ) (y : ℝ) : oddPart g (-y) = - oddPart g y := by
  simp only [oddPart]
  rw [neg_neg]
  ring
theorem transf_oddPart {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g)
    (z : ℂ) :
    transf (oddPart g) z = (transf g z - transf g (-z)) / 2 := by
  have hrefl_s : ContDiff ℝ ∞ (fun y : ℝ => g (-y)) := hg.comp (by fun_prop)
  have hrefl_c : HasCompactSupport (fun y : ℝ => g (-y)) := by
    have hsub : Function.support (fun y : ℝ => g (-y)) ⊆ Neg.neg '' tsupport g := by
      intro y hy
      exact ⟨-y, subset_tsupport g (Function.mem_support.mpr hy), by simp⟩
    exact HasCompactSupport.of_support_subset_isCompact
      ((show IsCompact (tsupport g) from hs).image continuous_neg) hsub
  have hsm1_s : ContDiff ℝ ∞ ((1 / 2 : ℂ) • g) := hg.const_smul (1 / 2 : ℂ)
  have hsm1_c : HasCompactSupport ((1 / 2 : ℂ) • g) := HasCompactSupport.smul_left hs
  have hsm2_s : ContDiff ℝ ∞ (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) :=
    hrefl_s.const_smul ((-1 / 2 : ℂ))
  have hsm2_c : HasCompactSupport (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) :=
    HasCompactSupport.smul_left hrefl_c
  have hsum : oddPart g = ((1 / 2 : ℂ) • g) + (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) := by
    funext y
    simp only [oddPart, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hsum, transf_add (integrable_transf_kernel_of_contDiff hsm1_s hsm1_c z)
      (integrable_transf_kernel_of_contDiff hsm2_s hsm2_c z),
    transf_smul, transf_smul, transf_reflect]
  ring
theorem integral_comp_add_right_line (t : ℝ) (F : ℝ → ℂ) :
    (∫ x : ℝ, F (x + t)) = ∫ x : ℝ, F x :=
  (measurePreserving_add_right (volume : Measure ℝ) t).integral_comp
    (Homeomorph.addRight t).isClosedEmbedding.measurableEmbedding F
theorem transf_translate (φ : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    transf (fun x => φ (x - t)) z = Complex.exp (z * t) * transf φ z := by
  rw [transf, transf]
  have htrans : (∫ x : ℝ, φ (x - t) * Complex.exp (z * ((x : ℂ) - t)))
      = ∫ u : ℝ, φ u * Complex.exp (z * (u : ℂ)) := by
    have h := integral_comp_add_right_line (-t)
      (fun u : ℝ => φ u * Complex.exp (z * (u : ℂ)))
    simpa [sub_eq_add_neg] using h
  have hsplit : (∫ x : ℝ, φ (x - t) * Complex.exp (z * ((x : ℂ) - t)))
      = (∫ x : ℝ, φ (x - t) * Complex.exp (z * (x : ℂ))) *
        Complex.exp (-(z * t)) := by
    rw [← integral_mul_const (Complex.exp (-(z * t)))
      (fun x : ℝ => φ (x - t) * Complex.exp (z * (x : ℂ)))]
    congr 1 with x
    rw [show z * ((x : ℂ) - t) = z * (x : ℂ) + (-(z * t)) by ring, Complex.exp_add]
    ring
  have h1 : (∫ x : ℝ, φ (x - t) * Complex.exp (z * (x : ℂ))) *
      Complex.exp (-(z * t)) = ∫ u : ℝ, φ u * Complex.exp (z * (u : ℂ)) := by
    rw [← hsplit]
    exact htrans
  have h2 := congrArg (fun c : ℂ => c * Complex.exp (z * t)) h1
  have h3 : (∫ x : ℝ, φ (x - t) * Complex.exp (z * (x : ℂ))) =
      (∫ u : ℝ, φ u * Complex.exp (z * (u : ℂ))) * Complex.exp (z * t) := by
    simpa [mul_assoc, ← Complex.exp_add, Complex.exp_zero, mul_one] using h2
  rw [h3, mul_comm]
open scoped Convolution
theorem transf_convolution {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) (z : ℂ) :
    transf (f ⋆[ContinuousLinearMap.mul ℝ ℂ] g) z = transf f z * transf g z := by
  have hconv : ∀ x : ℝ, (f ⋆[ContinuousLinearMap.mul ℝ ℂ] g) x =
      ∫ t : ℝ, f t * g (x - t) := by
    intro x
    rw [MeasureTheory.convolution_def]
    simp [ContinuousLinearMap.mul_apply]
  rw [transf]
  simp only [hconv]
  have hpt : ∀ x : ℝ, (∫ t : ℝ, f t * g (x - t)) * Complex.exp (z * (x : ℂ))
      = ∫ t : ℝ, f t * g (x - t) * Complex.exp (z * (x : ℂ)) := by
    intro x
    rw [← integral_mul_const]
  simp only [hpt]
  have hF : Integrable (Function.uncurry
      (fun x t : ℝ => f t * g (x - t) * Complex.exp (z * (x : ℂ))))
      (volume.prod volume) := by
    have hcont : Continuous (Function.uncurry
        (fun x t : ℝ => f t * g (x - t) * Complex.exp (z * (x : ℂ)))) := by
      have h1 : Continuous (fun p : ℝ × ℝ => f p.2) :=
        hf.continuous.comp continuous_snd
      have h2 : Continuous (fun p : ℝ × ℝ => g (p.1 - p.2)) :=
        hg.continuous.comp (continuous_fst.sub continuous_snd)
      have h3 : Continuous (fun p : ℝ × ℝ => Complex.exp (z * (p.1 : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
      show Continuous (fun p : ℝ × ℝ =>
        f p.2 * g (p.1 - p.2) * Complex.exp (z * (p.1 : ℂ)))
      exact (h1.mul h2).mul h3
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      ((hgs.isCompact.add hfs.isCompact).prod hfs.isCompact) ?_
    intro p hp
    have hfne : f p.2 ≠ 0 := by
      intro h0
      exact hp (by simp [Function.uncurry, h0])
    have hgne : g (p.1 - p.2) ≠ 0 := by
      intro h0
      exact hp (by simp [Function.uncurry, h0])
    exact ⟨⟨p.1 - p.2, subset_tsupport g (Function.mem_support.mpr hgne),
        p.2, subset_tsupport f (Function.mem_support.mpr hfne), by ring⟩,
      subset_tsupport f (Function.mem_support.mpr hfne)⟩
  rw [integral_integral_swap hF]
  have hinner : ∀ t : ℝ, (∫ x : ℝ, f t * g (x - t) * Complex.exp (z * (x : ℂ)))
      = f t * (Complex.exp (z * t) * ∫ u : ℝ, g u * Complex.exp (z * (u : ℂ))) := by
    intro t
    have h1 : (∫ x : ℝ, f t * g (x - t) * Complex.exp (z * (x : ℂ)))
        = f t * ∫ x : ℝ, g (x - t) * Complex.exp (z * (x : ℂ)) := by
      rw [← integral_const_mul (f t) (fun x : ℝ => g (x - t) * Complex.exp (z * (x : ℂ)))]
      congr 1 with x
      ring
    rw [h1]
    have h2 : (∫ x : ℝ, g (x - t) * Complex.exp (z * (x : ℂ)))
        = Complex.exp (z * t) * ∫ u : ℝ, g u * Complex.exp (z * (u : ℂ)) := by
      simpa only [transf] using transf_translate g t z
    rw [h2]
  simp_rw [hinner]
  have hlast : (∫ t : ℝ, f t * (Complex.exp (z * t) *
      ∫ u : ℝ, g u * Complex.exp (z * (u : ℂ))))
      = (∫ t : ℝ, f t * Complex.exp (z * t)) *
        (∫ u : ℝ, g u * Complex.exp (z * (u : ℂ))) := by
    rw [← integral_mul_const (∫ u : ℝ, g u * Complex.exp (z * (u : ℂ)))
      (fun t : ℝ => f t * Complex.exp (z * t))]
    congr 1 with t
    ring
  rw [hlast]
  simp only [transf]
noncomputable def psiPow (ψ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => ψ
  | M + 1 => psiPow ψ M ⋆[ContinuousLinearMap.mul ℝ ℂ] ψ
theorem psiPow_contDiff (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) :
    ∀ M, ContDiff ℝ ∞ (psiPow ψ M)
  | 0 => hψ
  | M + 1 => by
      have hM := psiPow_contDiff ψ hψ hs M
      exact hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
        hM.continuous.locallyIntegrable hψ
theorem psiPow_hasCompactSupport (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) :
    ∀ M, HasCompactSupport (psiPow ψ M)
  | 0 => hs
  | M + 1 => by
      have hM := psiPow_hasCompactSupport ψ hψ hs M
      exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hM hs
theorem transf_psiPow (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ) :
    ∀ (M : ℕ) (z : ℂ), transf (psiPow ψ M) z = (transf ψ z) ^ (M + 1)
  | 0, z => by simp [psiPow]
  | M + 1, z => by
      have hcd := psiPow_contDiff ψ hψ hs M
      have hcs := psiPow_hasCompactSupport ψ hψ hs M
      rw [show psiPow ψ (M + 1) =
          psiPow ψ M ⋆[ContinuousLinearMap.mul ℝ ℂ] ψ from rfl,
        transf_convolution hcd hcs hψ hs z,
        transf_psiPow ψ hψ hs M z]
      rw [← pow_succ]
theorem transf_even_arg {ψ : ℝ → ℂ} (hψ : ∀ x, ψ (-x) = ψ x) (z : ℂ) :
    transf ψ (-z) = transf ψ z := by
  have h : (fun y : ℝ => ψ (-y)) = ψ := funext hψ
  have h1 := transf_reflect ψ (-z)
  rw [neg_neg, h] at h1
  exact h1
theorem transf_psiPow_even (ψ : ℝ → ℂ) (hψ_s : ContDiff ℝ ∞ ψ)
    (hψ_c : HasCompactSupport ψ) (hψ_even : ∀ x, ψ (-x) = ψ x) (M : ℕ) (z : ℂ) :
    transf (psiPow ψ M) (-z) = transf (psiPow ψ M) z := by
  rw [transf_psiPow ψ hψ_s hψ_c M, transf_psiPow ψ hψ_s hψ_c M,
    transf_even_arg hψ_even]
theorem transf_psiPow_conj (ψ : ℝ → ℂ) (hψ_s : ContDiff ℝ ∞ ψ)
    (hψ_c : HasCompactSupport ψ) (hψ_real : ∀ x, star (ψ x) = ψ x) (M : ℕ) (z : ℂ) :
    transf (psiPow ψ M) (star z) = star (transf (psiPow ψ M) z) := by
  rw [transf_psiPow ψ hψ_s hψ_c M, transf_psiPow ψ hψ_s hψ_c M, transf_conj hψ_real,
    star_pow]
theorem oddPart_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (oddPart g) := by
  have hrefl : ContDiff ℝ ∞ (fun y : ℝ => g (-y)) := hg.comp (by fun_prop)
  have hsum : oddPart g = ((1 / 2 : ℂ) • g) + (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) := by
    funext y
    simp only [oddPart, Pi.add_apply, Pi.smul_apply]
    ring
  rw [hsum]
  exact (hg.const_smul (1 / 2 : ℂ)).add (hrefl.const_smul (-1 / 2 : ℂ))
theorem hasCompactSupport_neg_comp {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun y : ℝ => g (-y)) := by
  have hsub : Function.support (fun y : ℝ => g (-y)) ⊆ Neg.neg '' tsupport g := by
    intro y hy
    exact ⟨-y, subset_tsupport g (Function.mem_support.mpr hy), by simp⟩
  exact HasCompactSupport.of_support_subset_isCompact
    ((show IsCompact (tsupport g) from hg).image continuous_neg) hsub
theorem oddPart_hasCompactSupport {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (oddPart g) := by
  have hrefl := hasCompactSupport_neg_comp hg
  have hsum : oddPart g = ((1 / 2 : ℂ) • g) + (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) := by
    funext y
    simp only [oddPart, Pi.add_apply, Pi.smul_apply]
    ring
  have h1 : HasCompactSupport ((1 / 2 : ℂ) • g) := HasCompactSupport.smul_left hg
  have h2 : HasCompactSupport (((-1 / 2 : ℂ)) • (fun y : ℝ => g (-y))) :=
    HasCompactSupport.smul_left hrefl
  rw [hsum]
  exact h1.add h2
theorem exists_model_test (ψ : ℝ → ℂ) (hψ_s : ContDiff ℝ ∞ ψ)
    (hψ_c : HasCompactSupport ψ) (hψ_even : ∀ x, ψ (-x) = ψ x)
    (Q : Polynomial ℂ) (hQ_even : ∀ z, Q.eval (-z) = Q.eval z)
    (M : ℕ) (lam c : ℂ)
    (hc1 : c * (lam * Q.eval lam * (transf ψ lam) ^ (M + 1)) = 1)
    (hc2 : c * (star lam * Q.eval (star lam) * (transf ψ (star lam)) ^ (M + 1)) = 1) :
    ∃ f : ℝ → ℂ, f ∈ oddCore ∧
      (∀ z, transf f z = c * (z * Q.eval z * (transf ψ z) ^ (M + 1))) ∧
      transf f lam = 1 ∧ transf f (star lam) = 1 ∧
      (∀ z, transf f (-z) = -transf f z) := by
  obtain ⟨g, hg_s, hg_c, hg⟩ := exists_transf_mul_polynomial Q (psiPow ψ M)
    (psiPow_contDiff ψ hψ_s hψ_c M) (psiPow_hasCompactSupport ψ hψ_s hψ_c M)
  have hgD_s : ContDiff ℝ ∞ (deriv g) := by
    simpa using ContDiff.iterate_deriv 1 hg_s
  have hgD_c : HasCompactSupport (deriv g) := HasCompactSupport.deriv hg_c
  have hgD_t : ∀ z : ℂ, transf (deriv g) z = -z * Q.eval z * (transf ψ z) ^ (M + 1) := by
    intro z
    have h1 : ContDiff ℝ 1 g := hg_s.of_le (by simp : (1 : ℕ∞) ≤ ∞)
    rw [transf_deriv h1 hg_c z, hg z, transf_psiPow ψ hψ_s hψ_c M z]
    ring
  have hgD_odd : ∀ z : ℂ, transf (deriv g) (-z) = -transf (deriv g) z := by
    intro z
    rw [hgD_t z, hgD_t (-z), hQ_even]
    simp only [transf_even_arg hψ_even, neg_mul]
  have hodd_t : ∀ z : ℂ, transf (oddPart (deriv g)) z = transf (deriv g) z := by
    intro z
    rw [transf_oddPart hgD_s hgD_c z, hgD_odd z]
    ring
  refine ⟨(-c) • oddPart (deriv g), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (oddPart_contDiff hgD_s).const_smul (-c)
  · exact (oddPart_hasCompactSupport hgD_c).smul_left
  · intro x
    simp only [Pi.smul_apply]
    rw [oddPart_odd]
    ring
  · intro z
    rw [transf_smul, hodd_t z, hgD_t z]
    ring
  · rw [transf_smul, hodd_t lam, hgD_t lam]
    linear_combination hc1
  · rw [transf_smul, hodd_t (star lam), hgD_t (star lam)]
    linear_combination hc2
  · intro z
    rw [transf_smul, transf_smul, hodd_t z, hodd_t (-z), hgD_odd z]
    ring
theorem exists_normalization {ψ : ℝ → ℂ} {lam : ℂ}
    (hψ_norm : ‖transf ψ lam‖ = 1) (hψ_norm' : ‖transf ψ (star lam)‖ = 1)
    (hlam_re : lam.re ≠ 0) (P : Polynomial ℂ) (hP_even : ∀ z, P.eval (-z) = P.eval z)
    (hP_lam : P.eval lam ≠ 0) (hP_star : P.eval (star lam) ≠ 0) (M : ℕ) :
    ∃ Q : Polynomial ℂ, ∃ c : ℂ,
      (∀ z, Q.eval (-z) = Q.eval z) ∧
      (∀ z, P.eval z = 0 → Q.eval z = 0) ∧
      c * (lam * Q.eval lam * (transf ψ lam) ^ (M + 1)) = 1 ∧
      c * (star lam * Q.eval (star lam) * (transf ψ (star lam)) ^ (M + 1)) = 1 ∧
      ‖c‖ ≤ max 1 ((‖lam‖ * ‖P.eval lam‖)⁻¹) := by
  have hlam : lam ≠ 0 := fun h => hlam_re (by rw [h]; simp)
  have hΨ : transf ψ lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψ_norm
    norm_num at hψ_norm
  have hΨ' : transf ψ (star lam) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψ_norm'
    norm_num at hψ_norm'
  have hH : lam * P.eval lam * (transf ψ lam) ^ (M + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hlam hP_lam) (pow_ne_zero _ hΨ)
  by_cases hreal : lam ^ 2 = star (lam ^ 2)
  ·
    have hstar : star lam = lam := by
      have hsq : lam ^ 2 = (star lam) ^ 2 := hreal.trans (star_pow lam 2)
      have hfac : (lam - star lam) * (lam + star lam) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact (sub_eq_zero.mp h1).symm
      · exfalso
        have hre : (lam + star lam).re = 0 := by rw [h1]; simp
        simp only [Complex.add_re, RCLike.star_def, Complex.conj_re] at hre
        exact hlam_re (by linarith)
    refine ⟨P, (lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹, hP_even,
      fun z hz => hz, ?_, ?_, ?_⟩
    · rw [inv_mul_cancel₀ hH]
    · rw [hstar, inv_mul_cancel₀ hH]
    · rw [norm_inv]
      have hnorm : ‖lam * P.eval lam * (transf ψ lam) ^ (M + 1)‖
          = ‖lam‖ * ‖P.eval lam‖ := by
        rw [norm_mul, norm_mul, norm_pow, hψ_norm, one_pow, mul_one]
      rw [hnorm]
      exact le_max_right _ _
  ·
    have hstarlam : star lam ≠ 0 := fun h => hlam (by
      have := congrArg star h
      simpa using this)
    have hH' : star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hstarlam hP_star) (pow_ne_zero _ hΨ')
    obtain ⟨a, b, h1, h2⟩ :=
      exists_even_quadratic_normalization hH hH' hreal
    refine ⟨P * (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2), 1, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [hP_even z]
      ring
    · intro z hz
      rw [Polynomial.eval_mul, hz, zero_mul]
    · have hQeval : (P * (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2)).eval lam
          = P.eval lam * (a + b * lam ^ 2) := by
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
      rw [hQeval]
      have ht := h1
      rw [show lam * P.eval lam * (transf ψ lam) ^ (M + 1)
            = lam * (P.eval lam * (transf ψ lam) ^ (M + 1)) from by ring] at ht
      linear_combination ht
    · have hQeval : (P * (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2)).eval (star lam)
          = P.eval (star lam) * (a + b * star (lam ^ 2)) := by
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        rw [star_pow]
      rw [hQeval]
      have ht := h2
      rw [show star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1)
            = star lam * (P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))
            from by ring] at ht
      linear_combination ht
    · simp
theorem exists_normalization_uniform {ψ : ℝ → ℂ} {lam : ℂ}
    (hψ_norm : ‖transf ψ lam‖ = 1) (hψ_norm' : ‖transf ψ (star lam)‖ = 1)
    (hlam_re : lam.re ≠ 0) (P : Polynomial ℂ)
    (hP_lam : P.eval lam ≠ 0) (hP_star : P.eval (star lam) ≠ 0) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ M : ℕ, ∃ R : Polynomial ℂ, ∃ c : ℂ,
      (∀ z, R.eval (-z) = R.eval z) ∧
      c * (lam * (P * R).eval lam * (transf ψ lam) ^ (M + 1)) = 1 ∧
      c * (star lam * (P * R).eval (star lam) * (transf ψ (star lam)) ^ (M + 1)) = 1 ∧
      ‖c‖ ≤ max 1 ((‖lam‖ * ‖P.eval lam‖)⁻¹) ∧
      (∀ z, ‖R.eval z‖ ≤ Cb * (1 + ‖z‖) ^ 2) := by
  have hlam : lam ≠ 0 := fun h => hlam_re (by rw [h]; simp)
  have hΨ : transf ψ lam ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψ_norm
    norm_num at hψ_norm
  have hΨ' : transf ψ (star lam) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψ_norm'
    norm_num at hψ_norm'
  by_cases hreal : lam ^ 2 = star (lam ^ 2)
  · have hstar : star lam = lam := by
      have hsq : lam ^ 2 = (star lam) ^ 2 := hreal.trans (star_pow lam 2)
      have hfac : (lam - star lam) * (lam + star lam) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact (sub_eq_zero.mp h1).symm
      · exfalso
        have hre : (lam + star lam).re = 0 := by rw [h1]; simp
        simp only [Complex.add_re, RCLike.star_def, Complex.conj_re] at hre
        exact hlam_re (by linarith)
    refine ⟨1, zero_le_one, fun M => ?_⟩
    have hH : lam * P.eval lam * (transf ψ lam) ^ (M + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hlam hP_lam) (pow_ne_zero _ hΨ)
    refine ⟨1, (lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹, by intro z; simp,
      ?_, ?_, ?_, ?_⟩
    · rw [Polynomial.eval_mul, Polynomial.eval_one, mul_one, inv_mul_cancel₀ hH]
    · rw [Polynomial.eval_mul, Polynomial.eval_one, mul_one, hstar, inv_mul_cancel₀ hH]
    · rw [norm_inv]
      have hnorm : ‖lam * P.eval lam * (transf ψ lam) ^ (M + 1)‖
          = ‖lam‖ * ‖P.eval lam‖ := by
        rw [norm_mul, norm_mul, norm_pow, hψ_norm, one_pow, mul_one]
      rw [hnorm]
      exact le_max_right _ _
    · intro z
      rw [Polynomial.eval_one]
      have h1z : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by
        nlinarith [norm_nonneg z]
      simpa using h1z
  · have hstarlam : star lam ≠ 0 := fun h => hlam (by
      have := congrArg star h
      simpa using this)
    set cl : ℝ := (‖lam‖ * ‖P.eval lam‖)⁻¹ with hcl_def
    set cs : ℝ := (‖star lam‖ * ‖P.eval (star lam)‖)⁻¹ with hcs_def
    have hcl : 0 ≤ cl := by rw [hcl_def]; positivity
    have hcs : 0 ≤ cs := by rw [hcs_def]; positivity
    have hden : 0 < ‖lam ^ 2 - star (lam ^ 2)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hreal)
    set bbar : ℝ := (cl + cs) / ‖lam ^ 2 - star (lam ^ 2)‖ with hbbar_def
    set abar : ℝ := cl + bbar * ‖lam‖ ^ 2 with habar_def
    have hbbar_nn : 0 ≤ bbar := by
      rw [hbbar_def]
      exact div_nonneg (add_nonneg hcl hcs) hden.le
    have habar_nn : 0 ≤ abar := by
      rw [habar_def]
      exact add_nonneg hcl (mul_nonneg hbbar_nn (sq_nonneg _))
    refine ⟨max 1 (abar + bbar), le_trans zero_le_one (le_max_left _ _), fun M => ?_⟩
    have hH : lam * P.eval lam * (transf ψ lam) ^ (M + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hlam hP_lam) (pow_ne_zero _ hΨ)
    have hH' : star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hstarlam hP_star) (pow_ne_zero _ hΨ')
    obtain ⟨a, b, h1, h2⟩ :=
      exists_even_quadratic_normalization hH hH' hreal
    have hnormA : ‖lam * P.eval lam * (transf ψ lam) ^ (M + 1)‖
        = ‖lam‖ * ‖P.eval lam‖ := by
      rw [norm_mul, norm_mul, norm_pow, hψ_norm, one_pow, mul_one]
    have hnormB : ‖star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1)‖
        = ‖star lam‖ * ‖P.eval (star lam)‖ := by
      rw [norm_mul, norm_mul, norm_pow, hψ_norm', one_pow, mul_one]
    have e1 : a + b * lam ^ 2
        = (lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have e2 : a + b * star (lam ^ 2)
        = (star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))⁻¹ :=
      eq_inv_of_mul_eq_one_left h2
    have hb_eq : b = ((lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹
        - (star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))⁻¹)
        / (lam ^ 2 - star (lam ^ 2)) := by
      have hsub : b * (lam ^ 2 - star (lam ^ 2))
          = (lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹
            - (star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))⁻¹ := by
        rw [mul_sub, ← e1, ← e2]
        ring
      rw [eq_div_iff (sub_ne_zero.mpr hreal)]
      exact hsub
    have ha_eq : a = (lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹ - b * lam ^ 2 := by
      linear_combination e1
    have hb_le : ‖b‖ ≤ bbar := by
      rw [hb_eq, hbbar_def, norm_div]
      have hnum : ‖(lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹
          - (star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))⁻¹‖
          ≤ cl + cs := by
        calc _ ≤ ‖(lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹‖
              + ‖(star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))⁻¹‖ :=
              norm_sub_le _ _
          _ = cl + cs := by rw [norm_inv, norm_inv, hnormA, hnormB, hcl_def, hcs_def]
      exact div_le_div_of_nonneg_right hnum hden.le
    have ha_le : ‖a‖ ≤ abar := by
      rw [ha_eq, habar_def]
      calc ‖(lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹ - b * lam ^ 2‖
          ≤ ‖(lam * P.eval lam * (transf ψ lam) ^ (M + 1))⁻¹‖ + ‖b * lam ^ 2‖ :=
            norm_sub_le _ _
        _ = cl + ‖b‖ * ‖lam‖ ^ 2 := by
            rw [norm_mul, norm_pow, norm_inv, hnormA, hcl_def]
        _ ≤ cl + bbar * ‖lam‖ ^ 2 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hb_le (sq_nonneg _))
    refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2, 1, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring
    · have hQeval : (P * (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2)).eval lam
          = P.eval lam * (a + b * lam ^ 2) := by
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
      rw [hQeval]
      have ht := h1
      rw [show lam * P.eval lam * (transf ψ lam) ^ (M + 1)
            = lam * (P.eval lam * (transf ψ lam) ^ (M + 1)) from by ring] at ht
      linear_combination ht
    · have hQeval : (P * (Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2)).eval (star lam)
          = P.eval (star lam) * (a + b * star (lam ^ 2)) := by
        simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        rw [star_pow]
      rw [hQeval]
      have ht := h2
      rw [show star lam * P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1)
            = star lam * (P.eval (star lam) * (transf ψ (star lam)) ^ (M + 1))
            from by ring] at ht
      linear_combination ht
    · simp
    · intro z
      have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
      have h1z : (1 : ℝ) ≤ (1 + ‖z‖) ^ 2 := by nlinarith
      have hz2 : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := by nlinarith
      have hmax1 : (1 : ℝ) ≤ max 1 (abar + bbar) := le_max_left _ _
      have hmax2 : abar + bbar ≤ max 1 (abar + bbar) := le_max_right _ _
      calc ‖(Polynomial.C a + Polynomial.C b * Polynomial.X ^ 2).eval z‖
          = ‖a + b * z ^ 2‖ := by simp
        _ ≤ ‖a‖ + ‖b * z ^ 2‖ := norm_add_le _ _
        _ = ‖a‖ + ‖b‖ * ‖z‖ ^ 2 := by rw [norm_mul, norm_pow]
        _ ≤ abar + bbar * ‖z‖ ^ 2 :=
            add_le_add ha_le (mul_le_mul_of_nonneg_right hb_le (sq_nonneg _))
        _ ≤ max 1 (abar + bbar) * (1 + ‖z‖) ^ 2 := by
            nlinarith [habar_nn, hbbar_nn, hmax1, hmax2, h1z, hz2,
              mul_le_mul_of_nonneg_left h1z habar_nn,
              mul_le_mul_of_nonneg_left hz2 hbbar_nn]
noncomputable def weilSummand (f : ℝ → ℂ)
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) : ℂ :=
  transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))
theorem weilOdd_eq_tsum_weilSummand (f : ℝ → ℂ) :
    weilOdd f = (∑' p, weilSummand f p).re := rfl
theorem summable_weilSummand {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    Summable (weilSummand f) := summable_weil_summand hf
theorem quartet_summand_eq_neg_one {f : ℝ → ℂ} {lam : ℂ}
    (hodd : ∀ z, transf f (-z) = -transf f z)
    (h1 : transf f lam = 1) (h2 : transf f (star lam) = 1) :
    ∀ c ∈ ({lam, -lam, star lam, -star lam} : Finset ℂ),
      transf f c * star (transf f (-(star c))) = -1 := by
  intro c hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · rw [h1, hodd, h2]
    simp
  · rw [show -(star (-lam)) = star lam by simp, hodd lam, h1, h2]
    simp
  · rw [show -(star (star lam)) = -lam by simp, h2, hodd lam, h1]
    simp
  · rw [show -(star (-(star lam))) = lam by simp]
    rw [hodd, h2, h1]
    simp
private lemma inv_sq_le (l r : ℝ) (hl : 0 ≤ l) (hr : 0 < r)
    (h : r ≤ (3 / 2) * (1 + l)) : ((1 + l)⁻¹) ^ 2 ≤ (9 / 4) * (r⁻¹) ^ 2 := by
  have h1 : 0 < 1 + l := by linarith
  have hinv : (1 + l)⁻¹ ≤ (3 / 2) * r⁻¹ := by
    rw [← div_eq_mul_inv]
    rw [le_div_iff₀ hr]
    rw [inv_mul_eq_div, div_le_iff₀ h1]
    linarith
  calc ((1 + l)⁻¹) ^ 2 ≤ ((3 / 2) * r⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinv 2
    _ = (9 / 4) * (r⁻¹) ^ 2 := by ring
private lemma pow_mul_inv_pow (a : ℝ) (ha : 0 < a) (d : ℕ) :
    a ^ d * (a⁻¹) ^ (d + 1) = a⁻¹ := by
  rw [inv_pow, pow_succ]
  rw [mul_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d ha.ne'), one_mul]
private lemma half_sq_pow (k : ℕ) : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4) ^ k := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
private lemma far_bound_algebra (cbar CPz Cψ a : ℝ) (d M : ℕ) (ha : 0 < a) :
    cbar * (CPz * a ^ d * ((Cψ * a⁻¹) ^ (d + 1) * (1 / 2) ^ (M - d)))
      = (cbar * CPz * Cψ ^ (d + 1) * (1 / 2) ^ (M - d)) * a⁻¹ := by
  rw [mul_pow]
  have hkey := pow_mul_inv_pow a ha d
  linear_combination (cbar * CPz * Cψ ^ (d + 1) * (1 / 2) ^ (M - d)) * hkey
private lemma poly_growth_algebra (a CP Cb : ℝ) (n : ℕ) :
    (1 + a) * (CP * (1 + a) ^ n * (Cb * (1 + a) ^ 2))
      = (CP * Cb) * (1 + a) ^ (n + 3) := by
  have hza : (1 + a) * (1 + a) ^ n * (1 + a) ^ 2 = (1 + a) ^ (n + 3) := by
    rw [mul_comm (1 + a) ((1 + a) ^ n), ← pow_succ, ← pow_add]
  rw [show (1 + a) * (CP * (1 + a) ^ n * (Cb * (1 + a) ^ 2))
      = CP * Cb * ((1 + a) * (1 + a) ^ n * (1 + a) ^ 2) by ring, hza]
theorem model_far_bound {ψ : ℝ → ℂ} {c : ℂ} {Q : Polynomial ℂ} {d : ℕ}
    {cbar CPz Cψ : ℝ} {T : ℝ} {M : ℕ}
    (hc : ‖c‖ ≤ cbar) (hQ : ∀ z, ‖z * Q.eval z‖ ≤ CPz * (1 + ‖z‖) ^ d)
    (hCψ : ∀ z, |z.re| ≤ 1 / 2 → ‖transf ψ z‖ * (1 + ‖z‖) ≤ Cψ)
    (hdec : ∀ z, |z.re| ≤ 1 / 2 → T ≤ |z.im| → ‖transf ψ z‖ ≤ 1 / 2)
    (hM : d ≤ M) (hcbar : 0 ≤ cbar) (hCPz : 0 ≤ CPz) (hCψ0 : 0 ≤ Cψ) :
    ∀ z : ℂ, |z.re| ≤ 1 / 2 → T ≤ |z.im| →
      ‖c * (z * Q.eval z * (transf ψ z) ^ (M + 1))‖
        ≤ (cbar * CPz * Cψ ^ (d + 1) * (1 / 2) ^ (M - d)) * (1 + ‖z‖)⁻¹ := by
  intro z hzre hzim
  have hpos : (0 : ℝ) < 1 + ‖z‖ := by positivity
  have hΨ1 : ‖transf ψ z‖ ≤ Cψ * (1 + ‖z‖)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hCψ z hzre
  have hΨ2 : ‖transf ψ z‖ ≤ 1 / 2 := hdec z hzre hzim
  have hpowsplit : ‖transf ψ z‖ ^ (M + 1)
      = ‖transf ψ z‖ ^ (d + 1) * ‖transf ψ z‖ ^ (M - d) := by
    rw [← pow_add, show d + 1 + (M - d) = M + 1 by omega]
  have hpow1 : ‖transf ψ z‖ ^ (d + 1) ≤ (Cψ * (1 + ‖z‖)⁻¹) ^ (d + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hΨ1 _
  have hpow2 : ‖transf ψ z‖ ^ (M - d) ≤ (1 / 2) ^ (M - d) :=
    pow_le_pow_left₀ (norm_nonneg _) hΨ2 _
  have hbase : 0 ≤ Cψ * (1 + ‖z‖)⁻¹ := mul_nonneg hCψ0 (inv_nonneg.mpr hpos.le)
  have hpow : ‖transf ψ z‖ ^ (M + 1)
      ≤ (Cψ * (1 + ‖z‖)⁻¹) ^ (d + 1) * (1 / 2) ^ (M - d) := by
    rw [hpowsplit]
    exact mul_le_mul hpow1 hpow2 (pow_nonneg (norm_nonneg _) _) (pow_nonneg hbase _)
  have h1z : (0 : ℝ) ≤ 1 + ‖z‖ := hpos.le
  calc ‖c * (z * Q.eval z * (transf ψ z) ^ (M + 1))‖
      = ‖c‖ * (‖z * Q.eval z‖ * ‖transf ψ z‖ ^ (M + 1)) := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ cbar * (CPz * (1 + ‖z‖) ^ d *
          ((Cψ * (1 + ‖z‖)⁻¹) ^ (d + 1) * (1 / 2) ^ (M - d))) := by
        exact mul_le_mul hc (mul_le_mul (hQ z) hpow (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg hCPz (pow_nonneg h1z d))) (by positivity) hcbar
    _ = (cbar * CPz * Cψ ^ (d + 1) * (1 / 2) ^ (M - d)) * (1 + ‖z‖)⁻¹ :=
        far_bound_algebra cbar CPz Cψ (1 + ‖z‖) d M hpos
private lemma exists_large_cutoff (X : ℝ) (hX : 0 ≤ X) (d : ℕ) :
    ∃ M : ℕ, d ≤ M ∧ X * (1 / 4) ^ (M - d) < 2 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (x := 2 / (X + 1)) (y := 1 / 4) (by positivity) (by norm_num)
  refine ⟨d + n, by omega, ?_⟩
  have hexp : d + n - d = n := by omega
  rw [hexp]
  calc X * (1 / 4) ^ n ≤ X * (2 / (X + 1)) := mul_le_mul_of_nonneg_left hn.le hX
    _ = X * 2 / (X + 1) := by ring
    _ < 2 := by
        rw [div_lt_iff₀ (by linarith : (0 : ℝ) < X + 1)]
        linarith
private lemma tsum_subtype_le' {β : Type*} (f : β → ℝ) (hf : Summable f)
    (hfnn : ∀ b, 0 ≤ f b) (s : Finset β) :
    ∑' (b : {b // b ∉ s}), f b ≤ ∑' b, f b := by
  have hsplit := hf.sum_add_tsum_subtype_compl s
  have hfin : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg (fun x _ => hfnn x)
  linarith
end WeilOddCore
open MeasureTheory
def localizedCore (a : ℝ) : Set (ℝ → ℂ) :=
  {f | IsOddTest f ∧ Function.support f ⊆ Set.Ioo (-a) a}
noncomputable def archForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in Set.Ioo (-a) a, (∫ y in Set.Ioo (-a) a,
    ‖f x - f y‖ ^ 2 / ‖x - y‖ ∂volume) ∂volume
noncomputable def endpointPotential (a x : ℝ) : ℝ :=
  -(1 / 2) * Real.log (a ^ 2 - x ^ 2)
noncomputable def potentialForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-a) a, endpointPotential a x * ‖f x‖ ^ 2 ∂volume
noncomputable def physicalConstant : ℝ :=
  -Real.log (2 * Real.pi) - Real.eulerMascheroniConstant
noncomputable def c0 (a : ℝ) : ℝ :=
  physicalConstant - Real.log a
noncomputable def gammaKernel (z : ℝ) : ℝ :=
  if z = 0 then 1 / 4
  else Real.exp (z / 2) / (2 * Real.sinh z) - 1 / (2 * z)
noncomputable def gammaForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-a) a, (∫ y in Set.Ioo (-a) a,
    gammaKernel ‖x - y‖ * (f x * star (f y)).re ∂volume) ∂volume
noncomputable def sph (y : ℝ) : ℂ :=
  (Real.sinh (y / 2) : ℂ)
noncomputable def polarInner (a : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ y in Set.Ioo (-a) a, star (sph y) * f y ∂volume
noncomputable def polarForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  2 * ‖polarInner a f‖ ^ 2
noncomputable def arithCoeff (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
noncomputable def arithSupport (a : ℝ) : Finset ℕ :=
  Finset.Icc 2 (Nat.ceil (Real.exp (2 * a)) - 1)
noncomputable def activePowers (a : ℝ) : Finset ℕ := by
  classical
  exact (arithSupport a).filter (fun n => IsPrimePow n)
noncomputable def shiftLength (n : ℕ) : ℝ := Real.log n
noncomputable def shiftLengthRescaled (a : ℝ) (n : ℕ) : ℝ := Real.log n / a
noncomputable def shiftForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑ n ∈ arithSupport a, arithCoeff n *
    (2 * (∫ x in Set.Ioo (-a) a, f x * star (f (x + shiftLength n)) ∂volume).re)
noncomputable def localizedForm (a : ℝ) (f : ℝ → ℂ) : ℝ :=
  archForm a f + physicalConstant * (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume)
    + potentialForm a f - gammaForm a f - polarForm a f - shiftForm a f
def WeilBridge : Prop :=
  ∀ a : ℝ, 0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → weilOdd f = localizedForm a f
noncomputable def LocalPSD (a : ℝ) : Prop :=
  0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → 0 ≤ localizedForm a f
theorem LocalPSD_iff (a : ℝ) :
    LocalPSD a ↔
      (0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → 0 ≤ localizedForm a f) :=
  Iff.rfl
noncomputable def LocalPSDSpectral (a : ℝ) : Prop :=
  0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → 0 ≤ weilOdd f
theorem LocalPSDSpectral_iff (a : ℝ) :
    LocalPSDSpectral a ↔
      (0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → 0 ≤ weilOdd f) :=
  Iff.rfl
theorem LocalPSD_iff_spectral_of_bridge (hbridge : WeilBridge) (a : ℝ) :
    LocalPSD a ↔ LocalPSDSpectral a := by
  constructor
  · intro h ha f hf
    rw [hbridge a ha f hf]
    exact h ha f hf
  · intro h ha f hf
    have h' := h ha f hf
    rwa [hbridge a ha f hf] at h'
theorem localizedForm_compression_of_bridge (hbridge : WeilBridge) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {f : ℝ → ℂ} (hf : f ∈ localizedCore a) :
    localizedForm b f = localizedForm a f := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hfb : f ∈ localizedCore b :=
    ⟨hf.1, fun x hx => ⟨by linarith [(hf.2 hx).1, hab],
      by linarith [(hf.2 hx).2, hab]⟩⟩
  rw [← hbridge b hb f hfb, hbridge a ha f hf]
theorem LocalPSD_mono_of_bridge (hbridge : WeilBridge) {a b : ℝ} (hab : a ≤ b)
    (hb : LocalPSD b) : LocalPSD a := by
  intro ha f hf
  rw [← localizedForm_compression_of_bridge hbridge ha hab hf]
  exact hb (lt_of_lt_of_le ha hab) f
    ⟨hf.1, fun x hx => ⟨by linarith [(hf.2 hx).1, hab],
      by linarith [(hf.2 hx).2, hab]⟩⟩
theorem LocalPSDSpectral_mono {a b : ℝ} (hab : a ≤ b) (hb : LocalPSDSpectral b) :
    LocalPSDSpectral a := by
  intro ha f hf
  exact hb (lt_of_lt_of_le ha hab) f
    ⟨hf.1, fun x hx => ⟨by linarith [(hf.2 hx).1, hab],
      by linarith [(hf.2 hx).2, hab]⟩⟩
noncomputable def rescaledPotential (x : ℝ) : ℝ :=
  -(1 / 2) * Real.log (1 - x ^ 2)
noncomputable def sRescaled (a x : ℝ) : ℂ :=
  (Real.sinh (a * x / 2) : ℂ)
noncomputable def gammaKernelRescaled (a z : ℝ) : ℝ :=
  a * gammaKernel (a * z)
noncomputable def archFormRescaled (g : ℝ → ℂ) : ℝ :=
  (1 / 4) * ∫ x in Set.Ioo (-1) 1, (∫ y in Set.Ioo (-1) 1,
    ‖g x - g y‖ ^ 2 / ‖x - y‖ ∂volume) ∂volume
noncomputable def potentialFormRescaled (g : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-1) 1, rescaledPotential x * ‖g x‖ ^ 2 ∂volume
noncomputable def gammaFormRescaled (a : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (-1) 1, (∫ y in Set.Ioo (-1) 1,
    gammaKernelRescaled a ‖x - y‖ * (g x * star (g y)).re ∂volume) ∂volume
noncomputable def polarInnerRescaled (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ x in Set.Ioo (-1) 1, star (sRescaled a x) * g x ∂volume
noncomputable def polarFormRescaled (a : ℝ) (g : ℝ → ℂ) : ℝ :=
  2 * a * ‖polarInnerRescaled a g‖ ^ 2
noncomputable def shiftFormRescaled (a : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∑ n ∈ arithSupport a, arithCoeff n *
    ((∫ x in Set.Ioo (-1) (1 - shiftLengthRescaled a n),
        g x * star (g (x + shiftLengthRescaled a n)) ∂volume)
      + (∫ x in Set.Ioo (-1 + shiftLengthRescaled a n) 1,
        g x * star (g (x - shiftLengthRescaled a n)) ∂volume)).re
noncomputable def localizedFormRescaled (a : ℝ) (g : ℝ → ℂ) : ℝ :=
  archFormRescaled g + c0 a * (∫ x in Set.Ioo (-1) 1, ‖g x‖ ^ 2 ∂volume)
    + potentialFormRescaled g - gammaFormRescaled a g
    - polarFormRescaled a g - shiftFormRescaled a g
noncomputable def LocalPSDRescaled (a : ℝ) : Prop :=
  0 < a → ∀ g : ℝ → ℂ, g ∈ localizedCore 1 → 0 ≤ localizedFormRescaled a g
theorem gammaKernel_zero : gammaKernel 0 = 1 / 4 := by
  simp [gammaKernel]
theorem physicalConstant_eq_c0_add_log (a : ℝ) :
    physicalConstant = c0 a + Real.log a := by
  simp [physicalConstant, c0]
theorem c0_eq (a : ℝ) :
    c0 a = -Real.log a - Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
  simp [c0, physicalConstant]
  ring
theorem endpointPotential_scale (a x : ℝ) (ha : 0 < a) (hx : x ^ 2 < 1) :
    endpointPotential a (a * x) = rescaledPotential x - Real.log a := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
  have h1x : 1 - x ^ 2 ≠ 0 := by nlinarith
  have harg : a ^ 2 - (a * x) ^ 2 = a ^ 2 * (1 - x ^ 2) := by ring
  rw [endpointPotential, rescaledPotential, harg, Real.log_mul ha2 h1x, Real.log_pow]
  ring
theorem sph_scale (a x : ℝ) : sph (a * x) = sRescaled a x :=
  rfl
theorem localizedCore_mono {a b : ℝ} (hab : a ≤ b) :
    localizedCore a ⊆ localizedCore b := by
  rintro f ⟨hf, hsupp⟩
  exact ⟨hf, fun x hx =>
    ⟨lt_of_le_of_lt (neg_le_neg hab) (hsupp hx).1, lt_of_lt_of_le (hsupp hx).2 hab⟩⟩
theorem localizedForm_zero (a : ℝ) : localizedForm a (0 : ℝ → ℂ) = 0 := by
  simp [localizedForm, archForm, potentialForm, gammaForm, polarForm, polarInner,
    shiftForm]
theorem localizedForm_congr (a : ℝ) {f g : ℝ → ℂ} (h : ∀ x, f x = g x) :
    localizedForm a f = localizedForm a g := by
  simp only [localizedForm, archForm, potentialForm, gammaForm, polarForm,
    polarInner, shiftForm]
  simp only [h]
theorem archForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    archForm a (fun x => c * f x) = ‖c‖ ^ 2 * archForm a f := by
  unfold archForm
  have hinner : ∀ x : ℝ,
      (∫ y in Set.Ioo (-a) a, ‖(c * f x) - (c * f y)‖ ^ 2 / ‖x - y‖ ∂volume)
        = ‖c‖ ^ 2 *
          ∫ y in Set.Ioo (-a) a, ‖f x - f y‖ ^ 2 / ‖x - y‖ ∂volume := by
    intro x
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [← mul_sub, norm_mul, mul_pow]
      ring
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul]
  ring
theorem potentialForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    potentialForm a (fun x => c * f x) = ‖c‖ ^ 2 * potentialForm a f := by
  unfold potentialForm
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [norm_mul, mul_pow]
    ring
theorem gammaForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    gammaForm a (fun x => c * f x) = ‖c‖ ^ 2 * gammaForm a f := by
  unfold gammaForm
  have hinner : ∀ x : ℝ,
      (∫ y in Set.Ioo (-a) a,
          gammaKernel ‖x - y‖ * ((c * f x) * star (c * f y)).re ∂volume)
        = ‖c‖ ^ 2 *
          ∫ y in Set.Ioo (-a) a, gammaKernel ‖x - y‖ * (f x * star (f y)).re ∂volume := by
    intro x
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      have h1 : (c * f x) * star (c * f y)
          = (c * star c) * (f x * star (f y)) := by
        rw [star_mul]
        ring
      have h2 : ((↑(‖c‖ ^ 2) : ℂ) * (f x * star (f y))).re
          = ‖c‖ ^ 2 * (f x * star (f y)).re :=
        RCLike.re_ofReal_mul (‖c‖ ^ 2) (f x * star (f y))
      rw [h1, show c * star c = (↑(Complex.normSq c) : ℂ) from Complex.mul_conj c,
        Complex.normSq_eq_norm_sq, h2]
      ring
  simp_rw [hinner]
  rw [MeasureTheory.integral_const_mul]
theorem polarInner_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    polarInner a (fun x => c * f x) = c * polarInner a f := by
  unfold polarInner
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    ring
theorem polarForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    polarForm a (fun x => c * f x) = ‖c‖ ^ 2 * polarForm a f := by
  unfold polarForm
  rw [polarInner_smul, norm_mul]
  ring
theorem shiftForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    shiftForm a (fun x => c * f x) = ‖c‖ ^ 2 * shiftForm a f := by
  unfold shiftForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  have hI :
      (∫ x in Set.Ioo (-a) a, (c * f x) * star (c * f (x + shiftLength n)) ∂volume).re
        = ‖c‖ ^ 2 *
          (∫ x in Set.Ioo (-a) a, f x * star (f (x + shiftLength n)) ∂volume).re := by
    have hpt : ∀ x : ℝ, (c * f x) * star (c * f (x + shiftLength n))
        = (↑(‖c‖ ^ 2) : ℂ) * (f x * star (f (x + shiftLength n))) := by
      intro x
      have h1 : (c * f x) * star (c * f (x + shiftLength n))
          = (c * star c) * (f x * star (f (x + shiftLength n))) := by
        rw [star_mul]
        ring
      rw [h1, show c * star c = (↑(Complex.normSq c) : ℂ) from Complex.mul_conj c,
        Complex.normSq_eq_norm_sq]
    rw [show (∫ x in Set.Ioo (-a) a,
            (c * f x) * star (c * f (x + shiftLength n)) ∂volume)
          = ∫ x in Set.Ioo (-a) a,
            (↑(‖c‖ ^ 2) : ℂ) * (f x * star (f (x + shiftLength n))) ∂volume from by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall hpt]
    rw [MeasureTheory.integral_const_mul]
    exact RCLike.re_ofReal_mul (K := ℂ) (‖c‖ ^ 2) _
  rw [hI]
  ring
theorem localizedForm_smul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    localizedForm a (fun x => c * f x) = ‖c‖ ^ 2 * localizedForm a f := by
  have hnorm : (∫ x in Set.Ioo (-a) a, ‖c * f x‖ ^ 2 ∂volume)
      = ‖c‖ ^ 2 * ∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [norm_mul, mul_pow]
  unfold localizedForm
  rw [archForm_smul a c f, potentialForm_smul a c f,
    gammaForm_smul a c f, polarForm_smul a c f, shiftForm_smul a c f, hnorm]
  ring
theorem localizedForm_neg (a : ℝ) (f : ℝ → ℂ) :
    localizedForm a (fun x => -f x) = localizedForm a f := by
  have h := localizedForm_smul a (-1 : ℂ) f
  simpa using h
theorem shiftIntegral_eq_zero_of_two_mul_lt {a r : ℝ} (hr : 2 * a < r)
    {f : ℝ → ℂ} (hsupp : Function.support f ⊆ Set.Ioo (-a) a) :
    (∫ x in Set.Ioo (-a) a, f x * star (f (x + r)) ∂volume) = 0 := by
  have hzero : ∀ x ∈ Set.Ioo (-a) a, f x * star (f (x + r)) = 0 := by
    intro x hx
    have hxr : x + r ∉ Set.Ioo (-a) a := by
      intro h
      have ha : a < x + r := by linarith [hx.1]
      linarith [h.2]
    have hnot : x + r ∉ Function.support f := fun hmem => hxr (hsupp hmem)
    have hz : f (x + r) = 0 := by
      by_contra h
      exact hnot (Function.mem_support.mpr h)
    simp [hz]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hzero]
  simp
theorem exp_two_endpoint_seven : Real.exp (2 * (Real.log 7 / 2)) = 7 := by
  rw [show 2 * (Real.log 7 / 2) = Real.log 7 by ring, Real.exp_log (by norm_num)]
theorem arithSupport_endpoint_seven :
    arithSupport (Real.log 7 / 2) = Finset.Icc 2 6 := by
  unfold arithSupport
  rw [exp_two_endpoint_seven]
  norm_num
theorem shiftForm_endpoint_seven_expand (f : ℝ → ℂ) :
    shiftForm (Real.log 7 / 2) f
      = ∑ n ∈ Finset.Icc 2 6, arithCoeff n *
          (2 * (∫ x in Set.Ioo (-(Real.log 7 / 2)) (Real.log 7 / 2),
            f x * star (f (x + shiftLength n)) ∂volume).re) := by
  rw [shiftForm, arithSupport_endpoint_seven]
noncomputable def endpoint (k : ℕ) : ℝ := Real.log k / 2
noncomputable def dyadicEndpoint (k : ℕ) : ℝ := Real.log (2 ^ k) / 2
theorem dyadicEndpoint_eq_endpoint_pow (k : ℕ) :
    dyadicEndpoint k = endpoint (2 ^ k) := by
  unfold dyadicEndpoint endpoint
  rw [Nat.cast_pow, Nat.cast_ofNat]
theorem endpoint_pos {k : ℕ} (hk : 1 < k) : 0 < endpoint k := by
  unfold endpoint
  exact div_pos (Real.log_pos (by exact_mod_cast hk)) (by norm_num)
theorem endpoint_seven_pos : 0 < endpoint 7 :=
  endpoint_pos (by norm_num)
def Y7OperatorTarget : Prop := LocalPSD (endpoint 7)
def GateIIOperatorStep : Prop :=
  ∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k) → LocalPSD (endpoint (k + 1))
theorem endpoints_psd_of_targets (hY7 : Y7OperatorTarget) (hII : GateIIOperatorStep) :
    ∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hY7
  | succ n hn ih => exact hII n hn ih
theorem LocalPSD_of_weil_nonneg_of_bridge (hbridge : WeilBridge)
    (h : ∀ f : ℝ → ℂ, 0 ≤ weilOdd f) : ∀ a : ℝ, LocalPSD a := by
  intro a ha f hf
  rw [← hbridge a ha f hf]
  exact h f
theorem gateIII_cofinal_of_bridge (hbridge : WeilBridge) :
    (∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k)) → ∀ a : ℝ, 0 < a → LocalPSD a := by
  intro h a ha
  intro _ f hf
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Real.exp (2 * a) ≤ N := exists_nat_ge (Real.exp (2 * a))
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos (2 * a)) hN
  have hlogN : 2 * a ≤ Real.log (N : ℝ) := by
    have hmono := Real.log_le_log (Real.exp_pos (2 * a)) hN
    rwa [Real.log_exp] at hmono
  let k : ℕ := max N 7
  have hk : N ≤ k := le_max_left N 7
  have h7le : 7 ≤ k := le_max_right N 7
  have hlogk : Real.log (N : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hk)
  have ha_le : a ≤ endpoint k := by
    unfold endpoint
    linarith
  have hep : 0 < endpoint k := by
    unfold endpoint
    have h1 : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 7) h7le)
    have hpos := Real.log_pos h1
    linarith
  have hsub : Function.support f ⊆ Set.Ioo (-(endpoint k)) (endpoint k) := by
    intro x hx
    have hxa := hf.2 hx
    exact ⟨by linarith [hxa.1, ha_le], by linarith [hxa.2, ha_le]⟩
  rw [← localizedForm_compression_of_bridge hbridge ha ha_le hf]
  exact (h k h7le) hep f ⟨hf.1, hsub⟩
theorem exists_pos_support_subset_Ioo {f : ℝ → ℂ} (hf : f ∈ oddCore) :
    ∃ a : ℝ, 0 < a ∧ Function.support f ⊆ Set.Ioo (-a) a := by
  have hf' : IsOddTest f := hf
  obtain ⟨r, hr⟩ := hf'.2.1.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨|r| + 1, by positivity, ?_⟩
  intro y hy
  have hy' : dist y 0 ≤ r := by
    simpa [Metric.mem_closedBall] using hr (subset_tsupport f hy)
  have hlt : |y| < |r| + 1 := by
    calc |y| = dist y 0 := by rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
      _ ≤ r := hy'
      _ ≤ |r| := le_abs_self _
      _ < |r| + 1 := lt_add_one _
  exact abs_lt.mp hlt
theorem gateIII_closure_of_bridge (hbridge : WeilBridge) :
    (∀ a : ℝ, 0 < a → LocalPSD a) → ∀ f, f ∈ oddCore → 0 ≤ weilOdd f := by
  intro h f hf
  obtain ⟨a, ha, hsupp⟩ := exists_pos_support_subset_Ioo hf
  have hloc : f ∈ localizedCore a := ⟨hf, hsupp⟩
  have hpos : 0 ≤ localizedForm a f := (h a ha) ha f hloc
  rw [hbridge a ha f hloc]
  exact hpos
lemma riemannXi_val_eq_zero_of_weil
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    Complex.riemannXi (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  have hdiv := Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support (p := p)
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int Complex.differentiable_riemannXi] at hdiv
  simpa using hdiv
lemma riemannZeta_eq_zero_of_riemannXi_eq_zero_of_weil {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hξ : Complex.riemannXi ρ = 0) :
    riemannZeta ρ = 0 := by
  have hΛ : completedRiemannZeta ρ = 0 := by
    have hprod : ρ * (ρ - 1) * completedRiemannZeta ρ / 2 = 0 := by
      rw [← Complex.riemannXi_eq_mul_completedRiemannZeta (s := ρ) hρ0 hρ1]
      exact hξ
    have h' : (ρ * (ρ - 1) / 2) * completedRiemannZeta ρ = 0 := by
      rw [← hprod]; ring
    have hne : ρ * (ρ - 1) / 2 ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
      · norm_num
    exact (mul_eq_zero.mp h').resolve_left hne
  rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]
lemma riemannXi_eq_zero_of_riemannZeta_eq_zero_of_weil {s : ℂ}
    (hζ : riemannZeta s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) :
    Complex.riemannXi s = 0 := by
  have hΛ : completedRiemannZeta s = 0 := by
    have h := hζ
    rw [riemannZeta_def_of_ne_zero (s := s) hs0] at h
    rcases div_eq_zero_iff.mp h with h0 | hG
    · exact h0
    · rcases (Complex.Gammaℝ_eq_zero_iff).mp hG with ⟨n, hn⟩
      cases n with
      | zero => exact (hs0 (by simpa using hn)).elim
      | succ k => exact (htriv ⟨k, by rw [hn]; push_cast; ring⟩).elim
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hΛ]
  ring
theorem riemannXi_zero_re_eq_half_of_all_of_weil (hRH : RiemannHypothesis) {s : ℂ}
    (hξ : Complex.riemannXi s = 0) : s.re = 1 / 2 := by
  have hstrip := riemannXi_zero_re_mem_Ioo hξ
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hξ
    rw [Complex.riemannXi_zero] at hξ
    norm_num at hξ
  have hs1 : s ≠ 1 := by
    intro h
    apply riemannXi_one_ne_zero
    rwa [h] at hξ
  have hζ : riemannZeta s = 0 :=
    riemannZeta_eq_zero_of_riemannXi_eq_zero_of_weil hs0 hs1 hξ
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      have hcast : -2 * ((n : ℂ) + 1) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.ofReal_re]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hstrip.1]
  exact hRH s hζ htriv hs1
theorem exists_offline_zero_of_not_RH_of_weil (h : ¬RiemannHypothesis) :
    ∃ s : ℂ, Complex.riemannXi s = 0 ∧ s.re ≠ 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  apply h
  intro s hζ htriv hs1
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, riemannZeta_zero] at hζ
    norm_num at hζ
  exact hcon s (riemannXi_eq_zero_of_riemannZeta_eq_zero_of_weil hζ hs0 hs1 htriv)
theorem riemannXi_zero_re_eq_half_of_RH (hRH : RiemannHypothesis)
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    (Complex.Hadamard.divisorZeroIndex₀_val p).re = 1 / 2 := by
  have hstrip := val_re_mem_Ioo p
  have hξ : Complex.riemannXi (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 :=
    riemannXi_val_eq_zero_of_weil p
  have hρ0 : Complex.Hadamard.divisorZeroIndex₀_val p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hρ1 : Complex.Hadamard.divisorZeroIndex₀_val p ≠ 1 := by
    intro h
    rw [h] at hstrip
    exact lt_irrefl _ hstrip.2
  have hζ : riemannZeta (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 :=
    riemannZeta_eq_zero_of_riemannXi_eq_zero_of_weil hρ0 hρ1 hξ
  have htriv : ¬∃ n : ℕ, Complex.Hadamard.divisorZeroIndex₀_val p = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hre : (Complex.Hadamard.divisorZeroIndex₀_val p).re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      have hcast : -2 * ((n : ℂ) + 1) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.ofReal_re]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hstrip.1]
  exact hRH _ hζ htriv hρ1
lemma centered_fixed_of_RH_of_weil (hRH : RiemannHypothesis)
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    -(star (centeredZero p)) = centeredZero p := by
  rw [RCLike.star_def]
  have hre := riemannXi_zero_re_eq_half_of_RH hRH p
  have hre0 : (centeredZero p).re = 0 := by
    rw [centeredZero, Complex.sub_re, hre]
    norm_num
  apply Complex.ext
  · rw [Complex.neg_re, Complex.conj_re, hre0]
    simp
  · rw [Complex.neg_im, Complex.conj_im]
    simp
lemma weilOdd_summand_eq_normSq_of_RH_of_weil (hRH : RiemannHypothesis) (f : ℝ → ℂ)
    (p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :
    transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))
      = ((Complex.normSq (transf f (centeredZero p)) : ℝ) : ℂ) := by
  rw [centered_fixed_of_RH_of_weil hRH p, RCLike.star_def, RCLike.mul_conj,
    Complex.normSq_eq_norm_sq]
  simp
lemma re_tsum_ofReal_nonneg_of_weil {α : Type*} (g : α → ℝ) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ (∑' i, ((g i : ℝ) : ℂ)).re := by
  by_cases h : Summable fun i => ((g i : ℝ) : ℂ)
  · rw [Complex.re_tsum h]
    simpa using tsum_nonneg hg
  · rw [tsum_eq_zero_of_not_summable h]
    simp
theorem weilOdd_nonneg_of_RH (hRH : RiemannHypothesis) (f : ℝ → ℂ) :
    0 ≤ weilOdd f := by
  rw [weilOdd]
  rw [tsum_congr (fun p => weilOdd_summand_eq_normSq_of_RH_of_weil hRH f p)]
  exact re_tsum_ofReal_nonneg_of_weil
    (fun p => Complex.normSq (transf f (centeredZero p)))
    (fun p => by
      rw [Complex.normSq_eq_norm_sq]
      exact sq_nonneg _)
private lemma norm_tsum_tail_le {β : Type*} (f : β → ℂ) (g : β → ℝ) (s : Finset β)
    (hf : Summable f) (hfg : ∀ b ∉ s, ‖f b‖ ≤ g b) (hg : Summable g)
    (hs : ∑' (b : {b // b ∉ s}), g b < 2) :
    ‖∑' (b : {b // b ∉ s}), f b‖ < 2 := by
  have hfsub : Summable (fun b : {b // b ∉ s} => f b) := hf.subtype (fun b => b ∉ s)
  have hgsub : Summable (fun b : {b // b ∉ s} => g b) := hg.subtype (fun b => b ∉ s)
  calc ‖∑' (b : {b // b ∉ s}), f b‖
      ≤ ∑' (b : {b // b ∉ s}), ‖f b‖ := norm_tsum_le_tsum_norm hfsub.norm
    _ ≤ ∑' (b : {b // b ∉ s}), g b :=
        Summable.tsum_le_tsum (fun b => hfg b b.2) hfsub.norm hgsub
    _ < 2 := hs
set_option maxHeartbeats 800000 in
theorem exists_negative_weil_test (hRH : ¬ RiemannHypothesis) :
    ∃ f, f ∈ oddCore ∧ weilOdd f < 0 := by
  classical
  obtain ⟨ρ, hξρ, hre⟩ := exists_offline_zero_of_not_RH_of_weil hRH
  set lam : ℂ := ρ - 1 / 2 with hlam_def
  have hlam_re : lam.re ≠ 0 := by
    have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [hlam_def, Complex.sub_re, h12]
    intro h
    exact hre (by linarith)
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hξρ
    rw [Complex.riemannXi_zero] at hξρ
    norm_num at hξρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    apply riemannXi_one_ne_zero
    rwa [h] at hξρ
  obtain ⟨ψ, hψ_real, hψ_even, hψ_s, hψ_c, hψ_norm, T, hT, hψ_decay⟩ :=
    exists_orbit_test lam
  have hψ_norm' : ‖transf ψ (star lam)‖ = 1 := by
    rw [transf_conj hψ_real, norm_star, hψ_norm]
  have hfin := finite_indexSet_im_le T
  set quartet : Finset ℂ := {lam, -lam, star lam, -star lam} with hquartet_def
  set S : Finset ℂ := (hfin.toFinset.image centeredZero).filter (fun z => z ∉ quartet)
    with hS_def
  have hS : ∀ z ∈ S, z ≠ lam ∧ z ≠ -lam ∧ z ≠ star lam ∧ z ≠ -star lam := by
    intro z hz
    rw [hS_def] at hz
    have hz' : ¬ (z = lam ∨ z = -lam ∨ z = star lam ∨ z = -star lam) := by
      have h2 := (Finset.mem_filter.mp hz).2
      simpa only [hquartet_def, Finset.mem_insert, Finset.mem_singleton] using h2
    tauto
  obtain ⟨P, hP_even, hP_kill, hP_lam, hP_star⟩ :=
    exists_even_polynomial_killing S lam hS
  obtain ⟨Cb, hCb_nn, hnorm⟩ :=
    exists_normalization_uniform hψ_norm hψ_norm' hlam_re P hP_lam hP_star
  obtain ⟨CP, hCP_nn, hCP⟩ := exists_polynomial_eval_bound P
  obtain ⟨Cψ, hCψ_nn, hCψ⟩ := exists_transf_norm_mul_le hψ_s hψ_c
  set cbar : ℝ := max 1 ((‖lam‖ * ‖P.eval lam‖)⁻¹) with hcbar_def
  have hcbar_nn : 0 ≤ cbar := le_trans zero_le_one (le_max_left _ _)
  set d : ℕ := P.natDegree + 3 with hd_def
  set B0 : ℝ := cbar * (CP * Cb) * Cψ ^ (d + 1) with hB0_def
  have hB0_nn : 0 ≤ B0 := by
    rw [hB0_def]
    exact mul_nonneg (mul_nonneg hcbar_nn (mul_nonneg hCP_nn hCb_nn))
      (pow_nonneg hCψ_nn _)
  set Smaj : ℝ := ∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
      (Set.univ : Set ℂ), (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2 with hSmaj_def
  have hSmaj_nn : 0 ≤ Smaj := by
    rw [hSmaj_def]
    exact tsum_nonneg (fun p => sq_nonneg _)
  have hSmaj_summable : Summable (fun p : Complex.Hadamard.divisorZeroIndex₀
      Complex.riemannXi (Set.univ : Set ℂ) =>
      (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ (2 : ℕ)) :=
    summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
  have hXn : 0 ≤ B0 ^ 2 * (9 / 4) * Smaj := by positivity
  obtain ⟨M, hMd, hMbound⟩ := exists_large_cutoff (B0 ^ 2 * (9 / 4) * Smaj) hXn d
  obtain ⟨R, c, hR_even, hc1, hc2, hc_bound, hR_bound⟩ := hnorm M
  have hQR_even : ∀ z, (P * R).eval (-z) = (P * R).eval z := by
    intro z
    rw [Polynomial.eval_mul, Polynomial.eval_mul, hP_even z, hR_even z]
  obtain ⟨f, hf_core, hf_t, hf_lam, hf_star, hf_odd⟩ :=
    exists_model_test ψ hψ_s hψ_c hψ_even (P * R) hQR_even M lam c hc1 hc2
  set K : Finset (Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ)) :=
    quartet.biUnion (fun q => Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      Complex.riemannXi (q + 1 / 2)) with hK_def
  have hmemK_of_quartet : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
      (Set.univ : Set ℂ), centeredZero p ∈ quartet → p ∈ K := by
    intro p hp
    rw [hK_def]
    refine Finset.mem_biUnion.mpr ⟨centeredZero p, hp, ?_⟩
    simp only [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    rw [centeredZero]
    ring
  have hK_centered : ∀ p ∈ K, centeredZero p ∈ quartet := by
    intro p hp
    rw [hK_def, Finset.mem_biUnion] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have hv : Complex.Hadamard.divisorZeroIndex₀_val p = q + 1 / 2 := by
      simpa only [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] using hpq
    have hc : centeredZero p = q := by
      rw [centeredZero, hv]
      ring
    rw [hc]
    exact hq
  have hkill : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      |(centeredZero p).im| ≤ T → centeredZero p ∉ quartet → P.eval (centeredZero p) = 0 := by
    intro p hstrip hnot
    apply hP_kill
    rw [hS_def]
    refine Finset.mem_filter.mpr ⟨?_, hnot⟩
    exact Finset.mem_image.mpr ⟨p, (hfin.mem_toFinset).mpr hstrip, rfl⟩
  have hQt : ∀ w : ℂ, ‖w * (P * R).eval w‖ ≤ (CP * Cb) * (1 + ‖w‖) ^ d := by
    intro w
    have hzw : ‖w‖ ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
    calc ‖w * (P * R).eval w‖
        = ‖w‖ * (‖P.eval w‖ * ‖R.eval w‖) := by
          rw [norm_mul, Polynomial.eval_mul, norm_mul]
      _ ≤ (1 + ‖w‖) * (CP * (1 + ‖w‖) ^ P.natDegree * (Cb * (1 + ‖w‖) ^ 2)) := by
          refine mul_le_mul hzw (mul_le_mul (hCP w) (hR_bound w) (norm_nonneg _)
            (mul_nonneg hCP_nn (pow_nonneg (by positivity) _)))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (CP * Cb) * (1 + ‖w‖) ^ d := by
          rw [show d = P.natDegree + 3 from hd_def]
          exact poly_growth_algebra ‖w‖ CP Cb P.natDegree
  have hFfar : ∀ z : ℂ, |z.re| ≤ 1 / 2 → T ≤ |z.im| →
      ‖transf f z‖ ≤ (B0 * (1 / 2) ^ (M - d)) * (1 + ‖z‖)⁻¹ := by
    intro z hzre hzim
    rw [hf_t z]
    have hbound := model_far_bound (ψ := ψ) (c := c) (Q := P * R) (d := d)
      (cbar := cbar) (CPz := CP * Cb) (Cψ := Cψ) (T := T) (M := M)
      hc_bound hQt hCψ hψ_decay hMd hcbar_nn (mul_nonneg hCP_nn hCb_nn) hCψ_nn
      z hzre hzim
    rwa [hB0_def]
  have hpoint : ∀ p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ),
      p ∉ K → ‖weilSummand f p‖
        ≤ (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
            (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2 := by
    intro p hp
    rw [weilSummand]
    have hstrip : |(centeredZero p).re| ≤ 1 / 2 := by
      have hρ := val_re_mem_Ioo p
      have hre' : (centeredZero p).re = (Complex.Hadamard.divisorZeroIndex₀_val p).re - 1 / 2 := by
        rw [centeredZero, Complex.sub_re]
        norm_num
      rw [hre', abs_le]
      exact ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
    by_cases hfar : T ≤ |(centeredZero p).im|
    · have hstrip' : |(star (centeredZero p)).re| ≤ 1 / 2 := by
        have hre' : (star (centeredZero p)).re = (centeredZero p).re := by simp
        rw [hre']
        exact hstrip
      have hfar' : T ≤ |(star (centeredZero p)).im| := by
        have him' : (star (centeredZero p)).im = -((centeredZero p).im) := by simp
        rw [him', abs_neg]
        exact hfar
      have h1b := hFfar (centeredZero p) hstrip hfar
      have h2b := hFfar (star (centeredZero p)) hstrip' hfar'
      calc ‖transf f (centeredZero p) * star (transf f (-(star (centeredZero p))))‖
          = ‖transf f (centeredZero p)‖ * ‖transf f (star (centeredZero p))‖ := by
            rw [norm_mul, norm_star, hf_odd (star (centeredZero p)), norm_neg]
        _ ≤ ((B0 * (1 / 2) ^ (M - d)) * (1 + ‖centeredZero p‖)⁻¹) *
            ((B0 * (1 / 2) ^ (M - d)) * (1 + ‖star (centeredZero p)‖)⁻¹) :=
            mul_le_mul h1b h2b (by positivity) (by positivity)
        _ ≤ (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
              (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2 := by
            rw [norm_star]
            have hl : 0 ≤ ‖centeredZero p‖ := norm_nonneg _
            have hr : 0 < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ :=
              norm_pos_iff.mpr (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
            have hρle : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤
                (3 / 2) * (1 + ‖centeredZero p‖) := by
              have htri : ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤
                  ‖centeredZero p‖ + ‖(1 / 2 : ℂ)‖ := by
                have hsum : Complex.Hadamard.divisorZeroIndex₀_val p = centeredZero p + 1 / 2 := by
                  rw [centeredZero]
                  ring
                rw [hsum]
                exact norm_add_le _ _
              have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
              rw [hhalf] at htri
              nlinarith [norm_nonneg (centeredZero p)]
            have hkey := inv_sq_le ‖centeredZero p‖
              ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ hl hr hρle
            have hsq : ((1 / 2 : ℝ) ^ (M - d)) ^ 2 = (1 / 4) ^ (M - d) :=
              half_sq_pow (M - d)
            have hL : (B0 * (1 / 2) ^ (M - d) * (1 + ‖centeredZero p‖)⁻¹) *
                (B0 * (1 / 2) ^ (M - d) * (1 + ‖centeredZero p‖)⁻¹)
                = (B0 ^ 2 * ((1 / 2 : ℝ) ^ (M - d)) ^ 2) *
                  ((1 + ‖centeredZero p‖)⁻¹) ^ 2 := by ring
            rw [hL, hsq]
            calc B0 ^ 2 * (1 / 4) ^ (M - d) * (1 + ‖centeredZero p‖)⁻¹ ^ 2
                ≤ B0 ^ 2 * (1 / 4) ^ (M - d) *
                    (9 / 4 * (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2) :=
                  mul_le_mul_of_nonneg_left hkey
                    (mul_nonneg (sq_nonneg B0)
                      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _))
              _ = B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4) *
                    (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2 := by ring
    · push_neg at hfar
      have hnotq : centeredZero p ∉ quartet := fun hcon => hp (hmemK_of_quartet p hcon)
      have hP0 : P.eval (centeredZero p) = 0 := hkill p hfar.le hnotq
      have hQ0 : (P * R).eval (centeredZero p) = 0 := by
        rw [Polynomial.eval_mul, hP0, zero_mul]
      have hF0 : transf f (centeredZero p) = 0 := by
        rw [hf_t, hQ0]
        ring
      have hBnn : 0 ≤ B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4) := by positivity
      rw [hF0, zero_mul, norm_zero]
      exact mul_nonneg hBnn (sq_nonneg _)
  have hsmall : (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) * Smaj < 2 := by
    have heq : (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) * Smaj
        = B0 ^ 2 * (9 / 4) * Smaj * (1 / 4) ^ (M - d) := by ring
    rw [heq]
    exact hMbound
  have hcnn : 0 ≤ B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4) := by positivity
  have htail : ‖∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
      (Set.univ : Set ℂ) // p ∉ K}), weilSummand f p‖ < 2 := by
    have hsmall' : ∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) // p ∉ K}),
        (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
          (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹) ^ 2 < 2 := by
      have hsub : ∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
          (Set.univ : Set ℂ) // p ∉ K}),
          (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹) ^ 2 ≤ Smaj := by
        rw [hSmaj_def]
        exact tsum_subtype_le' _ summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
          (fun p => sq_nonneg _) K
      calc ∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
            (Set.univ : Set ℂ) // p ∉ K}),
            (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
              (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹) ^ 2
          = (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
            (∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
              (Set.univ : Set ℂ) // p ∉ K}),
              (‖Complex.Hadamard.divisorZeroIndex₀_val p.1‖⁻¹) ^ 2) := tsum_mul_left
        _ ≤ (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) * Smaj :=
            mul_le_mul_of_nonneg_left hsub hcnn
        _ < 2 := hsmall
    exact norm_tsum_tail_le (weilSummand f)
      (fun p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi (Set.univ : Set ℂ) =>
        (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4)) *
          (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹) ^ 2)
      K (summable_weilSummand hf_core) (fun p hp => hpoint p hp)
      (hSmaj_summable.mul_left (B0 ^ 2 * (1 / 4) ^ (M - d) * (9 / 4))) hsmall'
  have hK_value : ∑ p ∈ K, weilSummand f p = -(K.card : ℂ) := by
    have h : ∀ p ∈ K, weilSummand f p = (-1 : ℂ) := by
      intro p hp
      rw [weilSummand]
      exact quartet_summand_eq_neg_one hf_odd hf_lam hf_star (centeredZero p)
        (hK_centered p hp)
    rw [Finset.sum_congr rfl h]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hK_card : 2 ≤ K.card := by
    obtain ⟨p1, hp1⟩ := exists_index_of_riemannXi_eq_zero hρ0 hξρ
    have hρ2 : Complex.riemannXi (1 - ρ) = 0 := by
      rw [Complex.riemannXi_one_sub, hξρ]
    have h1ρ0 : (1 : ℂ) - ρ ≠ 0 := by
      intro h
      apply hρ1
      linear_combination -h
    obtain ⟨p2, hp2⟩ := exists_index_of_riemannXi_eq_zero h1ρ0 hρ2
    have hp1K : p1 ∈ K := by
      refine hmemK_of_quartet p1 ?_
      have hc : centeredZero p1 = lam := by
        rw [centeredZero, hp1, hlam_def]
      rw [hc]
      rw [hquartet_def]
      simp
    have hp2K : p2 ∈ K := by
      refine hmemK_of_quartet p2 ?_
      have hc : centeredZero p2 = -lam := by
        rw [centeredZero, hp2, hlam_def]
        ring
      rw [hc]
      rw [hquartet_def]
      simp
    have hne12 : p1 ≠ p2 := by
      intro h
      have hval : Complex.Hadamard.divisorZeroIndex₀_val p1 =
          Complex.Hadamard.divisorZeroIndex₀_val p2 := by rw [h]
      rw [hp1, hp2] at hval
      have hv : ρ = 1 - ρ := hval
      have hre12 : ρ.re = 1 / 2 := by
        have := congrArg Complex.re hv
        simp only [Complex.sub_re, Complex.one_re] at this
        linarith
      exact hre hre12
    have hsub : ({p1, p2} : Finset (Complex.Hadamard.divisorZeroIndex₀
        Complex.riemannXi (Set.univ : Set ℂ))).card ≤ K.card :=
      Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hp1K
        · exact hp2K)
    rwa [Finset.card_pair hne12] at hsub
  have htotal : weilOdd f < 0 := by
    rw [weilOdd_eq_tsum_weilSummand]
    have hsplit := (summable_weilSummand hf_core).sum_add_tsum_subtype_compl K
    have hre : (∑' p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
          (Set.univ : Set ℂ), weilSummand f p).re
        = (-(K.card : ℂ)).re + (∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀
            Complex.riemannXi (Set.univ : Set ℂ) // p ∉ K}), weilSummand f p).re := by
      rw [← hsplit, hK_value, Complex.add_re]
    rw [hre, Complex.neg_re, Complex.natCast_re]
    have h2 : (∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) // p ∉ K}), weilSummand f p).re
        ≤ ‖∑' (p : {p : Complex.Hadamard.divisorZeroIndex₀ Complex.riemannXi
        (Set.univ : Set ℂ) // p ∉ K}), weilSummand f p‖ :=
      Complex.re_le_norm _
    have hK2 : (2 : ℝ) ≤ (K.card : ℝ) := by exact_mod_cast hK_card
    linarith [h2, htail, hK2]
  exact ⟨f, hf_core, htotal⟩
theorem weil_odd_criterion_converse :
    (∀ f, f ∈ oddCore → 0 ≤ weilOdd f) → RiemannHypothesis := by
  intro hpos
  by_contra hRH
  obtain ⟨f, hf_core, hf_neg⟩ := exists_negative_weil_test hRH
  exact absurd (hpos f hf_core) (not_le.mpr hf_neg)
theorem weil_odd_criterion :
    (∀ f, f ∈ oddCore → 0 ≤ weilOdd f) ↔ RiemannHypothesis :=
  ⟨weil_odd_criterion_converse, fun hRH f _ => weilOdd_nonneg_of_RH hRH f⟩
theorem weil_criterion :
    ((∀ f : ℝ → ℂ, f ∈ weilCore → 0 ≤ weilOdd f) ↔ RiemannHypothesis) := by
  constructor
  · intro h
    exact weil_odd_criterion_converse fun f hf => h f ⟨hf.1, hf.2.1⟩
  · intro hRH f _
    exact weilOdd_nonneg_of_RH hRH f
theorem weil_criterion_all :
    ((∀ f : ℝ → ℂ, 0 ≤ weilOdd f) ↔ RiemannHypothesis) := by
  constructor
  · intro h
    exact weil_odd_criterion_converse fun f _ => h f
  · intro hRH f
    exact weilOdd_nonneg_of_RH hRH f
theorem rh_full_proof (hbridge : WeilBridge) (hY7 : Y7OperatorTarget)
    (hII : GateIIOperatorStep) : RiemannHypothesis :=
  weil_odd_criterion_converse
    (gateIII_closure_of_bridge hbridge
      (gateIII_cofinal_of_bridge hbridge (endpoints_psd_of_targets hY7 hII)))
theorem operator_targets_iff_RH_of_bridge (hbridge : WeilBridge) :
    (Y7OperatorTarget ∧ GateIIOperatorStep) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨hY7, hII⟩
    exact rh_full_proof hbridge hY7 hII
  · intro hRH
    have hwei : ∀ f : ℝ → ℂ, 0 ≤ weilOdd f :=
      fun f => weilOdd_nonneg_of_RH hRH f
    have hpsd : ∀ a : ℝ, LocalPSD a :=
      LocalPSD_of_weil_nonneg_of_bridge hbridge hwei
    exact ⟨hpsd (endpoint 7), fun k _ _ => hpsd (endpoint (k + 1))⟩
theorem base_certificate_of_bridge_y7
    (_hbridge : ∀ a : ℝ, 0 < a → ∀ f : ℝ → ℂ,
      f ∈ localizedCore a → weilOdd f = localizedForm a f)
    (hY7 : ∀ f : ℝ → ℂ,
      f ∈ localizedCore (endpoint 7) → 0 ≤ localizedForm (endpoint 7) f) :
    LocalPSD (endpoint 7) := by
  intro _ha f hf
  exact hY7 f hf
theorem gateII_step_of_bridge_localized
    (_hbridge : ∀ a : ℝ, 0 < a → ∀ f : ℝ → ℂ,
      f ∈ localizedCore a → weilOdd f = localizedForm a f)
    (hII : ∀ k : ℕ, 7 ≤ k →
      (0 < endpoint k → ∀ f : ℝ → ℂ,
        f ∈ localizedCore (endpoint k) → 0 ≤ localizedForm (endpoint k) f) →
      (0 < endpoint (k + 1) → ∀ f : ℝ → ℂ,
        f ∈ localizedCore (endpoint (k + 1)) → 0 ≤ localizedForm (endpoint (k + 1)) f)) :
    ∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k) → LocalPSD (endpoint (k + 1)) :=
  hII
theorem rh_of_workstream_targets
    (hbridge : ∀ a : ℝ, 0 < a → ∀ f : ℝ → ℂ,
      f ∈ localizedCore a → weilOdd f = localizedForm a f)
    (hY7 : ∀ f : ℝ → ℂ,
      f ∈ localizedCore (endpoint 7) → 0 ≤ localizedForm (endpoint 7) f)
    (hII : ∀ k : ℕ, 7 ≤ k →
      (0 < endpoint k → ∀ f : ℝ → ℂ,
        f ∈ localizedCore (endpoint k) → 0 ≤ localizedForm (endpoint k) f) →
      (0 < endpoint (k + 1) → ∀ f : ℝ → ℂ,
        f ∈ localizedCore (endpoint (k + 1)) → 0 ≤ localizedForm (endpoint (k + 1)) f)) :
    RiemannHypothesis := by
  have hbase := base_certificate_of_bridge_y7 hbridge hY7
  have hstep := gateII_step_of_bridge_localized hbridge hII
  have hends : ∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k) :=
    endpoints_psd_of_targets hbase hstep
  exact weil_odd_criterion_converse
    (gateIII_closure_of_bridge hbridge (gateIII_cofinal_of_bridge hbridge hends))
theorem young_penalty {a c x : ℝ} (ha : 0 < a) :
    -(c ^ 2 / a) ≤ a * x ^ 2 - 2 * c * x := by
  have h : 0 ≤ (a * x - c) ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
  have h' : (a * x - c) ^ 2 / a = a * x ^ 2 - 2 * c * x + c ^ 2 / a := by
    field_simp
    ring
  linarith [h, h']
theorem schur_criterion {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hA : A.PosDef) [Invertible A] (hS : (D - Bᴴ * A⁻¹ * B).PosSemidef) :
    (fromBlocks A B Bᴴ D).PosSemidef :=
  (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS
example : (439 : ℚ) / 250 = 1 + 189 / 250 := by norm_num
example : ((5 : ℚ) / 3) * (44041 / 100000) < 189 / 250 := by norm_num
theorem mixed_debit_bound
    {Pi0 A χ ρ c θ Γ : ℝ}
    (hPi0 : 0 < Pi0) (hA : A = (1 - θ ^ 2) * Pi0) (hθ : θ ^ 2 < 1)
    (hχ : 0 ≤ χ) (hρ0 : 0 ≤ ρ) (hΓ : Γ ^ 2 ≤ ρ * χ)
    (hrho : ρ ≤ c * (1 - θ ^ 2) * Pi0) (hc : 0 ≤ c)
    (hc5 : (5 / 3) * c ≤ 189 / 250) :
    (θ * Γ) ^ 2 / ((3 / 5) * A) ≤ (189 / 250) * χ := by
  have h1 : 0 < (1 : ℝ) - θ ^ 2 := by nlinarith
  have hApos : 0 < A := by rw [hA]; exact mul_pos h1 hPi0
  have h3A : 0 < (3 / 5 : ℝ) * A := by positivity
  rw [div_le_iff₀ h3A]
  have hθ2 : θ ^ 2 ≤ 1 := by nlinarith
  have hθ2' : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
  have hc' : c ≤ (189 / 250) * (3 / 5) := by nlinarith
  calc (θ * Γ) ^ 2 = θ ^ 2 * Γ ^ 2 := by ring
    _ ≤ θ ^ 2 * (ρ * χ) := by
          exact mul_le_mul_of_nonneg_left hΓ hθ2'
    _ = ρ * (θ ^ 2 * χ) := by ring
    _ ≤ (c * (1 - θ ^ 2) * Pi0) * (θ ^ 2 * χ) := by
          exact mul_le_mul_of_nonneg_right hrho (mul_nonneg hθ2' hχ)
    _ = c * θ ^ 2 * A * χ := by rw [hA]; ring
    _ ≤ c * A * χ := by
          have hcAχ : 0 ≤ c * A * χ := mul_nonneg (mul_nonneg hc hApos.le) hχ
          nlinarith [mul_le_mul_of_nonneg_right hθ2 hcAχ]
    _ ≤ (189 / 250) * χ * ((3 / 5) * A) := by
          have hAχ : 0 ≤ A * χ := mul_nonneg hApos.le hχ
          have := mul_le_mul_of_nonneg_right hc' hAχ
          nlinarith [this]
theorem W_identity
    {Pi0 A θ b : ℝ} (hPi0 : 0 < Pi0) (hA : A = (1 - θ ^ 2) * Pi0)
    (hθ : θ ^ 2 < 1) :
    ((1 - θ) * b) ^ 2 / ((2 / 5) * A)
      = (5 / 2) * (((1 - θ) / (1 + θ)) * b ^ 2 / Pi0) := by
  have h1 : 0 < (1 : ℝ) - θ ^ 2 := by nlinarith
  have hApos : 0 < A := by rw [hA]; exact mul_pos h1 hPi0
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hPi0ne : Pi0 ≠ 0 := ne_of_gt hPi0
  have hA' : A = (1 - θ) * (1 + θ) * Pi0 := by rw [hA]; ring
  rw [hA']
  field_simp
theorem aligned_penalty_core
    {Pi0 A χ ρ c θ b y Γ : ℝ}
    (hPi0 : 0 < Pi0) (hA : A = (1 - θ ^ 2) * Pi0) (hθ : θ ^ 2 < 1)
    (hχ : 0 ≤ χ) (hρ0 : 0 ≤ ρ) (hΓ : Γ ^ 2 ≤ ρ * χ)
    (hrho : ρ ≤ c * (1 - θ ^ 2) * Pi0) (hc : 0 ≤ c)
    (hc5 : (5 / 3) * c ≤ 189 / 250) :
    -((189 / 250) * χ) - (5 / 2) * (((1 - θ) / (1 + θ)) * b ^ 2 / Pi0)
      ≤ A * y ^ 2 - 2 * θ * Γ * y - 2 * (1 - θ) * b * y := by
  have hApos : 0 < A := by
    have h1 : 0 < (1 : ℝ) - θ ^ 2 := by nlinarith
    rw [hA]; exact mul_pos h1 hPi0
  have h3A : 0 < (3 / 5 : ℝ) * A := by positivity
  have h2A : 0 < (2 / 5 : ℝ) * A := by positivity
  have y1 := young_penalty (a := (3 / 5) * A) (c := θ * Γ) (x := y) h3A
  have y2 := young_penalty (a := (2 / 5) * A) (c := (1 - θ) * b) (x := y) h2A
  have b1 := mixed_debit_bound (Pi0 := Pi0) (A := A) (χ := χ) (ρ := ρ) (c := c) (θ := θ) (Γ := Γ) hPi0 hA hθ hχ hρ0 hΓ hrho hc hc5
  have b2 := W_identity (Pi0 := Pi0) (A := A) (θ := θ) (b := b) hPi0 hA hθ
  have y1' : -((189 / 250) * χ) ≤ (3 / 5) * A * y ^ 2 - 2 * θ * Γ * y := by
    linarith
  have y2' : -((5 / 2) * (((1 - θ) / (1 + θ)) * b ^ 2 / Pi0))
      ≤ (2 / 5) * A * y ^ 2 - 2 * (1 - θ) * b * y := by
    rw [b2] at y2
    linarith
  nlinarith [y1', y2']
theorem cstar_lt :
    (3 + 2 * Real.sqrt 2) / (16 * (Real.log 2 + 1 / 2) * Real.log 2)
      < (441 : ℝ) / 1000 := by
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hs : Real.sqrt 2 < (1.4143 : ℝ) := by
    have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2]
  have hs1 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hden : 0 < 16 * (Real.log 2 + 1 / 2) * Real.log 2 := by positivity
  rw [div_lt_iff₀ hden]
  nlinarith [hgt, hlt, hs, hs1]
theorem cstar_five_thirds :
    (5 / 3) *
        ((3 + 2 * Real.sqrt 2) /
          (16 * (Real.log 2 + 1 / 2) * Real.log 2))
      < (189 : ℝ) / 250 := by
  have h := cstar_lt
  nlinarith [h]
theorem parent_estimate_core
    {v θ t e β L : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (he0 : 0 ≤ e) (he : e ≤ Real.sqrt 2)
    (hv : v ≤ t ^ 2 * e ^ 2 / 4) (hθ : t ^ 2 ≤ 1 - θ ^ 2) :
    v / (4 * β * L) ≤ ((3 + 2 * Real.sqrt 2) / (16 * β * L)) * (1 - θ ^ 2) := by
  have he2 : e ^ 2 ≤ 2 := by
    have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg e, h2, he]
  have h1θ : 0 ≤ 1 - θ ^ 2 := le_trans (sq_nonneg t) hθ
  have ht2e2 : t ^ 2 * e ^ 2 ≤ (1 - θ ^ 2) * 2 := by
    have := mul_le_mul hθ he2 (sq_nonneg e) h1θ
    nlinarith [this]
  have hv' : v ≤ (1 - θ ^ 2) / 2 := by nlinarith [hv, ht2e2]
  have hden : 0 < 4 * β * L := by positivity
  rw [div_le_iff₀ hden]
  have hconst : (1 : ℝ) / 2 ≤ (3 + 2 * Real.sqrt 2) / 4 := by
    have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hrhs : ((3 + 2 * Real.sqrt 2) / (16 * β * L)) * (1 - θ ^ 2) * (4 * β * L)
      = (3 + 2 * Real.sqrt 2) / 4 * (1 - θ ^ 2) := by
    field_simp
    ring
  rw [hrhs]
  nlinarith [hv', hconst, h1θ]
section ParentEstimateConcrete
noncomputable def wm (m : ℕ) : ℝ := Real.log (1 + 1 / (m : ℝ))
noncomputable def eOf (m : ℕ) : ℝ := Real.exp (wm m / 2)
noncomputable def tOf (m : ℕ) : ℝ := (eOf m - 1) / (eOf m + 1)
theorem eOf_pos (m : ℕ) : 0 < eOf m := Real.exp_pos _
theorem eOf_one_add_pos (m : ℕ) : 0 < eOf m + 1 := by linarith [eOf_pos m]
theorem eOf_sq (m : ℕ) (hm : 1 ≤ m) : eOf m ^ 2 = 1 + 1 / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm0 : (0 : ℝ) < 1 + 1 / (m : ℝ) := by positivity
  rw [eOf, sq, ← Real.exp_add, wm]
  have : Real.log (1 + 1 / (m : ℝ)) / 2 + Real.log (1 + 1 / (m : ℝ)) / 2
      = Real.log (1 + 1 / (m : ℝ)) := by ring
  rw [this, Real.exp_log hm0]
theorem eOf_le_sqrt_two (m : ℕ) (hm : 1 ≤ m) : eOf m ≤ Real.sqrt 2 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1m : 1 / (m : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hm0]; linarith
  have hsq : eOf m ^ 2 ≤ 2 := by
    rw [eOf_sq m hm]; linarith
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [le_of_lt (eOf_pos m), Real.sqrt_nonneg 2, h2, hsq]
theorem tOf_identity (m : ℕ) :
    (eOf m - 1) ^ 2 = tOf m ^ 2 * (eOf m + 1) ^ 2 := by
  have hne : eOf m + 1 ≠ 0 := ne_of_gt (eOf_one_add_pos m)
  rw [tOf]
  field_simp
theorem parent_estimate_concrete (m : ℕ) (hm : 1 ≤ m)
    {v θ β L : ℝ} (hβ : 0 < β) (hL : 0 < L)
    (hv : v ≤ (eOf m - 1) ^ 2 / 4) (hθ : tOf m ^ 2 ≤ 1 - θ ^ 2) :
    v / (4 * β * L) ≤ ((3 + 2 * Real.sqrt 2) / (16 * β * L)) * (1 - θ ^ 2) := by
  have he : eOf m + 1 ≤ 1 + Real.sqrt 2 := by
    linarith [eOf_le_sqrt_two m hm]
  have h1θ : 0 ≤ 1 - θ ^ 2 := le_trans (sq_nonneg (tOf m)) hθ
  have h1 : (eOf m + 1) ^ 2 ≤ (1 + Real.sqrt 2) ^ 2 := by
    have h0 : 0 ≤ eOf m + 1 := (eOf_one_add_pos m).le
    nlinarith [he, h0]
  have h2 : tOf m ^ 2 * (eOf m + 1) ^ 2
      ≤ (1 - θ ^ 2) * (1 + Real.sqrt 2) ^ 2 :=
    mul_le_mul hθ h1 (sq_nonneg (eOf m + 1)) h1θ
  have h3 := tOf_identity m
  have hv' : v ≤ ((1 + Real.sqrt 2) ^ 2 / 4) * (1 - θ ^ 2) := by
    nlinarith [hv, h2, h3]
  have hsp : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
    have h2' : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [h2']
  rw [hsp] at hv'
  have hden : 0 < 4 * β * L := by positivity
  rw [div_le_iff₀ hden]
  have hrhs : ((3 + 2 * Real.sqrt 2) / (16 * β * L)) * (1 - θ ^ 2) * (4 * β * L)
      = (3 + 2 * Real.sqrt 2) / 4 * (1 - θ ^ 2) := by
    field_simp
    ring
  rw [hrhs]
  exact hv'
end ParentEstimateConcrete
section PhiMonotone
noncomputable def N (u : ℝ) : ℝ :=
  (u / 2) * (Real.exp (u / 2) + Real.exp (-u / 2))
    - (Real.exp (u / 2) - Real.exp (-u / 2))
theorem hasDerivAt_exp_half (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x / 2)) ((1 / 2) * Real.exp (u / 2)) u := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      (Real.exp (u / 2) * (1 / 2)) u := by
    simpa only [Function.comp_def, id_eq] using
      (Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)
  convert h using 1
  ring
theorem hasDerivAt_exp_neg_half (u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x / 2)) (-(1 / 2) * Real.exp (-u / 2)) u := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
      (Real.exp (-u / 2) * (-(1 / 2))) u := by
    simpa only [Function.comp_def, Pi.neg_apply, id_eq, neg_div] using
      (Real.hasDerivAt_exp (-u / 2)).comp u ((hasDerivAt_id u).neg.div_const 2)
  convert h using 1
  ring
theorem N_deriv (u : ℝ) :
    HasDerivAt N ((u / 4) * (Real.exp (u / 2) - Real.exp (-u / 2))) u := by
  have h1 := hasDerivAt_exp_half u
  have h2 := hasDerivAt_exp_neg_half u
  have h3 := h1.add h2
  have h4 := ((hasDerivAt_id u).div_const 2).mul h3
  have h5 := h1.sub h2
  have h := h4.sub h5
  unfold N
  convert h using 1
  all_goals
    try ext x
    simp only [id_eq, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    try ring_nf
theorem N_pos {u : ℝ} (hu : 0 < u) : 0 < N u := by
  have hc : Continuous N := by unfold N; fun_prop
  have hmono : StrictMonoOn N (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hc.continuousOn
    intro x hx
    have hxpos : 0 < x := by
      have hx' := hx
      rw [interior_Ici] at hx'
      exact hx'
    have hpos : 0 < (x / 4) * (Real.exp (x / 2) - Real.exp (-x / 2)) := by
      have hx0 : 0 < x / 4 := by positivity
      have hdiff : 0 < Real.exp (x / 2) - Real.exp (-x / 2) := by
        have hlt := Real.exp_lt_exp.mpr (by linarith : -x / 2 < x / 2)
        linarith
      positivity
    rw [(N_deriv x).deriv]
    exact hpos
  have h0 : N 0 = 0 := by norm_num [N]
  have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu.le) hu
  rwa [h0] at hlt
end PhiMonotone
section QMonotone
noncomputable def q (u : ℝ) : ℝ := (Real.exp (u / 2) - Real.exp (-u / 2)) / u
theorem q_deriv {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt q (N u / u ^ 2) u := by
  have h1 := hasDerivAt_exp_half u
  have h2 := hasDerivAt_exp_neg_half u
  have hp := h1.sub h2
  have hq := hp.div (hasDerivAt_id u) hu
  unfold q N
  convert hq using 1
  all_goals
    try ext x
    simp only [id_eq, Pi.div_apply, Pi.sub_apply]
    try ring
theorem q_pos {u : ℝ} (hu : 0 < u) : 0 < q u := by
  have hnum : 0 < Real.exp (u / 2) - Real.exp (-u / 2) := by
    have hlt := Real.exp_lt_exp.mpr (by linarith : -u / 2 < u / 2)
    linarith
  rw [q]
  positivity
theorem q_strictMonoOn : StrictMonoOn q (Set.Ioi 0) := by
  have hcont : ContinuousOn q (Set.Ioi 0) := by
    have hnum : ContinuousOn (fun x : ℝ => Real.exp (x / 2) - Real.exp (-x / 2))
        (Set.Ioi 0) := (by fun_prop : Continuous fun x : ℝ => Real.exp (x / 2) - Real.exp (-x / 2)).continuousOn
    exact hnum.div continuous_id.continuousOn (fun x hx => ne_of_gt hx)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont
  intro x hx
  rw [interior_Ioi] at hx
  have hxpos : 0 < x := hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  rw [(q_deriv hxne).deriv]
  have hN : 0 < N x := N_pos hxpos
  positivity
end QMonotone
section PhiDef
noncomputable def Phi (u : ℝ) : ℝ := 1 / (q u) ^ 2
theorem Phi_pos {u : ℝ} (hu : 0 < u) : 0 < Phi u := by
  rw [Phi]
  exact div_pos one_pos (pow_pos (q_pos hu) 2)
theorem Phi_antitone {a b : ℝ} (ha : 0 < a) (hab : a < b) : Phi b < Phi a := by
  have hb : 0 < b := lt_trans ha hab
  have hmono := q_strictMonoOn (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb) hab
  have hqa : 0 < q a := q_pos ha
  have hqb : 0 < q b := q_pos hb
  rw [Phi, Phi]
  have hsq : (q a) ^ 2 < (q b) ^ 2 := by nlinarith
  exact one_div_lt_one_div_of_lt (pow_pos hqa 2) hsq
theorem theta_sq_lt_one' {wk wm : ℝ} (hwk : 0 < wk) (hkm : wk < wm) :
    Phi wm / Phi wk < 1 ∧ 0 < Phi wm / Phi wk := by
  have hb : 0 < wm := lt_trans hwk hkm
  constructor
  · rw [div_lt_one (Phi_pos hwk)]
    exact Phi_antitone hwk hkm
  · exact div_pos (Phi_pos hb) (Phi_pos hwk)
end PhiDef
namespace GateII
open Finset
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
theorem mixedBlock_det_pos {θ P χ : ℝ} (hθ : θ ^ 2 < 1) (hP : 0 < P) (hχ : 0 < χ) :
    0 < (1 - θ ^ 2) * P * χ * (1 - (189 / 250) * θ ^ 2) := by
  have h1 : 0 < 1 - θ ^ 2 := by nlinarith
  have h2 : 0 < 1 - (189 / 250) * θ ^ 2 := by nlinarith
  positivity
theorem aligned_penalty_constant : (439 : ℚ) / 250 = 1 + 189 / 250 := by
  norm_num
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
theorem master_scalar_reduction {S W x : ℝ}
    (hS : S ≤ (12 / 100) * Real.log x + (2873 / 1000))
    (hW : W ≤ (47 / 1000) * Real.log x)
    (hX : 15 ≤ Real.log x) :
    (5784953 / 10000000) * Real.log x - (67783792 / 10000000)
      < 1 / 2 + Real.log x - (439 / (250 * Real.log 2)) * S - (5 / 2) * W ∧
    0 < 1 / 2 + Real.log x - (439 / (250 * Real.log 2)) * S - (5 / 2) * W := by
  set L := Real.log x with hL
  set C := 439 / (250 * Real.log 2) with hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by
    rw [hC]
    positivity
  have hnum : (439 : ℝ)
      < ((25333725 : ℝ) / 10000000) * (250 * 0.6931471803) := by norm_num
  have hCub : C < (25333725 : ℝ) / 10000000 := by
    rw [hC, div_lt_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9, hnum]
  have hL0 : 0 ≤ L := by linarith
  have harg0 : 0 ≤ (12 / 100) * L + (2873 / 1000) := by nlinarith [hL0]
  have hCmul : C * ((12 / 100) * L + (2873 / 1000))
      ≤ ((25333725 : ℝ) / 10000000) * ((12 / 100) * L + (2873 / 1000)) :=
    mul_le_mul_of_nonneg_right hCub.le harg0
  have hCS : C * S ≤ C * ((12 / 100) * L + (2873 / 1000)) :=
    mul_le_mul_of_nonneg_left hS hCpos.le
  have hCW : (5 / 2) * W ≤ (5 / 2) * ((47 / 1000) * L) :=
    mul_le_mul_of_nonneg_left hW (by norm_num)
  have hcore : (5784953 / 10000000) * L - (67783792 / 10000000)
      < 1 / 2 + L - ((25333725 : ℝ) / 10000000) * ((12 / 100) * L + (2873 / 1000))
          - (5 / 2) * ((47 / 1000) * L) := by
    ring_nf
    linarith
  have hg : (5784953 / 10000000) * L - (67783792 / 10000000)
      < 1 / 2 + L - C * S - (5 / 2) * W := by
    linarith
  constructor
  · exact hg
  · have h15 : (0 : ℝ) < (5784953 / 10000000) * 15 - (67783792 / 10000000) := by
      norm_num
    linarith
end GateII
end RHLean
section RHLeanY7FinalIntervalInline
set_option maxHeartbeats 2000000
namespace RHLean.Y7FinalInterval
def center (i j : Fin 7) : ℚ :=
  match i.val, j.val with
  | 0, 0 => (2223075804921872764310763661166363522379403009516663 / 2000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 1 => (1519422867248165229457643314807475291286348148003031 / 10000000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 2 => (398467297272234207675721779020218521548502298628617 / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 3 => (212102911650510199531348044629268684452122830890151 / 100000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 4 => (-4795955486527404504852945646197182332749082958009 / 50000000000000000000000000000000000000000000000000000000000000000)
  | 0, 5 => (64310290452907548970847675588166601367919429295221 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 0, 6 => (75265769958931856122797669816500836686415446026483 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 1, 0 => (1519422867248165229457643314807475291286348148003031 / 10000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 1 => (9040985646404259650603164405533148857336460733538579 / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 2 => (-674721563363143559250047917737666888473945321779291 / 10000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 3 => (-641419958269178683019819583133722617443539408806533 / 100000000000000000000000000000000000000000000000000000000000000000)
  | 1, 4 => (-421615554960749679012774150734722255843196873177 / 2500000000000000000000000000000000000000000000000000000000000)
  | 1, 5 => (-854213649103666878304270708541111931209352334019 / 312500000000000000000000000000000000000000000000000000000000)
  | 1, 6 => (-51511750437061297519951355958356764863014658694397 / 10000000000000000000000000000000000000000000000000000000000000)
  | 2, 0 => (398467297272234207675721779020218521548502298628617 / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 2, 1 => (-674721563363143559250047917737666888473945321779291 / 10000000000000000000000000000000000000000000000000000000000000000000)
  | 2, 2 => (57368319135209955314625386823269548938455899437291 / 250000000000000000000000000000000000000000000000000000000000000)
  | 2, 3 => (-496037413101353602681808030875356308353534118799451 / 100000000000000000000000000000000000000000000000000000000000000)
  | 2, 4 => (-149535256344871567781966198302483075855398830536487 / 500000000000000000000000000000000000000000000000000000000000)
  | 2, 5 => (19543889527284145448024094212628420104190754071999 / 5000000000000000000000000000000000000000000000000000000000)
  | 2, 6 => (29691138673238154476309234991462744381477570746773 / 10000000000000000000000000000000000000000000000000000000000)
  | 3, 0 => (212102911650510199531348044629268684452122830890151 / 100000000000000000000000000000000000000000000000000000000000000000000)
  | 3, 1 => (-641419958269178683019819583133722617443539408806533 / 100000000000000000000000000000000000000000000000000000000000000000)
  | 3, 2 => (-496037413101353602681808030875356308353534118799451 / 100000000000000000000000000000000000000000000000000000000000000)
  | 3, 3 => (5996448045571686309420613785997623443877753301571697 / 1000000000000000000000000000000000000000000000000000000000000)
  | 3, 4 => (-78025045395371410248784801265055368819834952570961 / 1000000000000000000000000000000000000000000000000000000000)
  | 3, 5 => (16608730737449458703473412123969400683258809769973 / 10000000000000000000000000000000000000000000000000000000)
  | 3, 6 => (170018201068314546833670666859354929493121541742417 / 100000000000000000000000000000000000000000000000000000000)
  | 4, 0 => (-4795955486527404504852945646197182332749082958009 / 50000000000000000000000000000000000000000000000000000000000000000)
  | 4, 1 => (-421615554960749679012774150734722255843196873177 / 2500000000000000000000000000000000000000000000000000000000000)
  | 4, 2 => (-149535256344871567781966198302483075855398830536487 / 500000000000000000000000000000000000000000000000000000000000)
  | 4, 3 => (-78025045395371410248784801265055368819834952570961 / 1000000000000000000000000000000000000000000000000000000000)
  | 4, 4 => (126338783742777103082332848119061909896997063373801 / 2000000000000000000000000000000000000000000000000000000)
  | 4, 5 => (139061394248755815682949908278954748204726741637127 / 500000000000000000000000000000000000000000000000000000)
  | 4, 6 => (307771074884766880284402045837745865887636405257401 / 1000000000000000000000000000000000000000000000000000000)
  | 5, 0 => (64310290452907548970847675588166601367919429295221 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 5, 1 => (-854213649103666878304270708541111931209352334019 / 312500000000000000000000000000000000000000000000000000000000)
  | 5, 2 => (19543889527284145448024094212628420104190754071999 / 5000000000000000000000000000000000000000000000000000000000)
  | 5, 3 => (16608730737449458703473412123969400683258809769973 / 10000000000000000000000000000000000000000000000000000000)
  | 5, 4 => (139061394248755815682949908278954748204726741637127 / 500000000000000000000000000000000000000000000000000000)
  | 5, 5 => (7136439153526201036307633814421464907247503368014231 / 100000000000000000000000000000000000000000000000000000)
  | 5, 6 => (-931180539353299343918631387336969249750078208758529 / 100000000000000000000000000000000000000000000000000000)
  | 6, 0 => (75265769958931856122797669816500836686415446026483 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 6, 1 => (-51511750437061297519951355958356764863014658694397 / 10000000000000000000000000000000000000000000000000000000000000)
  | 6, 2 => (29691138673238154476309234991462744381477570746773 / 10000000000000000000000000000000000000000000000000000000000)
  | 6, 3 => (170018201068314546833670666859354929493121541742417 / 100000000000000000000000000000000000000000000000000000000)
  | 6, 4 => (307771074884766880284402045837745865887636405257401 / 1000000000000000000000000000000000000000000000000000000)
  | 6, 5 => (-931180539353299343918631387336969249750078208758529 / 100000000000000000000000000000000000000000000000000000)
  | 6, 6 => (6996323566924715689526572851183563193650306570365351 / 10000000000000000000000000000000000000000000000000000)
  | _, _ => 0
def radius (i j : Fin 7) : ℚ :=
  match i.val, j.val with
  | 0, 0 => (93 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 1 => (849 / 10000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 2 => (311 / 5000000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 3 => (173 / 25000000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 4 => (23 / 20000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 5 => (77 / 5000000000000000000000000000000000000000000000000000000000000000000)
  | 0, 6 => (213 / 5000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 0 => (849 / 10000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 1 => (157 / 2500000000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 2 => (331 / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 3 => (429 / 50000000000000000000000000000000000000000000000000000000000000000000)
  | 1, 4 => (7 / 3125000000000000000000000000000000000000000000000000000000000000)
  | 1, 5 => (281 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 1, 6 => (307 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 2, 0 => (311 / 5000000000000000000000000000000000000000000000000000000000000000000000000)
  | 2, 1 => (331 / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 2, 2 => (23 / 1000000000000000000000000000000000000000000000000000000000000000000)
  | 2, 3 => (471 / 100000000000000000000000000000000000000000000000000000000000000000)
  | 2, 4 => (823 / 1000000000000000000000000000000000000000000000000000000000000000)
  | 2, 5 => (17 / 312500000000000000000000000000000000000000000000000000000000)
  | 2, 6 => (103 / 2500000000000000000000000000000000000000000000000000000000000)
  | 3, 0 => (173 / 25000000000000000000000000000000000000000000000000000000000000000000000)
  | 3, 1 => (429 / 50000000000000000000000000000000000000000000000000000000000000000000)
  | 3, 2 => (471 / 100000000000000000000000000000000000000000000000000000000000000000)
  | 3, 3 => (1 / 1250000000000000000000000000000000000000000000000000000000000)
  | 3, 4 => (211 / 500000000000000000000000000000000000000000000000000000000000)
  | 3, 5 => (7 / 4000000000000000000000000000000000000000000000000000000000)
  | 3, 6 => (57 / 10000000000000000000000000000000000000000000000000000000000)
  | 4, 0 => (23 / 20000000000000000000000000000000000000000000000000000000000000000000)
  | 4, 1 => (7 / 3125000000000000000000000000000000000000000000000000000000000000)
  | 4, 2 => (823 / 1000000000000000000000000000000000000000000000000000000000000000)
  | 4, 3 => (211 / 500000000000000000000000000000000000000000000000000000000000)
  | 4, 4 => (563 / 10000000000000000000000000000000000000000000000000000000000)
  | 4, 5 => (223 / 1000000000000000000000000000000000000000000000000000000000)
  | 4, 6 => (309 / 500000000000000000000000000000000000000000000000000000000)
  | 5, 0 => (77 / 5000000000000000000000000000000000000000000000000000000000000000000)
  | 5, 1 => (281 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 5, 2 => (17 / 312500000000000000000000000000000000000000000000000000000000)
  | 5, 3 => (7 / 4000000000000000000000000000000000000000000000000000000000)
  | 5, 4 => (223 / 1000000000000000000000000000000000000000000000000000000000)
  | 5, 5 => (371 / 50000000000000000000000000000000000000000000000000000000)
  | 5, 6 => (877 / 100000000000000000000000000000000000000000000000000000000)
  | 6, 0 => (213 / 5000000000000000000000000000000000000000000000000000000000000000000)
  | 6, 1 => (307 / 10000000000000000000000000000000000000000000000000000000000000000)
  | 6, 2 => (103 / 2500000000000000000000000000000000000000000000000000000000000)
  | 6, 3 => (57 / 10000000000000000000000000000000000000000000000000000000000)
  | 6, 4 => (309 / 500000000000000000000000000000000000000000000000000000000)
  | 6, 5 => (877 / 100000000000000000000000000000000000000000000000000000000)
  | 6, 6 => (139 / 2500000000000000000000000000000000000000000000000000000)
  | _, _ => 0
private def scale (i : Fin 7) : ℚ :=
  match i.val with
  | 0 => (2108589957730934829 / 2000000000000000000000000000000)
  | 1 => (95084097757744221289 / 100000000000000000000000000000)
  | 2 => (47903369040271042429 / 100000000000000000000000000)
  | 3 => (15487347152526395551 / 200000000000000000000000)
  | 4 => (79479174549933866019 / 10000000000000000000000)
  | 5 => (13357057267158624633 / 50000000000000000000)
  | 6 => (83644028877886529561 / 100000000000000000000)
  | _ => 1
private def margin (i : Fin 7) : ℚ :=
  (center i i - radius i i) / (scale i * scale i) -
    ∑ j : Fin 7,
      if i = j then 0 else
        (|center i j| + radius i j) / (scale i * scale j)
theorem rational_row_margins :
    ∀ i : Fin 7, (5198729787 / 10000000000 : ℚ) < margin i := by
  intro i
  fin_cases i <;>
    norm_num [margin, center, radius, scale, Fin.sum_univ_succ]
open Matrix
theorem posDef_of_strict_diagDominant {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsSymm)
    (h : ∀ i, 0 < M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) :
    M.PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ((Matrix.isHermitian_iff_isSymm).mpr hM) ?_
  intro x hx
  simp only [star_trivial]
  have hx0 : ∃ i, x i ≠ 0 := by
    by_contra hcon
    apply hx
    funext j
    by_contra hj
    exact hcon ⟨j, hj⟩
  have hpair : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i,
      (2 * (x i * M i j * x j) + |M i j| * (x i ^ 2 + x j ^ 2)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have h1 : 2 * |x i| * |x j| ≤ x i ^ 2 + x j ^ 2 := by
      have := two_mul_le_add_sq (|x i|) (|x j|)
      simpa [sq_abs] using this
    have h2 : -(2 * (x i * M i j * x j)) ≤ 2 * (|M i j| * |x i| * |x j|) := by
      have habs : |2 * (x i * M i j * x j)| = 2 * (|M i j| * |x i| * |x j|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      have := neg_le_abs (2 * (x i * M i j * x j))
      rwa [habs] at this
    have h3 : 0 ≤ |M i j| := abs_nonneg _
    have h4 : 2 * |M i j| * |x i| * |x j| ≤ |M i j| * (x i ^ 2 + x j ^ 2) := by
      have := mul_le_mul_of_nonneg_left h1 h3
      nlinarith
    linarith
  have hAB : (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
      = ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2 := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.univ.erase i)
        (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)
        (f := fun i j => |M i j| * x i ^ 2) (by intro i j; simp [ne_comm])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM.apply j i]
  have hsplit : (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2))
      = 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2 := by
    have h1 : (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2))
        = (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
          + (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x j ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, hAB]
    ring
  have hB1 : -(∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2)
      ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j := by
    have hsum : (∑ i, ∑ j ∈ Finset.univ.erase i,
        (2 * (x i * M i j * x j) + |M i j| * (x i ^ 2 + x j ^ 2)))
        = 2 * (∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j)
          + 2 * (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2) := by
      have h1 : (∑ i, ∑ j ∈ Finset.univ.erase i,
          (2 * (x i * M i j * x j) + |M i j| * (x i ^ 2 + x j ^ 2)))
          = ∑ i, ((∑ j ∈ Finset.univ.erase i, 2 * (x i * M i j * x j))
            + (∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_add_distrib
      have h1' : (∑ i, ∑ j ∈ Finset.univ.erase i,
          (2 * (x i * M i j * x j) + |M i j| * (x i ^ 2 + x j ^ 2)))
          = (∑ i, ∑ j ∈ Finset.univ.erase i, 2 * (x i * M i j * x j))
            + (∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * (x i ^ 2 + x j ^ 2)) := by
        rw [h1, Finset.sum_add_distrib]
      have h2 : (∑ i, ∑ j ∈ Finset.univ.erase i, 2 * (x i * M i j * x j))
          = 2 * (∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j) := by
        simp_rw [Finset.mul_sum]
      rw [h1', h2, hsplit]
    linarith
  have hkey : (∑ i, (M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2)
      ≤ x ⬝ᵥ (M *ᵥ x) := by
    have hquad : x ⬝ᵥ (M *ᵥ x)
        = (∑ i, M i i * x i ^ 2)
          + ∑ i, ∑ j ∈ Finset.univ.erase i, x i * M i j * x j := by
      have hL : x ⬝ᵥ (M *ᵥ x)
          = ∑ i, (M i i * x i ^ 2
              + ∑ j ∈ Finset.univ.erase i, x i * M i j * x j) := by
        simp only [dotProduct, mulVec]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        rw [← Finset.sum_erase_add (Finset.univ : Finset n)
          (fun j => x i * (M i j * x j)) (Finset.mem_univ i)]
        ring
      rw [hL, Finset.sum_add_distrib]
    rw [hquad]
    have hsum : (∑ i, (M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2)
        = (∑ i, M i i * x i ^ 2)
          - ∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    have hCeq : (∑ i, (∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2)
        = ∑ i, ∑ j ∈ Finset.univ.erase i, |M i j| * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    rw [hCeq]
    linarith
  have hpos : 0 < ∑ i, (M i i - ∑ j ∈ Finset.univ.erase i, |M i j|) * x i ^ 2 := by
    obtain ⟨i, hi⟩ := hx0
    refine Finset.sum_pos' ?_ ⟨i, Finset.mem_univ i, ?_⟩
    · intro k _
      exact mul_nonneg (le_of_lt (h k)) (sq_nonneg _)
    · exact mul_pos (h i) (sq_pos_of_ne_zero hi)
  linarith
def InY7Family (F : Matrix (Fin 7) (Fin 7) ℝ) : Prop :=
  F.IsSymm ∧ ∀ i j, ((center i j - radius i j : ℚ) : ℝ) ≤ F i j ∧
                    F i j ≤ ((center i j + radius i j : ℚ) : ℝ)
private lemma scale_pos (i : Fin 7) : (0 : ℚ) < scale i := by
  fin_cases i <;> norm_num [scale]
private lemma radius_nonneg (i j : Fin 7) : (0 : ℚ) ≤ radius i j := by
  fin_cases i <;> fin_cases j <;> norm_num [radius]
private lemma abs_le_of_mem {c r x : ℝ}
    (h : c - r ≤ x ∧ x ≤ c + r) : |x| ≤ |c| + r := by
  rw [abs_le]
  constructor
  · have : -|c| ≤ c := neg_abs_le c
    linarith [h.1]
  · have : c ≤ |c| := le_abs_self c
    linarith [h.2]
private lemma margin_erase (i : Fin 7) :
    margin i = (center i i - radius i i) / (scale i * scale i)
      - ∑ j ∈ Finset.univ.erase i, (|center i j| + radius i j) / (scale i * scale j) := by
  rw [margin]
  congr 1
  rw [← Finset.sum_erase (s := Finset.univ)
    (f := fun j : Fin 7 => if i = j then (0 : ℚ) else
      (|center i j| + radius i j) / (scale i * scale j)) (a := i) (by simp)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (Ne.symm (Finset.mem_erase.mp hj).1)]
theorem Y7_family_posDef (F : Matrix (Fin 7) (Fin 7) ℝ) (hF : InY7Family F) :
    F.PosDef := by
  classical
  obtain ⟨hFsym, hFint⟩ := hF
  let S : Matrix (Fin 7) (Fin 7) ℝ := fun i j =>
    F i j / ((scale i : ℝ) * (scale j : ℝ))
  have hSsym : S.IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp only [S]
    rw [hFsym.apply i j]
    ring
  have hmargin : ∀ i, (5198729787 / 10000000000 : ℝ) < (margin i : ℝ) := by
    intro i
    have h := rational_row_margins i
    have h' : ((5198729787 : ℚ) / 10000000000 : ℝ) < (margin i : ℝ) :=
      by exact_mod_cast h
    simpa using h'
  have hgersh : ∀ i, 0 < S i i - ∑ j ∈ Finset.univ.erase i, |S i j| := by
    intro i
    have hsi : (0 : ℝ) < (scale i : ℝ) := by
      exact_mod_cast scale_pos i
    have hdiag : ((center i i - radius i i : ℚ) : ℝ) / ((scale i : ℝ) * (scale i : ℝ)) ≤ S i i := by
      simp only [S]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (hFint i i).1)
        (le_of_lt (mul_pos hsi hsi))
    have hoff : ∀ j ∈ Finset.univ.erase i,
        |S i j| ≤ (|((center i j : ℚ) : ℝ)| + ((radius i j : ℚ) : ℝ))
          / ((scale i : ℝ) * (scale j : ℝ)) := by
      intro j _
      have hsj : (0 : ℝ) < (scale j : ℝ) := by exact_mod_cast scale_pos j
      have hle : |F i j| ≤ |((center i j : ℚ) : ℝ)| + ((radius i j : ℚ) : ℝ) := by
        have hmem1 : ((center i j : ℚ) : ℝ) - ((radius i j : ℚ) : ℝ) ≤ F i j := by
          have := (hFint i j).1
          push_cast at this
          exact this
        have hmem2 : F i j ≤ ((center i j : ℚ) : ℝ) + ((radius i j : ℚ) : ℝ) := by
          have := (hFint i j).2
          push_cast at this
          exact this
        exact abs_le_of_mem ⟨hmem1, hmem2⟩
      simp only [S]
      rw [abs_div, abs_of_pos (mul_pos hsi hsj)]
      exact div_le_div_of_nonneg_right hle (le_of_lt (mul_pos hsi hsj))
    have hmargin_eq : (margin i : ℝ)
        = ((center i i - radius i i : ℚ) : ℝ) / ((scale i : ℝ) * (scale i : ℝ))
          - ∑ j ∈ Finset.univ.erase i,
              (|((center i j : ℚ) : ℝ)| + ((radius i j : ℚ) : ℝ))
                / ((scale i : ℝ) * (scale j : ℝ)) := by
      rw [margin_erase i]
      push_cast
      rfl
    have hle : ((center i i - radius i i : ℚ) : ℝ) / ((scale i : ℝ) * (scale i : ℝ))
          - ∑ j ∈ Finset.univ.erase i,
              (|((center i j : ℚ) : ℝ)| + ((radius i j : ℚ) : ℝ))
                / ((scale i : ℝ) * (scale j : ℝ))
        ≤ S i i - ∑ j ∈ Finset.univ.erase i, |S i j| :=
      sub_le_sub hdiag (Finset.sum_le_sum hoff)
    have h2 : (5198729787 / 10000000000 : ℝ) <
        S i i - ∑ j ∈ Finset.univ.erase i, |S i j| := by
      rw [← hmargin_eq] at hle
      exact lt_of_lt_of_le (hmargin i) hle
    linarith
  have hSpos : S.PosDef := posDef_of_strict_diagDominant S hSsym hgersh
  let D : Matrix (Fin 7) (Fin 7) ℝ := diagonal (fun i => (scale i : ℝ))
  have hDunit : IsUnit D := by
    rw [Matrix.isUnit_diagonal]
    refine isUnit_iff_exists.mpr ⟨fun i => ((scale i : ℝ))⁻¹, ?_, ?_⟩
    · funext i
      exact mul_inv_cancel₀ (ne_of_gt (by exact_mod_cast scale_pos i : (0 : ℝ) < (scale i : ℝ)))
    · funext i
      exact inv_mul_cancel₀ (ne_of_gt (by exact_mod_cast scale_pos i : (0 : ℝ) < (scale i : ℝ)))
  have hstar : star D = D := by
    change star (diagonal (fun i => (scale i : ℝ))) = diagonal (fun i => (scale i : ℝ))
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp
  have hcong : (D * S * D).PosDef := by
    have := hDunit.posDef_star_right_conjugate_iff.mpr hSpos
    rwa [hstar] at this
  have hDSD : D * S * D = F := by
    ext i j
    simp only [D]
    rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [S]
    have hsi : (scale i : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast scale_pos i : (0 : ℝ) < (scale i : ℝ))
    have hsj : (scale j : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast scale_pos j : (0 : ℝ) < (scale j : ℝ))
    field_simp [hsi, hsj]
  rwa [hDSD] at hcong
theorem posDef_of_strict_diagDominant_box {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (C Rad : Matrix n n ℚ) (hM : M.IsSymm)
    (hmem : ∀ i j, ((C i j - Rad i j : ℚ) : ℝ) ≤ M i j ∧
      M i j ≤ ((C i j + Rad i j : ℚ) : ℝ))
    (h : ∀ i, 0 < ((C i i - Rad i i : ℚ) : ℝ) -
      ∑ j ∈ Finset.univ.erase i, (|(C i j : ℝ)| + (Rad i j : ℝ))) :
    M.PosDef := by
  refine posDef_of_strict_diagDominant M hM fun i => ?_
  have hdiag : ((C i i - Rad i i : ℚ) : ℝ) ≤ M i i := (hmem i i).1
  have hrow : ∑ j ∈ Finset.univ.erase i, |M i j| ≤
      ∑ j ∈ Finset.univ.erase i, (|(C i j : ℝ)| + (Rad i j : ℝ)) := by
    apply Finset.sum_le_sum
    intro j _
    have hmem' := hmem i j
    have h1 : ((C i j - Rad i j : ℚ) : ℝ) = (C i j : ℝ) - (Rad i j : ℝ) := by
      push_cast; ring
    have h2 : ((C i j + Rad i j : ℚ) : ℝ) = (C i j : ℝ) + (Rad i j : ℝ) := by
      push_cast; ring
    rw [h1] at hmem'
    rw [h2] at hmem'
    exact abs_le_of_mem hmem'
  linarith [h i]
theorem sum_eq_list_sum_of_nodup {α : Type*} [DecidableEq α] {l : List α}
    (h : l.Nodup) (f : α → ℚ) : (∑ x ∈ l.toFinset, f x) = List.sum (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    rw [List.toFinset_cons, Finset.sum_insert, List.map_cons, List.sum_cons, ih h.2]
    rw [List.mem_toFinset]
    exact h.1
theorem sum_erase_eq_list_sum {n : ℕ} (i : Fin n) (f : Fin n → ℚ) :
    (∑ j ∈ Finset.univ.erase i, f j) =
      List.sum (List.map f ((List.finRange n).filter (· ≠ i))) := by
  have hnodup : ((List.finRange n).filter (· ≠ i)).Nodup :=
    (List.nodup_finRange n).filter _
  have htofinset : ((List.finRange n).filter (· ≠ i)).toFinset =
      Finset.univ.erase i := by
    ext j
    simp [Finset.mem_erase]
  rw [← htofinset, sum_eq_list_sum_of_nodup hnodup]
theorem abs_sum_mul_inv_le {ι : Type*} (s : Finset ι) (a b d A B : ι → ℝ) (w : ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ A i) (hb : ∀ i ∈ s, |b i| ≤ B i)
    (hd0 : ∀ i ∈ s, 0 < d i) (hd : ∀ i ∈ s, (d i)⁻¹ ≤ w)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) (hw : 0 ≤ w) :
    |∑ i ∈ s, a i * b i * (d i)⁻¹| ≤ ∑ i ∈ s, A i * B i * w := by
  calc |∑ i ∈ s, a i * b i * (d i)⁻¹|
      ≤ ∑ i ∈ s, |a i * b i * (d i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |a i| * |b i| * |(d i)⁻¹| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_mul]
    _ ≤ ∑ i ∈ s, A i * B i * w := by
        apply Finset.sum_le_sum
        intro i hi
        have h1 : |a i| * |b i| ≤ A i * B i :=
          mul_le_mul (ha i hi) (hb i hi) (abs_nonneg _) (hA i hi)
        have h2 : |(d i)⁻¹| ≤ w := by
          rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hd0 i hi)))]
          exact hd i hi
        exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (hA i hi) (hB i hi))
end RHLean.Y7FinalInterval
end RHLeanY7FinalIntervalInline
section Inline_Y7_GammaTaylor
noncomputable section
open Complex
namespace Y7Density
noncomputable def gammaFull (z : ℂ) : ℂ :=
  Complex.exp (z / 2) / (2 * Complex.sinh z) - 1 / (2 * z)
theorem gammaFull_ofReal_re {t : ℝ} (ht : t ≠ 0) :
    (gammaFull (t : ℂ)).re = RHLean.gammaKernel t := by
  have h : gammaFull (t : ℂ)
      = (((Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t)) : ℝ) : ℂ) := by
    unfold gammaFull
    rw [show ((t : ℂ) / 2) = ((t / 2 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_exp (t / 2), ← Complex.ofReal_sinh t]
    push_cast
    ring
  rw [h, RHLean.gammaKernel, if_neg ht]
  exact Complex.ofReal_re _
theorem gammaFull_functional_identity {z : ℂ} (hz : z ≠ 0) (hsinh : Complex.sinh z ≠ 0) :
    (1 + 2 * z * gammaFull z) * (Complex.exp (2 * z) - 1)
      = 2 * z * Complex.exp (3 * z / 2) := by
  have h1 : 1 + 2 * z * gammaFull z =
      z * Complex.exp (z / 2) / Complex.sinh z := by
    unfold gammaFull
    field_simp
    ring
  have h2 : Complex.exp (2 * z) - 1 = 2 * Complex.exp z * Complex.sinh z := by
    rw [show Complex.exp (2 * z) = Complex.exp z * Complex.exp z by
          rw [show (2 : ℂ) * z = z + z by ring, Complex.exp_add]]
    simp only [Complex.sinh, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero z]
  rw [h1, h2]
  field_simp
  rw [show z * 3 / 2 = z / 2 + z by ring, Complex.exp_add]
end Y7Density
end
end Inline_Y7_GammaTaylor
section Inline_Y7_GammaLimit
noncomputable section
open Complex
open scoped BigOperators Topology
namespace Y7Density
noncomputable def sigmaSinh (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (2 * n) / (((2 * n + 1).factorial : ℕ) : ℂ)
theorem hasSum_sigmaSinh (z : ℂ) :
    HasSum (fun n : ℕ => z ^ (2 * n) / (((2 * n + 1).factorial : ℕ) : ℂ))
      (sigmaSinh z) := by
  have hsumm : Summable (fun n : ℕ => z ^ (2 * n) / (((2 * n + 1).factorial : ℕ) : ℂ)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (Real.summable_pow_div_factorial (‖z‖ ^ 2))
    rw [norm_div, norm_pow, show ‖z‖ ^ (2 * n) = (‖z‖ ^ 2) ^ n by rw [← pow_mul]]
    have h2 : ((n.factorial : ℕ) : ℝ) ≤ ‖((((2 * n + 1).factorial : ℕ) : ℂ))‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.factorial_le (by omega)
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  exact hsumm.hasSum
theorem sinh_eq_mul_sigmaSinh {z : ℂ} (hz : z ≠ 0) :
    Complex.sinh z = z * sigmaSinh z := by
  have h := (Complex.hasSum_sinh z).mul_left z⁻¹
  have hterm : ∀ n : ℕ, z⁻¹ * (z ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ))
      = z ^ (2 * n) / (((2 * n + 1).factorial : ℕ) : ℂ) := by
    intro n
    rw [show z ^ (2 * n + 1) = z * z ^ (2 * n) by rw [pow_succ']]
    field_simp
  have h' : HasSum (fun n : ℕ => z ^ (2 * n) / (((2 * n + 1).factorial : ℕ) : ℂ))
      (z⁻¹ * Complex.sinh z) := by
    have hs := h
    rw [funext hterm] at hs
    exact hs
  have hs : sigmaSinh z = z⁻¹ * Complex.sinh z := h'.tsum_eq
  rw [hs, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
theorem tendsto_sinh_sub_id_div_sq :
    Filter.Tendsto (fun z : ℂ => (Complex.sinh z - z) / z ^ 2) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  refine squeeze_zero_norm'
    (f := fun z : ℂ => (Complex.sinh z - z) / z ^ 2) (a := fun z : ℂ => 2 * ‖z‖) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
        (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))] with z hz hball
    have hz' : z ≠ 0 := hz
    have hzle : ‖z‖ ≤ 1 / 2 := by
      rw [Metric.mem_ball, dist_zero_right] at hball
      exact hball.le
    have hshift : HasSum
        (fun n : ℕ => z ^ (2 * (n + 1) + 1) / (((2 * (n + 1) + 1).factorial : ℕ) : ℂ))
        (Complex.sinh z - z) := by
      have h := (hasSum_nat_add_iff'
        (f := fun n : ℕ => z ^ (2 * n + 1) / (((2 * n + 1).factorial : ℕ) : ℂ)) 1).2
        (Complex.hasSum_sinh z)
      have h0 : (∑ i ∈ Finset.range 1,
          z ^ (2 * i + 1) / (((2 * i + 1).factorial : ℕ) : ℂ)) = z := by
        simp
      rw [h0] at h
      simpa using h
    have hdiv := hshift.div_const (z ^ 2)
    have hterm : ∀ n : ℕ,
        z ^ (2 * (n + 1) + 1) / (((2 * (n + 1) + 1).factorial : ℕ) : ℂ) / z ^ 2
          = z ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℂ) := by
      intro n
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega]
      rw [show 2 * n + 3 = 2 + (2 * n + 1) by omega, pow_add]
      field_simp
    have htsum_eq : (Complex.sinh z - z) / z ^ 2
        = ∑' n : ℕ, z ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℂ) := by
      rw [← hdiv.tsum_eq]
      exact tsum_congr hterm
    have hgeom : Summable (fun n : ℕ => ‖z‖ * (1 / 2 : ℝ) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left ‖z‖
    have h3 : ∀ n : ℕ, ‖z‖ ^ (2 * n) ≤ (1 / 2 : ℝ) ^ n := by
      intro n
      have hzsq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        simpa [sq] using mul_self_le_mul_self (norm_nonneg z) hzle
      calc ‖z‖ ^ (2 * n) = (‖z‖ ^ 2) ^ n := pow_mul ‖z‖ 2 n
        _ ≤ ((1 / 2 : ℝ) ^ 2) ^ n := pow_le_pow_left₀ (by positivity) hzsq n
        _ = (1 / 2 : ℝ) ^ (2 * n) := (pow_mul (1 / 2 : ℝ) 2 n).symm
        _ ≤ (1 / 2 : ℝ) ^ n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hmid_summ : Summable (fun n : ℕ => ‖z‖ ^ (2 * n + 1)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeom
      calc ‖z‖ ^ (2 * n + 1) = ‖z‖ * ‖z‖ ^ (2 * n) := by rw [pow_succ']
        _ ≤ ‖z‖ * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left (h3 n) (norm_nonneg z)
    have hnorm_summ : Summable (fun n : ℕ =>
        ‖z‖ ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmid_summ
      exact div_le_self (by positivity)
        (by exact_mod_cast Nat.factorial_pos (2 * n + 3))
    have hnorm_summ' : Summable (fun n : ℕ =>
        ‖z ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℂ)‖) :=
      hnorm_summ.congr (fun n => by simp [norm_div, norm_pow])
    calc ‖(Complex.sinh z - z) / z ^ 2‖
        = ‖∑' n : ℕ, z ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℂ)‖ := by
          rw [htsum_eq]
      _ ≤ ∑' n : ℕ, ‖z ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℂ)‖ :=
          norm_tsum_le_tsum_norm hnorm_summ'
      _ = ∑' n : ℕ, ‖z‖ ^ (2 * n + 1) / (((2 * n + 3).factorial : ℕ) : ℝ) := by
          congr 1
          ext n
          simp [norm_div, norm_pow]
      _ ≤ ∑' n : ℕ, ‖z‖ ^ (2 * n + 1) :=
          Summable.tsum_le_tsum (fun n => div_le_self (by positivity)
            (by exact_mod_cast Nat.factorial_pos (2 * n + 3))) hnorm_summ hmid_summ
      _ ≤ ∑' n : ℕ, ‖z‖ * (1 / 2 : ℝ) ^ n := by
          refine Summable.tsum_le_tsum (fun n => ?_) hmid_summ hgeom
          calc ‖z‖ ^ (2 * n + 1) = ‖z‖ * ‖z‖ ^ (2 * n) := by rw [pow_succ']
            _ ≤ ‖z‖ * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left (h3 n) (norm_nonneg z)
      _ = 2 * ‖z‖ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1)]
          norm_num
          ring
  · have h : Filter.Tendsto (fun z : ℂ => 2 * ‖z‖) (𝓝 (0 : ℂ)) (𝓝 0) := by
      have hcont : Continuous fun z : ℂ => 2 * ‖z‖ := continuous_const.mul continuous_norm
      simpa using hcont.tendsto 0
    exact h.mono_left nhdsWithin_le_nhds
theorem gammaFull_decomp {z : ℂ} (hsinh : Complex.sinh (z / 2) ≠ 0)
    (hcosh : Complex.cosh (z / 2) ≠ 0) :
    gammaFull z = -((Complex.sinh (z / 2) - z / 2) / (z / 2) ^ 2
        * ((z / 2) / (4 * Complex.sinh (z / 2))))
      + 1 / (4 * Complex.cosh (z / 2)) := by
  have hz : z ≠ 0 := by
    rintro rfl
    simp at hsinh
  have hs2 : Complex.sinh z = 2 * Complex.sinh (z / 2) * Complex.cosh (z / 2) := by
    have h := Complex.sinh_add (z / 2) (z / 2)
    rw [show z / 2 + z / 2 = z by ring] at h
    rw [h]; ring
  have he : Complex.exp (z / 2) = Complex.cosh (z / 2) + Complex.sinh (z / 2) :=
    (Complex.cosh_add_sinh (z / 2)).symm
  unfold gammaFull
  rw [hs2, he]
  field_simp
  ring
theorem tendsto_gammaFull_zero :
    Filter.Tendsto gammaFull (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 4)) := by
  have hhalf : Filter.Tendsto (fun z : ℂ => z / 2) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun z : ℂ => z / 2 := continuous_id.div_const 2
      have hct := (hc.tendsto (0 : ℂ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      simpa using hct
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact div_ne_zero hz (by norm_num)
  have hsinh_div : Filter.Tendsto (fun u : ℂ => Complex.sinh u / u)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (Complex.hasDerivAt_sinh 0).tendsto_slope
    rw [slope_fun_def_field] at h
    simpa using h
  have hratio : Filter.Tendsto (fun u : ℂ => u / Complex.sinh u)
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := hsinh_div.inv₀ one_ne_zero
    simpa [inv_div] using h
  have hsinh_ne : ∀ᶠ u : ℂ in 𝓝[≠] (0 : ℂ), Complex.sinh u ≠ 0 := by
    have h := hsinh_div.eventually_ne one_ne_zero
    filter_upwards [self_mem_nhdsWithin, h] with u hu hne
    intro h0
    exact hne (by rw [h0, zero_div])
  have hcosh_ne : ∀ᶠ u : ℂ in 𝓝[≠] (0 : ℂ), Complex.cosh u ≠ 0 :=
    ((Complex.continuous_cosh.continuousAt (x := 0)).eventually_ne
      (by rw [Complex.cosh_zero]; norm_num)).filter_mono nhdsWithin_le_nhds
  have hfirst : Filter.Tendsto
      (fun z : ℂ => (Complex.sinh (z / 2) - z / 2) / (z / 2) ^ 2
        * ((z / 2) / (4 * Complex.sinh (z / 2)))) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun z : ℂ => (Complex.sinh (z / 2) - z / 2) / (z / 2) ^ 2)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      tendsto_sinh_sub_id_div_sq.comp hhalf
    have h2 : Filter.Tendsto (fun z : ℂ => (z / 2) / (4 * Complex.sinh (z / 2)))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 4)) := by
      have h := (hratio.comp hhalf).div_const 4
      convert h using 1
      ext z
      rw [div_div]
      simp only [Function.comp_apply]
      ring_nf
    have hmul := h1.mul h2
    simpa using hmul
  have hsecond : Filter.Tendsto (fun z : ℂ => 1 / (4 * Complex.cosh (z / 2)))
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 4)) := by
    have hc : Filter.Tendsto (fun z : ℂ => Complex.cosh (z / 2)) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
      have hcon : Continuous fun z : ℂ => Complex.cosh (z / 2) :=
        Complex.continuous_cosh.comp (continuous_id.div_const 2)
      simpa [Complex.cosh_zero] using (hcon.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
    have h := (Filter.Tendsto.const_mul (4 : ℂ) hc).inv₀ (by norm_num : (4 : ℂ) * 1 ≠ 0)
    simpa [one_div] using h
  have hdecomp : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      gammaFull z = -((Complex.sinh (z / 2) - z / 2) / (z / 2) ^ 2
          * ((z / 2) / (4 * Complex.sinh (z / 2))))
        + 1 / (4 * Complex.cosh (z / 2)) := by
    filter_upwards [hhalf.eventually hsinh_ne, hhalf.eventually hcosh_ne] with z hsinh hcosh
    exact gammaFull_decomp hsinh hcosh
  have hlim : Filter.Tendsto
      (fun z : ℂ => -((Complex.sinh (z / 2) - z / 2) / (z / 2) ^ 2
          * ((z / 2) / (4 * Complex.sinh (z / 2))))
        + 1 / (4 * Complex.cosh (z / 2))) (𝓝[≠] (0 : ℂ)) (𝓝 (1 / 4)) := by
    have h := hfirst.neg.add hsecond
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [hdecomp] with z hz
  exact hz.symm
theorem sinh_ne_zero_of_norm_lt_pi {z : ℂ} (hz0 : 0 < ‖z‖) (hz : ‖z‖ < Real.pi) :
    Complex.sinh z ≠ 0 := by
  intro h
  have hdef : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 := rfl
  have hexp : Complex.exp z = Complex.exp (-z) := by
    have h' : (Complex.exp z - Complex.exp (-z)) / 2 = 0 := by
      rw [← hdef]; exact h
    rcases (div_eq_zero_iff.mp h') with h'' | h''
    · linear_combination h''
    · norm_num at h''
  have h2 : Complex.exp (2 * z) = 1 := by
    have hmul : Complex.exp z * Complex.exp z = Complex.exp z * Complex.exp (-z) := by
      rw [hexp]
    rw [show 2 * z = z + z by ring, Complex.exp_add, hmul, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  have hz' : z = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    have h' := congrArg (fun w : ℂ => w / 2) hn
    field_simp at h'
    simpa [mul_assoc, mul_comm, mul_left_comm] using h'
  have hnorm : ‖z‖ = |(n : ℝ)| * Real.pi := by
    rw [hz']
    simp [Complex.norm_I, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc]
  have hlt : |(n : ℝ)| * Real.pi < Real.pi := by
    rw [← hnorm]; exact hz
  have : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
  have hn0 : n = 0 := by
    have h1 : -1 < ((n : ℤ) : ℝ) ∧ ((n : ℤ) : ℝ) < 1 := abs_lt.mp this
    have h2 : n < 1 := by exact_mod_cast h1.2
    have h3 : -1 < n := by exact_mod_cast h1.1
    omega
  rw [hn0] at hz'
  simp at hz'
  rw [hz'] at hz0
  simp at hz0
noncomputable def gammaExt (z : ℂ) : ℂ := if z = 0 then 1 / 4 else gammaFull z
theorem gammaExt_of_ne {z : ℂ} (hz : z ≠ 0) : gammaExt z = gammaFull z := if_neg hz
theorem continuousAt_gammaExt_zero : ContinuousAt gammaExt 0 := by
  rw [continuousAt_iff_punctured_nhds,
    show gammaExt 0 = 1 / 4 by rw [gammaExt, if_pos rfl]]
  refine tendsto_gammaFull_zero.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (gammaExt_of_ne (by simpa using hz)).symm
theorem differentiableAt_gammaFull {z : ℂ} (hz : z ≠ 0) (hsinh : Complex.sinh z ≠ 0) :
    DifferentiableAt ℂ gammaFull z := by
  unfold gammaFull
  refine DifferentiableAt.sub ?_ ?_
  · refine DifferentiableAt.div ?_ ?_ (mul_ne_zero two_ne_zero hsinh)
    · exact DifferentiableAt.comp z (Complex.differentiableAt_exp (𝕜 := ℂ) (x := z / 2))
        (differentiableAt_id.div_const (2 : ℂ))
    · exact (differentiableAt_const (2 : ℂ)).mul
        (Complex.hasDerivAt_sinh z).differentiableAt
  · exact (differentiableAt_const (1 : ℂ)).div
      ((differentiableAt_const (2 : ℂ)).mul differentiableAt_id)
      (mul_ne_zero two_ne_zero hz)
theorem differentiableAt_gammaExt {z : ℂ} (hz : z ≠ 0) (hzR : ‖z‖ < Real.pi) :
    DifferentiableAt ℂ gammaExt z := by
  have h : DifferentiableAt ℂ gammaFull z :=
    differentiableAt_gammaFull hz (sinh_ne_zero_of_norm_lt_pi (norm_pos_iff.mpr hz) hzR)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hz] with w hw
  exact gammaExt_of_ne hw
theorem continuousOn_gammaExt_closedBall :
    ContinuousOn gammaExt (Metric.closedBall (0 : ℂ) (14 / 5)) := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact continuousAt_gammaExt_zero.continuousWithinAt
  · have hnorm : ‖z‖ ≤ 14 / 5 := by
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hpi : (14 : ℝ) / 5 < Real.pi := by
      have h3 := Real.pi_gt_three
      norm_num at h3 ⊢
      linarith
    exact (differentiableAt_gammaExt hz0 (lt_of_le_of_lt hnorm hpi)).continuousAt
      |>.continuousWithinAt
theorem hasFPowerSeriesOnBall_gammaExt :
    HasFPowerSeriesOnBall gammaExt (cauchyPowerSeries gammaExt 0 ((14 : ℝ) / 5)) 0
      (14 / 5 : NNReal) :=
  Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable
    (R := (14 / 5 : NNReal)) (c := (0 : ℂ)) (f := gammaExt) (s := {0})
    (Set.countable_singleton 0) continuousOn_gammaExt_closedBall
    (fun z hz => by
      have hz0 : z ≠ 0 := by
        simpa using hz.2
      have hzn : ‖z‖ < (14 : ℝ) / 5 := by
        simpa [Metric.mem_ball, dist_zero_right] using hz.1
      have hpi : (14 : ℝ) / 5 < Real.pi := by
        have h3 := Real.pi_gt_three
        norm_num at h3 ⊢
        linarith
      exact differentiableAt_gammaExt hz0 (lt_of_lt_of_le hzn hpi.le))
    (by
      show (0 : ℝ) < ((14 / 5 : NNReal) : ℝ)
      norm_num)
end Y7Density
end
end Inline_Y7_GammaLimit
section Inline_Y7_Legendre
noncomputable section
open Polynomial
open MeasureTheory
namespace Y7Legendre
def legP (n : ℕ) : ℝ[X] :=
  C ((1 : ℝ) / ((2 : ℝ) ^ n * n.factorial)) *
    (Polynomial.derivative^[n]) ((X ^ 2 - C 1) ^ n)
@[simp]
lemma legP_zero : legP 0 = 1 := by
  simp [legP]
def J1 (P : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  C ((2 * (n : ℝ) + 1)⁻¹) * (P (n + 1) - P (n - 1))
def J (P : ℕ → ℝ[X]) : ℕ → ℕ → ℝ[X]
  | 0, _ => 0
  | 1, n => J1 P n
  | (r + 2), n =>
      C ((2 * (n : ℝ) + 1)⁻¹) * (J P (r + 1) (n + 1) - J P (r + 1) (n - 1))
@[simp]
lemma J_zero (P : ℕ → ℝ[X]) (n : ℕ) : J P 0 n = 0 := rfl
lemma J_one (P : ℕ → ℝ[X]) (n : ℕ) :
    J P 1 n = C ((2 * (n : ℝ) + 1)⁻¹) * (P (n + 1) - P (n - 1)) := rfl
lemma J_succ (P : ℕ → ℝ[X]) (r n : ℕ) :
    J P (r + 2) n =
      C ((2 * (n : ℝ) + 1)⁻¹) * (J P (r + 1) (n + 1) - J P (r + 1) (n - 1)) := rfl
lemma J_one_div (P : ℕ → ℝ[X]) (n : ℕ) :
    J P 1 n = (P (n + 1) - P (n - 1)) * C ((2 * (n : ℝ) + 1)⁻¹) := by
  rw [J_one]
  ring
lemma J_succ_eq_div (P : ℕ → ℝ[X]) (r n : ℕ) :
    J P (r + 2) n =
      (J P (r + 1) (n + 1) - J P (r + 1) (n - 1)) * C ((2 * (n : ℝ) + 1)⁻¹) := by
  rw [J_succ]
  ring
lemma derivative_comp_neg_X (p : ℝ[X]) :
    derivative (p.comp (-X)) = -(p.derivative.comp (-X)) := by
  rw [derivative_comp]
  simp
lemma iterate_derivative_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    derivative^[k] (p.comp (-X)) = (-1 : ℝ) ^ k • (derivative^[k] p).comp (-X) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih => simp [ih (derivative p), derivative_comp_neg_X, pow_succ]
lemma sq_sub_one_comp_neg_X (n : ℕ) :
    ((X ^ 2 - C (1 : ℝ)) ^ n).comp (-X) = (X ^ 2 - C (1 : ℝ)) ^ n := by
  rw [pow_comp, sub_comp, pow_comp, X_comp, C_comp]
  congr 1
  ring
lemma iterate_derivative_comp_neg_X_inv (p : ℝ[X]) (k : ℕ) :
    (derivative^[k] p).comp (-X) = (-1 : ℝ) ^ k • derivative^[k] (p.comp (-X)) := by
  have h := iterate_derivative_comp_neg_X p k
  calc (derivative^[k] p).comp (-X)
      = (-1 : ℝ) ^ k • ((-1 : ℝ) ^ k • (derivative^[k] p).comp (-X)) := by
        rw [smul_smul, ← pow_add]
        have : (-1 : ℝ) ^ (k + k) = 1 := Even.neg_one_pow ⟨k, rfl⟩
        rw [this, one_smul]
    _ = (-1 : ℝ) ^ k • derivative^[k] (p.comp (-X)) := by rw [← h]
theorem legP_comp_neg_X (n : ℕ) :
    (legP n).comp (-X) = (-1 : ℝ) ^ n • legP n := by
  unfold legP
  rw [mul_comp, C_comp, iterate_derivative_comp_neg_X_inv, sq_sub_one_comp_neg_X,
    mul_smul_comm]
end Y7Legendre
namespace Y7Legendre
lemma natDegree_sq_sub_one : (X ^ 2 - C (1 : ℝ)).natDegree = 2 := by
  rw [natDegree_sub_eq_left_of_natDegree_lt (show (C (1 : ℝ)).natDegree <
    (X ^ 2 : ℝ[X]).natDegree by
    rw [natDegree_C, natDegree_X_pow]
    norm_num)]
  rw [natDegree_X_pow]
lemma monic_sq_sub_one : (X ^ 2 - C (1 : ℝ)).Monic :=
  monic_X_pow_sub_C (1 : ℝ) (by norm_num)
lemma monic_sq_sub_one_pow (n : ℕ) : ((X ^ 2 - C (1 : ℝ)) ^ n).Monic :=
  monic_sq_sub_one.pow n
lemma coeff_sq_sub_one_pow_top (n : ℕ) :
    ((X ^ 2 - C (1 : ℝ)) ^ n).coeff (2 * n) = 1 := by
  have hdeg : ((X ^ 2 - C (1 : ℝ)) ^ n).natDegree = 2 * n := by
    rw [natDegree_pow, natDegree_sq_sub_one]
    ring
  rw [← hdeg, coeff_natDegree]
  exact monic_sq_sub_one_pow n
lemma coeff_sq_sub_one_pow_top' (n : ℕ) :
    ((X ^ 2 - C (1 : ℝ)) ^ n).coeff (n + n) = 1 := by
  rw [show n + n = 2 * n by omega, coeff_sq_sub_one_pow_top n]
theorem natDegree_legP (n : ℕ) : (legP n).natDegree = n := by
  have hc : (1 : ℝ) / ((2 : ℝ) ^ n * n.factorial) ≠ 0 := by positivity
  have hcoeff : ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).coeff n ≠ 0 := by
    rw [coeff_iterate_derivative, nsmul_eq_mul]
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega : n ≤ n + n)).ne'
    · rw [show n + n = 2 * n by omega, coeff_sq_sub_one_pow_top n]
      norm_num
  unfold legP
  refine le_antisymm ?_ ?_
  · calc ((C (1 / ((2 : ℝ) ^ n * n.factorial)) *
          (Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).natDegree)
        ≤ ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).natDegree :=
          natDegree_C_mul_le _ _
      _ ≤ ((X ^ 2 - C (1 : ℝ)) ^ n).natDegree - n :=
          natDegree_iterate_derivative _ _
      _ = n := by rw [natDegree_pow, natDegree_sq_sub_one]; omega
  · by_contra h
    have hlt : (C (1 / ((2 : ℝ) ^ n * n.factorial)) *
        (Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).natDegree < n :=
      Nat.lt_of_not_le h
    have hzero := coeff_eq_zero_of_natDegree_lt hlt
    rw [coeff_C_mul] at hzero
    exact mul_ne_zero hc hcoeff hzero
lemma coeff_legP_self_ne_zero (n : ℕ) : (legP n).coeff n ≠ 0 := by
  unfold legP
  rw [coeff_C_mul]
  apply mul_ne_zero
  · exact (by positivity : (1 : ℝ) / ((2 : ℝ) ^ n * n.factorial) ≠ 0)
  · rw [coeff_iterate_derivative, nsmul_eq_mul]
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega : n ≤ n + n)).ne'
    · rw [show n + n = 2 * n by omega, coeff_sq_sub_one_pow_top n]
      norm_num
lemma legP_ne_zero (n : ℕ) : legP n ≠ 0 := by
  intro h
  have := coeff_legP_self_ne_zero n
  rw [h, coeff_zero] at this
  exact this rfl
lemma leadingCoeff_legP_ne_zero (n : ℕ) : (legP n).leadingCoeff ≠ 0 := by
  rw [leadingCoeff, natDegree_legP]
  exact coeff_legP_self_ne_zero n
theorem coeff_legP_self (n : ℕ) :
    (legP n).coeff n = ((2 * n).factorial : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ) ^ 2) := by
  have hdesc : (((n + n).descFactorial n : ℕ) : ℝ) =
      ((2 * n).factorial : ℝ) / (n.factorial : ℝ) := by
    rw [show n + n = 2 * n by omega, Nat.descFactorial_eq_div (by omega : n ≤ 2 * n),
      show 2 * n - n = n by omega,
      Nat.cast_div (Nat.factorial_dvd_factorial (by omega : n ≤ 2 * n))]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  unfold legP
  rw [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, coeff_sq_sub_one_pow_top' n, mul_one,
    hdesc]
  ring_nf
theorem eval_one_legP (n : ℕ) : (legP n).eval 1 = 1 := by
  have hcomp : taylor (1 : ℝ) ((X ^ 2 - C 1 : ℝ[X]) ^ n) = (X * (X + C 2)) ^ n := by
    rw [taylor_apply, pow_comp]
    congr 1
    rw [sub_comp, pow_comp, X_comp, C_comp]
    simp only [map_one, map_ofNat]
    ring
  have hcoeff : (taylor (1 : ℝ) ((X ^ 2 - C 1 : ℝ[X]) ^ n)).coeff n = (2 : ℝ) ^ n := by
    rw [hcomp, mul_pow]
    have h0 : ((X ^ n : ℝ[X]) * (X + C 2) ^ n).coeff (0 + n) =
        ((X + C 2 : ℝ[X]) ^ n).coeff 0 :=
      coeff_X_pow_mul ((X + C 2 : ℝ[X]) ^ n) n 0
    rw [zero_add] at h0
    rw [h0, coeff_zero_eq_eval_zero]
    simp
  have hderiv : ((Polynomial.derivative^[n]) ((X ^ 2 - C 1 : ℝ[X]) ^ n)).eval (1 : ℝ) =
      (n.factorial : ℝ) * (2 : ℝ) ^ n := by
    have h1 : (Polynomial.derivative^[n]) ((X ^ 2 - C 1 : ℝ[X]) ^ n) =
        (n.factorial : ℕ) • (Polynomial.hasseDeriv n ((X ^ 2 - C 1 : ℝ[X]) ^ n)) := by
      have h := congr_fun (Polynomial.factorial_smul_hasseDeriv (k := n) (R := ℝ))
        ((X ^ 2 - C 1 : ℝ[X]) ^ n)
      simpa only [LinearMap.smul_apply] using h.symm
    have h2 : ((Polynomial.derivative^[n]) ((X ^ 2 - C 1 : ℝ[X]) ^ n)).eval 1 =
        (n.factorial : ℝ) * (Polynomial.hasseDeriv n ((X ^ 2 - C 1 : ℝ[X]) ^ n)).eval 1 := by
      rw [h1, Polynomial.eval_smul, nsmul_eq_mul]
    have h3 : (Polynomial.hasseDeriv n ((X ^ 2 - C 1 : ℝ[X]) ^ n)).eval 1 =
        (taylor (1 : ℝ) ((X ^ 2 - C 1 : ℝ[X]) ^ n)).coeff n := by
      rw [Polynomial.taylor_coeff]
    rw [h2, h3, hcoeff]
  unfold legP
  rw [eval_mul, eval_C, hderiv]
  field_simp
lemma eval_legP_neg (n : ℕ) (x : ℝ) :
    (legP n).eval (-x) = (-1 : ℝ) ^ n * (legP n).eval x := by
  have h := congr_arg (fun p : ℝ[X] => p.eval x) (legP_comp_neg_X n)
  simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_smul,
    smul_eq_mul] using h
theorem integral_pow_mul_legP_eq_zero_of_odd (m n : ℕ) (hodd : Odd (m + n)) :
    (∫ x in (-1 : ℝ)..1, x ^ m * (legP n).eval x) = 0 := by
  have hodd_f : ∀ x : ℝ,
      (-x) ^ m * (legP n).eval (-x) = -(x ^ m * (legP n).eval x) := by
    intro x
    rw [eval_legP_neg, neg_pow]
    calc ((-1 : ℝ) ^ m * x ^ m) * ((-1 : ℝ) ^ n * (legP n).eval x)
        = ((-1 : ℝ) ^ m * (-1 : ℝ) ^ n) * (x ^ m * (legP n).eval x) := by ring
      _ = (-1 : ℝ) ^ (m + n) * (x ^ m * (legP n).eval x) := by rw [← pow_add]
      _ = -(x ^ m * (legP n).eval x) := by rw [hodd.neg_one_pow]; ring
  have hcont : Continuous (fun x : ℝ => x ^ m * (legP n).eval x) :=
    (continuous_id.pow m).mul (legP n).continuous
  have hint0 : IntervalIntegrable (fun x : ℝ => x ^ m * (legP n).eval x) volume (-1) 0 :=
    hcont.intervalIntegrable (-1) 0
  have hint1 : IntervalIntegrable (fun x : ℝ => x ^ m * (legP n).eval x) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => x ^ m * (legP n).eval x) (a := (-1 : ℝ)) (b := 0)
  have hneg : (∫ x in (-1 : ℝ)..0, (-x) ^ m * (legP n).eval (-x)) =
      -(∫ x in (-1 : ℝ)..0, x ^ m * (legP n).eval x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact hodd_f x
  rw [hneg] at hcomp
  simp only [neg_zero, neg_neg] at hcomp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
  rw [← hsplit]
  linarith
lemma integral_eval_eq_zero_of_comp_neg_neg (p : ℝ[X]) (hp : p.comp (-X) = -p) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = 0 := by
  have hodd_f : ∀ x : ℝ, p.eval (-x) = -(p.eval x) := by
    intro x
    have h := congr_arg (fun q : ℝ[X] => q.eval x) hp
    simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using h
  have hcont : Continuous (fun x : ℝ => p.eval x) := p.continuous
  have hint0 : IntervalIntegrable (fun x : ℝ => p.eval x) volume (-1) 0 :=
    hcont.intervalIntegrable (-1) 0
  have hint1 : IntervalIntegrable (fun x : ℝ => p.eval x) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hcomp := intervalIntegral.integral_comp_neg (f := fun x : ℝ => p.eval x)
    (a := (-1 : ℝ)) (b := 0)
  have hneg : (∫ x in (-1 : ℝ)..0, p.eval (-x)) = -(∫ x in (-1 : ℝ)..0, p.eval x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact hodd_f x
  rw [hneg] at hcomp
  simp only [neg_zero, neg_neg] at hcomp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
  rw [← hsplit]
  linarith
lemma legP_mul_comp_neg_X (m n : ℕ) :
    (legP m * legP n).comp (-X) = (-1 : ℝ) ^ (m + n) • (legP m * legP n) := by
  rw [mul_comp, legP_comp_neg_X, legP_comp_neg_X, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← pow_add]
theorem integral_legP_mul_legP_eq_zero_of_odd (m n : ℕ) (hodd : Odd (m + n)) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) = 0 := by
  have hp : (legP m * legP n).comp (-X) = -(legP m * legP n) := by
    rw [legP_mul_comp_neg_X, hodd.neg_one_pow, neg_one_smul]
  have h := integral_eval_eq_zero_of_comp_neg_neg (legP m * legP n) hp
  simpa only [Polynomial.eval_mul] using h
def phi (n : ℕ) : ℝ[X] :=
  C (Real.sqrt ((2 * (n : ℝ) + 1) / 2)) * legP n
lemma phi_comp_neg_X (n : ℕ) :
    (phi n).comp (-X) = (-1 : ℝ) ^ n • phi n := by
  unfold phi
  rw [mul_comp, C_comp, legP_comp_neg_X, mul_smul_comm]
lemma phi_eval_one (n : ℕ) :
    (phi n).eval 1 = Real.sqrt ((2 * (n : ℝ) + 1) / 2) := by
  unfold phi
  rw [eval_mul, eval_C, eval_one_legP, mul_one]
lemma phi_eval_neg_one (n : ℕ) :
    (phi n).eval (-1) = (-1 : ℝ) ^ n * Real.sqrt ((2 * (n : ℝ) + 1) / 2) := by
  have h := congr_arg (fun p : ℝ[X] => p.eval 1) (phi_comp_neg_X n)
  simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_smul,
    smul_eq_mul, phi_eval_one] using h
lemma integral_eval_eq_two_mul_integral_of_comp_neg_self (p : ℝ[X])
    (hp : p.comp (-X) = p) :
    (∫ x in (-1 : ℝ)..1, p.eval x) = 2 * ∫ x in (0 : ℝ)..1, p.eval x := by
  have heven_f : ∀ x : ℝ, p.eval (-x) = p.eval x := by
    intro x
    have h := congr_arg (fun q : ℝ[X] => q.eval x) hp
    simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using h
  have hcont : Continuous (fun x : ℝ => p.eval x) := p.continuous
  have hint0 : IntervalIntegrable (fun x : ℝ => p.eval x) volume (-1) 0 :=
    hcont.intervalIntegrable (-1) 0
  have hint1 : IntervalIntegrable (fun x : ℝ => p.eval x) volume 0 1 :=
    hcont.intervalIntegrable 0 1
  have hcomp := intervalIntegral.integral_comp_neg (f := fun x : ℝ => p.eval x)
    (a := (-1 : ℝ)) (b := 0)
  have hcongr : (∫ x in (-1 : ℝ)..0, p.eval (-x)) = ∫ x in (-1 : ℝ)..0, p.eval x := by
    apply intervalIntegral.integral_congr
    intro x _
    exact heven_f x
  rw [hcongr] at hcomp
  simp only [neg_zero, neg_neg] at hcomp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
  rw [← hsplit]
  linarith
theorem integral_phi_sq (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (phi n).eval x * (phi n).eval x) =
      ((2 * (n : ℝ) + 1) / 2) *
        (∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP n).eval x) := by
  have hpoint : ∀ x : ℝ,
      (phi n).eval x * (phi n).eval x =
        ((2 * (n : ℝ) + 1) / 2) * ((legP n).eval x * (legP n).eval x) := by
    intro x
    have hs : Real.sqrt ((2 * (n : ℝ) + 1) / 2) ^ 2 = (2 * (n : ℝ) + 1) / 2 :=
      Real.sq_sqrt (by positivity)
    unfold phi
    rw [eval_mul, eval_C]
    rw [show Real.sqrt ((2 * (n : ℝ) + 1) / 2) * (legP n).eval x *
        (Real.sqrt ((2 * (n : ℝ) + 1) / 2) * (legP n).eval x) =
        (Real.sqrt ((2 * (n : ℝ) + 1) / 2)) ^ 2 * ((legP n).eval x) ^ 2 by ring]
    rw [hs]
    ring
  calc (∫ x in (-1 : ℝ)..1, (phi n).eval x * (phi n).eval x)
      = ∫ x in (-1 : ℝ)..1,
          ((2 * (n : ℝ) + 1) / 2) * ((legP n).eval x * (legP n).eval x) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hpoint x
    _ = ((2 * (n : ℝ) + 1) / 2) *
          (∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP n).eval x) := by
        rw [intervalIntegral.integral_const_mul]
lemma legP_sq_comp_neg_X (n : ℕ) :
    (legP n * legP n).comp (-X) = legP n * legP n := by
  rw [legP_mul_comp_neg_X]
  have h : (-1 : ℝ) ^ (n + n) = 1 := Even.neg_one_pow ⟨n, rfl⟩
  rw [h, one_smul]
theorem integral_legP_sq_eq_two_mul_integral_zero_one (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP n).eval x) =
      2 * ∫ x in (0 : ℝ)..1, (legP n).eval x * (legP n).eval x := by
  have h := integral_eval_eq_two_mul_integral_of_comp_neg_self (legP n * legP n)
    (legP_sq_comp_neg_X n)
  simpa only [Polynomial.eval_mul] using h
end Y7Legendre
namespace Y7Parseval
open Matrix
theorem parseval_remainder_posSemidef {ι m n p : Type*} [Fintype ι] [Fintype m]
    [Fintype n] [Fintype p] (K2 : Matrix ι ι ℝ) (K : Matrix m ι ℝ) (B : Matrix n ι ℝ)
    (C : Matrix p ι ℝ) (h : K2 = Kᴴ * K + Bᴴ * B + Cᴴ * C) :
    (K2 - Kᴴ * K - Bᴴ * B).PosSemidef := by
  rw [h]
  have hsub : Kᴴ * K + Bᴴ * B + Cᴴ * C - Kᴴ * K - Bᴴ * B = Cᴴ * C := by
    abel
  rw [hsub]
  exact Matrix.posSemidef_conjTranspose_mul_self C
end Y7Parseval
open Polynomial MeasureTheory
set_option maxHeartbeats 800000
namespace Y7Rodrigues
open Y7Legendre
lemma integral_derivative_mul (q p : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, (Polynomial.derivative q).eval x * p.eval x) =
      q.eval 1 * p.eval 1 - q.eval (-1) * p.eval (-1) -
        ∫ x in (-1 : ℝ)..1, q.eval x * (Polynomial.derivative p).eval x := by
  have hderiv : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y : ℝ => (q * p).eval y)
        ((Polynomial.derivative q).eval x * p.eval x +
          q.eval x * (Polynomial.derivative p).eval x) x := by
    intro x _
    have h := (q * p).hasDerivAt x
    have hder : ((q * p).derivative).eval x =
        (Polynomial.derivative q).eval x * p.eval x +
          q.eval x * (Polynomial.derivative p).eval x := by
      rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
    rw [hder] at h
    exact h
  have hcont : ContinuousOn (fun y : ℝ => (q * p).eval y) (Set.Icc (-1 : ℝ) 1) :=
    (q * p).continuous.continuousOn
  have hint : IntervalIntegrable
      (fun y : ℝ => (Polynomial.derivative q).eval y * p.eval y +
        q.eval y * (Polynomial.derivative p).eval y) volume (-1) 1 :=
    (((Polynomial.derivative q).continuous.mul p.continuous).add
      (q.continuous.mul (Polynomial.derivative p).continuous)).intervalIntegrable (-1) 1
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (-1 : ℝ)) (b := 1)
    (by norm_num) hcont hderiv hint
  rw [Polynomial.eval_mul, Polynomial.eval_mul] at hF
  have h1 : IntervalIntegrable
      (fun y : ℝ => (Polynomial.derivative q).eval y * p.eval y) volume (-1) 1 :=
    ((Polynomial.derivative q).continuous.mul p.continuous).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun y : ℝ => q.eval y * (Polynomial.derivative p).eval y) volume (-1) 1 :=
    (q.continuous.mul (Polynomial.derivative p).continuous).intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_add h1 h2] at hF
  linarith
lemma eval_iterate_derivative_sq_sub_one_pow_eq_zero (n k : ℕ) (hk : k < n) :
    ((Polynomial.derivative^[k]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval (1 : ℝ) = 0 := by
  obtain ⟨h, hh⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow (X ^ 2 - C (1 : ℝ)) n k
  rw [hh, Polynomial.eval_mul]
  have hroot : (((X ^ 2 - C (1 : ℝ)) ^ (n - k))).eval (1 : ℝ) = 0 := by
    rw [Polynomial.eval_pow]
    have h1 : ((X ^ 2 - C (1 : ℝ))).eval (1 : ℝ) = 0 := by
      simp
    rw [h1, zero_pow (by omega : n - k ≠ 0)]
  rw [hroot, zero_mul]
lemma eval_iterate_derivative_sq_sub_one_pow_eq_zero_neg (n k : ℕ) (hk : k < n) :
    ((Polynomial.derivative^[k]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval (-1 : ℝ) = 0 := by
  obtain ⟨h, hh⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow (X ^ 2 - C (1 : ℝ)) n k
  rw [hh, Polynomial.eval_mul]
  have hroot : (((X ^ 2 - C (1 : ℝ)) ^ (n - k))).eval (-1 : ℝ) = 0 := by
    rw [Polynomial.eval_pow]
    have h1 : ((X ^ 2 - C (1 : ℝ))).eval (-1 : ℝ) = 0 := by
      simp
    rw [h1, zero_pow (by omega : n - k ≠ 0)]
  rw [hroot, zero_mul]
lemma integral_iterate_derivative_sq_sub_one_pow_mul (n : ℕ) :
    ∀ k ≤ n, ∀ p : ℝ[X],
      (∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[k]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x * p.eval x) =
        (-1 : ℝ) ^ k * ∫ x in (-1 : ℝ)..1,
          ((X ^ 2 - C (1 : ℝ)) ^ n).eval x *
            ((Polynomial.derivative^[k]) p).eval x := by
  intro k
  induction k with
  | zero =>
      intro _ p
      simp
  | succ k ih =>
      intro hk p
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hb1 : ((Polynomial.derivative^[k]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval (1 : ℝ) = 0 :=
        eval_iterate_derivative_sq_sub_one_pow_eq_zero n k (by omega)
      have hbm1 : ((Polynomial.derivative^[k]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval (-1 : ℝ) = 0 :=
        eval_iterate_derivative_sq_sub_one_pow_eq_zero_neg n k (by omega)
      rw [Function.iterate_succ_apply', integral_derivative_mul]
      rw [hb1, hbm1]
      rw [ih hk' (Polynomial.derivative p), ← Function.iterate_succ_apply, pow_succ]
      ring
lemma iterate_derivative_legP_self (n : ℕ) :
    (Polynomial.derivative^[n]) (legP n) =
      C ((n.factorial : ℝ) * (legP n).coeff n) := by
  have h2 : Polynomial.hasseDeriv n (legP n) = C ((legP n).coeff n) := by
    have h := Polynomial.hasseDeriv_natDegree_eq_C (f := legP n)
    rwa [natDegree_legP, leadingCoeff, natDegree_legP] at h
  calc (Polynomial.derivative^[n]) (legP n)
      = (n.factorial : ℕ) • (Polynomial.hasseDeriv n (legP n)) := by
        simpa only [LinearMap.smul_apply] using
          (congr_fun (Polynomial.factorial_smul_hasseDeriv (k := n) (R := ℝ))
            (legP n)).symm
    _ = C ((n.factorial : ℝ) * (legP n).coeff n) := by
        rw [h2, nsmul_eq_mul, ← C_eq_natCast, ← C_mul]
lemma integral_one_sub_sq_pow_succ (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((1 - x ^ 2) ^ (n + 1))) =
      (2 * ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) *
        (∫ x in (-1 : ℝ)..1, ((1 - x ^ 2) ^ n)) := by
  have hderiv : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1))
        ((1 - x ^ 2) ^ (n + 1) -
          2 * ((n : ℝ) + 1) * (x ^ 2 * (1 - x ^ 2) ^ n)) x := by
    intro x _
    have hg : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      have h0 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).pow 2)
      refine h0.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · norm_num
    have hp : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ (n + 1))
        ((n + 1 : ℕ) * (1 - x ^ 2) ^ n * (-(2 * x))) x := by
      refine hg.pow (n + 1) |>.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · push_cast
        ring
    have hmul : HasDerivAt (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1))
        (1 * (1 - x ^ 2) ^ (n + 1) +
          x * ((n + 1 : ℕ) * (1 - x ^ 2) ^ n * (-(2 * x)))) x := by
      refine (hasDerivAt_id x).mul hp |>.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · simp only [id_eq]
    have hder : 1 * (1 - x ^ 2) ^ (n + 1) +
          x * ((n + 1 : ℕ) * (1 - x ^ 2) ^ n * (-(2 * x))) =
        (1 - x ^ 2) ^ (n + 1) -
          2 * ((n : ℝ) + 1) * (x ^ 2 * (1 - x ^ 2) ^ n) := by
      push_cast
      ring
    rw [hder] at hmul
    exact hmul
  have hcont : ContinuousOn (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1))
      (Set.Icc (-1 : ℝ) 1) :=
    (by fun_prop : Continuous fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1)).continuousOn
  have hint : IntervalIntegrable
      (fun y : ℝ => (1 - y ^ 2) ^ (n + 1) -
        2 * ((n : ℝ) + 1) * (y ^ 2 * (1 - y ^ 2) ^ n)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (-1 : ℝ)) (b := 1)
    (by norm_num) hcont hderiv hint
  have hFval : (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1)) 1 -
      (fun y : ℝ => y * (1 - y ^ 2) ^ (n + 1)) (-1) = 0 := by
    norm_num [zero_pow (Nat.succ_ne_zero n)]
  rw [hFval] at hF
  have h1 : IntervalIntegrable (fun y : ℝ => (1 - y ^ 2) ^ (n + 1)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h4 : IntervalIntegrable (fun y : ℝ => (1 - y ^ 2) ^ n) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : IntervalIntegrable
      (fun y : ℝ => 2 * ((n : ℝ) + 1) * (y ^ 2 * (1 - y ^ 2) ^ n)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul] at hF
  have hx2 : (∫ y in (-1 : ℝ)..1, y ^ 2 * (1 - y ^ 2) ^ n) =
      (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ n) -
        (∫ y in (-1 : ℝ)..1, (1 - y ^ 2) ^ (n + 1)) := by
    rw [← intervalIntegral.integral_sub h4 h1]
    apply intervalIntegral.integral_congr
    intro y _
    change y ^ 2 * (1 - y ^ 2) ^ n = (1 - y ^ 2) ^ n - (1 - y ^ 2) ^ (n + 1)
    rw [show y ^ 2 = 1 - (1 - y ^ 2) by ring, sub_mul, one_mul, pow_succ']
    ring
  rw [hx2] at hF
  field_simp
  linarith
lemma integral_eval_one_sub_sq_pow_succ (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ (n + 1)).eval x) =
      (2 * ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) *
        (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x) := by
  have e1 : (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ (n + 1)).eval x) =
      ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ (n + 1) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp
  have e2 : (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ n) =
      ∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp
  rw [e1, integral_one_sub_sq_pow_succ n, e2]
theorem integral_one_sub_sq_pow (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x) =
      (2 : ℝ) ^ (2 * n + 1) * (n.factorial : ℝ) ^ 2 /
        (((2 * n + 1).factorial : ℕ) : ℝ) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [integral_eval_one_sub_sq_pow_succ n, ih]
      have hfac : (((2 * (n + 1) + 1).factorial : ℕ) : ℝ) =
          (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) *
            (((2 * n + 1).factorial : ℕ) : ℝ) := by
        have e1 : 2 * (n + 1) + 1 = 2 * n + 2 + 1 := by omega
        rw [e1, Nat.factorial_succ]
        have e2 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
        rw [e2, Nat.factorial_succ]
        push_cast
        ring
      have hfac2 : (((n + 1).factorial : ℕ) : ℝ) =
          ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac, hfac2]
      rw [show (2 : ℝ) ^ (2 * (n + 1) + 1) = (2 : ℝ) ^ (2 * n + 1) * 4 by
        rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by omega, pow_add]
        norm_num]
      field_simp
      ring
theorem integral_legP_mul_legP_eq_zero_of_lt (m n : ℕ) (hmn : m < n) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) = 0 := by
  have hDm : (Polynomial.derivative^[n]) (legP m) = 0 :=
    Polynomial.iterate_derivative_eq_zero (by rwa [natDegree_legP])
  have hcongr : (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        (∫ x in (-1 : ℝ)..1, (legP m).eval x *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    unfold legP
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hcongr]
  have hzero : (∫ x in (-1 : ℝ)..1, (legP m).eval x *
        ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) = 0 := by
    have hswap : (∫ x in (-1 : ℝ)..1, (legP m).eval x *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
        ∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x *
            (legP m).eval x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [hswap, integral_iterate_derivative_sq_sub_one_pow_mul n n le_rfl (legP m), hDm]
    simp
  rw [hzero, mul_zero]
theorem integral_legP_mul_legP_eq_zero_of_gt (m n : ℕ) (hmn : n < m) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) = 0 := by
  rw [show (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) =
      ∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP m).eval x from
    intervalIntegral.integral_congr (fun x _ => by ring)]
  exact integral_legP_mul_legP_eq_zero_of_lt n m hmn
theorem integral_legP_mul_legP_eq_zero_of_ne (m n : ℕ) (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · exact integral_legP_mul_legP_eq_zero_of_lt m n h
  · exact integral_legP_mul_legP_eq_zero_of_gt m n h
lemma integral_sq_sub_one_pow_eq_neg_one_pow (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x) =
      (-1 : ℝ) ^ n *
        (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x) := by
  have hpoly : ((X ^ 2 - C (1 : ℝ)) ^ n) =
      ((-1 : ℝ[X]) ^ n) * (((1 : ℝ[X]) - X ^ 2) ^ n) := by
    have h1 : (X ^ 2 - C (1 : ℝ)) = -((1 : ℝ[X]) - X ^ 2) := by
      rw [Polynomial.C_1]
      ring
    rw [h1, neg_pow]
  have hpt : ∀ x : ℝ, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x =
      (-1 : ℝ) ^ n * ((((1 : ℝ[X]) - X ^ 2) ^ n).eval x) := by
    intro x
    rw [hpoly]
    simp
  have hcongr : (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x) =
      ∫ x in (-1 : ℝ)..1, (-1 : ℝ) ^ n *
        ((((1 : ℝ[X]) - X ^ 2) ^ n).eval x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hpt x
  rw [hcongr]
  exact intervalIntegral.integral_const_mul ((-1 : ℝ) ^ n)
    (fun x : ℝ => ((((1 : ℝ[X]) - X ^ 2) ^ n)).eval x)
theorem integral_legP_sq (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP n).eval x) =
      2 / (2 * (n : ℝ) + 1) := by
  have hconst : (∫ x in (-1 : ℝ)..1, (legP n).eval x * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        (∫ x in (-1 : ℝ)..1, (legP n).eval x *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    unfold legP
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hconst]
  have hcrux : (∫ x in (-1 : ℝ)..1, (legP n).eval x *
        ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
      (-1 : ℝ) ^ n * ((n.factorial : ℝ) * (legP n).coeff n) *
        (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x) := by
    have hswap : (∫ x in (-1 : ℝ)..1, (legP n).eval x *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
        ∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x *
            (legP n).eval x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [hswap, integral_iterate_derivative_sq_sub_one_pow_mul n n le_rfl (legP n),
      iterate_derivative_legP_self n]
    have hpt : (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x *
          (C ((n.factorial : ℝ) * (legP n).coeff n)).eval x) =
        ∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x *
          ((n.factorial : ℝ) * (legP n).coeff n) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp
    rw [hpt, intervalIntegral.integral_mul_const]
    ring
  rw [hcrux, integral_sq_sub_one_pow_eq_neg_one_pow n]
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n, by ring⟩
  have hsign_mul : ∀ x : ℝ, ((-1 : ℝ) ^ n) * (((-1 : ℝ) ^ n) * x) = x := fun x => by
    rw [← mul_assoc, hsign, one_mul]
  rw [mul_assoc ((-1 : ℝ) ^ n),
    mul_left_comm ((n.factorial : ℝ) * (legP n).coeff n) ((-1 : ℝ) ^ n), hsign_mul,
    coeff_legP_self n, integral_one_sub_sq_pow n]
  have hpow : (2 : ℝ) ^ (2 * n + 1) = (2 : ℝ) ^ n * (2 : ℝ) ^ n * 2 := by
    rw [show 2 * n + 1 = n + n + 1 by omega, pow_add, pow_add]
    ring
  rw [hpow]
  have hfact : (((2 * n + 1).factorial : ℕ) : ℝ) =
      (2 * (n : ℝ) + 1) * (((2 * n).factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  field_simp
theorem integral_pow_mul_legP_reduction (m n : ℕ) (hmn : n ≤ m) :
    (∫ x in (-1 : ℝ)..1, x ^ m * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) * (-1 : ℝ) ^ n *
        ((m.descFactorial n : ℕ) : ℝ) *
        (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (m - n)) := by
  have hconst : (∫ x in (-1 : ℝ)..1, x ^ m * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        (∫ x in (-1 : ℝ)..1, x ^ m *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    unfold legP
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hconst]
  have hswap : (∫ x in (-1 : ℝ)..1, x ^ m *
        ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
      (-1 : ℝ) ^ n * ((m.descFactorial n : ℕ) : ℝ) *
        (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (m - n)) := by
    rw [show (∫ x in (-1 : ℝ)..1, x ^ m *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
        ∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x *
            (Polynomial.X ^ m).eval x from
      intervalIntegral.integral_congr (fun x _ => by
        simp only [Polynomial.eval_pow, Polynomial.eval_X]
        ring)]
    rw [integral_iterate_derivative_sq_sub_one_pow_mul n n le_rfl (Polynomial.X ^ m),
      Polynomial.iterate_derivative_X_pow_eq_C_mul]
    have hpt : (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x *
          (C ((m.descFactorial n : ℕ) : ℝ) * Polynomial.X ^ (m - n)).eval x) =
        ((m.descFactorial n : ℕ) : ℝ) *
          (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (m - n)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      ring
    rw [hpt]
    ring
  rw [hswap]
  ring
theorem integral_phi_mul_phi (m n : ℕ) (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1, (phi m).eval x * (phi n).eval x) = 0 := by
  have hred : (∫ x in (-1 : ℝ)..1, (phi m).eval x * (phi n).eval x) =
      (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
        (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    unfold phi
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hred, integral_legP_mul_legP_eq_zero_of_ne m n hmn, mul_zero]
theorem integral_phi_sq_eq_one (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (phi n).eval x * (phi n).eval x) = 1 := by
  rw [integral_phi_sq n, integral_legP_sq n]
  field_simp
theorem integral_phi_mul_phi_eq_ite (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1, (phi m).eval x * (phi n).eval x) =
      if m = n then 1 else 0 := by
  by_cases h : m = n
  · subst h
    simp [integral_phi_sq_eq_one]
  · simp [h, integral_phi_mul_phi m n h]
end Y7Rodrigues
namespace Y7Beta
open Y7Legendre
lemma integral_zero_one_sq_pow_mul_sq_succ (k n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (2 * k) * (1 - x ^ 2) ^ (n + 1)) =
      (2 * ((n : ℝ) + 1) / (2 * (k : ℝ) + 1)) *
        (∫ x in (0 : ℝ)..1, x ^ (2 * (k + 1)) * (1 - x ^ 2) ^ n) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1))
        ((2 * (k : ℝ) + 1) * (x ^ (2 * k) * (1 - x ^ 2) ^ (n + 1)) -
          2 * ((n : ℝ) + 1) * (x ^ (2 * (k + 1)) * (1 - x ^ 2) ^ n)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
        (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) x := by
      have hp := hasDerivAt_pow (2 * k + 1) x
      rw [show 2 * k + 1 - 1 = 2 * k by omega] at hp
      simpa using hp
    have hg : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      have h0 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).pow 2)
      refine h0.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · norm_num
    have h2 : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ (n + 1))
        (((n : ℝ) + 1) * (1 - x ^ 2) ^ n * (-(2 * x))) x := by
      refine hg.pow (n + 1) |>.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · push_cast
        ring
    have h12 : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1))
        ((((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) * (1 - x ^ 2) ^ (n + 1) +
          x ^ (2 * k + 1) * (((n : ℝ) + 1) * (1 - x ^ 2) ^ n * (-(2 * x)))) x := by
      refine (h1.mul h2).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · filter_upwards with y
        rfl
      · ring
    have hder : (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k)) * (1 - x ^ 2) ^ (n + 1) +
          x ^ (2 * k + 1) * (((n : ℝ) + 1) * (1 - x ^ 2) ^ n * (-(2 * x))) =
        (2 * (k : ℝ) + 1) * (x ^ (2 * k) * (1 - x ^ 2) ^ (n + 1)) -
          2 * ((n : ℝ) + 1) * (x ^ (2 * (k + 1)) * (1 - x ^ 2) ^ n) := by
      have hx : x ^ (2 * (k + 1)) = x ^ (2 * k + 1) * x := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pow_add]
        ring
      rw [hx]
      push_cast
      ring
    rw [hder] at h12
    exact h12
  have hcont : ContinuousOn (fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1))
      (Set.Icc (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1)).continuousOn
  have hint : IntervalIntegrable
      (fun y : ℝ => (2 * (k : ℝ) + 1) * (y ^ (2 * k) * (1 - y ^ 2) ^ (n + 1)) -
        2 * ((n : ℝ) + 1) * (y ^ (2 * (k + 1)) * (1 - y ^ 2) ^ n)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) hcont hderiv hint
  have hFval : (fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1)) 1 -
      (fun y : ℝ => y ^ (2 * k + 1) * (1 - y ^ 2) ^ (n + 1)) 0 = 0 := by
    simp [zero_pow (Nat.succ_ne_zero n), zero_pow (by omega : 2 * k + 1 ≠ 0)]
  rw [hFval] at hF
  have hA : IntervalIntegrable
      (fun y : ℝ => (2 * (k : ℝ) + 1) * (y ^ (2 * k) * (1 - y ^ 2) ^ (n + 1)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC : IntervalIntegrable
      (fun y : ℝ => 2 * ((n : ℝ) + 1) * (y ^ (2 * (k + 1)) * (1 - y ^ 2) ^ n))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hA hC, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hF
  field_simp
  linarith
theorem integral_zero_one_sq_pow_mul_sq (k n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (2 * k) * (1 - x ^ 2) ^ n) =
      (2 : ℝ) ^ (2 * n) * (n.factorial : ℝ) * (((k + n).factorial : ℕ) : ℝ) *
          (((2 * k).factorial : ℕ) : ℝ) /
        ((((2 * k + 2 * n + 1).factorial : ℕ) : ℝ) * (k.factorial : ℝ)) := by
  induction n generalizing k with
  | zero =>
      have hzero : (∫ x in (0 : ℝ)..1, x ^ (2 * k)) = 1 / (2 * (k : ℝ) + 1) := by
        rw [integral_pow]
        simp [zero_pow (by omega : 2 * k + 1 ≠ 0)]
      have hcongr : (∫ x in (0 : ℝ)..1, x ^ (2 * k) * (1 - x ^ 2) ^ 0) =
          ∫ x in (0 : ℝ)..1, x ^ (2 * k) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp
      rw [hcongr, hzero]
      simp only [Nat.factorial_zero, Nat.cast_one, Nat.add_zero, Nat.mul_zero]
      have hfac : (((2 * k + 1).factorial : ℕ) : ℝ) =
          (2 * (k : ℝ) + 1) * (((2 * k).factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      field_simp
  | succ n ih =>
      rw [integral_zero_one_sq_pow_mul_sq_succ k n, ih (k + 1)]
      have hfac2k : (((2 * (k + 1)).factorial : ℕ) : ℝ) =
          (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) *
            (((2 * k).factorial : ℕ) : ℝ) := by
        have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [e1, show 2 * k + 2 = (2 * k + 1) + 1 by omega, Nat.factorial_succ,
          Nat.factorial_succ]
        push_cast
        ring
      have hfacn : (((n + 1).factorial : ℕ) : ℝ) =
          ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hfack : (((k + 1).factorial : ℕ) : ℝ) =
          ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have e1 : k + 1 + n = k + (n + 1) := by omega
      have e2 : 2 * (k + 1) + 2 * n + 1 = 2 * k + 2 * (n + 1) + 1 := by omega
      rw [e1, e2, hfac2k, hfacn, hfack]
      rw [show (2 : ℝ) ^ (2 * (n + 1)) = (2 : ℝ) ^ (2 * n) * 4 by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        norm_num]
      field_simp
      ring
lemma integral_one_sub_sq_pow_mul_sq (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((((1 : ℝ[X]) - X ^ 2) ^ n)).eval x * x ^ (2 * k)) =
      2 * (∫ x in (0 : ℝ)..1, x ^ (2 * k) * (1 - x ^ 2) ^ n) := by
  have hA : ((((1 : ℝ[X]) - X ^ 2) ^ n).comp (-X)) = ((1 : ℝ[X]) - X ^ 2) ^ n := by
    rw [pow_comp, sub_comp, one_comp, pow_comp, X_comp]
    rw [show (-X) ^ 2 = X ^ 2 by ring]
  have hB : (((X : ℝ[X]) ^ (2 * k)).comp (-X)) = (X : ℝ[X]) ^ (2 * k) := by
    rw [pow_comp, X_comp, Even.neg_pow (show Even (2 * k) by exact ⟨k, by omega⟩)]
  have hp : ((((1 : ℝ[X]) - X ^ 2) ^ n * X ^ (2 * k)).comp (-X)) =
      ((1 : ℝ[X]) - X ^ 2) ^ n * X ^ (2 * k) := by
    rw [mul_comp, hA, hB]
  have h := Y7Legendre.integral_eval_eq_two_mul_integral_of_comp_neg_self
      (((1 : ℝ[X]) - X ^ 2) ^ n * X ^ (2 * k)) hp
  have hL : (∫ x in (-1 : ℝ)..1, ((((1 : ℝ[X]) - X ^ 2) ^ n)).eval x * x ^ (2 * k)) =
      ∫ x in (-1 : ℝ)..1, ((((1 : ℝ[X]) - X ^ 2) ^ n * X ^ (2 * k)).eval x) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [hL, h]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  ring
lemma integral_sq_sub_one_pow_mul_sq (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (2 * k)) =
      (-1 : ℝ) ^ n *
        (∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x * x ^ (2 * k)) := by
  have hpoly : ((X ^ 2 - C (1 : ℝ)) ^ n) =
      ((-1 : ℝ[X]) ^ n) * (((1 : ℝ[X]) - X ^ 2) ^ n) := by
    have h1 : (X ^ 2 - C (1 : ℝ)) = -((1 : ℝ[X]) - X ^ 2) := by
      rw [Polynomial.C_1]
      ring
    rw [h1, neg_pow]
  have hpt : ∀ x : ℝ, ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (2 * k) =
      (-1 : ℝ) ^ n * ((((1 : ℝ[X]) - X ^ 2) ^ n).eval x * x ^ (2 * k)) := by
    intro x
    rw [hpoly, Polynomial.eval_mul]
    simp
    ring
  have hcongr : (∫ x in (-1 : ℝ)..1,
        ((X ^ 2 - C (1 : ℝ)) ^ n).eval x * x ^ (2 * k)) =
      ∫ x in (-1 : ℝ)..1, (-1 : ℝ) ^ n *
        ((((1 : ℝ[X]) - X ^ 2) ^ n).eval x * x ^ (2 * k)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hpt x
  rw [hcongr, intervalIntegral.integral_const_mul]
lemma even_sign_collect (n k : ℕ) (J : ℝ) :
    (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) * ((-1 : ℝ) ^ n) *
        ((n + 2 * k).descFactorial n : ℝ) * (((-1 : ℝ) ^ n) * J) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ((n + 2 * k).descFactorial n : ℝ) * J := by
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨n, by ring⟩
  have hsign_mul : ∀ x : ℝ, ((-1 : ℝ) ^ n) * (((-1 : ℝ) ^ n) * x) = x := fun x => by
    rw [← mul_assoc, hsign, one_mul]
  calc (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) * ((-1 : ℝ) ^ n) *
        ((n + 2 * k).descFactorial n : ℝ) * (((-1 : ℝ) ^ n) * J)
      = (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
          ((n + 2 * k).descFactorial n : ℝ) *
          (((-1 : ℝ) ^ n) * (((-1 : ℝ) ^ n) * J)) := by ring
    _ = (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
          ((n + 2 * k).descFactorial n : ℝ) * J := by
        rw [hsign_mul J]
theorem integral_pow_mul_legP_even (n k : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ (n + 2 * k) * (legP n).eval x) =
      2 ^ (n + 1) * (((n + 2 * k).factorial : ℕ) : ℝ) *
          (((k + n).factorial : ℕ) : ℝ) /
        ((((2 * k + 2 * n + 1).factorial : ℕ) : ℝ) * ((k.factorial : ℕ) : ℝ)) := by
  rw [Y7Rodrigues.integral_pow_mul_legP_reduction (n + 2 * k) n (by omega)]
  rw [show n + 2 * k - n = 2 * k by omega]
  rw [integral_sq_sub_one_pow_mul_sq k n]
  set J : ℝ := ∫ x in (-1 : ℝ)..1, (((1 : ℝ[X]) - X ^ 2) ^ n).eval x * x ^ (2 * k) with hJ
  rw [even_sign_collect n k J, hJ]
  rw [integral_one_sub_sq_pow_mul_sq k n, integral_zero_one_sq_pow_mul_sq k n]
  have hdesc : (((n + 2 * k).descFactorial n : ℕ) : ℝ) =
      (((n + 2 * k).factorial : ℕ) : ℝ) / (((2 * k).factorial : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_div (by omega : n ≤ n + 2 * k),
      show n + 2 * k - n = 2 * k by omega,
      Nat.cast_div (Nat.factorial_dvd_factorial (by omega : 2 * k ≤ n + 2 * k))]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * k))
  rw [hdesc]
  have hpow : (2 : ℝ) ^ (2 * n) = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show 2 * n = n + n by omega, pow_add]
  rw [hpow, pow_succ]
  field_simp
theorem integral_pow_mul_legP (m n : ℕ) (hmn : n ≤ m) :
    (∫ x in (-1 : ℝ)..1, x ^ m * (legP n).eval x) =
      if Odd (m + n) then 0 else
        2 ^ (n + 1) * ((m.factorial : ℕ) : ℝ) *
            (((n + (m - n) / 2).factorial : ℕ) : ℝ) /
          ((((m + n + 1).factorial : ℕ) : ℝ) *
            ((((m - n) / 2).factorial : ℕ) : ℝ)) := by
  by_cases h : Odd (m + n)
  · rw [if_pos h]
    exact Y7Legendre.integral_pow_mul_legP_eq_zero_of_odd m n h
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.mp h
    have hk : m = n + 2 * (j - n) := by omega
    have hdiv : (m - n) / 2 = j - n := by
      rw [hk]
      have h1 : n + 2 * (j - n) - n = 2 * (j - n) := by omega
      rw [h1, Nat.mul_div_cancel_left (j - n) zero_lt_two]
    rw [hdiv, hk]
    have h1 : n + (j - n) = (j - n) + n := by omega
    have h2 : n + 2 * (j - n) + n + 1 = 2 * (j - n) + 2 * n + 1 := by omega
    rw [h1, h2]
    exact integral_pow_mul_legP_even n (j - n)
end Y7Beta
namespace Y7J
open Y7Legendre
lemma eval_one_J (r n : ℕ) (hr : 1 ≤ r) : (J legP r n).eval 1 = 0 := by
  revert hr n
  refine Nat.strong_induction_on r ?_
  intro k ih n hr
  rcases k with _ | _ | k
  · omega
  · simp [J_one, eval_one_legP]
  · rw [J_succ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [ih (k + 1) (by omega) (n + 1) (by omega),
      ih (k + 1) (by omega) (n - 1) (by omega)]
    ring
lemma eval_neg_one_J (r n : ℕ) (hrn : r ≤ n) (hr : 1 ≤ r) :
    (J legP r n).eval (-1) = 0 := by
  revert hr hrn n
  refine Nat.strong_induction_on r ?_
  intro k ih n hrn hr
  rcases k with _ | _ | k
  · omega
  · have h1 : (legP (n + 1)).eval (-1) = (-1 : ℝ) ^ (n + 1) := by
      rw [eval_legP_neg, eval_one_legP, mul_one]
    have h2 : (legP (n - 1)).eval (-1) = (-1 : ℝ) ^ (n - 1) := by
      rw [eval_legP_neg, eval_one_legP, mul_one]
    rw [J_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, h1, h2]
    have hsign : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
      norm_num
    rw [hsign]
    ring
  · rw [J_succ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [ih (k + 1) (by omega) (n + 1) (by omega) (by omega),
      ih (k + 1) (by omega) (n - 1) (by omega) (by omega)]
    ring
lemma comp_neg_X_J (r n : ℕ) (hrn : r ≤ n) (hr : 1 ≤ r) :
    (J legP r n).comp (-X) = (-1 : ℝ) ^ (n + r) • (J legP r n) := by
  revert hr hrn n
  refine Nat.strong_induction_on r ?_
  intro k ih n hrn hr
  rcases k with _ | _ | k
  · omega
  · have h1 := legP_comp_neg_X (n + 1)
    have h2 := legP_comp_neg_X (n - 1)
    have hsign : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
      norm_num
    rw [J_one, mul_comp, C_comp, sub_comp, h1, h2, hsign, ← smul_sub,
      mul_smul_comm]
  · rw [J_succ, mul_comp, C_comp, sub_comp]
    rw [ih (k + 1) (by omega) (n + 1) (by omega) (by omega),
      ih (k + 1) (by omega) (n - 1) (by omega) (by omega)]
    have hsign1 : (-1 : ℝ) ^ (n + 1 + (k + 1)) = (-1 : ℝ) ^ (n + (k + 2)) := by
      rw [show n + 1 + (k + 1) = n + (k + 2) by omega]
    have htwo : ∀ m : ℕ, (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ m := by
      intro m
      rw [pow_add]
      norm_num
    have hsign2 : (-1 : ℝ) ^ (n - 1 + (k + 1)) = (-1 : ℝ) ^ (n + (k + 2)) := by
      have e : n + (k + 2) = (n - 1 + (k + 1)) + 2 := by omega
      rw [e]
      exact (htwo (n - 1 + (k + 1))).symm
    rw [hsign1, hsign2, ← smul_sub, mul_smul_comm]
end Y7J
namespace Y7Deriv
open Polynomial Y7Legendre
noncomputable def c (m : ℕ) : ℝ := 1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))
lemma legP_eq_C_c (m : ℕ) :
    legP m = C (c m) * (Polynomial.derivative^[m]) ((X ^ 2 - C (1 : ℝ)) ^ m) := rfl
lemma c_succ_mul (n : ℕ) : c (n + 1) * (2 * ((n : ℝ) + 1)) = c n := by
  unfold c
  have hfac : (((n + 1).factorial : ℕ) : ℝ) =
      ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac, pow_succ]
  field_simp
lemma c_pred (n : ℕ) (hn : 1 ≤ n) : c (n - 1) = 2 * (n : ℝ) * c n := by
  have h := c_succ_mul (n - 1)
  have hcast : (((n - 1 : ℕ)) : ℝ) + 1 = (n : ℝ) := by
    rw [show n = n - 1 + 1 by omega]
    push_cast
    ring
  rw [hcast, show n - 1 + 1 = n by omega] at h
  rw [← h]
  ring
lemma legP_one : legP 1 = (X : ℝ[X]) := by
  have hpow : ((X ^ 2 - C (1 : ℝ)) ^ 1) = (X ^ 2 - C (1 : ℝ)) := pow_one _
  unfold legP
  rw [Function.iterate_one, hpow]
  rw [show (1 : ℝ) / ((2 : ℝ) ^ 1 * ((((1 : ℕ)).factorial : ℝ))) = 1 / 2 by norm_num]
  rw [show Polynomial.derivative (X ^ 2 - C (1 : ℝ)) = C 2 * X by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero]
    norm_num]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num, Polynomial.C_1, one_mul]
lemma derivative_sq_sq_sub_one_pow (n : ℕ) :
    (Polynomial.derivative^[2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)) =
      C (2 * ((n : ℝ) + 1)) * (X ^ 2 - C (1 : ℝ)) ^ n +
        C (4 * (n : ℝ) * ((n : ℝ) + 1)) *
          (X ^ 2 * (X ^ 2 - C (1 : ℝ)) ^ (n - 1)) := by
  have hd1 : Polynomial.derivative (X ^ 2 - C (1 : ℝ)) = C 2 * X := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero]
    norm_num
  have hD1 : Polynomial.derivative ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)) =
      C ((n : ℝ) + 1) * ((X ^ 2 - C (1 : ℝ)) ^ n * (C 2 * X)) := by
    rw [Polynomial.derivative_pow, hd1, show n + 1 - 1 = n by omega]
    push_cast
    ring
  have hD2 : Polynomial.derivative
        (C ((n : ℝ) + 1) * ((X ^ 2 - C (1 : ℝ)) ^ n * (C 2 * X))) =
      C ((n : ℝ) + 1) *
        (C (n : ℝ) * ((X ^ 2 - C (1 : ℝ)) ^ (n - 1) * (C 2 * X)) * (C 2 * X) +
          (X ^ 2 - C (1 : ℝ)) ^ n * C 2) := by
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_mul, Polynomial.derivative_pow,
      hd1, Polynomial.derivative_C_mul_X]
    ring
  change Polynomial.derivative
      (Polynomial.derivative ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))) =
      C (2 * ((n : ℝ) + 1)) * (X ^ 2 - C (1 : ℝ)) ^ n +
        C (4 * (n : ℝ) * ((n : ℝ) + 1)) *
          (X ^ 2 * (X ^ 2 - C (1 : ℝ)) ^ (n - 1))
  rw [hD1, hD2, mul_add]
  rw [show C ((n : ℝ) + 1) *
        (C (n : ℝ) * ((X ^ 2 - C 1) ^ (n - 1) * (C 2 * X)) * (C 2 * X)) =
      C ((n : ℝ) + 1) * C (n : ℝ) *
        (((X ^ 2 - C 1) ^ (n - 1) * (C 2 * X)) * (C 2 * X)) by ring]
  rw [show C ((n : ℝ) + 1) * ((X ^ 2 - C 1) ^ n * C 2) =
      C ((n : ℝ) + 1) * C 2 * (X ^ 2 - C 1) ^ n by ring]
  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
  have hP : ((X ^ 2 - C (1 : ℝ)) ^ (n - 1) * (C 2 * X)) * (C 2 * X) =
      C 4 * (X ^ 2 * (X ^ 2 - C (1 : ℝ)) ^ (n - 1)) := by
    rw [Polynomial.C_ofNat 2, Polynomial.C_ofNat 4]
    ring
  rw [hP, ← mul_assoc, ← Polynomial.C_mul]
  rw [show ((n : ℝ) + 1) * n * 4 = 4 * (n : ℝ) * ((n : ℝ) + 1) by ring,
    show ((n : ℝ) + 1) * 2 = 2 * ((n : ℝ) + 1) by ring]
  ring
lemma deriv2_legP_base (n : ℕ) (hn : 1 ≤ n) :
    C (c (n + 1)) *
        ((Polynomial.derivative^[2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))) -
      C (c (n - 1)) * (X ^ 2 - C (1 : ℝ)) ^ (n - 1) =
      C ((2 * (n : ℝ) + 1) * c n) * (X ^ 2 - C (1 : ℝ)) ^ n := by
  rw [derivative_sq_sq_sub_one_pow]
  rw [mul_add]
  have hT1 : C (c (n + 1)) * (C (2 * ((n : ℝ) + 1)) * (X ^ 2 - C 1) ^ n) =
      C (c n) * (X ^ 2 - C 1) ^ n := by
    rw [← mul_assoc, ← Polynomial.C_mul, c_succ_mul n]
  have hc2 : c (n + 1) * (4 * (n : ℝ) * ((n : ℝ) + 1)) = c (n - 1) := by
    rw [c_pred n hn, ← c_succ_mul n]
    ring
  have hT2 : C (c (n + 1)) *
        (C (4 * (n : ℝ) * ((n : ℝ) + 1)) * (X ^ 2 * (X ^ 2 - C 1) ^ (n - 1))) =
      C (c (n - 1)) * (X ^ 2 * (X ^ 2 - C 1) ^ (n - 1)) := by
    rw [← mul_assoc, ← Polynomial.C_mul, hc2]
  rw [hT1, hT2]
  have hX : (X ^ 2 : ℝ[X]) * (X ^ 2 - C 1) ^ (n - 1) =
      (X ^ 2 - C 1) ^ n + (X ^ 2 - C 1) ^ (n - 1) := by
    have h1 : ((X : ℝ[X]) ^ 2 - C (1 : ℝ)) ^ n =
        ((X : ℝ[X]) ^ 2 - C (1 : ℝ)) * ((X : ℝ[X]) ^ 2 - C (1 : ℝ)) ^ (n - 1) := by
      rw [show n = (n - 1) + 1 by omega]
      exact pow_succ' ((X : ℝ[X]) ^ 2 - C (1 : ℝ)) (n - 1)
    rw [h1, Polynomial.C_1]
    ring
  rw [hX, mul_add]
  rw [show (2 * (n : ℝ) + 1) * c n = c n + c (n - 1) by
    rw [c_pred n hn]
    ring]
  rw [Polynomial.C_add, add_mul]
  ring
theorem derivative_legP_succ_sub_pred (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.derivative (legP (n + 1)) - Polynomial.derivative (legP (n - 1)) =
      C (2 * (n : ℝ) + 1) * legP n := by
  have hbase := deriv2_legP_base n hn
  have h := congrArg (fun p : ℝ[X] => (Polynomial.derivative^[n]) p) hbase
  simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_sub] at h
  have hiter2 : (Polynomial.derivative^[n])
        ((Polynomial.derivative^[2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))) =
      (Polynomial.derivative^[n + 2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)) := by
    rw [← Function.iterate_add_apply (f := Polynomial.derivative) (m := n) (n := 2)
      (x := ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)))]
  rw [hiter2] at h
  rw [legP_eq_C_c (n + 1), legP_eq_C_c (n - 1), legP_eq_C_c n]
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_C_mul]
  have hi1 : Polynomial.derivative
        ((Polynomial.derivative^[n + 1]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))) =
      (Polynomial.derivative^[n + 2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)) := by
    rw [show (Polynomial.derivative^[n + 2]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1)) =
        Polynomial.derivative
          ((Polynomial.derivative^[n + 1]) ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))) from by
      rw [show n + 2 = (n + 1) + 1 by omega]
      exact Function.iterate_succ_apply' (f := Polynomial.derivative) (n := n + 1)
        ((X ^ 2 - C (1 : ℝ)) ^ (n + 1))]
  have hi3 : Polynomial.derivative
        ((Polynomial.derivative^[n - 1]) ((X ^ 2 - C (1 : ℝ)) ^ (n - 1))) =
      (Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ (n - 1)) := by
    rw [show (Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ (n - 1)) =
        Polynomial.derivative
          ((Polynomial.derivative^[n - 1]) ((X ^ 2 - C (1 : ℝ)) ^ (n - 1))) from by
      rw [show n = (n - 1) + 1 by omega]
      exact Function.iterate_succ_apply' (f := Polynomial.derivative) (n := n - 1)
        ((X ^ 2 - C (1 : ℝ)) ^ (n - 1))]
  rw [hi1, hi3, h]
  rw [← mul_assoc, ← Polynomial.C_mul]
lemma derivative_J_one (n : ℕ) : Polynomial.derivative (J legP 1 n) = legP n := by
  rcases n with _ | n
  · rw [J_one, show (2 * ((0 : ℕ) : ℝ) + 1)⁻¹ = 1 by norm_num, Polynomial.C_1, one_mul,
      Polynomial.derivative_sub, legP_one, legP_zero, Polynomial.derivative_X,
      Polynomial.derivative_one, sub_zero]
  · rw [J_one, Polynomial.derivative_C_mul, Polynomial.derivative_sub,
      derivative_legP_succ_sub_pred (n + 1) (by omega)]
    rw [← mul_assoc, ← Polynomial.C_mul]
    rw [show (2 * ((n + 1 : ℕ) : ℝ) + 1)⁻¹ * (2 * ((n + 1 : ℕ) : ℝ) + 1) = 1 by
      rw [inv_mul_cancel₀ (by positivity)]]
    rw [Polynomial.C_1, one_mul]
lemma derivative_J_succ (r n : ℕ) (hr : 1 ≤ r) :
    Polynomial.derivative (J legP (r + 1) n) = J legP r n := by
  revert hr n
  refine Nat.strong_induction_on r ?_
  intro k ih n hr
  rcases k with _ | _ | k
  · omega
  · rw [J_succ, Polynomial.derivative_C_mul, Polynomial.derivative_sub,
      derivative_J_one (n + 1), derivative_J_one (n - 1), J_one]
  · rw [J_succ (P := legP) (r := k) (n := n),
      J_succ (P := legP) (r := k + 1) (n := n),
      Polynomial.derivative_C_mul, Polynomial.derivative_sub,
      ih (k + 1) (by omega) (n + 1) (by omega),
      ih (k + 1) (by omega) (n - 1) (by omega)]
end Y7Deriv
open scoped BigOperators
namespace Y7Ibp
open Polynomial Y7Legendre Y7Deriv
private lemma sum_pow_neg_succ (f : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ (d + 1) * f d) =
      -(∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d * f d) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun d _ => by rw [pow_succ]; ring
lemma integral_iterate_derivative_J_chain (n : ℕ) (a b : ℝ) :
    ∀ D m : ℕ, 1 ≤ m → ∀ w : ℝ[X], w.natDegree ≤ D →
      (∫ t in a..b, w.eval t * (J legP m n).eval t) =
        ∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d *
          (((Polynomial.derivative^[d]) w).eval b * (J legP (m + d + 1) n).eval b -
            ((Polynomial.derivative^[d]) w).eval a * (J legP (m + d + 1) n).eval a) := by
  intro D
  induction D with
  | zero =>
      intro m hm w hw
      rw [Polynomial.eq_C_of_natDegree_le_zero hw]
      rw [Finset.sum_range_one]
      simp only [Function.iterate_zero_apply, pow_zero, one_mul, Polynomial.eval_C]
      rw [intervalIntegral.integral_const_mul]
      have hF : (∫ t in a..b, (J legP m n).eval t) =
          (J legP (m + 1) n).eval b - (J legP (m + 1) n).eval a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro t _
          have h := (J legP (m + 1) n).hasDerivAt t
          rw [Y7Deriv.derivative_J_succ m n hm] at h
          exact h
        · exact (J legP m n).continuous.intervalIntegrable a b
      rw [hF]
      ring
  | succ D ih =>
      intro m hm w hw
      have hw' : w.derivative.natDegree ≤ D := by
        have := Polynomial.natDegree_derivative_le w
        omega
      have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        (u := fun t : ℝ => w.eval t)
        (v := fun t : ℝ => (J legP (m + 1) n).eval t)
        (u' := fun t : ℝ => w.derivative.eval t)
        (v' := fun t : ℝ => (J legP m n).eval t)
        w.continuous.continuousOn ((J legP (m + 1) n).continuous.continuousOn)
        (fun x _ => w.hasDerivAt x)
        (fun x _ => by
          have h := (J legP (m + 1) n).hasDerivAt x
          rw [Y7Deriv.derivative_J_succ m n hm] at h
          exact h)
        (w.derivative.continuous.intervalIntegrable a b)
        ((J legP m n).continuous.intervalIntegrable a b)
      have hih := ih (m + 1) (by omega) w.derivative hw'
      have hshift : ∀ k : ℕ, (Polynomial.derivative^[k + 1]) w =
          (Polynomial.derivative^[k]) w.derivative := fun k => by
        rw [show k + 1 = k.succ by omega]
        exact Function.iterate_succ_apply (f := Polynomial.derivative) (n := k) w
      rw [hIBP, hih]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [hshift]
      rw [sum_pow_neg_succ]
      simp only [pow_zero, one_mul, Function.iterate_zero_apply]
      ring
end Y7Ibp
namespace Y7Ibp
open Polynomial Y7Legendre Y7Deriv
lemma integral_iterate_derivative_legP_chain (n : ℕ) (a b : ℝ)
    (D : ℕ) (w : ℝ[X]) (hw : w.natDegree ≤ D) :
    (∫ t in a..b, w.eval t * (legP n).eval t) =
      ∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d *
        (((Polynomial.derivative^[d]) w).eval b * (J legP (d + 1) n).eval b -
          ((Polynomial.derivative^[d]) w).eval a * (J legP (d + 1) n).eval a) := by
  cases D with
  | zero =>
      rw [Polynomial.eq_C_of_natDegree_le_zero hw]
      rw [Finset.sum_range_one]
      simp only [Function.iterate_zero_apply, pow_zero, one_mul, Polynomial.eval_C]
      rw [intervalIntegral.integral_const_mul]
      have hF : (∫ t in a..b, (legP n).eval t) =
          (J legP 1 n).eval b - (J legP 1 n).eval a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro t _
          have h := (J legP 1 n).hasDerivAt t
          rw [Y7Deriv.derivative_J_one n] at h
          exact h
        · exact (legP n).continuous.intervalIntegrable a b
      rw [hF]
      ring
  | succ D =>
      have hw' : w.derivative.natDegree ≤ D := by
        have := Polynomial.natDegree_derivative_le w
        omega
      have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        (u := fun t : ℝ => w.eval t)
        (v := fun t : ℝ => (J legP 1 n).eval t)
        (u' := fun t : ℝ => w.derivative.eval t)
        (v' := fun t : ℝ => (legP n).eval t)
        w.continuous.continuousOn ((J legP 1 n).continuous.continuousOn)
        (fun x _ => w.hasDerivAt x)
        (fun x _ => by
          have h := (J legP 1 n).hasDerivAt x
          rw [Y7Deriv.derivative_J_one n] at h
          exact h)
        (w.derivative.continuous.intervalIntegrable a b)
        ((legP n).continuous.intervalIntegrable a b)
      have hih := integral_iterate_derivative_J_chain n a b D 1 le_rfl w.derivative hw'
      have hshift : ∀ k : ℕ, (Polynomial.derivative^[k + 1]) w =
          (Polynomial.derivative^[k]) w.derivative := fun k => by
        rw [show k + 1 = k.succ by omega]
        exact Function.iterate_succ_apply (f := Polynomial.derivative) (n := k) w
      rw [hIBP, hih]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [hshift]
      rw [sum_pow_neg_succ]
      simp only [pow_zero, one_mul, Function.iterate_zero_apply]
      ring
lemma iterate_derivative_comp_C_sub_X (u : ℝ[X]) (c : ℝ) (d : ℕ) :
    (Polynomial.derivative^[d]) (u.comp (C c - X)) =
      (-1 : ℝ) ^ d • ((Polynomial.derivative^[d]) u).comp (C c - X) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show d + 1 = d.succ by omega, Function.iterate_succ_apply', ih,
        Polynomial.derivative_smul, Polynomial.derivative_comp]
      rw [show Polynomial.derivative (C c - X : ℝ[X]) = -1 by
        rw [Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X]
        ring]
      have hshift_d : Polynomial.derivative ((Polynomial.derivative^[d]) u) =
          (Polynomial.derivative^[d + 1]) u := by
        rw [show d + 1 = d.succ by omega]
        exact (Function.iterate_succ_apply' (f := Polynomial.derivative) (n := d) u).symm
      rw [hshift_d, neg_one_mul, smul_neg, ← neg_smul, neg_eq_neg_one_mul, mul_comm,
        ← pow_succ]
lemma eval_iterate_derivative_comp_C_sub_X (u : ℝ[X]) (c x : ℝ) (d : ℕ) :
    ((Polynomial.derivative^[d]) (u.comp (C c - X))).eval x =
      (-1 : ℝ) ^ d * ((Polynomial.derivative^[d]) u).eval (c - x) := by
  rw [iterate_derivative_comp_C_sub_X, Polynomial.eval_smul, smul_eq_mul]
  congr 1
  rw [Polynomial.eval_comp]
  congr 1
  simp [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
theorem integral_reflected_translation (n D : ℕ) (u : ℝ[X]) (hu : u.natDegree ≤ D)
    (r : ℝ) :
    (∫ t in (1 - r)..1, u.eval (2 - r - t) * (legP n).eval t) =
      -∑ d ∈ Finset.range (D + 1), ((Polynomial.derivative^[d]) u).eval 1 *
        (J legP (d + 1) n).eval (1 - r) := by
  set q : ℝ[X] := C (2 - r) - X with hq
  set w : ℝ[X] := u.comp q with hw
  have hqle : q.natDegree ≤ 1 := by
    rw [hq, show (C (2 - r) - X : ℝ[X]) = -(X - C (2 - r)) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hwdeg : w.natDegree ≤ D := by
    rw [hw]
    calc (u.comp q).natDegree ≤ u.natDegree * q.natDegree := Polynomial.natDegree_comp_le
      _ ≤ D * 1 := Nat.mul_le_mul hu hqle
      _ = D := by ring
  have hchain := integral_iterate_derivative_legP_chain n (1 - r) 1 D w hwdeg
  have hcongr : (∫ t in (1 - r)..1, u.eval (2 - r - t) * (legP n).eval t) =
      ∫ t in (1 - r)..1, w.eval t * (legP n).eval t := by
    apply intervalIntegral.integral_congr
    intro t _
    have hwt : w.eval t = u.eval (2 - r - t) := by
      rw [hw, Polynomial.eval_comp, hq]
      simp [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    change u.eval (2 - r - t) * (legP n).eval t =
      w.eval t * (legP n).eval t
    rw [hwt]
  rw [hcongr, hchain]
  rw [show (∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d *
        (((Polynomial.derivative^[d]) w).eval 1 * (J legP (d + 1) n).eval 1 -
          ((Polynomial.derivative^[d]) w).eval (1 - r) * (J legP (d + 1) n).eval (1 - r))) =
      -∑ d ∈ Finset.range (D + 1), ((Polynomial.derivative^[d]) u).eval 1 *
        (J legP (d + 1) n).eval (1 - r) from by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    simp only [hw, hq]
    rw [eval_iterate_derivative_comp_C_sub_X u (2 - r) 1 d,
      Y7J.eval_one_J (d + 1) n (by omega),
      eval_iterate_derivative_comp_C_sub_X u (2 - r) (1 - r) d]
    rw [show (2 - r) - 1 = 1 - r by ring, show (2 - r) - (1 - r) = 1 by ring]
    have hsgn : ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ d) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨d, by ring⟩
    rw [mul_sub]
    simp only [mul_zero]
    rw [mul_assoc, ← mul_assoc, hsgn, one_mul, zero_sub]]
end Y7Ibp
namespace Y7Convolution
open Polynomial MeasureTheory Y7Legendre Y7Beta Y7Deriv
theorem integral_legP_zero_mul_legP_mul_pow (n ℓ : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP 0).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      ∫ x in (-1 : ℝ)..1, x ^ (2 * ℓ) * (legP n).eval x := by
  apply intervalIntegral.integral_congr
  intro x _
  change (legP 0).eval x * (legP n).eval x * x ^ (2 * ℓ) =
    x ^ (2 * ℓ) * (legP n).eval x
  rw [legP_zero, Polynomial.eval_one, one_mul]
  ring
theorem integral_legP_one_mul_legP_mul_pow (n ℓ : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP 1).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      ∫ x in (-1 : ℝ)..1, x ^ (2 * ℓ + 1) * (legP n).eval x := by
  apply intervalIntegral.integral_congr
  intro x _
  change (legP 1).eval x * (legP n).eval x * x ^ (2 * ℓ) =
    x ^ (2 * ℓ + 1) * (legP n).eval x
  rw [Y7Deriv.legP_one, Polynomial.eval_X, pow_succ x (2 * ℓ)]
  ring
end Y7Convolution
namespace Y7Convolution
open Polynomial MeasureTheory Y7Legendre Y7Beta Y7Deriv Y7Rodrigues
theorem integral_legP_mul_legP_mul_pow_reduction (m n ℓ : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) * (-1 : ℝ) ^ m *
        (∫ x in (-1 : ℝ)..1, ((X ^ 2 - C (1 : ℝ)) ^ m).eval x *
          ((Polynomial.derivative^[m]) ((legP n) * Polynomial.X ^ (2 * ℓ))).eval x) := by
  have hconst : (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        (∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[m]) ((X ^ 2 - C (1 : ℝ)) ^ m)).eval x *
            ((legP n) * Polynomial.X ^ (2 * ℓ)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        (((Polynomial.derivative^[m]) ((X ^ 2 - C (1 : ℝ)) ^ m)).eval x *
          ((legP n) * Polynomial.X ^ (2 * ℓ)).eval x)
    unfold legP
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  rw [hconst,
    integral_iterate_derivative_sq_sub_one_pow_mul m m le_rfl
      ((legP n) * Polynomial.X ^ (2 * ℓ))]
  ring
end Y7Convolution
namespace Y7Convolution
open Polynomial MeasureTheory Y7Legendre Y7Rodrigues
theorem integral_legP_mul_legP_mul_pow_eq_zero_of_odd (m n ℓ : ℕ) (hmn : Odd (m + n)) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) = 0 := by
  have hp : ((legP m * legP n * Polynomial.X ^ (2 * ℓ)).comp (-Polynomial.X)) =
      -(legP m * legP n * Polynomial.X ^ (2 * ℓ)) := by
    rw [mul_comp, legP_mul_comp_neg_X, pow_comp, X_comp,
      Even.neg_pow (show Even (2 * ℓ) by exact ⟨ℓ, by ring⟩),
      hmn.neg_one_pow, neg_one_smul, neg_mul]
  have h := integral_eval_eq_zero_of_comp_neg_neg
      (legP m * legP n * Polynomial.X ^ (2 * ℓ)) hp
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] using h
end Y7Convolution
namespace Y7Monomial
open Polynomial Finset
open Y7Legendre Y7Beta Y7Rodrigues
theorem sq_sub_one_pow_eq_sum (n : ℕ) :
    (X ^ 2 - C (1 : ℝ)) ^ n =
      ∑ k ∈ Finset.range (n + 1),
        C (((-1 : ℝ) ^ (n - k)) * (n.choose k : ℝ)) * X ^ (2 * k) := by
  have hbase : (X ^ 2 - C (1 : ℝ)) = X ^ 2 + C (-1) := by
    rw [sub_eq_add_neg, map_neg, map_one]
  rw [hbase, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← map_pow (C : ℝ →+* ℝ[X]) (-1) (n - k),
    ← map_natCast (C : ℝ →+* ℝ[X]) (n.choose k)]
  rw [mul_assoc, ← map_mul]
  rw [pow_mul]
  ring
theorem iterate_derivative_sq_sub_one_pow_eq_sum (n : ℕ) :
    (Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n) =
      ∑ k ∈ Finset.range (n + 1),
        C ((((-1 : ℝ) ^ (n - k)) * (n.choose k : ℝ)) *
            (((2 * k).descFactorial n : ℕ) : ℝ)) * X ^ (2 * k - n) := by
  rw [sq_sub_one_pow_eq_sum, iterate_derivative_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul,
    ← mul_assoc, ← map_mul]
theorem legP_eq_sum (n : ℕ) :
    legP n = C ((1 : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
      ∑ k ∈ Finset.range (n + 1),
        C ((((-1 : ℝ) ^ (n - k)) * (n.choose k : ℝ)) *
            (((2 * k).descFactorial n : ℕ) : ℝ)) * X ^ (2 * k - n) := by
  unfold legP
  rw [iterate_derivative_sq_sub_one_pow_eq_sum]
lemma eval_legP_eq_sum (n : ℕ) (x : ℝ) :
    (legP n).eval x =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ k ∈ Finset.range (n + 1),
          ((((-1 : ℝ) ^ (n - k)) * (n.choose k : ℝ)) *
            (((2 * k).descFactorial n : ℕ) : ℝ)) * x ^ (2 * k - n) := by
  conv_lhs => rw [legP_eq_sum n]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
theorem integral_pow_mul_legP_eq_zero_of_lt (M n : ℕ) (h : M < n) :
    (∫ x in (-1 : ℝ)..1, x ^ M * (legP n).eval x) = 0 := by
  have hconst : (∫ x in (-1 : ℝ)..1, x ^ M * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        (∫ x in (-1 : ℝ)..1, x ^ M *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [legP, Polynomial.eval_C_mul]
    ring
  have hswap : (∫ x in (-1 : ℝ)..1, x ^ M *
        ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) = 0 := by
    have hcongr : (∫ x in (-1 : ℝ)..1, x ^ M *
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x) =
        ∫ x in (-1 : ℝ)..1,
          ((Polynomial.derivative^[n]) ((X ^ 2 - C (1 : ℝ)) ^ n)).eval x *
            (Polynomial.X ^ M).eval x := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      ring
    rw [hcongr, integral_iterate_derivative_sq_sub_one_pow_mul n n le_rfl
        (Polynomial.X ^ M),
      Polynomial.iterate_derivative_X_pow_eq_C_mul,
      Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp
  rw [hconst, hswap, mul_zero]
theorem integral_pow_mul_legP_all (M n : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ M * (legP n).eval x) =
      if n ≤ M then
        (if Odd (M + n) then 0 else
          2 ^ (n + 1) * ((M.factorial : ℕ) : ℝ) *
              (((n + (M - n) / 2).factorial : ℕ) : ℝ) /
            ((((M + n + 1).factorial : ℕ) : ℝ) *
              ((((M - n) / 2).factorial : ℕ) : ℝ)))
      else 0 := by
  by_cases h : n ≤ M
  · rw [if_pos h]
    exact Y7Beta.integral_pow_mul_legP M n h
  · rw [if_neg h]
    exact integral_pow_mul_legP_eq_zero_of_lt M n (Nat.lt_of_not_le h)
end Y7Monomial
namespace Y7Convolution
open Polynomial Finset
open MeasureTheory
open Y7Legendre Y7Beta Y7Monomial
theorem integral_mul_legP_eq_sum (m : ℕ) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume (-1 : ℝ) 1) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * g x) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) *
          (∫ x in (-1 : ℝ)..1, x ^ (2 * k - m) * g x) := by
  have hpt : (fun x : ℝ => (legP m).eval x * g x) =
      fun x : ℝ => (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ((∑ k ∈ Finset.range (m + 1),
            ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
              (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m)) * g x) := by
    funext x
    rw [eval_legP_eq_sum]
    ring
  rw [hpt, intervalIntegral.integral_const_mul]
  congr 1
  rw [show (fun x : ℝ => (∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m)) * g x) =
      fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
        ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
          (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m) * g x from by
    funext x
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · intro k hk
    exact hg.continuousOn_mul
      ((continuous_const.mul (continuous_id.pow (2 * k - m))).continuousOn)
theorem integral_legP_mul_legP_mul_pow_eq_sum (m n ℓ : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) *
          (∫ x in (-1 : ℝ)..1,
            x ^ (2 * k - m) * ((legP n).eval x * x ^ (2 * ℓ))) := by
  have hcongr : (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      ∫ x in (-1 : ℝ)..1, (legP m).eval x * ((legP n).eval x * x ^ (2 * ℓ)) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have h := integral_mul_legP_eq_sum m
      (fun x : ℝ => (legP n).eval x * x ^ (2 * ℓ))
      (((legP n).continuous.mul (continuous_id.pow (2 * ℓ))).intervalIntegrable (-1) 1)
  rw [hcongr, h]
theorem integral_legP_mul_legP_mul_pow (m n ℓ : ℕ) :
    (∫ x in (-1 : ℝ)..1, (legP m).eval x * (legP n).eval x * x ^ (2 * ℓ)) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) *
          (if n ≤ 2 * k - m + 2 * ℓ then
            (if Odd (2 * k - m + 2 * ℓ + n) then 0 else
              2 ^ (n + 1) * (((2 * k - m + 2 * ℓ).factorial : ℕ) : ℝ) *
                  (((n + (2 * k - m + 2 * ℓ - n) / 2).factorial : ℕ) : ℝ) /
                ((((2 * k - m + 2 * ℓ + n + 1).factorial : ℕ) : ℝ) *
                  ((((2 * k - m + 2 * ℓ - n) / 2).factorial : ℕ) : ℝ)))
          else 0) := by
  rw [integral_legP_mul_legP_mul_pow_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hpt : (fun x : ℝ => x ^ (2 * k - m) * ((legP n).eval x * x ^ (2 * ℓ))) =
      fun x : ℝ => x ^ (2 * k - m + 2 * ℓ) * (legP n).eval x := by
    funext x
    rw [pow_add]
    ring
  rw [hpt, integral_pow_mul_legP_all]
end Y7Convolution
namespace Y7Convolution
open Polynomial Finset
open MeasureTheory
open Y7Legendre Y7Beta Y7Monomial
theorem integral_mul_legP_eq_sum' (m : ℕ) (g : ℝ → ℝ) (a b : ℝ)
    (hg : IntervalIntegrable g volume a b) :
    (∫ x in a..b, (legP m).eval x * g x) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) *
          (∫ x in a..b, x ^ (2 * k - m) * g x) := by
  have hpt : (fun x : ℝ => (legP m).eval x * g x) =
      fun x : ℝ => (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
        ((∑ k ∈ Finset.range (m + 1),
            ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
              (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m)) * g x) := by
    funext x
    rw [eval_legP_eq_sum]
    ring
  rw [hpt, intervalIntegral.integral_const_mul]
  congr 1
  rw [show (fun x : ℝ => (∑ k ∈ Finset.range (m + 1),
          ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
            (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m)) * g x) =
      fun x : ℝ => ∑ k ∈ Finset.range (m + 1),
        ((((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
          (((2 * k).descFactorial m : ℕ) : ℝ)) * x ^ (2 * k - m) * g x from by
    funext x
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · intro k hk
    exact hg.continuousOn_mul
      ((continuous_const.mul (continuous_id.pow (2 * k - m))).continuousOn)
end Y7Convolution
namespace Y7Critical
open Polynomial Finset
open Y7Legendre Y7Ibp
noncomputable def criticalJSum (D n : ℕ) (u : ℝ[X]) (r : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d *
    ((Polynomial.derivative^[d]) u).eval 1 * (J legP (d + 1) n).eval (1 - r)
noncomputable def criticalRowCoeff (c : ℝ) (D n : ℕ) (u : ℝ[X]) (r : ℝ) : ℝ :=
  -2 * c * Real.sqrt ((2 * (n : ℝ) + 1) / 2) * criticalJSum D n u r
theorem integral_reflected_translation_neg (n D : ℕ) (u : ℝ[X])
    (hu : u.natDegree ≤ D) (r : ℝ) :
    (∫ t in (1 - r)..1, u.eval (t + r) * (legP n).eval t) =
      -criticalJSum D n u r := by
  set w : ℝ[X] := u.comp (C (2 : ℝ) - X) with hw
  have hqdeg : (C (2 : ℝ) - X : ℝ[X]).natDegree ≤ 1 := by
    rw [show (C (2 : ℝ) - X : ℝ[X]) = -(X - C 2) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hwdeg : w.natDegree ≤ D := by
    rw [hw]
    calc (u.comp (C (2 : ℝ) - X : ℝ[X])).natDegree
        ≤ u.natDegree * (C (2 : ℝ) - X : ℝ[X]).natDegree :=
          Polynomial.natDegree_comp_le
      _ ≤ D * 1 := Nat.mul_le_mul hu hqdeg
      _ = D := by ring
  have h := integral_reflected_translation n D w hwdeg (r := r)
  have hcongr : (∫ t in (1 - r)..1, w.eval (2 - r - t) * (legP n).eval t) =
      ∫ t in (1 - r)..1, u.eval (t + r) * (legP n).eval t := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hwt : w.eval (2 - r - t) = u.eval (t + r) := by
      rw [hw]
      simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X]
      congr 1
      ring
    rw [hwt]
  rw [hcongr] at h
  have hsum : (∑ d ∈ Finset.range (D + 1),
        ((Polynomial.derivative^[d]) w).eval 1 * (J legP (d + 1) n).eval (1 - r)) =
      ∑ d ∈ Finset.range (D + 1), (-1 : ℝ) ^ d *
        ((Polynomial.derivative^[d]) u).eval 1 * (J legP (d + 1) n).eval (1 - r) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [hw, eval_iterate_derivative_comp_C_sub_X]
    ring
  rw [hsum] at h
  simpa [criticalJSum] using h
end Y7Critical
end
end Inline_Y7_Legendre
section Inline_Y7_Moments
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators Real
namespace Y7Moments
lemma tendsto_pow_mul_neg_log (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ (n + 1) * (-Real.log x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hupper : Tendsto (fun x : ℝ => (2 : ℝ) * x ^ n * Real.sqrt x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => (2 : ℝ) * x ^ n * Real.sqrt x) :=
      (continuous_const.mul (continuous_id.pow n)).mul Real.continuous_sqrt
    have hlim : Tendsto (fun x : ℝ => (2 : ℝ) * x ^ n * Real.sqrt x) (𝓝 (0 : ℝ))
        (𝓝 ((2 : ℝ) * (0 : ℝ) ^ n * Real.sqrt 0)) := hcont.continuousAt.tendsto
    have hlim' : Tendsto (fun x : ℝ => (2 : ℝ) * x ^ n * Real.sqrt x) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hlim
    exact hlim'.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · have h0mem : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x ∈ Ioo (-1 : ℝ) 1 :=
      Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
    have h2 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      (h0mem.filter_mono nhdsWithin_le_nhds).mono (fun x hx => hx.2)
    filter_upwards [self_mem_nhdsWithin, h2] with x hx hx1
    exact mul_nonneg (pow_pos hx _).le (neg_nonneg.mpr (Real.log_nonpos hx.le hx1.le))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have h1 : -Real.log x ≤ 2 / Real.sqrt x := by
      have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 / Real.sqrt x by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt hs), Real.log_one,
        Real.log_sqrt hxpos.le] at h
      have h' : -Real.log x / 2 ≤ 1 / Real.sqrt x := by linarith
      have h2 : (2 : ℝ) / Real.sqrt x = 2 * (1 / Real.sqrt x) := by ring
      rw [h2]
      linarith
    refine (mul_le_mul_of_nonneg_left h1 (pow_nonneg hxpos.le _)).trans_eq ?_
    have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
    have hs' : Real.sqrt x * Real.sqrt x = x := by rw [← sq, hs]
    have hsne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxpos)
    have hxdiv : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
      rw [← div_eq_mul_inv, div_eq_iff hsne]
      exact hs'.symm
    rw [div_eq_mul_inv]
    calc x ^ (n + 1) * (2 * (Real.sqrt x)⁻¹)
        = 2 * (x ^ (n + 1) * (Real.sqrt x)⁻¹) := by ring
      _ = 2 * (x ^ n * (x * (Real.sqrt x)⁻¹)) := by rw [pow_succ]; ring
      _ = 2 * (x ^ n * Real.sqrt x) := by rw [hxdiv]
      _ = 2 * x ^ n * Real.sqrt x := by ring
lemma neg_log_le_two_div_sqrt {x : ℝ} (hx : 0 < x) :
    -Real.log x ≤ 2 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 / Real.sqrt x by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hs), Real.log_one,
    Real.log_sqrt hx.le] at h
  have h' : -Real.log x / 2 ≤ 1 / Real.sqrt x := by linarith
  have h2 : (2 : ℝ) / Real.sqrt x = 2 * (1 / Real.sqrt x) := by ring
  rw [h2]
  linarith
theorem integral_x_pow_mul_neg_log (n : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ n * (-Real.log x) = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x)
          + x ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (x ^ n * (-Real.log x)) x := by
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    have hpow : HasDerivAt (fun x : ℝ => x ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) x
    have h1 : HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1))
        (((n : ℝ) + 1) * x ^ n / ((n : ℝ) + 1)) x :=
      hpow.div_const _
    have h2 : HasDerivAt (fun x : ℝ => -Real.log x) (-(1 / x)) x := by
      convert (Real.hasDerivAt_log hxne).neg using 1
      simp [one_div]
    have h3 : HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (((n : ℝ) + 1) * x ^ n / ((n : ℝ) + 1) ^ 2) x :=
      hpow.div_const _
    have hsum := (h1.mul h2).add h3
    convert hsum using 1
    field_simp [hxne, show ((n : ℝ) + 1) ≠ 0 by positivity]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => x ^ n * (-Real.log x)) volume 0 1 := by
    have hg : IntervalIntegrable (fun x : ℝ => (2 : ℝ) * x ^ (-(1 / 2) : ℝ)) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow'
        (show (-1 : ℝ) < -(1 / 2) by norm_num)).const_mul 2
    refine hg.mono_fun' ?_ ?_
    · exact ((continuous_id.pow n).measurable.mul Real.measurable_log.neg).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hx1 : 0 < x := hx.1
      have hx2 : x ≤ 1 := hx.2
      have hlog : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx1.le hx2)
      have hnorm : ‖x ^ n * (-Real.log x)‖ = x ^ n * (-Real.log x) :=
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx1.le _) hlog)
      rw [hnorm]
      calc x ^ n * (-Real.log x) ≤ 1 * (2 / Real.sqrt x) :=
            mul_le_mul (pow_le_one₀ hx1.le hx2) (neg_log_le_two_div_sqrt hx1)
              hlog (by norm_num)
        _ = 2 * x ^ (-(1 / 2) : ℝ) := by
            rw [one_mul, Real.rpow_neg hx1.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hlim0 : Tendsto (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x)
      + x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_pow_mul_neg_log n).div_const ((n : ℝ) + 1)
      have heq : (fun x : ℝ => x ^ (n + 1) * (-Real.log x) / ((n : ℝ) + 1))
          = fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x) := by
        funext x
        ring
      rw [heq] at h
      simpa using h
    have h2 : Tendsto (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) 0 :=
        (continuousAt_id.pow (n + 1)).div_const _
      have hval : ((0 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) = 0 := by simp
      simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.add h2
  have hlim1 : Tendsto (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x)
      + x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (1 / ((n : ℝ) + 1) ^ 2)) := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log x)
        + x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) 1 :=
      (((continuousAt_id.pow (n + 1)).div_const _).mul
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt.neg).add
        ((continuousAt_id.pow (n + 1)).div_const _)
    have hval : ((1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log 1)
        + (1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) ^ 2) = 1 / ((n : ℝ) + 1) ^ 2 := by
      simp
    simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) < 1) hderiv hint hlim0 hlim1
  simpa using hmain
lemma hasDerivAt_sum_powers (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), x ^ (k + 1) / ((k : ℝ) + 1))
      (∑ k ∈ Finset.range (n + 1), x ^ k) x := by
  have h : HasDerivAt (∑ k ∈ Finset.range (n + 1), fun y : ℝ => y ^ (k + 1) / ((k : ℝ) + 1))
      (∑ k ∈ Finset.range (n + 1), x ^ k) x := by
    refine HasDerivAt.sum (u := Finset.range (n + 1))
      (A := fun k y => y ^ (k + 1) / ((k : ℝ) + 1)) (A' := fun k => x ^ k) ?_
    intro k _
    have hpow : HasDerivAt (fun y : ℝ => y ^ (k + 1)) (((k : ℝ) + 1) * x ^ k) x := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (k + 1) x
    convert hpow.div_const ((k : ℝ) + 1) using 1
    field_simp
  convert h using 1
  funext y
  simp only [Finset.sum_apply]
set_option maxHeartbeats 2000000 in
lemma intervalIntegrable_x_pow_mul_neg_log_one_sub (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * (-Real.log (1 - x))) volume 0 1 := by
    have hg : IntervalIntegrable (fun x : ℝ => (2 : ℝ) * (1 - x) ^ (-(1 / 2) : ℝ)) volume 0 1 := by
      have h0 : IntervalIntegrable (fun x : ℝ => (2 : ℝ) * x ^ (-(1 / 2) : ℝ)) volume 1 0 :=
        (intervalIntegral.intervalIntegrable_rpow'
          (show (-1 : ℝ) < -(1 / 2) by norm_num)).const_mul 2
      have h1 := h0.comp_sub_left (1 : ℝ) (by simp)
      simpa using h1
    refine hg.mono_fun' ?_ ?_
    · exact ((continuous_id.pow n).measurable.mul
        (Real.measurable_log.comp (measurable_const.sub measurable_id)).neg).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have hx1 : 0 < x := hx.1
      have hx2 : x ≤ 1 := hx.2
      rcases eq_or_lt_of_le hx2 with rfl | hx2'
      · simp
      · have h1x : 0 < 1 - x := by linarith
        have hlog2 : 0 ≤ -Real.log (1 - x) :=
          neg_nonneg.mpr (Real.log_nonpos h1x.le (by linarith))
        have hnorm : ‖x ^ n * (-Real.log (1 - x))‖ = x ^ n * (-Real.log (1 - x)) :=
          Real.norm_of_nonneg (mul_nonneg (pow_nonneg hx1.le _) hlog2)
        rw [hnorm]
        calc x ^ n * (-Real.log (1 - x)) ≤ 1 * (2 / Real.sqrt (1 - x)) :=
              mul_le_mul (pow_le_one₀ hx1.le hx2) (neg_log_le_two_div_sqrt h1x) hlog2 (by norm_num)
          _ = 2 * (1 - x) ^ (-(1 / 2) : ℝ) := by
              rw [one_mul, Real.rpow_neg h1x.le, Real.sqrt_eq_rpow, div_eq_mul_inv]
set_option maxHeartbeats 2000000 in
theorem integral_x_pow_mul_neg_log_one_sub (n : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ n * (-Real.log (1 - x)) =
      (∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1)) / ((n : ℝ) + 1) := by
  set F : ℝ → ℝ := fun x => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log (1 - x))
    + (1 / ((n : ℝ) + 1)) * ((∑ k ∈ Finset.range (n + 1), x ^ (k + 1) / ((k : ℝ) + 1))
        + Real.log (1 - x)) with hF
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (x ^ n * (-Real.log (1 - x))) x := by
    intro x hx
    rw [hF]
    have hne : (1 - x) ≠ 0 := by linarith [hx.2]
    have hpow : HasDerivAt (fun x : ℝ => x ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) x
    have hp1 : HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1)) (x ^ n) x := by
      convert hpow.div_const ((n : ℝ) + 1) using 1
      field_simp
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      have h := ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => rfl))
      convert h using 1
      · funext y
        rfl
      · norm_num
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 / (1 - x))) x := by
      convert hsub.log hne using 1
      ring
    have hneglog : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 / (1 - x)) x := by
      convert hlog.neg using 1
      ring
    have hsum := hasDerivAt_sum_powers n x
    have htotal := (hp1.mul hneglog).add ((hsum.add hlog).const_mul (1 / ((n : ℝ) + 1)))
    have hgeom : (∑ k ∈ Finset.range (n + 1), x ^ k) * (1 - x) = 1 - x ^ (n + 1) :=
      geom_sum_mul_neg x (n + 1)
    have hgeom' : (1 - x) * (∑ k ∈ Finset.range (n + 1), x ^ k) = 1 - x ^ (n + 1) := by
      rw [mul_comm, hgeom]
    refine htotal.congr_deriv ?_
    field_simp [hne, show ((n : ℝ) + 1) ≠ 0 by positivity]
    rw [hgeom']
    ring
  have hlim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [hF]
    have hcont : ContinuousAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log (1 - x))
        + (1 / ((n : ℝ) + 1)) * ((∑ k ∈ Finset.range (n + 1),
            x ^ (k + 1) / ((k : ℝ) + 1)) + Real.log (1 - x))) 0 := by
      have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
        (continuousAt_const.sub continuousAt_id).log (by norm_num : (1 - (0 : ℝ)) ≠ 0)
      have hsum : ContinuousAt (fun x : ℝ =>
          ∑ k ∈ Finset.range (n + 1), x ^ (k + 1) / ((k : ℝ) + 1)) 0 :=
        (hasDerivAt_sum_powers n 0).continuousAt
      exact (((continuousAt_id.pow (n + 1)).div_const _).mul hlog.neg).add
        ((hsum.add hlog).const_mul _)
    have hval : ((0 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log (1 - 0))
        + (1 / ((n : ℝ) + 1)) * ((∑ k ∈ Finset.range (n + 1),
            (0 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) + Real.log (1 - 0))) = 0 := by
      simp
    simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto F (𝓝[<] (1 : ℝ))
      (𝓝 ((∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1)) / ((n : ℝ) + 1))) := by
    have hsub' : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      have h1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
        have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
          tendsto_const_nhds
        have hid : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa using hconst.sub hid
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      show 0 < 1 - x
      exact sub_pos.mpr hx
    have hG : Tendsto (fun x : ℝ => (1 - x) * (-Real.log (1 - x))) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun x : ℝ => (1 - x) ^ (0 + 1) * (-Real.log (1 - x)))
          (𝓝[<] (1 : ℝ)) (𝓝 0) :=
        (tendsto_pow_mul_neg_log 0).comp hsub'
      refine h.congr' (Filter.Eventually.of_forall (fun x => ?_))
      simp
    have hsum1 : Tendsto (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        x ^ (k + 1) / ((k : ℝ) + 1)) (𝓝[<] (1 : ℝ))
        (𝓝 (∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1))) := by
      have hcont : ContinuousAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
          x ^ (k + 1) / ((k : ℝ) + 1)) 1 :=
        (continuous_finsetSum _ (fun k _ => (continuous_id.pow (k + 1)).div_const _)).continuousAt
      have hval : (∑ k ∈ Finset.range (n + 1), (1 : ℝ) ^ (k + 1) / ((k : ℝ) + 1))
          = ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1) := by simp
      simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hsumk : Tendsto (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), x ^ k) (𝓝[<] (1 : ℝ))
        (𝓝 ((n : ℝ) + 1)) := by
      have hcont : ContinuousAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1), x ^ k) 1 :=
        (continuous_finsetSum _ (fun k _ => continuous_id.pow k)).continuousAt
      have hval : (∑ k ∈ Finset.range (n + 1), (1 : ℝ) ^ k) = (n : ℝ) + 1 := by simp
      simpa [hval] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hmul : Tendsto (fun x : ℝ => -(∑ k ∈ Finset.range (n + 1), x ^ k)
        * ((1 - x) * (-Real.log (1 - x)))) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have h := hsumk.neg.mul hG
      simpa using h
    have hfac : Tendsto (fun x : ℝ => (1 / ((n : ℝ) + 1)) * (-(∑ k ∈ Finset.range (n + 1), x ^ k)
        * ((1 - x) * (-Real.log (1 - x))) + ∑ k ∈ Finset.range (n + 1),
          x ^ (k + 1) / ((k : ℝ) + 1))) (𝓝[<] (1 : ℝ))
        (𝓝 ((∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1)) / ((n : ℝ) + 1))) := by
      have h := (hmul.add hsum1).const_mul (1 / ((n : ℝ) + 1))
      rw [show (1 / ((n : ℝ) + 1)) * (0 + ∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1))
          = (∑ k ∈ Finset.range (n + 1), 1 / ((k : ℝ) + 1)) / ((n : ℝ) + 1) by ring] at h
      exact h
    rw [hF]
    refine hfac.congr' (Filter.Eventually.of_forall ?_)
    intro x
    have hgeom : (∑ k ∈ Finset.range (n + 1), x ^ k) * (1 - x) = 1 - x ^ (n + 1) :=
      geom_sum_mul_neg x (n + 1)
    have key : x ^ (n + 1) * (-Real.log (1 - x)) + Real.log (1 - x)
        = (∑ k ∈ Finset.range (n + 1), x ^ k) * (1 - x) * Real.log (1 - x) := by
      rw [hgeom]
      ring
    field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]
    linear_combination -key
  have hint := intervalIntegrable_x_pow_mul_neg_log_one_sub n
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) < 1) hderiv hint hlim0 hlim1
  simpa using hmain
lemma hasDerivAt_sum_signed_powers (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * (x ^ (k + 1) / ((k : ℝ) + 1)))
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k) x := by
  have h : HasDerivAt (∑ k ∈ Finset.range (n + 1),
      fun y : ℝ => (-1 : ℝ) ^ k * (y ^ (k + 1) / ((k : ℝ) + 1)))
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k) x := by
    refine HasDerivAt.sum (u := Finset.range (n + 1))
      (A := fun k y => (-1 : ℝ) ^ k * (y ^ (k + 1) / ((k : ℝ) + 1)))
      (A' := fun k => (-1 : ℝ) ^ k * x ^ k) ?_
    intro k _
    have hpow : HasDerivAt (fun y : ℝ => y ^ (k + 1)) (((k : ℝ) + 1) * x ^ k) x := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (k + 1) x
    have hp1 : HasDerivAt (fun y : ℝ => y ^ (k + 1) / ((k : ℝ) + 1)) (x ^ k) x := by
      convert hpow.div_const ((k : ℝ) + 1) using 1
      field_simp
    exact hp1.const_mul ((-1 : ℝ) ^ k)
  convert h using 1
  funext y
  simp only [Finset.sum_apply]
set_option maxHeartbeats 2000000 in
lemma intervalIntegrable_x_pow_mul_neg_log_one_add (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * (-Real.log (1 + x))) volume 0 1 := by
    have hc : ContinuousOn (fun x : ℝ => x ^ n * (-Real.log (1 + x))) (Set.uIcc 0 1) := by
      have hlog : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.uIcc 0 1) :=
        (continuous_const.add continuous_id).continuousOn.log (fun x hx => by
          rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
          have hpos : (0 : ℝ) < 1 + x := by linarith [hx.1]
          simpa only [Pi.add_apply, id_eq] using hpos.ne')
      exact (continuous_id.continuousOn.pow n).mul hlog.neg
    exact hc.intervalIntegrable
set_option maxHeartbeats 2000000 in
theorem integral_x_pow_mul_neg_log_one_add (n : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ n * (-Real.log (1 + x)) =
      (((-1 : ℝ) ^ n * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1))) +
        ((-1 : ℝ) ^ (n + 1) - 1) * Real.log 2) / ((n : ℝ) + 1) := by
  set F : ℝ → ℝ := fun x => x ^ (n + 1) / ((n : ℝ) + 1) * (-Real.log (1 + x))
    + (1 / ((n : ℝ) + 1)) * ((-1 : ℝ) ^ n * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * (x ^ (k + 1) / ((k : ℝ) + 1))) + (-1 : ℝ) ^ (n + 1) * Real.log (1 + x))
    with hF
  have hderiv : ∀ x : ℝ, x ≠ -1 → HasDerivAt F (x ^ n * (-Real.log (1 + x))) x := by
    intro x hx
    rw [hF]
    have h1x : (1 + x) ≠ 0 := by intro h; exact hx (by linarith)
    have hpow : HasDerivAt (fun x : ℝ => x ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      simpa [Nat.cast_add, Nat.cast_one] using hasDerivAt_pow (n + 1) x
    have hp1 : HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n : ℝ) + 1)) (x ^ n) x := by
      convert hpow.div_const ((n : ℝ) + 1) using 1
      field_simp
    have hadd1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by
      have h := (hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x)
      convert h using 1
      · funext y
        rfl
      · ring
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x := by
      convert hadd1.log h1x using 1
    have hneglog : HasDerivAt (fun x : ℝ => -Real.log (1 + x)) (-(1 / (1 + x))) x := by
      convert hlog.neg using 1
    have hsum := hasDerivAt_sum_signed_powers n x
    have htotal := (hp1.mul hneglog).add
      (((hsum.const_mul ((-1 : ℝ) ^ n)).add (hlog.const_mul ((-1 : ℝ) ^ (n + 1)))).const_mul
        (1 / ((n : ℝ) + 1)))
    have hgeom : (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k) * (1 + x)
        = 1 - (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) := by
      have h := geom_sum_mul_neg (-x) (n + 1)
      have hsum' : (∑ i ∈ Finset.range (n + 1), (-x) ^ i)
          = ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [neg_pow]
      rw [hsum'] at h
      rw [show (1 : ℝ) - -x = 1 + x by ring] at h
      rw [h, neg_pow]
    have hgeom' : (1 + x) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k)
        = 1 - (-1 : ℝ) ^ (n + 1) * x ^ (n + 1) := by
      rw [mul_comm, hgeom]
    refine htotal.congr_deriv ?_
    have hodd : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by rw [pow_succ]; ring
    have hsq : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_add, show n + n = 2 * n by ring, pow_mul]
      simp
    field_simp [h1x, show ((n : ℝ) + 1) ≠ 0 by positivity]
    rw [show (1 + x) * (-1 : ℝ) ^ n * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k)
        = (1 + x) * (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k) * (-1 : ℝ) ^ n by ring]
    rw [hgeom', hodd]
    linear_combination (x ^ (n + 1)) * hsq
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = (((-1 : ℝ) ^ n * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k / ((k : ℝ) + 1))) + ((-1 : ℝ) ^ (n + 1) - 1) * Real.log 2)
      / ((n : ℝ) + 1) := by
    simp [hF]
    ring
  have hlim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
      (((hderiv 0 (by norm_num)).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
    simpa [hF0] using h
  have hlim1 : Tendsto F (𝓝[<] (1 : ℝ))
      (𝓝 ((((-1 : ℝ) ^ n * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k / ((k : ℝ) + 1))) + ((-1 : ℝ) ^ (n + 1) - 1) * Real.log 2)
        / ((n : ℝ) + 1))) := by
    have h : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 (F 1)) :=
      (((hderiv 1 (by norm_num)).continuousAt).tendsto).mono_left nhdsWithin_le_nhds
    simpa [hF1] using h
  have hint := intervalIntegrable_x_pow_mul_neg_log_one_add n
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) < 1) (fun x hx => hderiv x (by have := hx.1; linarith)) hint
    hlim0 hlim1
  simpa using hmain
lemma sum_range_two_mul_add_one (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m + 1), f k)
      = (∑ j ∈ Finset.range (m + 1), f (2 * j)) + ∑ j ∈ Finset.range m, f (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    conv_lhs =>
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    conv_rhs =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    ring
lemma sum_one_div_add_alternating (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m + 1), (1 : ℝ) / ((k : ℝ) + 1))
      + (∑ k ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1))
    = 2 * ∑ r ∈ Finset.range (m + 1), 1 / (((2 * r : ℕ) : ℝ) + 1) := by
  rw [← Finset.sum_add_distrib]
  rw [show (fun k : ℕ => 1 / ((k : ℝ) + 1) + (-1 : ℝ) ^ k / ((k : ℝ) + 1))
      = fun k : ℕ => (1 + (-1 : ℝ) ^ k) / ((k : ℝ) + 1) by
    funext k
    rw [add_div]]
  rw [sum_range_two_mul_add_one]
  have hodd : (∑ j ∈ Finset.range m,
      (1 + (-1 : ℝ) ^ (2 * j + 1)) / (((2 * j + 1 : ℕ) : ℝ) + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Odd.neg_one_pow ⟨j, by ring⟩]
    norm_num
  rw [hodd, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Even.neg_one_pow ⟨r, by ring⟩]
  ring
theorem integral_x_pow_mul_neg_log_one_add_even (ℓ : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ (2 * ℓ) * (-Real.log (1 + x)) =
      ((∑ k ∈ Finset.range (2 * ℓ + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1))
        - 2 * Real.log 2) / (((2 * ℓ : ℕ) : ℝ) + 1) := by
  have h := integral_x_pow_mul_neg_log_one_add (2 * ℓ)
  have h1 : (-1 : ℝ) ^ (2 * ℓ) = 1 := Even.neg_one_pow ⟨ℓ, by ring⟩
  have h2 : (-1 : ℝ) ^ (2 * ℓ + 1) = -1 := Odd.neg_one_pow ⟨ℓ, by ring⟩
  rw [h1, h2] at h
  have hrw : (1 * (∑ k ∈ Finset.range (2 * ℓ + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1))
      + (-1 - 1) * Real.log 2) / (((2 * ℓ : ℕ) : ℝ) + 1)
      = ((∑ k ∈ Finset.range (2 * ℓ + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1))
        - 2 * Real.log 2) / (((2 * ℓ : ℕ) : ℝ) + 1) := by
    ring
  rw [hrw] at h
  exact h
lemma integral_neg_one_zero_x_pow_mul_neg_log_one_sub (ℓ : ℕ) :
    ∫ x in (-1 : ℝ)..0, x ^ (2 * ℓ) * (-Real.log (1 - x))
      = ∫ x in (0 : ℝ)..1, x ^ (2 * ℓ) * (-Real.log (1 + x)) := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => x ^ (2 * ℓ) * (-Real.log (1 + x))) (a := (-1 : ℝ)) (b := 0)
  rw [show (fun x : ℝ => (-x) ^ (2 * ℓ) * (-Real.log (1 + -x)))
      = fun x : ℝ => x ^ (2 * ℓ) * (-Real.log (1 - x)) by
    funext x
    rw [Even.neg_pow ⟨ℓ, by ring⟩ x, show (1 : ℝ) + -x = 1 - x by ring]] at h
  simpa using h
lemma integral_neg_one_zero_x_pow_mul_neg_log_one_add (ℓ : ℕ) :
    ∫ x in (-1 : ℝ)..0, x ^ (2 * ℓ) * (-Real.log (1 + x))
      = ∫ x in (0 : ℝ)..1, x ^ (2 * ℓ) * (-Real.log (1 - x)) := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun x : ℝ => x ^ (2 * ℓ) * (-Real.log (1 - x))) (a := (-1 : ℝ)) (b := 0)
  rw [show (fun x : ℝ => (-x) ^ (2 * ℓ) * (-Real.log (1 - -x)))
      = fun x : ℝ => x ^ (2 * ℓ) * (-Real.log (1 + x)) by
    funext x
    rw [Even.neg_pow ⟨ℓ, by ring⟩ x, show (1 : ℝ) - -x = 1 + x by ring]] at h
  simpa using h
lemma even_x_pow_mul_potential_expansion (l : ℕ) {x : ℝ} (hx1 : 0 < 1 - x)
    (hx2 : 0 < 1 + x) :
    x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2))
      = (1 / 2) * (x ^ (2 * l) * (-Real.log (1 - x)))
        + (1 / 2) * (x ^ (2 * l) * (-Real.log (1 + x))) := by
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hlog : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
    rw [hfac, Real.log_mul (ne_of_gt hx1) (ne_of_gt hx2)]
  rw [hlog]
  ring_nf
lemma intervalIntegrable_neg_one_zero_x_pow_mul_neg_log_one_sub (l : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * l) * (-Real.log (1 - x)))
      volume (-1) 0 := by
  rw [IntervalIntegrable.iff_comp_neg
    (f := fun x : ℝ => x ^ (2 * l) * (-Real.log (1 - x))) (a := (-1 : ℝ)) (b := 0)]
  have hb : IntervalIntegrable (fun x : ℝ => x ^ (2 * l) * (-Real.log (1 + x)))
      volume 1 0 := (intervalIntegrable_x_pow_mul_neg_log_one_add (2 * l)).symm
  have hfun : (fun x : ℝ => (-x) ^ (2 * l) * (-Real.log (1 - -x)))
      = fun x : ℝ => x ^ (2 * l) * (-Real.log (1 + x)) := by
    funext x
    rw [Even.neg_pow ⟨l, by ring⟩ x, sub_neg_eq_add]
  rw [hfun]
  simpa using hb
lemma intervalIntegrable_neg_one_zero_x_pow_mul_neg_log_one_add (l : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * l) * (-Real.log (1 + x)))
      volume (-1) 0 := by
  rw [IntervalIntegrable.iff_comp_neg
    (f := fun x : ℝ => x ^ (2 * l) * (-Real.log (1 + x))) (a := (-1 : ℝ)) (b := 0)]
  have hb : IntervalIntegrable (fun x : ℝ => x ^ (2 * l) * (-Real.log (1 - x)))
      volume 1 0 := (intervalIntegrable_x_pow_mul_neg_log_one_sub (2 * l)).symm
  have hfun : (fun x : ℝ => (-x) ^ (2 * l) * (-Real.log (1 + -x)))
      = fun x : ℝ => x ^ (2 * l) * (-Real.log (1 - x)) := by
    funext x
    rw [Even.neg_pow ⟨l, by ring⟩ x, show (1 : ℝ) + -x = 1 - x by ring]
  rw [hfun]
  simpa using hb
set_option maxHeartbeats 2000000 in
theorem integral_even_x_pow_mul_potential (l : ℕ) :
    ∫ x in (-1 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2))
      = ((∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1)) - Real.log 2)
          / ((l : ℝ) + 1 / 2) := by
  have hint0 : IntervalIntegrable
      (fun x : ℝ => x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2))) volume (-1) 0 :=
    (((intervalIntegrable_neg_one_zero_x_pow_mul_neg_log_one_sub l).const_mul (1 / 2)).add
      ((intervalIntegrable_neg_one_zero_x_pow_mul_neg_log_one_add l).const_mul (1 / 2))).congr_uIoo
      (by
        intro x hx
        rw [uIoo_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
        exact (even_x_pow_mul_potential_expansion l (by linarith [hx.2])
          (by linarith [hx.1])).symm)
  have hint1 : IntervalIntegrable
      (fun x : ℝ => x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2))) volume 0 1 :=
    (((intervalIntegrable_x_pow_mul_neg_log_one_sub (2 * l)).const_mul (1 / 2)).add
      ((intervalIntegrable_x_pow_mul_neg_log_one_add (2 * l)).const_mul (1 / 2))).congr_uIoo
      (by
        intro x hx
        rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact (even_x_pow_mul_potential_expansion l (by linarith [hx.2])
          (by linarith [hx.1])).symm)
  have hneg : (∫ x in (-1 : ℝ)..0, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)))
      = ∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)))
      (a := (-1 : ℝ)) (b := 0)
    have hcongr : (∫ x in (-1 : ℝ)..0, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)))
        = ∫ x in (-1 : ℝ)..0,
            (-x) ^ (2 * l) * (-(1 / 2) * Real.log (1 - (-x) ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro x _
      show x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2))
          = (-x) ^ (2 * l) * (-(1 / 2) * Real.log (1 - (-x) ^ 2))
      rw [Even.neg_pow ⟨l, by ring⟩ x, show (1 : ℝ) - (-x) ^ 2 = 1 - x ^ 2 by ring]
    rw [hcongr]
    simpa using hcomp
  have h01 : (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)))
      = (1 / 2) * ((∑ k ∈ Finset.range (2 * l + 1), 1 / ((k : ℝ) + 1))
            / (((2 * l : ℕ) : ℝ) + 1))
        + (1 / 2) * (((∑ k ∈ Finset.range (2 * l + 1),
              (-1 : ℝ) ^ k / ((k : ℝ) + 1)) - 2 * Real.log 2)
            / (((2 * l : ℕ) : ℝ) + 1)) := by
    calc (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)))
        = ∫ x in (0 : ℝ)..1, ((1 / 2) * (x ^ (2 * l) * (-Real.log (1 - x)))
            + (1 / 2) * (x ^ (2 * l) * (-Real.log (1 + x)))) := by
          apply intervalIntegral.integral_congr_uIoo
          intro x hx
          rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
          exact even_x_pow_mul_potential_expansion l (x := x) (by linarith [hx.2])
            (by linarith [hx.1])
      _ = (1 / 2) * (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 - x)))
            + (1 / 2) * (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 + x))) := by
          rw [intervalIntegral.integral_add
              ((intervalIntegrable_x_pow_mul_neg_log_one_sub (2 * l)).const_mul (1 / 2))
              ((intervalIntegrable_x_pow_mul_neg_log_one_add (2 * l)).const_mul (1 / 2))]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = (1 / 2) * ((∑ k ∈ Finset.range (2 * l + 1), 1 / ((k : ℝ) + 1))
            / (((2 * l : ℕ) : ℝ) + 1))
        + (1 / 2) * (((∑ k ∈ Finset.range (2 * l + 1),
              (-1 : ℝ) ^ k / ((k : ℝ) + 1)) - 2 * Real.log 2)
            / (((2 * l : ℕ) : ℝ) + 1)) := by
          rw [integral_x_pow_mul_neg_log_one_sub, integral_x_pow_mul_neg_log_one_add_even]
  have hmain := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
  rw [← hmain, hneg, h01]
  set H := ∑ k ∈ Finset.range (2 * l + 1), 1 / ((k : ℝ) + 1) with hHdef
  set Alt := ∑ k ∈ Finset.range (2 * l + 1), (-1 : ℝ) ^ k / ((k : ℝ) + 1) with hAltdef
  set D := (((2 * l : ℕ) : ℝ) + 1) with hDdef
  set hl := ∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1) with hhldef
  have hD : D = 2 * ((l : ℝ) + 1 / 2) := by
    rw [hDdef]
    push_cast
    ring
  have hcast : (∑ r ∈ Finset.range (l + 1), 1 / (((2 * r : ℕ) : ℝ) + 1)) = hl := by
    rw [hhldef]
    apply Finset.sum_congr rfl
    intro r _
    have h2r : (((2 * r : ℕ) : ℝ)) = 2 * (r : ℝ) := by
      push_cast
      ring
    rw [h2r]
  have hHA : H + Alt = 2 * hl := by
    rw [hHdef, hAltdef, ← hcast]
    exact sum_one_div_add_alternating l
  rw [hD]
  have hden : (2 : ℝ) * ((l : ℝ) + 1 / 2) ≠ 0 := by positivity
  have hden' : ((l : ℝ) + 1 / 2) ≠ 0 := by positivity
  field_simp
  linarith [hHA]
lemma bernoulli_two_eval_one_half :
    (Polynomial.bernoulli 2).eval ((1 : ℚ) / 2) = -1 / 12 := by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero, Polynomial.eval_zero, zero_add]
  rw [_root_.bernoulli_zero, _root_.bernoulli_one, _root_.bernoulli_two]
  norm_num
lemma hasSum_alternating_zeta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hcos := hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num)
    (x := (1 / 2 : ℝ)) (by norm_num)
  have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval
      (1 / 2 : ℝ) = -1 / 12 := by
    have hcast : (1 / 2 : ℝ) = algebraMap ℚ ℝ (1 / 2 : ℚ) := by norm_num
    rw [show 2 * 1 = 2 by norm_num, hcast, Polynomial.eval_map_apply,
      bernoulli_two_eval_one_half]
    norm_num
  have hcos' : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 * (-1) ^ n)
      (-(π ^ 2 / 12)) := by
    have hfun : (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * 1) *
        Real.cos (2 * π * (n : ℝ) * (1 / 2)))
        = fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 * (-1) ^ n := by
      funext n
      rw [show 2 * π * (n : ℝ) * (1 / 2) = (n : ℝ) * π by ring,
        Real.cos_nat_mul_pi]
    have hval : (-1 : ℝ) ^ (1 + 1) * (2 * π) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℝ) *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval
          (1 / 2 : ℝ) = -(π ^ 2 / 12) := by
      rw [hB]
      norm_num
      ring
    rwa [hfun, hval] at hcos
  have hoff : HasSum (fun n : ℕ => -(1 / (n : ℝ) ^ 2 * (-1) ^ n)) (π ^ 2 / 12) := by
    simpa using hcos'.neg
  have hshift : HasSum
      (fun n : ℕ => -(1 / (((n + 1 : ℕ)) : ℝ) ^ 2 * (-1 : ℝ) ^ (n + 1)))
      (π ^ 2 / 12) :=
    (hasSum_nat_add_iff (f := fun m : ℕ => -(1 / (m : ℝ) ^ 2 * (-1 : ℝ) ^ m)) 1).mpr
      (by simpa using hoff)
  have hfun : (fun n : ℕ => -(1 / (((n + 1 : ℕ)) : ℝ) ^ 2 * (-1 : ℝ) ^ (n + 1)))
      = fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 := by
    funext n
    push_cast
    rw [pow_succ]
    ring
  rwa [hfun] at hshift
lemma hasSum_neg_one_pow_mul_pow_div_nat_add (t : ℝ) (ht : t ≠ 0) (ht1 : |t| < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * t ^ n / ((n : ℝ) + 1)) (Real.log (1 + t) / t) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := -t) (by rwa [abs_neg])
  have h2 := h.neg.mul_left (1 / t)
  have hfun : (fun n : ℕ => (1 / t) * (-(((-t) ^ (n + 1)) / ((n : ℝ) + 1))))
      = fun n : ℕ => (-1 : ℝ) ^ n * t ^ n / ((n : ℝ) + 1) := by
    funext n
    rw [neg_pow]
    have hodd : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by rw [pow_succ]; ring
    rw [hodd]
    field_simp [ht]
    rw [pow_succ]
    ring
  rw [hfun] at h2
  rw [show (1 : ℝ) - -t = 1 + t by ring, neg_neg] at h2
  have h3 : (1 / t) * Real.log (1 + t) = Real.log (1 + t) / t := by
    rw [div_eq_mul_inv]
    ring
  rwa [h3] at h2
set_option maxHeartbeats 2000000 in
theorem integral_log_one_add_div_self :
    ∫ t in (0 : ℝ)..1, Real.log (1 + t) / t = π ^ 2 / 12 := by
  let μ : Measure ℝ := volume.restrict (Set.uIoc (0 : ℝ) 1)
  have hF_int : ∀ i : ℕ,
      Integrable (fun t : ℝ => (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)) μ := by
    intro i
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)) :=
      (continuous_const.mul (continuous_id.pow i)).div_const _
    exact (hcont.intervalIntegrable 0 1).def'
  have hnorm_int : ∀ i : ℕ,
      (∫ t, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ ∂μ) = 1 / ((i : ℝ) + 1) ^ 2 := by
    intro i
    have hconv : (∫ t, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ ∂μ)
        = ∫ t in (0 : ℝ)..1, t ^ i / ((i : ℝ) + 1) := by
      have hL : (∫ t, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ ∂μ)
          = ∫ t in (0 : ℝ)..1, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ := by
        change (∫ t, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖
            ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)))
          = ∫ t in (0 : ℝ)..1, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [hL]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have ht0 : 0 ≤ t := ht.1
      change ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ = t ^ i / ((i : ℝ) + 1)
      have h1 : ‖(-1 : ℝ) ^ i‖ = 1 := by
        rw [norm_pow, Real.norm_eq_abs, abs_neg, abs_one, one_pow]
      have h2 : ‖t ^ i‖ = t ^ i := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
      have h3 : ‖((i : ℝ) + 1)‖ = (i : ℝ) + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [norm_div, norm_mul, h1, h2, h3, one_mul]
    rw [hconv]
    have hfun : (fun t : ℝ => t ^ i / ((i : ℝ) + 1))
        = fun t : ℝ => (1 / ((i : ℝ) + 1)) * t ^ i := by
      funext t
      rw [div_eq_mul_inv]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero i), sub_zero]
    field_simp
  have hF_sum : Summable (fun i : ℕ =>
      ∫ t, ‖(-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)‖ ∂μ) := by
    have hs : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
      have h' : Summable (fun i : ℕ => (1 : ℝ) / (((i + 1 : ℕ)) : ℝ) ^ 2) :=
        (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr
          hasSum_zeta_two.summable
      simpa only [Nat.cast_add, Nat.cast_one] using h'
    simpa only [hnorm_int] using hs
  have hmain := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_sum
  have hae : (fun t : ℝ => ∑' i : ℕ, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1))
      =ᵐ[μ] fun t : ℝ => Real.log (1 + t) / t := by
    have h1null : μ {1} = 0 := by
      rw [show μ = volume.restrict (Set.uIoc (0 : ℝ) 1) from rfl,
        MeasureTheory.Measure.restrict_apply (measurableSet_singleton (1 : ℝ))]
      exact measure_mono_null Set.inter_subset_left Real.volume_singleton
    have hne1 : ∀ᵐ t ∂μ, t ≠ 1 := by
      rw [MeasureTheory.ae_iff (μ := μ)]
      simpa using h1null
    filter_upwards [hne1, self_mem_ae_restrict measurableSet_uIoc] with t htne htmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at htmem
    have ht0 : 0 < t := htmem.1
    have ht1 : t < 1 := lt_of_le_of_ne htmem.2 htne
    exact (hasSum_neg_one_pow_mul_pow_div_nat_add t (ne_of_gt ht0)
      (by rwa [abs_of_nonneg ht0.le])).tsum_eq
  have hR : (∫ t, (∑' i : ℕ, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)) ∂μ)
      = ∫ t in (0 : ℝ)..1, Real.log (1 + t) / t := by
    rw [MeasureTheory.integral_congr_ae hae]
    change (∫ t, Real.log (1 + t) / t ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)))
        = ∫ t in (0 : ℝ)..1, Real.log (1 + t) / t
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hL : (∑' i : ℕ, ∫ t, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1) ∂μ) = π ^ 2 / 12 := by
    have hterm : ∀ i : ℕ, (∫ t, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1) ∂μ)
        = (-1 : ℝ) ^ i / ((i : ℝ) + 1) ^ 2 := by
      intro i
      have hconv : (∫ t, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1) ∂μ)
          = ∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1) := by
        change (∫ t, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)
            ∂(volume.restrict (Set.uIoc (0 : ℝ) 1)))
          = ∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1)
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [hconv]
      have hfun : (fun t : ℝ => (-1 : ℝ) ^ i * t ^ i / ((i : ℝ) + 1))
          = fun t : ℝ => ((-1 : ℝ) ^ i / ((i : ℝ) + 1)) * t ^ i := by
        funext t
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (Nat.succ_ne_zero i), sub_zero]
      field_simp
    simpa only [hterm] using hasSum_alternating_zeta_two.tsum_eq
  rw [← hR, ← hmain]
  exact hL
lemma integral_one_div_one_add :
    ∫ t in (0 : ℝ)..1, (1 : ℝ) / (1 + t) = Real.log 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h1t : (1 + t) ≠ 0 := by linarith [ht.1]
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      have h' := (hasDerivAt_const (x := t) (c := (1 : ℝ))).add (hasDerivAt_id t)
      convert h' using 1
      · funext y
        rfl
      · ring
    exact h.log h1t
  have hcont : ContinuousOn (fun t : ℝ => (1 : ℝ) / (1 + t)) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id) ?_
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hmain]
  norm_num [Real.log_one]
lemma integral_log_one_add_div_one_add :
    ∫ t in (0 : ℝ)..1, Real.log (1 + t) / (1 + t) = Real.log 2 ^ 2 / 2 := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (1 + t) / (1 + t))
      (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_id) ?_
    · refine ContinuousOn.log (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
    · intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.log (1 + s) ^ 2 / 2)
        (Real.log (1 + t) / (1 + t)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have h1t : (1 + t) ≠ 0 := by linarith [ht.1]
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      have h' := (hasDerivAt_const (x := t) (c := (1 : ℝ))).add (hasDerivAt_id t)
      convert h' using 1
      · funext y
        rfl
      · ring
    have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t :=
      h.log h1t
    have h2 := (hlog.pow 2).div_const 2
    convert h2 using 1
    ring_nf
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hmain]
  norm_num [Real.log_one]
lemma hasDerivAt_log_mul_log_one_add {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.log s * Real.log (1 + s))
      (Real.log (1 + t) / t + Real.log t / (1 + t)) t := by
  have h1t : (1 + t) ≠ 0 := by linarith
  have hlog1 : HasDerivAt Real.log (1 / t) t := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt ht)
  have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have h : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      have h' := (hasDerivAt_const (x := t) (c := (1 : ℝ))).add (hasDerivAt_id t)
      convert h' using 1
      · funext y
        rfl
      · ring
    exact h.log h1t
  have h := hlog1.mul h2
  convert h using 1
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  ring
lemma intervalIntegrable_log_self_div_one_add :
    IntervalIntegrable (fun t : ℝ => Real.log t / (1 + t)) volume 0 1 := by
  have hg : IntervalIntegrable (fun t : ℝ => 2 * t ^ (-(1 / 2) : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul 2
  refine hg.mono_fun' ?_ ?_
  · exact (((Real.measurable_log).div (measurable_const.add measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 + t := by linarith
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
    have hnorm : ‖Real.log t / (1 + t)‖ = -Real.log t / (1 + t) := by
      rw [Real.norm_eq_abs,
        abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hlog h1t.le), neg_div]
    rw [hnorm]
    calc -Real.log t / (1 + t) ≤ -Real.log t := by
          rw [div_le_iff₀ h1t]
          exact le_mul_of_one_le_right (neg_nonneg.mpr hlog) (by linarith)
      _ ≤ 2 * t ^ (-(1 / 2) : ℝ) := by
          have h := neg_log_le_two_div_sqrt ht0
          have hsqrt : 2 / Real.sqrt t = 2 * t ^ (-(1 / 2) : ℝ) := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg ht0.le, div_eq_mul_inv]
          rwa [hsqrt] at h
set_option maxHeartbeats 2000000 in
lemma intervalIntegrable_log_one_add_div_self :
    IntervalIntegrable (fun t : ℝ => Real.log (1 + t) / t) volume 0 1 := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
  · exact ((Real.measurable_log.comp (measurable_const.add measurable_id)).div
      measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 + t := by linarith
    have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    have hnorm : ‖Real.log (1 + t) / t‖ = Real.log (1 + t) / t :=
      Real.norm_of_nonneg (div_nonneg hlog ht0.le)
    rw [hnorm, div_le_iff₀ ht0]
    have := Real.log_le_sub_one_of_pos h1t
    linarith
set_option maxHeartbeats 2000000 in
lemma integral_log_self_div_one_add :
    ∫ t in (0 : ℝ)..1, Real.log t / (1 + t) = -(π ^ 2 / 12) := by
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.log s * Real.log (1 + s))
        (Real.log (1 + t) / t + Real.log t / (1 + t)) t :=
    fun t ht => hasDerivAt_log_mul_log_one_add ht.1
  have hint : IntervalIntegrable
      (fun t : ℝ => Real.log (1 + t) / t + Real.log t / (1 + t)) volume 0 1 :=
    intervalIntegrable_log_one_add_div_self.add intervalIntegrable_log_self_div_one_add
  have hlim0 : Tendsto (fun s : ℝ => Real.log s * Real.log (1 + s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlow : Tendsto (fun s : ℝ => Real.log s * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (tendsto_pow_mul_neg_log 0).neg
      have heq : (fun x : ℝ => -(x ^ (0 + 1) * -Real.log x)) = fun x : ℝ => Real.log x * x := by
        funext x
        ring
      rw [heq] at h
      simpa using h
    have hlt1 : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < 1 := by
      have h0mem : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x ∈ Ioo (-1 : ℝ) 1 :=
        Ioo_mem_nhds (by norm_num) (by norm_num)
      exact (h0mem.filter_mono nhdsWithin_le_nhds).mono (fun x hx => hx.2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, hlt1] with s hs hs1
      have hs0 : 0 < s := hs
      have hlogs : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1.le
      have hlog1s : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
      have hle : Real.log (1 + s) ≤ s := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + s)
        linarith
      exact mul_le_mul_of_nonpos_left hle hlogs
    · filter_upwards [self_mem_nhdsWithin, hlt1] with s hs hs1
      have hs0 : 0 < s := hs
      exact mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hs0.le hs1.le)
        (Real.log_nonneg (by linarith))
  have hlim1 : Tendsto (fun s : ℝ => Real.log s * Real.log (1 + s)) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.log 1 * Real.log 2)) := by
    have h1 : ContinuousAt (fun s : ℝ => Real.log s) 1 :=
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => Real.log (1 + s)) 1 :=
      (((hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_id (1 : ℝ))).log (by norm_num : (1 + (1 : ℝ)) ≠ 0)).continuousAt
    have hcont : ContinuousAt (fun s : ℝ => Real.log s * Real.log (1 + s)) 1 := h1.mul h2
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) < 1) hderiv hint hlim0 hlim1
  rw [intervalIntegral.integral_add intervalIntegrable_log_one_add_div_self
      intervalIntegrable_log_self_div_one_add] at hmain
  rw [Real.log_one, zero_mul, sub_zero] at hmain
  have hJ := integral_log_one_add_div_self
  linarith
set_option maxHeartbeats 2000000 in
lemma integral_log_one_sub_div_one_add :
    ∫ x in (0 : ℝ)..1, Real.log (1 - x) / (1 + x) = Real.log 2 ^ 2 / 2 - π ^ 2 / 12 := by
  have hf : ContinuousOn (fun t : ℝ => (1 - t) / (1 + t)) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div (continuousOn_const.sub continuousOn_id)
      (continuousOn_const.add continuousOn_id) ?_
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
  have hff' : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun t : ℝ => (1 - t) / (1 + t)) (-2 / (1 + x) ^ 2) x := by
    intro x hx
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have h1x : (1 + x) ≠ 0 := by linarith [hx.1]
    have hnum : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      have h' := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
      convert h' using 1
      · funext y
        rfl
      · ring
    have hden : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      have h' := (hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x)
      convert h' using 1
      · funext y
        rfl
      · ring
    convert hnum.div hden h1x using 1
    field_simp
    ring_nf
  have hf' : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), (-2 / (1 + x) ^ 2 : ℝ) ≤ 0 := by
    intro x hx
    rw [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hpos : 0 < (1 + x) ^ 2 := by
      exact pow_pos (by linarith [hx.1] : (0 : ℝ) < 1 + x) 2
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hpos.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun x : ℝ => Real.log (1 - x) / (1 + x)) hf hff' hf'
  have hsub' : (∫ t in (0 : ℝ)..1,
        (fun x : ℝ => Real.log (1 - x) / (1 + x)) ((1 - t) / (1 + t)) * (-2 / (1 + t) ^ 2))
      = ∫ u in (1 : ℝ)..0, Real.log (1 - u) / (1 + u) := by
    simpa using hsub
  have hcomp : (∫ t in (0 : ℝ)..1,
        (fun x : ℝ => Real.log (1 - x) / (1 + x)) ((1 - t) / (1 + t)) * (-2 / (1 + t) ^ 2))
      = ∫ t in (0 : ℝ)..1,
          -(Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 < t := ht.1
    have h1t : 0 < 1 + t := by linarith
    show Real.log (1 - (1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) * (-2 / (1 + t) ^ 2)
        = -(Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t)
    have hnum : 1 - (1 - t) / (1 + t) = 2 * t / (1 + t) := by
      field_simp
      ring
    have hden : 1 + (1 - t) / (1 + t) = 2 / (1 + t) := by
      field_simp
      ring
    have hlog : Real.log (2 * t / (1 + t)) = Real.log 2 + Real.log t - Real.log (1 + t) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt ht0)]
    rw [hnum, hden, hlog]
    field_simp
  have hD : (∫ x in (0 : ℝ)..1, Real.log (1 - x) / (1 + x))
      = ∫ t in (0 : ℝ)..1, (Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t) := by
    have h1 := hsub'
    rw [hcomp] at h1
    rw [show (∫ u in (1 : ℝ)..0, Real.log (1 - u) / (1 + u))
        = -(∫ u in (0 : ℝ)..1, Real.log (1 - u) / (1 + u)) from
      intervalIntegral.integral_symm 0 1] at h1
    have hneg : (∫ t in (0 : ℝ)..1,
          -(Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t))
        = -(∫ t in (0 : ℝ)..1,
          (Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      show -(Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t)
          = -((Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t))
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hneg] at h1
    exact (neg_inj.mp h1).symm
  have hsplit : (∫ t in (0 : ℝ)..1, (Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t))
      = Real.log 2 * (∫ t in (0 : ℝ)..1, (1 : ℝ) / (1 + t))
        + (∫ t in (0 : ℝ)..1, Real.log t / (1 + t))
        - (∫ t in (0 : ℝ)..1, Real.log (1 + t) / (1 + t)) := by
    have hcont1 : ContinuousOn (fun t : ℝ => (1 : ℝ) / (1 + t)) (Set.uIcc (0 : ℝ) 1) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
    have hcont2 : ContinuousOn (fun t : ℝ => Real.log (1 + t) / (1 + t))
        (Set.uIcc (0 : ℝ) 1) := by
      refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_id) ?_
      · refine ContinuousOn.log (continuousOn_const.add continuousOn_id) ?_
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
      · intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
    have hcongr : (∫ t in (0 : ℝ)..1,
          (Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t))
        = ∫ t in (0 : ℝ)..1, (Real.log 2 * ((1 : ℝ) / (1 + t)) + Real.log t / (1 + t)
            - Real.log (1 + t) / (1 + t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring_nf
    rw [hcongr,
      intervalIntegral.integral_sub
        ((hcont1.intervalIntegrable.const_mul (Real.log 2)).add
          intervalIntegrable_log_self_div_one_add)
        hcont2.intervalIntegrable,
      intervalIntegral.integral_add (hcont1.intervalIntegrable.const_mul (Real.log 2))
        intervalIntegrable_log_self_div_one_add,
      intervalIntegral.integral_const_mul]
  have hFval : (∫ t in (0 : ℝ)..1, (Real.log 2 + Real.log t - Real.log (1 + t)) / (1 + t))
      = Real.log 2 * Real.log 2 + (-(π ^ 2 / 12)) - Real.log 2 ^ 2 / 2 := by
    rw [hsplit, integral_one_div_one_add, integral_log_self_div_one_add,
      integral_log_one_add_div_one_add]
  rw [hD, hFval]
  ring
lemma intervalIntegrable_log_one_sub_div_one_add :
    IntervalIntegrable (fun x : ℝ => Real.log (1 - x) / (1 + x)) volume 0 1 := by
  have hrpow : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) volume (0 : ℝ) 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
  have hcomp : IntervalIntegrable (fun x : ℝ => 2 * (1 - x) ^ (-(1 / 2) : ℝ)) volume 0 1 := by
    have h := (hrpow.const_mul 2).comp_sub_left (1 : ℝ) (by simp)
    simpa using h.symm
  refine hcomp.mono_fun' ?_ ?_
  · exact (((Real.measurable_log.comp (measurable_const.sub measurable_id)).div
      (measurable_const.add measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    rcases lt_or_eq_of_le hx.2 with hx1 | rfl
    · have h1x : 0 < 1 - x := by linarith
      have hlog : Real.log (1 - x) ≤ 0 := Real.log_nonpos h1x.le (by linarith)
      have hnorm : ‖Real.log (1 - x) / (1 + x)‖ = -Real.log (1 - x) / (1 + x) := by
        rw [Real.norm_eq_abs,
          abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hlog (by linarith)), neg_div]
      rw [hnorm]
      calc -Real.log (1 - x) / (1 + x) ≤ -Real.log (1 - x) := by
            rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + x)]
            exact le_mul_of_one_le_right (neg_nonneg.mpr hlog) (by linarith)
        _ ≤ 2 * (1 - x) ^ (-(1 / 2) : ℝ) := by
            have h := neg_log_le_two_div_sqrt h1x
            have hsqrt : 2 / Real.sqrt (1 - x) = 2 * (1 - x) ^ (-(1 / 2) : ℝ) := by
              rw [Real.sqrt_eq_rpow, Real.rpow_neg h1x.le, div_eq_mul_inv]
            rwa [hsqrt] at h
    · simp
lemma intervalIntegrable_log_one_add_div_one_add :
    IntervalIntegrable (fun t : ℝ => Real.log (1 + t) / (1 + t)) volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ => Real.log (1 + t) / (1 + t))
      (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.div ?_ (continuousOn_const.add continuousOn_id) ?_
    · refine ContinuousOn.log (continuousOn_const.add continuousOn_id) ?_
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
    · intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < 1 + t)
  exact hcont.intervalIntegrable
set_option maxHeartbeats 2000000 in
lemma integral_log_one_sub_sq_div_one_add :
    ∫ x in (0 : ℝ)..1, Real.log (1 - x ^ 2) / (1 + x) = Real.log 2 ^ 2 - π ^ 2 / 12 := by
  have hcongr : (∫ x in (0 : ℝ)..1, Real.log (1 - x ^ 2) / (1 + x))
      = ∫ x in (0 : ℝ)..1,
          (Real.log (1 - x) / (1 + x) + Real.log (1 + x) / (1 + x)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have h2x : 0 < 1 + x := by linarith [hx.1]
    show Real.log (1 - x ^ 2) / (1 + x)
        = Real.log (1 - x) / (1 + x) + Real.log (1 + x) / (1 + x)
    have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h2x)]
    rw [add_div]
  rw [hcongr]
  rw [intervalIntegral.integral_add intervalIntegrable_log_one_sub_div_one_add
    intervalIntegrable_log_one_add_div_one_add]
  rw [integral_log_one_sub_div_one_add, integral_log_one_add_div_one_add]
  ring
lemma intervalIntegrable_log_sq : IntervalIntegrable (fun u : ℝ => Real.log u ^ 2) volume 0 1 := by
  have hg : IntervalIntegrable (fun u : ℝ => 16 * u ^ (-(1 / 2) : ℝ)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul 16
  refine hg.mono_fun' ?_ ?_
  · measurability
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with u hu
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hu0 : 0 < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hnorm : ‖Real.log u ^ 2‖ = (-Real.log u) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), neg_sq]
    rw [hnorm]
    have hbound : -Real.log u ≤ 4 * u ^ (-(1 / 4) : ℝ) := by
      have h := Real.log_le_rpow_div (x := u⁻¹) (inv_nonneg.mpr hu0.le)
        (by norm_num : (0 : ℝ) < 1 / 4)
      rw [Real.log_inv] at h
      have h1 : (u⁻¹) ^ ((1 : ℝ) / 4) = u ^ (-(1 / 4) : ℝ) := by
        rw [Real.inv_rpow hu0.le, Real.rpow_neg hu0.le]
      rw [h1] at h
      have h2 : u ^ (-(1 / 4) : ℝ) / (1 / 4) = 4 * u ^ (-(1 / 4) : ℝ) := by ring
      rwa [h2] at h
    have hlog : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
    have hsq := pow_le_pow_left₀ (neg_nonneg.mpr hlog) hbound 2
    have h16 : (4 * u ^ (-(1 / 4) : ℝ)) ^ 2 = 16 * u ^ (-(1 / 2) : ℝ) := by
      rw [mul_pow]
      have hpow : (u ^ (-(1 / 4) : ℝ)) ^ (2 : ℕ) = u ^ (-(1 / 2) : ℝ) := by
        rw [← Real.rpow_natCast (u ^ (-(1 / 4) : ℝ)) 2, ← Real.rpow_mul hu0.le]
        norm_num
      rw [hpow]
      ring
    calc (-Real.log u) ^ 2 ≤ (4 * u ^ (-(1 / 4) : ℝ)) ^ 2 := hsq
      _ = 16 * u ^ (-(1 / 2) : ℝ) := h16
lemma intervalIntegrable_neg_log_one_sub_sq :
    IntervalIntegrable (fun x : ℝ => (-Real.log (1 - x)) ^ 2) volume 0 1 := by
  have h := intervalIntegrable_log_sq.comp_sub_left (1 : ℝ) (by simp)
  have hfun : (fun x : ℝ => Real.log (1 - x) ^ 2) = fun x : ℝ => (-Real.log (1 - x)) ^ 2 := by
    funext x
    rw [neg_sq]
  rw [hfun] at h
  simpa using h.symm
lemma intervalIntegrable_neg_log_one_sub_sq_two :
    IntervalIntegrable (fun x : ℝ => (-Real.log (1 - x ^ 2)) ^ 2) volume 0 1 := by
  refine intervalIntegrable_neg_log_one_sub_sq.mono_fun' ?_ ?_
  · have h1 : Measurable (fun x : ℝ => Real.log (1 - x ^ 2)) := by
      measurability
    have h2 : Measurable (fun x : ℝ => Real.log (1 - x ^ 2) ^ 2) := h1.pow_const 2
    simpa [neg_sq] using h2.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hnorm : ‖(-Real.log (1 - x ^ 2)) ^ 2‖ = (-Real.log (1 - x ^ 2)) ^ 2 :=
      Real.norm_of_nonneg (sq_nonneg _)
    rw [hnorm]
    rcases lt_or_eq_of_le hx1 with hx1' | rfl
    · have h1x : 0 < 1 - x := by linarith
      have h1p : 0 < 1 + x := by linarith
      have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
      have hWnn : 0 ≤ -Real.log (1 - x ^ 2) := by
        apply neg_nonneg.mpr
        apply Real.log_nonpos
        · nlinarith [hx0, hx1]
        · nlinarith [sq_nonneg x]
      have hle : -Real.log (1 - x ^ 2) ≤ -Real.log (1 - x) := by
        rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
        have := Real.log_nonneg (by linarith [hx0] : (1 : ℝ) ≤ 1 + x)
        linarith
      exact pow_le_pow_left₀ hWnn hle 2
    · simp
lemma tendsto_pow_mul_neg_log_sq (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ (n + 1) * (-Real.log x) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => Real.log x * x ^ (((n : ℝ) + 1) / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by positivity)
  have hsq : Tendsto (fun x : ℝ => (Real.log x * x ^ (((n : ℝ) + 1) / 2)) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hbase.mul hbase
    simpa [pow_two] using h
  have heq : (fun x : ℝ => (Real.log x * x ^ (((n : ℝ) + 1) / 2)) ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (n + 1) * (-Real.log x) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : 0 < x := hx
    have hpow : x ^ (n + 1) = (x ^ (((n : ℝ) + 1) / 2)) ^ 2 := by
      have h1 : x ^ (n + 1) = x ^ ((n : ℝ) + 1) := by
        rw [← Real.rpow_natCast x (n + 1)]
        push_cast
        rfl
      have h2 : (x ^ (((n : ℝ) + 1) / 2)) ^ 2 = x ^ ((n : ℝ) + 1) := by
        rw [← Real.rpow_natCast (x ^ (((n : ℝ) + 1) / 2)) 2, ← Real.rpow_mul hx0.le]
        congr 1
        ring
      exact h1.trans h2.symm
    rw [hpow]
    ring
  exact hsq.congr' heq
lemma tendsto_one_sub_pow_mul_neg_log_sq (n : ℕ) :
    Tendsto (fun x : ℝ => (1 - x) ^ (n + 1) * (-Real.log (1 - x)) ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hmap : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_const_nhds
      have hid : Tendsto (fun x : ℝ => x) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hconst.sub hid
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x < 1 := hx
    exact sub_pos.mpr hx'
  exact (tendsto_pow_mul_neg_log_sq n).comp hmap
lemma intervalIntegrable_pow_mul_neg_log_one_sub_sq_two (l : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2)
      volume 0 1 :=
  intervalIntegrable_neg_log_one_sub_sq_two.continuousOn_mul
    ((continuous_id.pow (2 * l)).continuousOn)
lemma intervalIntegrable_ibp_T (l : ℕ) :
    IntervalIntegrable
      (fun x : ℝ => -4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) *
        (-Real.log (1 - x ^ 2)) / ((((2 * l : ℕ) : ℝ) + 1) * (1 + x))) volume 0 1 := by
  have hbase : IntervalIntegrable (fun x : ℝ => 4 * (-Real.log (1 - x))) volume 0 1 := by
    simpa using (intervalIntegrable_x_pow_mul_neg_log_one_sub 0).const_mul 4
  refine hbase.mono_fun' ?_ ?_
  · have hsum : Measurable (fun x : ℝ => ∑ k ∈ Finset.range (2 * l + 1), x ^ k) := by
      apply Finset.measurable_sum
      intro k _
      exact measurable_id.pow_const k
    have hlog : Measurable (fun x : ℝ => Real.log (1 - x ^ 2)) := by
      measurability
    exact ((((measurable_const.mul measurable_id).mul hsum).mul hlog.neg).div
      (measurable_const.mul (measurable_const.add measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hSnn : 0 ≤ ∑ k ∈ Finset.range (2 * l + 1), x ^ k :=
      Finset.sum_nonneg (fun k _ => pow_nonneg hx0.le k)
    have hSle : (∑ k ∈ Finset.range (2 * l + 1), x ^ k) ≤ (((2 * l : ℕ) : ℝ) + 1) := by
      calc (∑ k ∈ Finset.range (2 * l + 1), x ^ k)
          ≤ ∑ k ∈ Finset.range (2 * l + 1), (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => pow_le_one₀ hx0.le hx1)
        _ = (((2 * l : ℕ) : ℝ) + 1) := by simp
    have hcpos : 0 < (((2 * l : ℕ) : ℝ) + 1) := by positivity
    have hdenpos : 0 < (((2 * l : ℕ) : ℝ) + 1) * (1 + x) := mul_pos hcpos (by linarith)
    have hWnn : 0 ≤ -Real.log (1 - x ^ 2) := by
      apply neg_nonneg.mpr
      apply Real.log_nonpos
      · nlinarith [hx0, hx1]
      · nlinarith [sq_nonneg x]
    have hWle : -Real.log (1 - x ^ 2) ≤ -Real.log (1 - x) := by
      rcases lt_or_eq_of_le hx1 with hxlt | rfl
      · have h1x : 0 < 1 - x := by linarith
        have h1p : 0 < 1 + x := by linarith
        have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
        linarith
      · simp
    have hvnonpos : -4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) *
        (-Real.log (1 - x ^ 2)) / ((((2 * l : ℕ) : ℝ) + 1) * (1 + x)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx0.le) hSnn) hWnn)
        hdenpos.le
    have hnorm : ‖-4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) *
        (-Real.log (1 - x ^ 2)) / ((((2 * l : ℕ) : ℝ) + 1) * (1 + x))‖
        = 4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) *
          (-Real.log (1 - x ^ 2)) / ((((2 * l : ℕ) : ℝ) + 1) * (1 + x)) := by
      rw [Real.norm_eq_abs, abs_of_nonpos hvnonpos, div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [hnorm]
    have hratio : x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) /
        ((((2 * l : ℕ) : ℝ) + 1) * (1 + x)) ≤ 1 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hSnn, hSle, hx0, hx1]
    calc 4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) /
          ((((2 * l : ℕ) : ℝ) + 1) * (1 + x))
        = 4 * (-Real.log (1 - x ^ 2)) *
            (x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) /
              ((((2 * l : ℕ) : ℝ) + 1) * (1 + x))) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ 4 * (-Real.log (1 - x ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 4 * (-Real.log (1 - x ^ 2)) := by ring
      _ ≤ 4 * (-Real.log (1 - x)) := by linarith
set_option maxHeartbeats 2000000 in
lemma hasDerivAt_ibp_primitive (l : ℕ) {x : ℝ} (hx1 : x ≠ 1) (hxm1 : x ≠ -1) :
    HasDerivAt
      (fun y : ℝ => ((y ^ (2 * l + 1) - 1) / (((2 * l : ℕ) : ℝ) + 1)) *
        (-Real.log (1 - y ^ 2)) ^ 2)
      (x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2
        + (-4 * x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2))
            / ((((2 * l : ℕ) : ℝ) + 1) * (1 + x)))) x := by
  have hc : (((2 * l : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have h1x : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have h1p : (1 + x) ≠ 0 := by intro h; exact hxm1 (by linarith)
  have hden : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero h1x h1p
  have hv : HasDerivAt (fun y : ℝ => (y ^ (2 * l + 1) - 1) / (((2 * l : ℕ) : ℝ) + 1))
      (x ^ (2 * l)) x := by
    have h := ((hasDerivAt_pow (2 * l + 1) x).sub_const 1).div_const (((2 * l : ℕ) : ℝ) + 1)
    convert h using 1
    rw [show 2 * l + 1 - 1 = 2 * l by omega]
    field_simp
    push_cast
    ring
  have hW : HasDerivAt (fun y : ℝ => -Real.log (1 - y ^ 2)) (2 * x / (1 - x ^ 2)) x := by
    have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have h2 := (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub h1
      convert h2 using 1
      ring
    have hlog := hinner.log hden
    have hneg := hlog.neg
    convert hneg using 1
    field_simp
  have hWsq : HasDerivAt (fun y : ℝ => (-Real.log (1 - y ^ 2)) ^ 2)
      (2 * (-Real.log (1 - x ^ 2)) * (2 * x / (1 - x ^ 2))) x := by
    have h := hW.pow 2
    convert h using 1
    ring
  have hderiv := hv.mul hWsq
  convert hderiv using 1
  have hS := geom_sum_mul_neg x (2 * l + 1)
  have hxS : x ^ (2 * l + 1) - 1 =
      -((1 - x) * (∑ k ∈ Finset.range (2 * l + 1), x ^ k)) := by
    linarith [hS]
  rw [hxS]
  field_simp
  ring
set_option maxHeartbeats 2000000 in
lemma integral_pow_mul_neg_log_one_sub_sq_ibp (l : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2)
      = (4 / (((2 * l : ℕ) : ℝ) + 1)) *
          ∫ x in (0 : ℝ)..1,
            x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2))
              / (1 + x) := by
  set c : ℝ := (((2 * l : ℕ) : ℝ) + 1) with hcdef
  set W : ℝ → ℝ := fun y => -Real.log (1 - y ^ 2) with hWdef
  set S : ℝ → ℝ := fun y => ∑ k ∈ Finset.range (2 * l + 1), y ^ k with hSdef
  set K : ℝ → ℝ := fun y => y ^ (2 * l) * W y ^ 2 with hKdef
  set T : ℝ → ℝ := fun y => -4 * y * S y * W y / (c * (1 + y)) with hTdef
  set F : ℝ → ℝ := fun y => ((y ^ (2 * l + 1) - 1) / c) * W y ^ 2 with hFdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hIntK' : IntervalIntegrable K volume 0 1 := by
    refine (intervalIntegrable_pow_mul_neg_log_one_sub_sq_two l).congr_uIoo ?_
    intro x _
    simp only [hKdef, hWdef]
  have hIntT' : IntervalIntegrable T volume 0 1 := by
    refine (intervalIntegrable_ibp_T l).congr_uIoo ?_
    intro x _
    simp only [hTdef, hcdef, hSdef, hWdef]
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (K x + T x) x := by
    intro x hx
    have h := hasDerivAt_ibp_primitive l (ne_of_lt hx.2) (by linarith [hx.1])
    simpa only [hFdef, hKdef, hTdef, hcdef, hSdef, hWdef] using h
  have hFs : ∀ x : ℝ, x < 1 → F x = -((1 - x) * S x * (W x) ^ 2 / c) := by
    intro x hx
    have hgeom := geom_sum_mul_neg x (2 * l + 1)
    have hxS : x ^ (2 * l + 1) - 1 = -((1 - x) * S x) := by
      rw [hSdef]
      linarith [hgeom]
    simp only [hFdef]
    rw [hxS, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hWnn : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ W x := by
    intro x hx0 hx1
    simp only [hWdef]
    apply neg_nonneg.mpr
    apply Real.log_nonpos
    · nlinarith [hx0, hx1]
    · nlinarith [sq_nonneg x]
  have hWle : ∀ x : ℝ, 0 ≤ x → x < 1 → W x ≤ -Real.log (1 - x) := by
    intro x hx0 hx1
    simp only [hWdef]
    have h1x : 0 < 1 - x := by linarith
    have h1p : 0 < 1 + x := by linarith
    have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
    linarith
  have hSnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ S x := by
    intro x hx0
    rw [hSdef]
    exact Finset.sum_nonneg (fun k _ => pow_nonneg hx0 k)
  have hSle : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → S x ≤ c := by
    intro x hx0 hx1
    rw [hSdef, hcdef]
    calc (∑ k ∈ Finset.range (2 * l + 1), x ^ k)
        ≤ ∑ k ∈ Finset.range (2 * l + 1), (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => pow_le_one₀ hx0 hx1)
      _ = (((2 * l : ℕ) : ℝ) + 1) := by simp
  have hF0 : F 0 = 0 := by simp [hFdef, hWdef]
  have hlim0 : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt F 0 := by
      have h := (hasDerivAt_ibp_primitive l (x := 0) (by norm_num) (by norm_num)).continuousAt
      simpa only [hFdef, hWdef, hcdef] using h
    simpa [hF0] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto F (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (1 - x) * (-Real.log (1 - x)) ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using tendsto_one_sub_pow_mul_neg_log_sq 0
    have h12 : ∀ᶠ x : ℝ in 𝓝[<] (1 : ℝ), (1 / 2 : ℝ) ≤ x := by
      have h : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), (1 / 2 : ℝ) < x :=
        Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      exact (h.filter_mono nhdsWithin_le_nhds).mono (fun x hx => hx.le)
    have hlow : Tendsto (fun x : ℝ => -((1 - x) * (-Real.log (1 - x)) ^ 2))
        (𝓝[<] (1 : ℝ)) (𝓝 0) := by simpa using hup.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, h12] with x hxlt hx12
      have hx0 : (0 : ℝ) < x := by linarith
      have hx1 : x ≤ 1 := le_of_lt hxlt
      have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hsq : (W x) ^ 2 ≤ (-Real.log (1 - x)) ^ 2 :=
        pow_le_pow_left₀ (hWnn x hx0.le hx1) (hWle x hx0.le hxlt) 2
      have hratio : S x / c ≤ 1 := (div_le_one hcpos).mpr (hSle x hx0.le hx1)
      have hbound : (1 - x) * S x * (W x) ^ 2 / c ≤ (1 - x) * (-Real.log (1 - x)) ^ 2 := by
        calc (1 - x) * S x * (W x) ^ 2 / c
            = (1 - x) * (W x) ^ 2 * (S x / c) := by field_simp
          _ ≤ (1 - x) * (-Real.log (1 - x)) ^ 2 * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hsq h1x) hratio
                (div_nonneg (hSnn x hx0.le) hcpos.le) (mul_nonneg h1x (sq_nonneg _))
          _ = (1 - x) * (-Real.log (1 - x)) ^ 2 := by ring
      linarith [hFs x hxlt, hbound]
    · filter_upwards [self_mem_nhdsWithin, h12] with x hxlt hx12
      have hx0 : (0 : ℝ) < x := by linarith
      have hx1 : x ≤ 1 := le_of_lt hxlt
      have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hnonneg : 0 ≤ (1 - x) * S x * (W x) ^ 2 / c :=
        div_nonneg (mul_nonneg (mul_nonneg h1x (hSnn x hx0.le)) (sq_nonneg _)) hcpos.le
      rw [hFs x hxlt]
      exact (neg_nonpos.mpr hnonneg).trans (mul_nonneg h1x (sq_nonneg _))
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) < 1) hderiv (hIntK'.add hIntT') hlim0 hlim1
  rw [intervalIntegral.integral_add hIntK' hIntT'] at hmain
  have hTval : (∫ x in (0 : ℝ)..1, T x) = -((4 / c) * ∫ x in (0 : ℝ)..1,
      x * S x * W x / (1 + x)) := by
    have hcongr : (∫ x in (0 : ℝ)..1, T x) = ∫ x in (0 : ℝ)..1,
        -((4 / c) * (x * S x * W x / (1 + x))) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have h1p : (1 + x) ≠ 0 := by linarith [hx.1]
      simp only [hTdef, hcdef]
      field_simp [hcne, h1p]
    rw [hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  have hKval : (∫ x in (0 : ℝ)..1, K x) = (4 / c) * ∫ x in (0 : ℝ)..1,
      x * S x * W x / (1 + x) := by
    linarith [hmain, hTval]
  have hLHS : (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2) =
      ∫ x in (0 : ℝ)..1, K x := by
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    simp only [hKdef, hWdef]
  rw [hLHS, hKval, hcdef]
lemma mul_geom_sum_add_one (l : ℕ) (x : ℝ) :
    x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) + 1
      = (1 + x) * (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) := by
  induction l with
  | zero =>
    norm_num [Finset.sum_range_one]
    ring
  | succ l ih =>
    have h1 : (∑ k ∈ Finset.range (2 * (l + 1) + 1), x ^ k)
        = (∑ k ∈ Finset.range (2 * l + 1), x ^ k) + x ^ (2 * l + 1) + x ^ (2 * l + 1 + 1) := by
      rw [show 2 * (l + 1) + 1 = 2 * l + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ]
    have h2 : (∑ j ∈ Finset.range (l + 1 + 1), x ^ (2 * j))
        = (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) + x ^ (2 * l + 1 + 1) := by
      rw [Finset.sum_range_succ]
      congr 1
    rw [h1, h2]
    have hexp : x * ((∑ k ∈ Finset.range (2 * l + 1), x ^ k) + x ^ (2 * l + 1) +
        x ^ (2 * l + 1 + 1)) + 1
        = (x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) + 1) +
          (x * x ^ (2 * l + 1) + x * x ^ (2 * l + 1 + 1)) := by ring
    rw [hexp, ih]
    have hxb : x * x ^ (2 * l + 1) = x ^ (2 * l + 1 + 1) := by rw [← pow_succ']
    rw [hxb, mul_add]
    ring
lemma integral_x_pow_mul_neg_log_one_sub_sq (j : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ (2 * j) * (-Real.log (1 - x ^ 2)))
      = 2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) - Real.log 2)
          / ((((2 * j : ℕ)) : ℝ) + 1) := by
  have hcongr : (∫ x in (0 : ℝ)..1, x ^ (2 * j) * (-Real.log (1 - x ^ 2)))
      = ∫ x in (0 : ℝ)..1,
          (x ^ (2 * j) * (-Real.log (1 - x)) + x ^ (2 * j) * (-Real.log (1 + x))) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    change x ^ (2 * j) * (-Real.log (1 - x ^ 2))
        = x ^ (2 * j) * (-Real.log (1 - x)) + x ^ (2 * j) * (-Real.log (1 + x))
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have h1p : 0 < 1 + x := by linarith [hx.1]
    have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_add (intervalIntegrable_x_pow_mul_neg_log_one_sub (2 * j))
    (intervalIntegrable_x_pow_mul_neg_log_one_add (2 * j))]
  rw [integral_x_pow_mul_neg_log_one_sub (2 * j), integral_x_pow_mul_neg_log_one_add_even j]
  have hsum := sum_one_div_add_alternating j
  have hd : ((((2 * j : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hsum]
lemma intervalIntegrable_neg_log_one_sub_sq_W :
    IntervalIntegrable (fun x : ℝ => -Real.log (1 - x ^ 2)) volume 0 1 := by
  have hbase : IntervalIntegrable (fun x : ℝ => -Real.log (1 - x) + Real.log 2) volume 0 1 := by
    simpa using (intervalIntegrable_x_pow_mul_neg_log_one_sub 0).add
      (intervalIntegrable_const (c := Real.log 2))
  refine hbase.mono_fun' ?_ ?_
  · have h1 : Measurable (fun x : ℝ => Real.log (1 - x ^ 2)) := by measurability
    exact h1.neg.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    rcases lt_or_eq_of_le hx1 with hxlt | rfl
    · have h1x : 0 < 1 - x := by linarith
      have h1p : 0 < 1 + x := by linarith
      have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
      have hlog : Real.log (1 - x ^ 2) = Real.log (1 - x) + Real.log (1 + x) := by
        rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
      have hlog2 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
      have hWnn : 0 ≤ -Real.log (1 - x ^ 2) := by
        apply neg_nonneg.mpr
        apply Real.log_nonpos
        · nlinarith [hx0, hx1]
        · nlinarith [sq_nonneg x]
      have hlog2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      rw [Real.norm_of_nonneg hWnn, hlog]
      linarith [hlog2, hlog2pos]
    · have h : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      simpa [Real.log_zero] using h
lemma integral_neg_log_one_sub_sq_div_one_add :
    (∫ x in (0 : ℝ)..1, (-Real.log (1 - x ^ 2)) / (1 + x)) = π ^ 2 / 12 - Real.log 2 ^ 2 := by
  have hcongr : (∫ x in (0 : ℝ)..1, (-Real.log (1 - x ^ 2)) / (1 + x))
      = ∫ x in (0 : ℝ)..1, -(Real.log (1 - x ^ 2) / (1 + x)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    change (-Real.log (1 - x ^ 2)) / (1 + x) = -(Real.log (1 - x ^ 2) / (1 + x))
    rw [neg_div]
  rw [hcongr, intervalIntegral.integral_neg, integral_log_one_sub_sq_div_one_add]
  ring
set_option maxHeartbeats 2000000 in
lemma finite_identity (m : ℕ) :
    2 * (∑ j ∈ Finset.range (m + 1),
          (∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
            / ((((2 * j : ℕ)) : ℝ) + 1))
      = (∑ r ∈ Finset.range (m + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) ^ 2
        + (∑ r ∈ Finset.range (m + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hL : (∑ j ∈ Finset.range (m + 1 + 1),
          (∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
            / ((((2 * j : ℕ)) : ℝ) + 1))
        = (∑ j ∈ Finset.range (m + 1),
          (∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
            / ((((2 * j : ℕ)) : ℝ) + 1))
          + (∑ r ∈ Finset.range (m + 1 + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
              / ((((2 * (m + 1) : ℕ)) : ℝ) + 1) :=
      Finset.sum_range_succ (fun j : ℕ =>
        (∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
          / ((((2 * j : ℕ)) : ℝ) + 1)) (m + 1)
    have hc : (∑ r ∈ Finset.range (m + 1 + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
        = (∑ r ∈ Finset.range (m + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
          + 1 / ((((2 * (m + 1) : ℕ)) : ℝ) + 1) :=
      Finset.sum_range_succ (fun r : ℕ => 1 / ((((2 * r : ℕ)) : ℝ) + 1)) (m + 1)
    have hc2 : (∑ r ∈ Finset.range (m + 1 + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2)
        = (∑ r ∈ Finset.range (m + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2)
          + 1 / ((((2 * (m + 1) : ℕ)) : ℝ) + 1) ^ 2 :=
      Finset.sum_range_succ (fun r : ℕ => 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2) (m + 1)
    rw [hL, hc, hc2]
    field_simp
    nlinarith [ih]
lemma integral_even_neg_one_one {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (h0 : IntervalIntegrable f volume (-1) 0) (h1 : IntervalIntegrable f volume 0 1) :
    (∫ x in (-1 : ℝ)..1, f x) = 2 * ∫ x in (0 : ℝ)..1, f x := by
  have hneg : (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1, f x := by
    have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 0)
    have hcongr : (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (-1 : ℝ)..0, f (-x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (hf x).symm
    rw [hcongr]
    simpa using hcomp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0 h1
  rw [← hsplit, hneg]
  ring
lemma intervalIntegrable_pow_mul_neg_log_one_sub_sq_W (j : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * j) * (-Real.log (1 - x ^ 2))) volume 0 1 :=
  intervalIntegrable_neg_log_one_sub_sq_W.continuousOn_mul
    ((continuous_id.pow (2 * j)).continuousOn)
lemma integral_P_mul_neg_log_one_sub_sq (l : ℕ) :
    (∫ x in (0 : ℝ)..1, (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) *
        (-Real.log (1 - x ^ 2)))
      = ∑ j ∈ Finset.range (l + 1),
          2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) - Real.log 2)
            / ((((2 * j : ℕ)) : ℝ) + 1) := by
  have hcongr : (∫ x in (0 : ℝ)..1, (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) *
        (-Real.log (1 - x ^ 2)))
      = ∫ x in (0 : ℝ)..1, ∑ j ∈ Finset.range (l + 1),
          x ^ (2 * j) * (-Real.log (1 - x ^ 2)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    simp only [Finset.sum_mul]
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_x_pow_mul_neg_log_one_sub_sq j
  · intro j _
    exact intervalIntegrable_pow_mul_neg_log_one_sub_sq_W j
lemma intervalIntegrable_P_mul_neg_log_one_sub_sq (l : ℕ) :
    IntervalIntegrable (fun x : ℝ => (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) *
      (-Real.log (1 - x ^ 2))) volume 0 1 := by
  have hbase : IntervalIntegrable (fun x : ℝ => ((l : ℝ) + 1) * (-Real.log (1 - x)))
      volume 0 1 := by
    simpa using (intervalIntegrable_x_pow_mul_neg_log_one_sub 0).const_mul ((l : ℝ) + 1)
  refine hbase.mono_fun' ?_ ?_
  · have hP : Measurable (fun x : ℝ => ∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) :=
      Finset.measurable_sum _ (fun j _ => measurable_id.pow_const (2 * j))
    have hlog : Measurable (fun x : ℝ => Real.log (1 - x ^ 2)) := by measurability
    exact (hP.mul hlog.neg).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hPnn : 0 ≤ ∑ j ∈ Finset.range (l + 1), x ^ (2 * j) :=
      Finset.sum_nonneg (fun j _ => pow_nonneg hx0.le _)
    have hPle : (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) ≤ (l : ℝ) + 1 := by
      calc (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) ≤ ∑ j ∈ Finset.range (l + 1), (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => pow_le_one₀ hx0.le hx1)
        _ = (l : ℝ) + 1 := by simp
    have hWnn : 0 ≤ -Real.log (1 - x ^ 2) := by
      apply neg_nonneg.mpr
      apply Real.log_nonpos
      · nlinarith [hx0, hx1]
      · nlinarith [sq_nonneg x]
    have hWle : -Real.log (1 - x ^ 2) ≤ -Real.log (1 - x) := by
      rcases lt_or_eq_of_le hx1 with hxlt | rfl
      · have h1x : 0 < 1 - x := by linarith
        have h1p : 0 < 1 + x := by linarith
        have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        rw [hfac, Real.log_mul (ne_of_gt h1x) (ne_of_gt h1p)]
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + x)
        linarith
      · simp
    rw [Real.norm_of_nonneg (mul_nonneg hPnn hWnn)]
    calc (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) * (-Real.log (1 - x ^ 2))
        ≤ ((l : ℝ) + 1) * (-Real.log (1 - x ^ 2)) := mul_le_mul_of_nonneg_right hPle hWnn
      _ ≤ ((l : ℝ) + 1) * (-Real.log (1 - x)) :=
          mul_le_mul_of_nonneg_left hWle (by positivity)
lemma integral_xS_div_one_add_mul_W (l : ℕ) :
    (∫ x in (0 : ℝ)..1,
        x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) / (1 + x))
      = (∫ x in (0 : ℝ)..1, (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) *
          (-Real.log (1 - x ^ 2)))
        - (∫ x in (0 : ℝ)..1, (-Real.log (1 - x ^ 2)) / (1 + x)) := by
  have hWdiv : IntervalIntegrable (fun x : ℝ => (-Real.log (1 - x ^ 2)) / (1 + x)) volume 0 1 := by
    have hcont : ContinuousOn (fun x : ℝ => (1 : ℝ) / (1 + x)) (Set.uIcc (0 : ℝ) 1) := by
      refine ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id) ?_
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact ne_of_gt (by linarith [hx.1] : (0 : ℝ) < 1 + x)
    refine (intervalIntegrable_neg_log_one_sub_sq_W.mul_continuousOn hcont).congr_uIoo ?_
    intro x _
    ring_nf
  have hdiv : ∀ x : ℝ, x ≠ -1 →
      x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) / (1 + x)
        = (∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) - 1 / (1 + x) := by
    intro x hx
    have h1p : (1 + x) ≠ 0 := by intro h; exact hx (by linarith)
    have h := mul_geom_sum_add_one l x
    field_simp
    linarith [h]
  have hcongr : (∫ x in (0 : ℝ)..1,
        x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) / (1 + x))
      = ∫ x in (0 : ℝ)..1,
          ((∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) - 1 / (1 + x)) *
            (-Real.log (1 - x ^ 2)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx1 : x ≠ -1 := by linarith [hx.1]
    change x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) / (1 + x)
        = ((∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) - 1 / (1 + x)) *
            (-Real.log (1 - x ^ 2))
    rw [show x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) / (1 + x)
        = (x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) / (1 + x)) *
            (-Real.log (1 - x ^ 2)) by ring]
    rw [hdiv x hx1]
  rw [hcongr]
  have hcongr2 : (∫ x in (0 : ℝ)..1,
        ((∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) - 1 / (1 + x)) * (-Real.log (1 - x ^ 2)))
      = ∫ x in (0 : ℝ)..1,
          ((∑ j ∈ Finset.range (l + 1), x ^ (2 * j)) * (-Real.log (1 - x ^ 2))
            - (-Real.log (1 - x ^ 2)) / (1 + x)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    ring_nf
  rw [hcongr2, intervalIntegral.integral_sub
    (intervalIntegrable_P_mul_neg_log_one_sub_sq l) hWdiv]
set_option maxHeartbeats 2000000 in
theorem integral_even_x_pow_mul_potential_sq (l : ℕ) :
    ∫ x in (-1 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) ^ 2
      = (((∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1)) - Real.log 2) ^ 2
          + (∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1) ^ 2) - π ^ 2 / 12)
          / ((l : ℝ) + 1 / 2) := by
  set H : ℝ := ∑ r ∈ Finset.range (l + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) with hHdef
  set H2 : ℝ := ∑ r ∈ Finset.range (l + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2 with hH2def
  have hI0 : (∫ x in (0 : ℝ)..1,
        x * (∑ k ∈ Finset.range (2 * l + 1), x ^ k) * (-Real.log (1 - x ^ 2)) / (1 + x))
      = (∑ j ∈ Finset.range (l + 1),
          2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) - Real.log 2)
            / ((((2 * j : ℕ)) : ℝ) + 1)) - (π ^ 2 / 12 - Real.log 2 ^ 2) := by
    rw [integral_xS_div_one_add_mul_W, integral_P_mul_neg_log_one_sub_sq,
      integral_neg_log_one_sub_sq_div_one_add]
  have hsum : (∑ j ∈ Finset.range (l + 1),
        2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) - Real.log 2)
          / ((((2 * j : ℕ)) : ℝ) + 1))
      = (H - Real.log 2) ^ 2 + H2 - Real.log 2 ^ 2 := by
    have hterm : ∀ j ∈ Finset.range (l + 1),
        2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1)) - Real.log 2)
          / ((((2 * j : ℕ)) : ℝ) + 1)
        = 2 * ((∑ r ∈ Finset.range (j + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
            / ((((2 * j : ℕ)) : ℝ) + 1))
          - 2 * Real.log 2 * (1 / ((((2 * j : ℕ)) : ℝ) + 1)) := by
      intro j _
      ring_nf
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hHdef, hH2def, finite_identity l]
    ring
  have hKval : (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2)
      = (4 / ((((2 * l : ℕ)) : ℝ) + 1)) * ((H - Real.log 2) ^ 2 + H2 - π ^ 2 / 12) := by
    rw [integral_pow_mul_neg_log_one_sub_sq_ibp, hI0, hsum]
    ring
  set f : ℝ → ℝ := fun x => x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) ^ 2 with hf
  have hInt01 : IntervalIntegrable f volume 0 1 := by
    refine ((intervalIntegrable_pow_mul_neg_log_one_sub_sq_two l).const_mul (1 / 4)).congr_uIoo ?_
    intro x _
    simp only [hf]
    ring
  have hIntneg : IntervalIntegrable f volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg (f := f) (a := (-1 : ℝ)) (b := 0)]
    have hfun : (fun x : ℝ => f (-x)) = f := by
      funext x
      simp only [hf]
      rw [Even.neg_pow ⟨l, by ring⟩ x, show (1 : ℝ) - (-x) ^ 2 = 1 - x ^ 2 by ring]
    rw [hfun]
    simpa using hInt01.symm
  have heven : (∫ x in (-1 : ℝ)..1, f x) = 2 * ∫ x in (0 : ℝ)..1, f x :=
    integral_even_neg_one_one (fun x => by
      simp only [hf]
      rw [Even.neg_pow ⟨l, by ring⟩ x, show (1 : ℝ) - (-x) ^ 2 = 1 - x ^ 2 by ring]) hIntneg hInt01
  have hfK : (∫ x in (0 : ℝ)..1, f x)
      = (1 / 4) * (∫ x in (0 : ℝ)..1, x ^ (2 * l) * (-Real.log (1 - x ^ 2)) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    simp only [hf]
    ring
  rw [show (∫ x in (-1 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) ^ 2)
      = ∫ x in (-1 : ℝ)..1, f x by
    apply intervalIntegral.integral_congr_uIoo
    intro x _
    simp only [hf]]
  rw [heven, hfK, hKval]
  rw [hHdef, hH2def]
  have hcast : (∑ r ∈ Finset.range (l + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1))
      = ∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1) := by
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    push_cast
    ring
  have hcast2 : (∑ r ∈ Finset.range (l + 1), 1 / ((((2 * r : ℕ)) : ℝ) + 1) ^ 2)
      = ∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1) ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    push_cast
    ring
  rw [hcast, hcast2]
  have hc2 : ((((2 * l : ℕ)) : ℝ) + 1) = 2 * ((l : ℝ) + 1 / 2) := by push_cast; ring
  rw [hc2]
  field_simp
end Y7Moments
end
end Inline_Y7_Moments
section Inline_Y7_Matrix
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Y7Matrix
open Y7Legendre Y7Rodrigues Y7Convolution Y7Monomial
def phiC (n : ℕ) : ℝ → ℂ := fun x => (((phi n).eval x : ℝ) : ℂ)
@[simp]
lemma phiC_apply (n : ℕ) (x : ℝ) : phiC n x = (((phi n).eval x : ℝ) : ℂ) := rfl
noncomputable def innerC (m n : ℕ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, phiC m x * star (phiC n x)
theorem innerC_eq_ite (m n : ℕ) : innerC m n = if m = n then 1 else 0 := by
  unfold innerC
  have h1 : (∫ x in (-1 : ℝ)..1, phiC m x * star (phiC n x)) =
      ∫ x in (-1 : ℝ)..1, (((phi m).eval x * (phi n).eval x : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp [phiC]
  rw [h1, intervalIntegral.integral_ofReal, integral_phi_mul_phi_eq_ite]
  split_ifs <;> norm_num
theorem innerC_self (n : ℕ) : innerC n n = 1 := by
  rw [innerC_eq_ite]
  simp
theorem integral_normSq_phiC (n : ℕ) :
    (∫ x in (-1 : ℝ)..1, ‖phiC n x‖ ^ 2) = 1 := by
  have h : (∫ x in (-1 : ℝ)..1, ‖phiC n x‖ ^ 2) =
      ∫ x in (-1 : ℝ)..1, (phi n).eval x * (phi n).eval x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [phiC]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h, integral_phi_sq_eq_one]
theorem innerC_conj_symm (m n : ℕ) : innerC n m = star (innerC m n) := by
  rw [innerC_eq_ite, innerC_eq_ite]
  by_cases h : m = n
  · rw [h]; simp
  · have h' : n ≠ m := fun hnm => h hnm.symm
    simp [h, h']
noncomputable def potentialMatrix (m n : ℕ) : ℝ :=
  ∫ x in Set.Ioo (-1 : ℝ) 1, RHLean.rescaledPotential x *
    ((phi m).eval x * (phi n).eval x)
theorem potentialMatrix_comm (m n : ℕ) : potentialMatrix m n = potentialMatrix n m := by
  unfold potentialMatrix
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring
theorem potentialFormRescaled_phiC (n : ℕ) :
    RHLean.potentialFormRescaled (phiC n) = potentialMatrix n n := by
  unfold potentialMatrix
  rw [show RHLean.potentialFormRescaled (phiC n) =
      ∫ x in Set.Ioo (-1 : ℝ) 1, RHLean.rescaledPotential x * ‖phiC n x‖ ^ 2
      from rfl]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [phiC]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring
noncomputable def shiftMatrix (m n : ℕ) (r : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1, phiC m x * star (phiC n (x + r))
noncomputable def polarMoment (a : ℝ) (n : ℕ) : ℂ :=
  RHLean.polarInnerRescaled a (phiC n)
theorem polarFormRescaled_phiC (a : ℝ) (n : ℕ) :
    RHLean.polarFormRescaled a (phiC n) = 2 * a * ‖polarMoment a n‖ ^ 2 := rfl
theorem normSq_phiC (n : ℕ) (x : ℝ) :
    ‖phiC n x‖ ^ 2 = (phi n).eval x * (phi n).eval x := by
  simp only [phiC]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring
theorem shiftMatrix_zero (m n : ℕ) : shiftMatrix m n 0 = innerC m n := by
  unfold shiftMatrix innerC
  apply intervalIntegral.integral_congr
  intro x _
  simp
noncomputable def potentialPowMoment (s : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x * x ^ s
@[reducible] def monoCoeff (m k : ℕ) : ℝ :=
  (((-1 : ℝ) ^ (m - k)) * (m.choose k : ℝ)) *
    (((2 * k).descFactorial m : ℕ) : ℝ)
@[reducible] def monoExp (m k : ℕ) : ℕ := 2 * k - m
lemma rescaledPotential_neg (x : ℝ) :
    RHLean.rescaledPotential (-x) = RHLean.rescaledPotential x := by
  unfold RHLean.rescaledPotential
  rw [show 1 - (-x) ^ 2 = 1 - x ^ 2 by ring]
lemma potentialPowMoment_even (l : ℕ) :
    potentialPowMoment (2 * l) =
      ((∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1)) - Real.log 2) /
        ((l : ℝ) + 1 / 2) := by
  unfold potentialPowMoment RHLean.rescaledPotential
  rw [show (∫ x in (-1 : ℝ)..1, (-(1 / 2) * Real.log (1 - x ^ 2)) * x ^ (2 * l)) =
      ∫ x in (-1 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) by
    apply intervalIntegral.integral_congr
    intro x _
    ring]
  exact Y7Moments.integral_even_x_pow_mul_potential l
lemma potentialPowMoment_odd (k : ℕ) : potentialPowMoment (2 * k + 1) = 0 := by
  unfold potentialPowMoment
  have hodd : ∀ x : ℝ,
      RHLean.rescaledPotential (-x) * (-x) ^ (2 * k + 1) =
        -(RHLean.rescaledPotential x * x ^ (2 * k + 1)) := by
    intro x
    rw [rescaledPotential_neg,
      Odd.neg_pow (show Odd (2 * k + 1) from ⟨k, by ring⟩) x]
    ring
  have hcomp : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential (-x) * (-x) ^ (2 * k + 1)) = ∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential x * x ^ (2 * k + 1) := by
    simpa using intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => RHLean.rescaledPotential x * x ^ (2 * k + 1))
      (a := (-1 : ℝ)) (b := 1)
  have h2 : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential (-x) * (-x) ^ (2 * k + 1)) =
      -∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x * x ^ (2 * k + 1) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact hodd x
  have hA : (∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x * x ^ (2 * k + 1)) =
      -∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x * x ^ (2 * k + 1) :=
    hcomp.symm.trans h2
  linarith
lemma intervalIntegrable_rescaledPotential_mul_pow (s : ℕ) :
    IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x * x ^ s) volume (-1) 1 := by
  have hW : IntervalIntegrable (fun x : ℝ => -Real.log (1 - x ^ 2)) volume 0 1 :=
    Y7Moments.intervalIntegrable_neg_log_one_sub_sq_W
  have h01 : IntervalIntegrable
      (fun x : ℝ => RHLean.rescaledPotential x * x ^ s) volume 0 1 := by
    refine (hW.continuousOn_mul ((continuous_id.pow s).continuousOn)).const_mul
      (1 / 2) |>.congr_uIoo ?_
    intro x hx
    change (1 / 2) * (x ^ s * -Real.log (1 - x ^ 2)) =
      RHLean.rescaledPotential x * x ^ s
    unfold RHLean.rescaledPotential
    ring
  have hneg : IntervalIntegrable
      (fun x : ℝ => RHLean.rescaledPotential x * x ^ s) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg (a := (-1 : ℝ)) (b := 0)]
    have hcomp : IntervalIntegrable
        (fun x : ℝ => RHLean.rescaledPotential (-x) * (-x) ^ s) volume 0 1 := by
      refine (h01.const_mul ((-1 : ℝ) ^ s)).congr_uIoo ?_
      intro x hx
      have hpow : (-x) ^ s = (-1 : ℝ) ^ s * x ^ s := by
        rw [neg_eq_neg_one_mul, mul_pow]
      change (-1 : ℝ) ^ s * (RHLean.rescaledPotential x * x ^ s) =
        RHLean.rescaledPotential (-x) * (-x) ^ s
      rw [rescaledPotential_neg, hpow]
      ring
    simpa using hcomp.symm
  exact hneg.trans h01
lemma intervalIntegrable_rescaledPotential_mul_legP (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x * (legP n).eval x)
      volume (-1) 1 := by
  refine (intervalIntegrable_rescaledPotential_mul_pow 0).continuousOn_mul
    ((legP n).continuous.continuousOn) |>.congr_uIoo ?_
  intro x hx
  ring
lemma integral_pow_mul_potential_mul_legP (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1, x ^ k * (RHLean.rescaledPotential x * (legP n).eval x)) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ j ∈ Finset.range (n + 1),
          monoCoeff n j * potentialPowMoment (k + monoExp n j) := by
  have hg : IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x * x ^ k)
      volume (-1) 1 := intervalIntegrable_rescaledPotential_mul_pow k
  have hcongr : (∫ x in (-1 : ℝ)..1,
        x ^ k * (RHLean.rescaledPotential x * (legP n).eval x)) =
      ∫ x in (-1 : ℝ)..1,
        (legP n).eval x * (RHLean.rescaledPotential x * x ^ k) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcongr, integral_mul_legP_eq_sum n
      (fun x : ℝ => RHLean.rescaledPotential x * x ^ k) hg]
  simp only [monoCoeff]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold potentialPowMoment monoExp
  apply intervalIntegral.integral_congr
  intro x _
  change x ^ (2 * j - n) * (RHLean.rescaledPotential x * x ^ k) =
    RHLean.rescaledPotential x * x ^ (k + (2 * j - n))
  rw [pow_add]
  ring
lemma sum_coeff_pull (m n : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
        monoCoeff m i * ((1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
          ∑ j ∈ Finset.range (n + 1),
            monoCoeff n j * potentialPowMoment (monoExp m i + monoExp n j))) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            potentialPowMoment (monoExp m i + monoExp n j) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
lemma integral_potential_mul_legP_mul_legP (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential x * (legP m).eval x * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            potentialPowMoment (monoExp m i + monoExp n j) := by
  have hg : IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x * (legP n).eval x)
      volume (-1) 1 := intervalIntegrable_rescaledPotential_mul_legP n
  have hcongr : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential x * (legP m).eval x * (legP n).eval x) =
      ∫ x in (-1 : ℝ)..1,
        (legP m).eval x * (RHLean.rescaledPotential x * (legP n).eval x) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcongr, integral_mul_legP_eq_sum m
      (fun x : ℝ => RHLean.rescaledPotential x * (legP n).eval x) hg]
  simp only [integral_pow_mul_potential_mul_legP]
  rw [sum_coeff_pull]
  ring
theorem potentialMatrix_eq_interval (m n : ℕ) :
    potentialMatrix m n =
      (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
        ∫ x in (-1 : ℝ)..1,
          RHLean.rescaledPotential x * (legP m).eval x * (legP n).eval x := by
  unfold potentialMatrix
  rw [show (∫ x in Set.Ioo (-1 : ℝ) 1,
        RHLean.rescaledPotential x * ((phi m).eval x * (phi n).eval x)) =
      ∫ x in Set.Ioo (-1 : ℝ) 1,
        (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
          (RHLean.rescaledPotential x * (legP m).eval x * (legP n).eval x) by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    unfold phi
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
theorem potentialMatrix_eq_sum (m n : ℕ) :
    potentialMatrix m n =
      (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        monoCoeff m i * monoCoeff n j *
          potentialPowMoment (monoExp m i + monoExp n j) := by
  rw [potentialMatrix_eq_interval, integral_potential_mul_legP_mul_legP]
  ring
lemma sum_mul_sum_pull (s t : Finset ℕ) (g : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (c : ℝ) :
    (∑ i ∈ s, g i * (c * ∑ j ∈ t, f i j)) = c * ∑ i ∈ s, ∑ j ∈ t, g i * f i j := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
theorem integral_pow_mul_translate_pow (a b r : ℝ) (s t : ℕ) :
    (∫ x in a..b, x ^ s * (x + r) ^ t) =
      ∑ k ∈ Finset.range (t + 1),
        (t.choose k : ℝ) * r ^ (t - k) *
          ((b ^ (s + k + 1) - a ^ (s + k + 1)) / ((s + k + 1 : ℕ) : ℝ)) := by
  have hpt : (fun x : ℝ => x ^ s * (x + r) ^ t) =
      fun x : ℝ => ∑ k ∈ Finset.range (t + 1),
        x ^ s * (x ^ k * r ^ (t - k) * (t.choose k : ℝ)) := by
    funext x
    rw [add_pow]
    rw [Finset.mul_sum]
  rw [hpt, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun x : ℝ => x ^ s * (x ^ k * r ^ (t - k) * (t.choose k : ℝ))) =
        fun x : ℝ => (r ^ (t - k) * (t.choose k : ℝ)) * x ^ (s + k) by
      funext x
      rw [pow_add]
      ring]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    push_cast
    ring
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop
theorem integral_pow_mul_legP_add (k n : ℕ) (a b r : ℝ) :
    (∫ x in a..b, x ^ k * (legP n).eval (x + r)) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ j ∈ Finset.range (n + 1),
          monoCoeff n j * (∫ x in a..b, x ^ k * (x + r) ^ monoExp n j) := by
  have hpt : (fun x : ℝ => x ^ k * (legP n).eval (x + r)) =
      fun x : ℝ => (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ j ∈ Finset.range (n + 1),
          x ^ k * (monoCoeff n j * (x + r) ^ monoExp n j) := by
    funext x
    rw [eval_legP_eq_sum]
    simp only [monoCoeff, monoExp]
    rw [← mul_assoc]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hpt, intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  · intro j hj
    apply Continuous.intervalIntegrable
    fun_prop
theorem integral_legP_translate_legP_eq_sum (m n : ℕ) (a b r : ℝ) :
    (∫ x in a..b, (legP m).eval x * (legP n).eval (x + r)) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            ∑ k ∈ Finset.range (monoExp n j + 1),
              ((monoExp n j).choose k : ℝ) * r ^ (monoExp n j - k) *
                ((b ^ (monoExp m i + k + 1) - a ^ (monoExp m i + k + 1)) /
                  ((monoExp m i + k + 1 : ℕ) : ℝ)) := by
  have hg : IntervalIntegrable (fun x : ℝ => (legP n).eval (x + r)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmain : (∑ i ∈ Finset.range (m + 1),
        monoCoeff m i * (∫ x in a..b,
          x ^ monoExp m i * (legP n).eval (x + r))) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            ∑ k ∈ Finset.range (monoExp n j + 1),
              ((monoExp n j).choose k : ℝ) * r ^ (monoExp n j - k) *
                ((b ^ (monoExp m i + k + 1) - a ^ (monoExp m i + k + 1)) /
                  ((monoExp m i + k + 1 : ℕ) : ℝ)) := by
    simp only [integral_pow_mul_legP_add]
    rw [sum_mul_sum_pull]
    apply congrArg ((1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) * ·)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_pow_mul_translate_pow]
    ring
  rw [integral_mul_legP_eq_sum' m (fun x : ℝ => (legP n).eval (x + r)) a b hg, hmain]
  ring
noncomputable def shiftOverlap (m n : ℕ) (r : ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..(1 - r), (legP m).eval x * (legP n).eval (x + r)
noncomputable def shiftOverlapNeg (m n : ℕ) (r : ℝ) : ℝ :=
  ∫ x in (-1 + r)..1, (legP m).eval x * (legP n).eval (x - r)
theorem shiftOverlap_eq_sum (m n : ℕ) (r : ℝ) :
    shiftOverlap m n r =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            ∑ k ∈ Finset.range (monoExp n j + 1),
              ((monoExp n j).choose k : ℝ) * r ^ (monoExp n j - k) *
                (((1 - r) ^ (monoExp m i + k + 1) - (-1 : ℝ) ^ (monoExp m i + k + 1)) /
                  ((monoExp m i + k + 1 : ℕ) : ℝ)) :=
  integral_legP_translate_legP_eq_sum m n (-1) (1 - r) r
theorem shiftOverlapNeg_eq_sum (m n : ℕ) (r : ℝ) :
    shiftOverlapNeg m n r =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            ∑ k ∈ Finset.range (monoExp n j + 1),
              ((monoExp n j).choose k : ℝ) * (-r) ^ (monoExp n j - k) *
                ((1 ^ (monoExp m i + k + 1) - (-1 + r) ^ (monoExp m i + k + 1)) /
                  ((monoExp m i + k + 1 : ℕ) : ℝ)) :=
  integral_legP_translate_legP_eq_sum m n (-1 + r) 1 (-r)
noncomputable def harmonicR (n : ℕ) : ℝ := (harmonic n : ℝ)
lemma harmonicR_zero : harmonicR 0 = 0 := by
  unfold harmonicR harmonic
  simp
lemma harmonicR_succ (n : ℕ) :
    harmonicR (n + 1) = harmonicR n + 1 / (n + 1 : ℝ) := by
  unfold harmonicR
  rw [harmonic_succ]
  push_cast
  ring
theorem harmonicR_eq_integral (n : ℕ) :
    harmonicR n = ∫ x in (0 : ℝ)..1, (1 - x ^ n) / (1 - x) := by
  have hcongr : (∫ x in (0 : ℝ)..1, (1 - x ^ n) / (1 - x)) =
      ∫ x in (0 : ℝ)..1, ∑ k ∈ Finset.range n, x ^ k := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx1 : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    rw [div_eq_iff hx1]
    have hgeom := geom_sum_mul_add (x - 1) n
    simp only [sub_add_cancel] at hgeom
    nlinarith [hgeom]
  rw [hcongr]
  unfold harmonicR harmonic
  push_cast
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_pow]
    simp [one_div]
  · intro k hk
    apply Continuous.intervalIntegrable
    fun_prop
noncomputable def potentialSqPowMoment (s : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x ^ 2 * x ^ s
lemma potentialSqPowMoment_even (l : ℕ) :
    potentialSqPowMoment (2 * l) =
      (((∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1)) - Real.log 2) ^ 2
          + (∑ r ∈ Finset.range (l + 1), 1 / ((2 * (r : ℝ)) + 1) ^ 2) - Real.pi ^ 2 / 12)
          / ((l : ℝ) + 1 / 2) := by
  unfold potentialSqPowMoment RHLean.rescaledPotential
  rw [show (∫ x in (-1 : ℝ)..1,
        (-(1 / 2) * Real.log (1 - x ^ 2)) ^ 2 * x ^ (2 * l)) =
      ∫ x in (-1 : ℝ)..1, x ^ (2 * l) * (-(1 / 2) * Real.log (1 - x ^ 2)) ^ 2 by
    apply intervalIntegral.integral_congr
    intro x _
    ring]
  exact Y7Moments.integral_even_x_pow_mul_potential_sq l
lemma potentialSqPowMoment_odd (k : ℕ) : potentialSqPowMoment (2 * k + 1) = 0 := by
  unfold potentialSqPowMoment
  have hodd : ∀ x : ℝ,
      RHLean.rescaledPotential (-x) ^ 2 * (-x) ^ (2 * k + 1) =
        -(RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1)) := by
    intro x
    rw [rescaledPotential_neg,
      Odd.neg_pow (show Odd (2 * k + 1) from ⟨k, by ring⟩) x]
    ring
  have hcomp : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential (-x) ^ 2 * (-x) ^ (2 * k + 1)) =
      ∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1) := by
    simpa using intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1))
      (a := (-1 : ℝ)) (b := 1)
  have h2 : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential (-x) ^ 2 * (-x) ^ (2 * k + 1)) =
      -∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    exact hodd x
  have hA : (∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1)) =
      -∫ x in (-1 : ℝ)..1, RHLean.rescaledPotential x ^ 2 * x ^ (2 * k + 1) :=
    hcomp.symm.trans h2
  linarith
lemma intervalIntegrable_rescaledPotential_sq_mul_pow (s : ℕ) :
    IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ s)
      volume (-1) 1 := by
  have hW : IntervalIntegrable (fun x : ℝ => (-Real.log (1 - x ^ 2)) ^ 2) volume 0 1 :=
    Y7Moments.intervalIntegrable_neg_log_one_sub_sq_two
  have h01 : IntervalIntegrable
      (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ s) volume 0 1 := by
    refine (hW.continuousOn_mul ((continuous_id.pow s).continuousOn)).const_mul
      (1 / 4) |>.congr_uIoo ?_
    intro x hx
    change (1 / 4) * (x ^ s * (-Real.log (1 - x ^ 2)) ^ 2) =
      RHLean.rescaledPotential x ^ 2 * x ^ s
    unfold RHLean.rescaledPotential
    ring
  have hneg : IntervalIntegrable
      (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ s) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg (a := (-1 : ℝ)) (b := 0)]
    have hcomp : IntervalIntegrable
        (fun x : ℝ => RHLean.rescaledPotential (-x) ^ 2 * (-x) ^ s) volume 0 1 := by
      refine (h01.const_mul ((-1 : ℝ) ^ s)).congr_uIoo ?_
      intro x hx
      have hpow : (-x) ^ s = (-1 : ℝ) ^ s * x ^ s := by
        rw [neg_eq_neg_one_mul, mul_pow]
      change (-1 : ℝ) ^ s * (RHLean.rescaledPotential x ^ 2 * x ^ s) =
        RHLean.rescaledPotential (-x) ^ 2 * (-x) ^ s
      rw [rescaledPotential_neg, hpow]
      ring
    simpa using hcomp.symm
  exact hneg.trans h01
lemma intervalIntegrable_rescaledPotential_sq_mul_legP (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * (legP n).eval x)
      volume (-1) 1 := by
  refine (intervalIntegrable_rescaledPotential_sq_mul_pow 0).continuousOn_mul
    ((legP n).continuous.continuousOn) |>.congr_uIoo ?_
  intro x hx
  ring
lemma integral_pow_mul_potential_sq_mul_legP (k n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        x ^ k * (RHLean.rescaledPotential x ^ 2 * (legP n).eval x)) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ j ∈ Finset.range (n + 1),
          monoCoeff n j * potentialSqPowMoment (k + monoExp n j) := by
  have hg : IntervalIntegrable (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ k)
      volume (-1) 1 := intervalIntegrable_rescaledPotential_sq_mul_pow k
  have hcongr : (∫ x in (-1 : ℝ)..1,
        x ^ k * (RHLean.rescaledPotential x ^ 2 * (legP n).eval x)) =
      ∫ x in (-1 : ℝ)..1,
        (legP n).eval x * (RHLean.rescaledPotential x ^ 2 * x ^ k) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcongr, integral_mul_legP_eq_sum n
      (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * x ^ k) hg]
  simp only [monoCoeff]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold potentialSqPowMoment monoExp
  apply intervalIntegral.integral_congr
  intro x _
  change x ^ (2 * j - n) * (RHLean.rescaledPotential x ^ 2 * x ^ k) =
    RHLean.rescaledPotential x ^ 2 * x ^ (k + (2 * j - n))
  rw [pow_add]
  ring
lemma sum_coeff_pull_gen (m n : ℕ) (M : ℕ → ℝ) :
    (∑ i ∈ Finset.range (m + 1),
        monoCoeff m i * ((1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
          ∑ j ∈ Finset.range (n + 1),
            monoCoeff n j * M (monoExp m i + monoExp n j))) =
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j * M (monoExp m i + monoExp n j) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
lemma integral_potential_sq_mul_legP_mul_legP (m n : ℕ) :
    (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential x ^ 2 * (legP m).eval x * (legP n).eval x) =
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          monoCoeff m i * monoCoeff n j *
            potentialSqPowMoment (monoExp m i + monoExp n j) := by
  have hg : IntervalIntegrable
      (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * (legP n).eval x)
      volume (-1) 1 := intervalIntegrable_rescaledPotential_sq_mul_legP n
  have hcongr : (∫ x in (-1 : ℝ)..1,
        RHLean.rescaledPotential x ^ 2 * (legP m).eval x * (legP n).eval x) =
      ∫ x in (-1 : ℝ)..1,
        (legP m).eval x * (RHLean.rescaledPotential x ^ 2 * (legP n).eval x) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hcongr, integral_mul_legP_eq_sum m
      (fun x : ℝ => RHLean.rescaledPotential x ^ 2 * (legP n).eval x) hg]
  simp only [integral_pow_mul_potential_sq_mul_legP]
  rw [sum_coeff_pull_gen (M := potentialSqPowMoment)]
  ring
noncomputable def potentialSqMatrix (m n : ℕ) : ℝ :=
  ∫ x in Set.Ioo (-1 : ℝ) 1, RHLean.rescaledPotential x ^ 2 *
    ((phi m).eval x * (phi n).eval x)
theorem potentialSqMatrix_eq_sum (m n : ℕ) :
    potentialSqMatrix m n =
      (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
      (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
      (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
      ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        monoCoeff m i * monoCoeff n j *
          potentialSqPowMoment (monoExp m i + monoExp n j) := by
  have hbridge : potentialSqMatrix m n =
      (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
        ∫ x in (-1 : ℝ)..1,
          RHLean.rescaledPotential x ^ 2 * (legP m).eval x * (legP n).eval x := by
    unfold potentialSqMatrix
    rw [show (∫ x in Set.Ioo (-1 : ℝ) 1,
          RHLean.rescaledPotential x ^ 2 * ((phi m).eval x * (phi n).eval x)) =
        ∫ x in Set.Ioo (-1 : ℝ) 1,
          (Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2)) *
            (RHLean.rescaledPotential x ^ 2 * (legP m).eval x * (legP n).eval x) by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      unfold phi
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [hbridge, integral_potential_sq_mul_legP_mul_legP]
  ring
theorem shiftOverlap_phi (m n : ℕ) (r : ℝ) :
    (∫ x in (-1 : ℝ)..(1 - r), (phi m).eval x * (phi n).eval (x + r)) =
      Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2) *
        shiftOverlap m n r := by
  unfold shiftOverlap
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  unfold phi
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring
theorem shiftOverlapNeg_phi (m n : ℕ) (r : ℝ) :
    (∫ x in (-1 + r : ℝ)..1, (phi m).eval x * (phi n).eval (x - r)) =
      Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2) *
        shiftOverlapNeg m n r := by
  unfold shiftOverlapNeg
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  unfold phi
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring
noncomputable def shiftGram (m n : ℕ) (r : ℝ) : ℝ :=
  Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2) *
    (shiftOverlap m n r + shiftOverlapNeg m n r)
theorem shiftGram_eq_sum (m n : ℕ) (r : ℝ) :
    shiftGram m n r =
      Real.sqrt ((2 * (m : ℝ) + 1) / 2) * Real.sqrt ((2 * (n : ℝ) + 1) / 2) *
        ((1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
         (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
           ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
             monoCoeff m i * monoCoeff n j *
               ∑ k ∈ Finset.range (monoExp n j + 1),
                 ((monoExp n j).choose k : ℝ) * r ^ (monoExp n j - k) *
                   (((1 - r) ^ (monoExp m i + k + 1) - (-1 : ℝ) ^ (monoExp m i + k + 1)) /
                     ((monoExp m i + k + 1 : ℕ) : ℝ))
          + (1 / ((2 : ℝ) ^ m * (m.factorial : ℝ))) *
            (1 / ((2 : ℝ) ^ n * (n.factorial : ℝ))) *
              ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
                monoCoeff m i * monoCoeff n j *
                  ∑ k ∈ Finset.range (monoExp n j + 1),
                    ((monoExp n j).choose k : ℝ) * (-r) ^ (monoExp n j - k) *
                      ((1 ^ (monoExp m i + k + 1) - (-1 + r) ^ (monoExp m i + k + 1)) /
                        ((monoExp m i + k + 1 : ℕ) : ℝ))) := by
  unfold shiftGram
  rw [shiftOverlap_eq_sum, shiftOverlapNeg_eq_sum]
noncomputable def archDiagonal (n : ℕ) : ℝ :=
  harmonicR n + RHLean.c0 (RHLean.endpoint 7)
theorem archDiagonal_zero :
    archDiagonal 0 = RHLean.physicalConstant - Real.log (Real.log 7 / 2) := by
  unfold archDiagonal harmonicR harmonic RHLean.c0 RHLean.endpoint
  simp
noncomputable def tailFloor (ε : ℝ) (j : ℕ) : ℝ :=
  harmonicR (2 * j + 1) + RHLean.c0 (RHLean.endpoint 7)
    - (RHLean.arithCoeff 2 + RHLean.arithCoeff 3 + RHLean.arithCoeff 4
        + RHLean.arithCoeff 5)
    - RHLean.endpoint 7 / 2
    - 2 * (Real.sinh (RHLean.endpoint 7) - RHLean.endpoint 7) - 3 * ε
noncomputable def tailFloorBase (j : ℕ) : ℝ := tailFloor 0 j
lemma tailFloor_eq_base_sub (ε : ℝ) (j : ℕ) :
    tailFloor ε j = tailFloorBase j - 3 * ε := by
  unfold tailFloorBase tailFloor
  ring
lemma tailFloor_anti (j : ℕ) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    tailFloor ε₂ j ≤ tailFloor ε₁ j := by
  rw [tailFloor_eq_base_sub, tailFloor_eq_base_sub]
  linarith
end Y7Matrix
namespace Y7Chain
open Polynomial Finset
open scoped BigOperators
noncomputable def rhoCoeff : ℕ → ℚ
  | m =>
      let A : ℚ := ((3 / 2 : ℚ) ^ (m + 1)) / (((m + 1).factorial : ℚ))
      let B : ℚ := ((2 : ℚ) ^ (m + 1)) / (((m + 2).factorial : ℚ))
      let S : ℚ := ∑ j ∈ Finset.Icc 2 (m + 1),
        if _h : 2 ≤ j ∧ 1 ≤ m then
          ((2 : ℚ) ^ j) / ((j.factorial : ℚ)) * rhoCoeff (m + 1 - j)
        else 0
      (A - B - S) / 2
termination_by m => m
decreasing_by
  omega
lemma rhoCoeff_zero : rhoCoeff 0 = 1 / 4 := by
  conv_lhs => rw [rhoCoeff.eq_1]
  norm_num
lemma rhoCoeff_one : rhoCoeff 1 = -(1 / 48) := by
  conv_lhs => rw [rhoCoeff.eq_1]
  have hsing : Finset.Icc 2 (1 + 1) = ({2} : Finset ℕ) := by
    rw [show (1 : ℕ) + 1 = 2 by norm_num, Finset.Icc_self]
  rw [hsing, Finset.sum_singleton]
  norm_num
  rw [rhoCoeff_zero]
  norm_num
noncomputable def sinhTaylorFun (a x : ℝ) (K : ℕ) : ℝ :=
  ∑ d ∈ Finset.range K,
    (a * x / 2) ^ (2 * d + 1) / (((2 * d + 1).factorial : ℕ) : ℝ)
noncomputable def gammaM (R : ℝ) : ℝ :=
  Real.exp (R / 2) / (2 * Real.sin R) + 1 / (2 * R)
noncomputable def epsilonGamma (a : ℝ) : ℝ :=
  2 * a * gammaM (14 / 5) * (2 * a / (14 / 5)) ^ 241 / (1 - 2 * a / (14 / 5))
noncomputable def sinhRemainder (a : ℝ) : ℝ :=
  (a / 2) ^ 201 / (((201).factorial : ℕ) : ℝ)
    / (1 - (a / 2) ^ 2 / (202 * 203))
noncomputable def epsilonPolar (a : ℝ) : ℝ :=
  2 * a * (2 * Real.sqrt (Real.sinh a / a - 1) * Real.sqrt 2 * sinhRemainder a
    + 2 * sinhRemainder a ^ 2)
noncomputable def epsilonTotal (a : ℝ) : ℝ := epsilonGamma a + epsilonPolar a
def GRes {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
    (K2 : Matrix ι ι ℝ) (K : Matrix m ι ℝ) (B : Matrix n ι ℝ) : Matrix ι ι ℝ :=
  K2 - K.conjTranspose * K - B.conjTranspose * B
theorem GRes_posSemidef {ι m n p : Type*} [Fintype ι] [Fintype m] [Fintype n]
    [Fintype p] (K2 : Matrix ι ι ℝ) (K : Matrix m ι ℝ) (B : Matrix n ι ℝ)
    (C : Matrix p ι ℝ)
    (h : K2 = K.conjTranspose * K + B.conjTranspose * B + C.conjTranspose * C) :
    (GRes K2 K B).PosSemidef := by
  unfold GRes
  exact Y7Parseval.parseval_remainder_posSemidef K2 K B C h
open Y7Matrix in
structure RBox (c : ℝ) (lo hi : ℚ) : Prop where
  lo_le : (lo : ℝ) ≤ c
  le_hi : c ≤ (hi : ℝ)
open Y7Matrix in
theorem harmonicR_201_box :
    RBox (harmonicR 201) (5883006072499553 / 10 ^ 15) (5883006072499555 / 10 ^ 15) := by
  constructor <;> unfold harmonicR <;> norm_num [harmonic]
open Y7Matrix in
theorem harmonicR_301_box :
    RBox (harmonicR 301) (628598613943571 / 10 ^ 14) (628598613943572 / 10 ^ 14) := by
  constructor <;> unfold harmonicR <;> norm_num [harmonic]
open Y7Matrix in
structure TailBoxes : Prop where
  log2pi : RBox (Real.log (2 * Real.pi))
    (918938533204671 / 500000000000000) (36757541328187 / 20000000000000)
  gamma : RBox Real.eulerMascheroniConstant
    (577215664901531953 / 10 ^ 18) (115443132980308107 / 200000000000000000)
  loglog : RBox (Real.log (Real.log 7 / 2))
    (-13708684990837 / 500000000000000) (-856792811927 / 31250000000000)
  log7 : RBox (Real.log 7)
    (121619384315957 / 62500000000000) (389182029811063 / 200000000000000)
  c2 : RBox (RHLean.arithCoeff 2)
    (490129071734271 / 1000000000000000) (122532267933569 / 250000000000000)
  c3 : RBox (RHLean.arithCoeff 3)
    (634284100597561 / 1000000000000000) (317142050298783 / 500000000000000)
  c4 : RBox (RHLean.arithCoeff 4)
    (346573590279971 / 1000000000000000) (13862943611199 / 40000000000000)
  c5 : RBox (RHLean.arithCoeff 5)
    (359881257776799 / 500000000000000) (719762515553603 / 1000000000000000)
  sinh : RBox (Real.sinh (Real.log 7 / 2))
    (7086833868923 / 6250000000000) (1133893419027683 / 1000000000000000)
open Y7Matrix in
theorem tailFloor_100_gt (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) (hb : TailBoxes) :
    tailFloor ε 100 > (496227206741 / 10 ^ 12 : ℝ) := by
  rw [tailFloor_eq_base_sub]
  unfold tailFloorBase tailFloor RHLean.c0 RHLean.physicalConstant RHLean.endpoint
  norm_num
  linarith [harmonicR_201_box.lo_le, hb.log2pi.le_hi, hb.gamma.le_hi,
    hb.loglog.le_hi, hb.log7.lo_le, hb.c2.le_hi, hb.c3.le_hi, hb.c4.le_hi,
    hb.c5.le_hi, hb.sinh.le_hi, hε]
open Y7Matrix in
theorem tailFloor_150_gt (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) (hb : TailBoxes) :
    tailFloor ε 150 > (899207273677 / 10 ^ 12 : ℝ) := by
  rw [tailFloor_eq_base_sub]
  unfold tailFloorBase tailFloor RHLean.c0 RHLean.physicalConstant RHLean.endpoint
  norm_num
  linarith [harmonicR_301_box.lo_le, hb.log2pi.le_hi, hb.gamma.le_hi,
    hb.loglog.le_hi, hb.log7.lo_le, hb.c2.le_hi, hb.c3.le_hi, hb.c4.le_hi,
    hb.c5.le_hi, hb.sinh.le_hi, hε]
open Y7Matrix in
theorem log_two_box :
    RBox (Real.log 2) (6931471805599453 / 10 ^ 16) (6931471805599454 / 10 ^ 16) := by
  constructor
  · have h := Real.sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 20
    norm_num at h
    linarith
  · have h := Real.sum_range_sub_log_div_le (x := (1 / 3 : ℝ)) (by norm_num) 20
    rw [abs_le] at h
    norm_num at h
    linarith [h.2]
open Y7Matrix in
lemma eulerMascheroniConstant_lt_gamma₂ (n : ℕ) (hn : 1 ≤ n) :
    Real.eulerMascheroniConstant < γ₂ n := by
  have h_strict_anti : StrictAnti (fun n : ℕ => γ₂ (n + 1)) := by
    refine strictAnti_nat_of_succ_lt ?_
    intro n
    have := euler_maclaurin_decreasing (n + 1) (by linarith)
    grind
  have h_tendsto : Filter.Tendsto (fun n : ℕ => γ₂ (n + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    euler_maclaurin_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have h_lt : ∀ n : ℕ, Real.eulerMascheroniConstant < γ₂ (n + 1) := by
    intro n
    exact lt_of_le_of_lt
      (le_of_tendsto h_tendsto <| Filter.eventually_atTop.mpr
        ⟨n + 1, fun m hm => h_strict_anti.antitone hm⟩)
      (h_strict_anti <| Nat.lt_succ_self _)
  cases n with
  | zero => omega
  | succ m => exact h_lt m
open Y7Matrix in
set_option maxRecDepth 1000000 in
theorem gamma_box :
    RBox Real.eulerMascheroniConstant
      (577215664901531953 / 10 ^ 18) (115443132980308107 / 200000000000000000) := by
  constructor
  · have hγ := γ₃_lower_bound 1024 (by norm_num)
    refine le_trans ?_ (le_of_lt hγ)
    unfold γ₃
    rw [show ((1024 : ℕ) : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    have h2 := log_two_box.le_hi
    norm_num [harmonic]
    linarith [h2]
  · have hγ := eulerMascheroniConstant_lt_gamma₂ 1024 (by norm_num)
    refine le_trans (le_of_lt hγ) ?_
    unfold γ₂
    rw [show ((1024 : ℕ) : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    have h2 := log_two_box.lo_le
    norm_num [harmonic]
    linarith [h2]
open Y7Matrix
lemma RBox.weaken {c : ℝ} {lo hi lo' hi' : ℚ} (h : RBox c lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : RBox c lo' hi' :=
  ⟨le_trans (by exact_mod_cast hlo) h.lo_le, le_trans h.le_hi (by exact_mod_cast hhi)⟩
lemma RBox.add {a b : ℝ} {alo ahi blo bhi : ℚ} (ha : RBox a alo ahi)
    (hb : RBox b blo bhi) : RBox (a + b) (alo + blo) (ahi + bhi) := by
  constructor
  · push_cast
    exact add_le_add ha.lo_le hb.lo_le
  · push_cast
    exact add_le_add ha.le_hi hb.le_hi
lemma RBox.sub {a b : ℝ} {alo ahi blo bhi : ℚ} (ha : RBox a alo ahi)
    (hb : RBox b blo bhi) : RBox (a - b) (alo - bhi) (ahi - blo) := by
  constructor
  · push_cast
    exact sub_le_sub ha.lo_le hb.le_hi
  · push_cast
    exact sub_le_sub ha.le_hi hb.lo_le
lemma RBox.div {a b : ℝ} {alo ahi blo bhi : ℚ}
    (ha : RBox a alo ahi) (hb : RBox b blo bhi) (hblo : (0 : ℚ) < blo)
    (halo : (0 : ℚ) ≤ alo) (hahi : (0 : ℚ) ≤ ahi) :
    RBox (a / b) (alo / bhi) (ahi / blo) := by
  have hbpos : 0 < b := lt_of_lt_of_le (by exact_mod_cast hblo) hb.lo_le
  have hbhipos : 0 < (bhi : ℝ) := lt_of_lt_of_le hbpos hb.le_hi
  constructor
  · rw [show ((alo / bhi : ℚ) : ℝ) = (alo : ℝ) / (bhi : ℝ) by push_cast; ring,
      le_div_iff₀ hbpos]
    calc ((alo : ℝ) / (bhi : ℝ)) * b
        ≤ ((alo : ℝ) / (bhi : ℝ)) * (bhi : ℝ) :=
          mul_le_mul_of_nonneg_left hb.le_hi
            (div_nonneg (by exact_mod_cast halo) (le_of_lt hbhipos))
      _ = (alo : ℝ) := by rw [div_mul_cancel₀ _ (ne_of_gt hbhipos)]
      _ ≤ a := ha.lo_le
  · rw [show ((ahi / blo : ℚ) : ℝ) = (ahi : ℝ) / (blo : ℝ) by push_cast; ring,
      div_le_iff₀ hbpos]
    calc a ≤ (ahi : ℝ) := ha.le_hi
      _ = ((ahi : ℝ) / (blo : ℝ)) * (blo : ℝ) :=
          (div_mul_cancel₀ _ (ne_of_gt (by exact_mod_cast hblo))).symm
      _ ≤ ((ahi : ℝ) / (blo : ℝ)) * b :=
          mul_le_mul_of_nonneg_left hb.lo_le
            (div_nonneg (by exact_mod_cast hahi) (le_of_lt (by exact_mod_cast hblo)))
lemma sqrt_box_nat (k : ℕ) (lo hi : ℚ)
    (hlo : (0 : ℝ) ≤ (lo : ℝ)) (hhi : (0 : ℝ) ≤ (hi : ℝ))
    (hlo2 : (lo : ℝ) ^ 2 ≤ (k : ℝ)) (hhi2 : (k : ℝ) ≤ (hi : ℝ) ^ 2) :
    RBox (Real.sqrt k) lo hi := by
  constructor
  · exact (Real.le_sqrt hlo (by positivity)).mpr hlo2
  · exact (Real.sqrt_le_left hhi).mpr hhi2
theorem log_three_box :
    RBox (Real.log 3) (274653072167027 / 250000000000000)
      (1098612288668111 / 1000000000000000) := by
  constructor
  · have h := Real.sum_range_le_log_div (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 30
    norm_num at h
    linarith
  · have h := Real.sum_range_sub_log_div_le (x := (1 / 2 : ℝ)) (by norm_num) 30
    rw [abs_le] at h
    norm_num at h
    linarith [h.2]
theorem log_five_box :
    RBox (Real.log 5) (1609437912434099 / 1000000000000000)
      (804718956217051 / 500000000000000) := by
  constructor
  · have h := Real.sum_range_le_log_div (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) 48
    norm_num at h
    linarith
  · have h := Real.sum_range_sub_log_div_le (x := (2 / 3 : ℝ)) (by norm_num) 48
    rw [abs_le] at h
    norm_num at h
    linarith [h.2]
theorem log_seven_box :
    RBox (Real.log 7) (121619384315957 / 62500000000000)
      (389182029811063 / 200000000000000) := by
  constructor
  · have h := Real.sum_range_le_log_div (x := (3 / 4 : ℝ)) (by norm_num) (by norm_num) 70
    norm_num at h
    linarith
  · have h := Real.sum_range_sub_log_div_le (x := (3 / 4 : ℝ)) (by norm_num) 70
    rw [abs_le] at h
    norm_num at h
    linarith [h.2]
theorem sqrt_two_box :
    RBox (Real.sqrt 2) (1414213562373095 / 10 ^ 15) (1414213562373096 / 10 ^ 15) :=
  sqrt_box_nat 2 (1414213562373095 / 10 ^ 15) (1414213562373096 / 10 ^ 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem sqrt_three_box :
    RBox (Real.sqrt 3) (1732050807568877 / 10 ^ 15) (1732050807568878 / 10 ^ 15) :=
  sqrt_box_nat 3 (1732050807568877 / 10 ^ 15) (1732050807568878 / 10 ^ 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem sqrt_five_box :
    RBox (Real.sqrt 5) (2236067977499789 / 10 ^ 15) (2236067977499790 / 10 ^ 15) :=
  sqrt_box_nat 5 (2236067977499789 / 10 ^ 15) (2236067977499790 / 10 ^ 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem sqrt_seven_box :
    RBox (Real.sqrt 7) (2645751311064590 / 10 ^ 15) (2645751311064591 / 10 ^ 15) :=
  sqrt_box_nat 7 (2645751311064590 / 10 ^ 15) (2645751311064591 / 10 ^ 15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem log_pi_box :
    RBox (Real.log Real.pi) (1144729885849399 / 10 ^ 15)
      (572364942924701 / 500000000000000) := by
  constructor
  · have hq : ((3141592653589793 : ℝ) / 10 ^ 15) ≤ Real.pi := by
      have h := Real.pi_gt_d20
      norm_num at h ⊢
      linarith
    have hlog : Real.log ((3141592653589793 : ℝ) / 10 ^ 15) ≤ Real.log Real.pi :=
      Real.log_le_log (by norm_num) hq
    have hx0 : 0 ≤ (((3141592653589793 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589793 : ℝ) / 10 ^ 15 + 1)) := by norm_num
    have hx1 : (((3141592653589793 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589793 : ℝ) / 10 ^ 15 + 1)) < 1 := by norm_num
    have h := Real.sum_range_le_log_div
      (x := (((3141592653589793 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589793 : ℝ) / 10 ^ 15 + 1))) hx0 hx1 35
    norm_num at h
    linarith [hlog]
  · have hq : Real.pi ≤ ((3141592653589794 : ℝ) / 10 ^ 15) := by
      have h := Real.pi_lt_d20
      norm_num at h ⊢
      linarith
    have hlog : Real.log Real.pi ≤ Real.log ((3141592653589794 : ℝ) / 10 ^ 15) :=
      Real.log_le_log (by positivity) hq
    have hx0 : 0 ≤ (((3141592653589794 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589794 : ℝ) / 10 ^ 15 + 1)) := by norm_num
    have hx1 : |(((3141592653589794 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589794 : ℝ) / 10 ^ 15 + 1))| < 1 := by norm_num
    have h := Real.sum_range_sub_log_div_le
      (x := (((3141592653589794 : ℝ) / 10 ^ 15 - 1) /
        ((3141592653589794 : ℝ) / 10 ^ 15 + 1))) hx1 35
    rw [abs_le] at h
    norm_num at h
    linarith [hlog, h.2]
theorem log_two_pi_box :
    RBox (Real.log (2 * Real.pi)) (918938533204671 / 500000000000000)
      (36757541328187 / 20000000000000) := by
  have hmul : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hmul]
  refine (RBox.add log_two_box log_pi_box).weaken ?_ ?_
  · norm_num
  · norm_num
theorem loglog7_box :
    RBox (Real.log (Real.log 7)) (332864905289137 / 500000000000000)
      (665729810578279 / 1000000000000000) := by
  constructor
  · have hlog : Real.log ((121619384315957 / 62500000000000 : ℚ) : ℝ) ≤ Real.log (Real.log 7) :=
      Real.log_le_log (x := ((121619384315957 / 62500000000000 : ℚ) : ℝ))
        (by norm_num) log_seven_box.lo_le
    have hx0 : 0 ≤ ((((121619384315957 / 62500000000000 : ℚ) : ℝ) - 1) /
        (((121619384315957 / 62500000000000 : ℚ) : ℝ) + 1)) := by norm_num
    have hx1 : ((((121619384315957 / 62500000000000 : ℚ) : ℝ) - 1) /
        (((121619384315957 / 62500000000000 : ℚ) : ℝ) + 1)) < 1 := by norm_num
    have h := Real.sum_range_le_log_div
      (x := ((((121619384315957 / 62500000000000 : ℚ) : ℝ) - 1) /
        (((121619384315957 / 62500000000000 : ℚ) : ℝ) + 1))) hx0 hx1 30
    norm_num at h
    linarith [hlog]
  · have hlog : Real.log (Real.log 7) ≤ Real.log ((389182029811063 / 200000000000000 : ℚ) : ℝ) :=
      Real.log_le_log (x := Real.log 7) (by positivity) log_seven_box.le_hi
    have hx0 : 0 ≤ ((((389182029811063 / 200000000000000 : ℚ) : ℝ) - 1) /
        (((389182029811063 / 200000000000000 : ℚ) : ℝ) + 1)) := by norm_num
    have hx1 : |((((389182029811063 / 200000000000000 : ℚ) : ℝ) - 1) /
        (((389182029811063 / 200000000000000 : ℚ) : ℝ) + 1))| < 1 := by norm_num
    have h := Real.sum_range_sub_log_div_le
      (x := ((((389182029811063 / 200000000000000 : ℚ) : ℝ) - 1) /
        (((389182029811063 / 200000000000000 : ℚ) : ℝ) + 1))) hx1 30
    rw [abs_le] at h
    norm_num at h
    linarith [hlog, h.2]
theorem loglog_div_two_box :
    RBox (Real.log (Real.log 7 / 2)) (-13708684990837 / 500000000000000)
      (-856792811927 / 31250000000000) := by
  have hdiv : Real.log (Real.log 7 / 2) = Real.log (Real.log 7) - Real.log 2 :=
    Real.log_div (ne_of_gt (Real.log_pos (by norm_num))) (by norm_num)
  rw [hdiv]
  refine (RBox.sub loglog7_box log_two_box).weaken ?_ ?_
  · norm_num
  · norm_num
lemma arithCoeff_two : RHLean.arithCoeff 2 = Real.log 2 / Real.sqrt 2 := by
  unfold RHLean.arithCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)]
  norm_num
lemma arithCoeff_three : RHLean.arithCoeff 3 = Real.log 3 / Real.sqrt 3 := by
  unfold RHLean.arithCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 3)]
  norm_num
lemma arithCoeff_four : RHLean.arithCoeff 4 = Real.log 2 / 2 := by
  unfold RHLean.arithCoeff
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num : (2 : ℕ) ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)]
  norm_num
lemma arithCoeff_five : RHLean.arithCoeff 5 = Real.log 5 / Real.sqrt 5 := by
  unfold RHLean.arithCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 5)]
  norm_num
theorem c2_box : RBox (RHLean.arithCoeff 2) (490129071734271 / 10 ^ 15)
    (122532267933569 / 250000000000000) := by
  rw [arithCoeff_two]
  refine (RBox.div log_two_box sqrt_two_box (by norm_num) (by norm_num) (by norm_num)).weaken ?_ ?_
  · norm_num
  · norm_num
theorem c3_box : RBox (RHLean.arithCoeff 3) (634284100597561 / 10 ^ 15)
    (317142050298783 / 500000000000000) := by
  rw [arithCoeff_three]
  refine (RBox.div log_three_box sqrt_three_box (by norm_num) (by norm_num) (by norm_num)).weaken ?_ ?_
  · norm_num
  · norm_num
theorem c4_box : RBox (RHLean.arithCoeff 4) (346573590279971 / 10 ^ 15)
    (13862943611199 / 40000000000000) := by
  rw [arithCoeff_four]
  refine (RBox.div log_two_box
    (show RBox (2 : ℝ) 2 2 from ⟨by norm_num, by norm_num⟩)
    (by norm_num) (by norm_num) (by norm_num)).weaken ?_ ?_
  · norm_num
  · norm_num
theorem c5_box : RBox (RHLean.arithCoeff 5) (359881257776799 / 500000000000000)
    (719762515553603 / 10 ^ 15) := by
  rw [arithCoeff_five]
  refine (RBox.div log_five_box sqrt_five_box (by norm_num) (by norm_num) (by norm_num)).weaken ?_ ?_
  · norm_num
  · norm_num
lemma sinh_half_log_seven : Real.sinh (Real.log 7 / 2) = 3 / Real.sqrt 7 := by
  have h7 : Real.exp (Real.log 7) = 7 := Real.exp_log (by norm_num)
  have hsq : Real.exp (Real.log 7 / 2) ^ 2 = 7 := by
    rw [pow_two, ← Real.exp_add, add_halves, h7]
  have hpos : 0 ≤ Real.exp (Real.log 7 / 2) := Real.exp_nonneg _
  have hsqrt : Real.exp (Real.log 7 / 2) = Real.sqrt 7 := by
    have h2 : Real.exp (Real.log 7 / 2) ^ 2 = (Real.sqrt 7) ^ 2 := by
      rw [hsq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
    nlinarith [hpos, Real.sqrt_nonneg 7]
  have hneg : Real.exp (-(Real.log 7 / 2)) = 1 / Real.sqrt 7 := by
    rw [Real.exp_neg, hsqrt, one_div]
  rw [Real.sinh_eq, hsqrt, hneg]
  have hne : Real.sqrt 7 ≠ 0 := by positivity
  have h7' : Real.sqrt 7 * Real.sqrt 7 = 7 := by
    rw [← pow_two]
    exact Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h7']
theorem sinh_box : RBox (Real.sinh (Real.log 7 / 2)) (7086833868923 / 6250000000000)
    (1133893419027683 / 10 ^ 15) := by
  rw [sinh_half_log_seven]
  refine (RBox.div (show RBox (3 : ℝ) 3 3 from ⟨by norm_num, by norm_num⟩) sqrt_seven_box
    (by norm_num) (by norm_num) (by norm_num)).weaken ?_ ?_
  · norm_num
  · norm_num
theorem tailBoxes : TailBoxes where
  log2pi := log_two_pi_box
  gamma := gamma_box
  loglog := loglog_div_two_box
  log7 := log_seven_box
  c2 := c2_box
  c3 := c3_box
  c4 := c4_box
  c5 := c5_box
  sinh := sinh_box
theorem tailFloor_100_gt' (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) :
    tailFloor ε 100 > (496227206741 / 10 ^ 12 : ℝ) :=
  tailFloor_100_gt ε hε tailBoxes
theorem tailFloor_150_gt' (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) :
    tailFloor ε 150 > (899207273677 / 10 ^ 12 : ℝ) :=
  tailFloor_150_gt ε hε tailBoxes
end Y7Chain
namespace Y7Schur
open Matrix
theorem schur_complement_posSemidef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (hD : D.PosDef) [Invertible D]
    (hS : (A - B * D⁻¹ * Bᴴ).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ D).PosSemidef :=
  (Matrix.PosDef.fromBlocks₂₂ A B hD).mpr hS
end Y7Schur
namespace Y7Chain
open Y7Matrix
lemma harmonicR_mono {j k : ℕ} (h : j ≤ k) : harmonicR j ≤ harmonicR k := by
  have hsub : Finset.range j ⊆ Finset.range k := Finset.range_subset_range.2 h
  have hq : harmonic j ≤ harmonic k := by
    unfold harmonic
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro x _ _
      positivity)
  unfold harmonicR
  exact_mod_cast hq
lemma tailFloor_mono (ε : ℝ) {j k : ℕ} (h : j ≤ k) : tailFloor ε j ≤ tailFloor ε k := by
  unfold tailFloor
  have hh : harmonicR (2 * j + 1) ≤ harmonicR (2 * k + 1) :=
    harmonicR_mono (by omega)
  linarith
theorem tailFloor_ge_100_gt (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) {j : ℕ} (hj : 100 ≤ j) :
    tailFloor ε j > (496227206741 / 10 ^ 12 : ℝ) :=
  lt_of_lt_of_le (tailFloor_100_gt' ε hε) (tailFloor_mono ε hj)
theorem tailFloor_ge_150_gt (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) {j : ℕ} (hj : 150 ≤ j) :
    tailFloor ε j > (899207273677 / 10 ^ 12 : ℝ) :=
  lt_of_lt_of_le (tailFloor_150_gt' ε hε) (tailFloor_mono ε hj)
end Y7Chain
namespace Y7Schur
open Matrix
theorem posSemidef_of_weighted_diagonal {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (d : n → ℝ) (hd : ∀ j, 0 < d j)
    (hS : (A - B * (Matrix.diagonal d)⁻¹ * Bᴴ).PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ (Matrix.diagonal d)).PosSemidef := by
  have hD : (Matrix.diagonal d).PosDef := Matrix.PosDef.diagonal hd
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => ne_of_gt (hd j))
  haveI : Invertible (Matrix.diagonal d).det := invertibleOfNonzero hdet
  haveI : Invertible (Matrix.diagonal d) :=
    Matrix.invertibleOfDetInvertible (Matrix.diagonal d)
  exact (Matrix.PosDef.fromBlocks₂₂ A B hD).mpr hS
end Y7Schur
namespace Y7Chain
open Y7Matrix
theorem tailFloor_inv_le (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) {j : ℕ}
    (hj : 150 ≤ j) :
    (tailFloor ε j)⁻¹ ≤ (10 ^ 12 / 899207273677 : ℝ) := by
  have h := tailFloor_ge_150_gt ε hε hj
  have hb : (0 : ℝ) < 899207273677 / 10 ^ 12 := by norm_num
  have := inv_anti₀ hb (le_of_lt h)
  simpa using this
theorem tailFloor_inv_le_100 (ε : ℝ) (hε : ε ≤ 1 / 10 ^ 15) {j : ℕ}
    (hj : 100 ≤ j) :
    (tailFloor ε j)⁻¹ ≤ (10 ^ 12 / 496227206741 : ℝ) := by
  have h := tailFloor_ge_100_gt ε hε hj
  have hb : (0 : ℝ) < 496227206741 / 10 ^ 12 := by norm_num
  have := inv_anti₀ hb (le_of_lt h)
  simpa using this
end Y7Chain
end
end Inline_Y7_Matrix
section Inline_GateII_Localized
noncomputable section
open Set
namespace RHLean.GateII.Localized
open RHLean
noncomputable def LocalPSDLocalized (a : ℝ) : Prop :=
  0 < a → ∀ f : ℝ → ℂ, f ∈ localizedCore a → 0 ≤ localizedForm a f
def Bridge (a : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, f ∈ localizedCore a → weilOdd f = localizedForm a f
theorem LocalPSDLocalized_mono_of_form_eq {a b : ℝ} (hab : a ≤ b)
    (hform : ∀ f : ℝ → ℂ, f ∈ localizedCore a → localizedForm b f = localizedForm a f)
    (hb : LocalPSDLocalized b) : LocalPSDLocalized a := by
  intro ha f hf
  rw [← hform f hf]
  exact hb (lt_of_lt_of_le ha hab) f
    ⟨hf.1, fun x hx => ⟨by linarith [(hf.2 hx).1, hab],
      by linarith [(hf.2 hx).2, hab]⟩⟩
theorem LocalPSD_iff_localized (_hbridge : ∀ a, Bridge a) (a : ℝ) :
    LocalPSD a ↔ LocalPSDLocalized a :=
  Iff.rfl
def GateIISpectralStep : Prop :=
  ∀ k : ℕ, 7 ≤ k → LocalPSD (endpoint k) → LocalPSD (endpoint (k + 1))
def GateIILocalizedStep : Prop :=
  ∀ k : ℕ, 7 ≤ k →
    LocalPSDLocalized (endpoint k) → LocalPSDLocalized (endpoint (k + 1))
theorem spectral_step_of_localized_step
    (hbridge : ∀ a, Bridge a)
    (hstep : ∀ k : ℕ, 7 ≤ k →
      LocalPSDLocalized (endpoint k) → LocalPSDLocalized (endpoint (k + 1))) :
    GateIISpectralStep := by
  intro k hk hkPSD
  have hkLoc : LocalPSDLocalized (endpoint k) :=
    (LocalPSD_iff_localized hbridge (endpoint k)).1 hkPSD
  have hnextLoc : LocalPSDLocalized (endpoint (k + 1)) := hstep k hk hkLoc
  exact (LocalPSD_iff_localized hbridge (endpoint (k + 1))).2 hnextLoc
theorem localized_step_of_spectral_step
    (hbridge : ∀ a, Bridge a)
    (hstep : ∀ k : ℕ, 7 ≤ k →
      LocalPSD (endpoint k) → LocalPSD (endpoint (k + 1))) :
    GateIILocalizedStep := by
  intro k hk hkLoc
  have hkPSD : LocalPSD (endpoint k) :=
    (LocalPSD_iff_localized hbridge (endpoint k)).2 hkLoc
  have hnextPSD : LocalPSD (endpoint (k + 1)) := hstep k hk hkPSD
  exact (LocalPSD_iff_localized hbridge (endpoint (k + 1))).1 hnextPSD
theorem GateIILocalizedStep_iff_spectral (hbridge : ∀ a, Bridge a) :
    GateIILocalizedStep ↔ GateIISpectralStep := by
  constructor
  · intro hstep
    exact spectral_step_of_localized_step hbridge hstep
  · intro hstep
    exact localized_step_of_spectral_step hbridge hstep
end RHLean.GateII.Localized
end
end Inline_GateII_Localized
section Inline_GateII_Collar
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RHLean.GateII.Localized
open RHLean
theorem localizedForm_sub_eq_collar_unfolded (a b : ℝ) (f : ℝ → ℂ) :
    (archForm b f + physicalConstant * (∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
        + potentialForm b f - gammaForm b f - polarForm b f - shiftForm b f)
      - (archForm a f + physicalConstant * (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume)
        + potentialForm a f - gammaForm a f - polarForm a f - shiftForm a f)
      = (archForm b f - archForm a f)
        + physicalConstant * ((∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
            - (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume))
        + (potentialForm b f - potentialForm a f)
        - (gammaForm b f - gammaForm a f)
        - (polarForm b f - polarForm a f)
        - (shiftForm b f - shiftForm a f) := by
  ring
theorem localizedForm_sub_eq_collar (a b : ℝ) (f : ℝ → ℂ) :
    localizedForm b f - localizedForm a f
      = (archForm b f - archForm a f)
        + physicalConstant * ((∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
            - (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume))
        + (potentialForm b f - potentialForm a f)
        - (gammaForm b f - gammaForm a f)
        - (polarForm b f - polarForm a f)
        - (shiftForm b f - shiftForm a f) := by
  have h := localizedForm_sub_eq_collar_unfolded a b f
  unfold localizedForm
  exact h
def CollarCancellation (a b : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, f ∈ localizedCore a →
    archForm b f - archForm a f = -(potentialForm b f - potentialForm a f)
theorem localizedCore_eq_zero_of_notMem {a : ℝ} {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) {x : ℝ} (hx : x ∉ Set.Ioo (-a) a) : f x = 0 := by
  by_contra h
  exact hx (hf.2 (Function.mem_support.mpr h))
theorem Ioo_subset_Ioo_of_le {a b : ℝ} (hab : a ≤ b) :
    Set.Ioo (-a) a ⊆ Set.Ioo (-b) b :=
  fun _ hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
theorem collar_norm_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) :
    (∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
      = (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume) := by
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioo (Ioo_subset_Ioo_of_le hab)
  intro x hx
  simp [localizedCore_eq_zero_of_notMem hf (fun h => hx.2 h)]
theorem collar_gamma_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) : gammaForm b f = gammaForm a f := by
  have hts := Ioo_subset_Ioo_of_le hab
  have hinner : ∀ x : ℝ,
      (∫ y in Set.Ioo (-b) b,
          gammaKernel ‖x - y‖ * (f x * star (f y)).re ∂volume)
        = ∫ y in Set.Ioo (-a) a,
            gammaKernel ‖x - y‖ * (f x * star (f y)).re ∂volume := by
    intro x
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioo hts
    intro y hy
    simp [localizedCore_eq_zero_of_notMem hf (fun h => hy.2 h)]
  unfold gammaForm
  rw [MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioo hts (fun x hx => by
      have hx0 : f x = 0 := localizedCore_eq_zero_of_notMem hf (fun h => hx.2 h)
      simp [hx0])]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun x _ => hinner x)
theorem collar_polar_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) : polarForm b f = polarForm a f := by
  have h : polarInner b f = polarInner a f := by
    unfold polarInner
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioo (Ioo_subset_Ioo_of_le hab)
    intro x hx
    simp [localizedCore_eq_zero_of_notMem hf (fun h => hx.2 h)]
  unfold polarForm
  rw [h]
theorem collar_shift_eq {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℂ}
    (hf : f ∈ localizedCore a) : shiftForm b f = shiftForm a f := by
  have hts := Ioo_subset_Ioo_of_le hab
  have hsubset : arithSupport a ⊆ arithSupport b := by
    intro n hn
    rw [arithSupport, Finset.mem_Icc] at hn ⊢
    obtain ⟨h2, hle⟩ := hn
    have hexp : Real.exp (2 * a) ≤ Real.exp (2 * b) :=
      Real.exp_le_exp.mpr (by linarith)
    have hceil : Nat.ceil (Real.exp (2 * a)) ≤ Nat.ceil (Real.exp (2 * b)) :=
      Nat.ceil_mono hexp
    omega
  unfold shiftForm
  rw [Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro n hn
    congr 1
    have hint : (∫ x in Set.Ioo (-b) b,
        f x * star (f (x + shiftLength n)) ∂volume)
        = ∫ x in Set.Ioo (-a) a, f x * star (f (x + shiftLength n)) ∂volume := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        measurableSet_Ioo hts
      intro x hx
      simp [localizedCore_eq_zero_of_notMem hf (fun h => hx.2 h)]
    rw [hint]
  · intro n hnb hna
    have h2 : 2 ≤ n := (Finset.mem_Icc.mp (by simpa [arithSupport] using hnb)).1
    have hlog : 2 * a ≤ Real.log n := by
      have hna' : Nat.ceil (Real.exp (2 * a)) ≤ n := by
        rw [arithSupport, Finset.mem_Icc] at hna
        omega
      have hexp : Real.exp (2 * a) ≤ (n : ℝ) :=
        (Nat.le_ceil (Real.exp (2 * a))).trans (by exact_mod_cast hna')
      calc 2 * a = Real.log (Real.exp (2 * a)) := (Real.log_exp (2 * a)).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos _) hexp
    have hzero : ∀ x : ℝ, f x * star (f (x + shiftLength n)) = 0 := by
      intro x
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hxmem : x ∈ Function.support f := Function.mem_support.mpr hfx
        have hxlt : x < a := (hf.2 hxmem).2
        have hxgt : -a < x := (hf.2 hxmem).1
        have hfar : a < x + shiftLength n := by
          unfold shiftLength
          linarith
        have hfz : f (x + shiftLength n) = 0 :=
          localizedCore_eq_zero_of_notMem hf (fun h => absurd h.2 (not_lt.mpr hfar.le))
        simp [hfz]
    have hz : ∀ s : Set ℝ,
        (∫ x in s, f x * star (f (x + shiftLength n)) ∂volume) = 0 := by
      intro s
      rw [show (fun x : ℝ => f x * star (f (x + shiftLength n))) = fun _ => 0 from
        funext hzero]
      simp
    rw [hz (Set.Ioo (-a) a)]
    simp
theorem localizedForm_eq_of_collar {a b : ℝ} (hcol : CollarCancellation a b)
    (hnorm : ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      (∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
        = (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume))
    (hgamma : ∀ f : ℝ → ℂ, f ∈ localizedCore a → gammaForm b f = gammaForm a f)
    (hpolar : ∀ f : ℝ → ℂ, f ∈ localizedCore a → polarForm b f = polarForm a f)
    (hshift : ∀ f : ℝ → ℂ, f ∈ localizedCore a → shiftForm b f = shiftForm a f) :
    ∀ f : ℝ → ℂ, f ∈ localizedCore a → localizedForm b f = localizedForm a f := by
  intro f hf
  have h := localizedForm_sub_eq_collar a b f
  have h1 := hcol f hf
  have h2 := hnorm f hf
  have h3 := hgamma f hf
  have h4 := hpolar f hf
  have h5 := hshift f hf
  rw [h1, h2, h3, h4, h5] at h
  linarith [h]
theorem LocalPSDLocalized_mono_of_collar {a b : ℝ} (hab : a ≤ b)
    (hcol : CollarCancellation a b)
    (hnorm : ∀ f : ℝ → ℂ, f ∈ localizedCore a →
      (∫ x in Set.Ioo (-b) b, ‖f x‖ ^ 2 ∂volume)
        = (∫ x in Set.Ioo (-a) a, ‖f x‖ ^ 2 ∂volume))
    (hgamma : ∀ f : ℝ → ℂ, f ∈ localizedCore a → gammaForm b f = gammaForm a f)
    (hpolar : ∀ f : ℝ → ℂ, f ∈ localizedCore a → polarForm b f = polarForm a f)
    (hshift : ∀ f : ℝ → ℂ, f ∈ localizedCore a → shiftForm b f = shiftForm a f)
    (hb : LocalPSDLocalized b) : LocalPSDLocalized a := by
  intro ha f hf
  have heq := localizedForm_eq_of_collar hcol hnorm hgamma hpolar hshift f hf
  have hb' : (0 : ℝ) ≤ localizedForm b f :=
    hb (lt_of_lt_of_le ha hab) f ⟨hf.1, fun x hx => ⟨by linarith [(hf.2 hx).1, hab],
      by linarith [(hf.2 hx).2, hab]⟩⟩
  rwa [heq] at hb'
theorem collarCancellation_of_bridge (hbridge : WeilBridge) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : CollarCancellation a b := by
  intro f hf
  have hsum := RHLean.localizedForm_compression_of_bridge hbridge ha hab hf
  have h1 := collar_norm_eq hab hf
  have h2 := collar_gamma_eq hab hf
  have h3 := collar_polar_eq hab hf
  have h4 := collar_shift_eq hab hf
  unfold localizedForm at hsum
  rw [h1, h2, h3, h4] at hsum
  linarith [hsum]
theorem localizedForm_eq_of_bridge (hbridge : WeilBridge) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∀ f : ℝ → ℂ, f ∈ localizedCore a → localizedForm b f = localizedForm a f :=
  fun f hf => RHLean.localizedForm_compression_of_bridge hbridge ha hab hf
theorem LocalPSDLocalized_mono_of_bridge (hbridge : WeilBridge) {a b : ℝ}
    (hab : a ≤ b) (hb : LocalPSDLocalized b) : LocalPSDLocalized a := by
  by_cases ha : 0 < a
  · exact LocalPSDLocalized_mono_of_form_eq hab
      (localizedForm_eq_of_bridge hbridge ha hab) hb
  · intro h
    exact absurd h ha
end RHLean.GateII.Localized
namespace RHLean.GateII.Collar
open Set Filter
def collarSet (a b : ℝ) : Set ℝ := Set.Ioo (-b) b \ Set.Ioo (-a) a
theorem endpoint_strict_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    RHLean.endpoint m < RHLean.endpoint n := by
  unfold RHLean.endpoint
  apply div_lt_div_of_pos_right
  · apply Real.log_lt_log
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
    · exact_mod_cast hmn
  · norm_num
lemma exp_sub_one_le_mul_exp {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u - 1 ≤ u * Real.exp u := by
  have h := Real.one_sub_le_exp_neg u
  have h1 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos u).le
  rw [sub_mul, one_mul] at hmul
  rw [h1] at hmul
  linarith
lemma sinh_le_mul_exp {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.exp z := by
  have h : 1 - Real.exp (-(2 * z)) ≤ 2 * z := by
    have := Real.one_sub_le_exp_neg (2 * z)
    linarith
  have he : Real.exp z * (1 - Real.exp (-(2 * z))) = Real.exp z - Real.exp (-z) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sinh_eq, ← he]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [Real.exp_pos z]
lemma sinh_sub_id_le {z : ℝ} (hz : 0 ≤ z) :
    Real.sinh z - z ≤ z ^ 2 / 2 * Real.sinh z := by
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · norm_num [Real.sinh_zero]
  · obtain ⟨ξ, hξ, hEq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sinh) (x := z) (x₀ := 0) (n := 1) (by linarith) (by fun_prop)
    have htz : taylorWithinEval Real.sinh 1 (uIcc (0 : ℝ) z) 0 z = z := by
      simp only [taylorWithinEval_succ, taylor_within_zero_eval, zero_add]
      rw [iteratedDerivWithin_one]
      have hd : derivWithin Real.sinh (Set.Icc 0 z) 0 = 1 := by
        have hnhds : Set.Iic z ∈ nhds (0 : ℝ) := Iic_mem_nhds hzpos
        have h := derivWithin_inter (f := Real.sinh) (s := Set.Ici 0) (t := Set.Iic z)
          (x := 0) hnhds
        rw [Set.Ici_inter_Iic] at h
        rw [h]
        have h2 := ((Real.hasDerivAt_sinh 0).hasDerivWithinAt (s := Set.Ici 0)).derivWithin
          (uniqueDiffWithinAt_Ici 0)
        rw [h2]
        norm_num [Real.cosh_zero]
      rw [uIcc_of_le hzpos.le, hd]
      norm_num [Real.sinh_zero]
    rw [htz] at hEq
    have hderiv : iteratedDeriv 2 Real.sinh ξ = Real.sinh ξ := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
      change deriv (deriv (fun x : ℝ => Real.sinh x)) ξ = Real.sinh ξ
      rw [Real.deriv_sinh]
      change deriv (fun x : ℝ => Real.cosh x) ξ = Real.sinh ξ
      rw [Real.deriv_cosh]
    rw [hderiv] at hEq
    have hξle : ξ ≤ z := by
      rw [uIoo, min_eq_left hzpos.le, max_eq_right hzpos.le] at hξ
      exact hξ.2.le
    have hsinh_le : Real.sinh ξ ≤ Real.sinh z := Real.sinh_le_sinh.mpr hξle
    have h2 : Real.sinh z - z = Real.sinh ξ * z ^ 2 / 2 := by
      rw [hEq]
      norm_num
    rw [h2]
    have hz2 : 0 ≤ z ^ 2 / 2 := by positivity
    calc Real.sinh ξ * z ^ 2 / 2 = (z ^ 2 / 2) * Real.sinh ξ := by ring
      _ ≤ (z ^ 2 / 2) * Real.sinh z :=
          mul_le_mul_of_nonneg_left hsinh_le hz2
      _ = z ^ 2 / 2 * Real.sinh z := rfl
theorem measurable_gammaKernel : Measurable RHLean.gammaKernel := by
  unfold RHLean.gammaKernel
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  have h1 : Measurable (fun z : ℝ => Real.exp (z / 2) / (2 * Real.sinh z)) :=
    (Real.measurable_exp.comp (measurable_id.div_const 2)).div
      ((measurable_const : Measurable fun _ : ℝ => (2 : ℝ)).mul
        (Real.measurable_sinh.comp measurable_id))
  have h2 : Measurable (fun z : ℝ => (1 : ℝ) / (2 * z)) :=
    (measurable_const : Measurable fun _ : ℝ => (1 : ℝ)).div
      ((measurable_const : Measurable fun _ : ℝ => (2 : ℝ)).mul measurable_id)
  convert h1.sub h2 using 1
theorem gammaKernel_abs_le {M z : ℝ} (hM : 0 ≤ M) (hz : z ∈ Set.Icc 0 M) :
    |RHLean.gammaKernel z| ≤ Real.exp M / 2 + Real.exp (M / 2) / 4 := by
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · subst hz0
    unfold RHLean.gammaKernel
    rw [if_pos rfl, abs_of_nonneg (by norm_num)]
    have h1 : (1 : ℝ) ≤ Real.exp M := Real.one_le_exp hM
    have h2 : (0 : ℝ) ≤ Real.exp (M / 2) := (Real.exp_pos _).le
    linarith
  · have hsinh_pos : 0 < Real.sinh z := Real.sinh_pos_iff.mpr hzpos
    have hden : 0 < 2 * z * Real.sinh z := by positivity
    have hsinh_ge : z ≤ Real.sinh z := Real.self_le_sinh_iff.mpr hzpos.le
    have hrew : RHLean.gammaKernel z
        = (z * Real.exp (z / 2) - Real.sinh z) / (2 * z * Real.sinh z) := by
      unfold RHLean.gammaKernel
      rw [if_neg (ne_of_gt hzpos)]
      field_simp
    rw [hrew, abs_div, abs_of_pos hden]
    have hupper : z * Real.exp (z / 2) - Real.sinh z
        ≤ (z ^ 2 / 2) * Real.exp (z / 2) := by
      have h2 : Real.exp (z / 2) - 1 ≤ (z / 2) * Real.exp (z / 2) :=
        exp_sub_one_le_mul_exp (by linarith)
      have h3 : z * (Real.exp (z / 2) - 1) ≤ z * ((z / 2) * Real.exp (z / 2)) :=
        mul_le_mul_of_nonneg_left h2 hzpos.le
      have h4 : z * Real.exp (z / 2) - z = z * (Real.exp (z / 2) - 1) := by ring
      linarith [h3, h4, hsinh_ge]
    have hlower : -(z * Real.exp (z / 2) - Real.sinh z)
        ≤ (z ^ 2 / 2) * Real.sinh z := by
      have hD := sinh_sub_id_le hzpos.le
      have h1 : z * Real.exp (z / 2) ≥ z := by
        have := Real.one_le_exp (show (0 : ℝ) ≤ z / 2 by linarith)
        nlinarith [Real.exp_pos (z / 2)]
      linarith
    have hB1 : 0 ≤ (z ^ 2 / 2) * Real.exp (z / 2) := by positivity
    have hB2 : 0 ≤ (z ^ 2 / 2) * Real.sinh z := by positivity
    have habs : |z * Real.exp (z / 2) - Real.sinh z|
        ≤ (z ^ 2 / 2) * Real.exp (z / 2) + (z ^ 2 / 2) * Real.sinh z := by
      rw [abs_le]
      constructor
      · linarith [hupper, hB2]
      · linarith [hlower, hB1]
    refine (div_le_iff₀ hden).2 ?_
    have hexp_le : Real.exp (z / 2) ≤ Real.exp (M / 2) :=
      Real.exp_le_exp.mpr (by linarith [hz.2])
    have hzM : z ≤ M := hz.2
    have hM2 : z / 4 ≤ Real.exp M / 2 := by
      have h1 : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
      have h2 : z / 4 ≤ M / 4 := by linarith
      linarith
    calc |z * Real.exp (z / 2) - Real.sinh z|
        ≤ (z ^ 2 / 2) * Real.exp (z / 2) + (z ^ 2 / 2) * Real.sinh z := habs
      _ = ((z ^ 2 / 2) * Real.exp (z / 2) / (2 * z * Real.sinh z)) * (2 * z * Real.sinh z)
            + (z / 4) * (2 * z * Real.sinh z) := by
          field_simp
          ring
      _ ≤ (Real.exp (M / 2) / 4) * (2 * z * Real.sinh z)
            + (Real.exp M / 2) * (2 * z * Real.sinh z) := by
          have h1 : (z ^ 2 / 2) * Real.exp (z / 2) / (2 * z * Real.sinh z)
              ≤ Real.exp (M / 2) / 4 := by
            rw [div_le_iff₀ hden]
            have hz2 : z ^ 2 ≤ z * Real.sinh z := by nlinarith [hsinh_ge, hzpos.le]
            calc (z ^ 2 / 2) * Real.exp (z / 2) ≤ (Real.exp (M / 2) / 2) * z ^ 2 := by
                  nlinarith [hexp_le, hzpos.le]
              _ ≤ (Real.exp (M / 2) / 2) * (z * Real.sinh z) := by
                  exact mul_le_mul_of_nonneg_left hz2 (by positivity)
              _ = Real.exp (M / 2) / 4 * (2 * z * Real.sinh z) := by ring
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hden.le)
            (mul_le_mul_of_nonneg_right hM2 hden.le)
      _ = (Real.exp M / 2 + Real.exp (M / 2) / 4) * (2 * z * Real.sinh z) := by ring
end RHLean.GateII.Collar
end
end Inline_GateII_Collar
section Inline_Y7_Operator
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Y7Op
open Y7Matrix
def legSum (x : ℕ → ℝ) (s : Finset ℕ) : ℝ → ℂ :=
  fun y => ∑ n ∈ s, (x n : ℂ) * phiC n y
@[simp]
lemma legSum_apply (x : ℕ → ℝ) (s : Finset ℕ) (y : ℝ) :
    legSum x s y = ∑ n ∈ s, (x n : ℂ) * phiC n y := rfl
theorem normSq_sum_eq (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ n ∈ s, c n‖ ^ 2 = ∑ m ∈ s, ∑ n ∈ s, (c m * star (c n)).re := by
  rw [Complex.sq_norm]
  have h : Complex.normSq (∑ n ∈ s, c n) =
      (star (∑ n ∈ s, c n) * (∑ n ∈ s, c n)).re := by
    have := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := ∑ n ∈ s, c n))
    simpa using this
  rw [h, star_sum, Finset.sum_mul_sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : star (c m) * c n = star (c m * star (c n)) := by
    rw [star_mul, star_star, mul_comm]
  rw [hc]
  simpa only [Complex.star_def] using Complex.conj_re (c m * star (c n))
theorem polarInner_legSum (a : ℝ) (s : Finset ℕ) (x : ℕ → ℝ) :
    RHLean.polarInnerRescaled a (legSum x s) =
      ∑ n ∈ s, (x n : ℂ) * polarMoment a n := by
  simp only [polarMoment, RHLean.polarInnerRescaled, legSum]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    ring
  · intro n hn
    have hc : Continuous (fun y : ℝ =>
        star (RHLean.sRescaled a y) * ((x n : ℂ) * phiC n y)) := by
      unfold RHLean.sRescaled phiC
      fun_prop
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mp hc.integrableOn_Icc
noncomputable def polarMatrix (a : ℝ) (m n : ℕ) : ℝ :=
  2 * a * ((polarMoment a m) * star (polarMoment a n)).re
theorem polarFormRescaled_legSum (a : ℝ) (s : Finset ℕ) (x : ℕ → ℝ) :
    RHLean.polarFormRescaled a (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * polarMatrix a m n := by
  unfold RHLean.polarFormRescaled polarMatrix
  rw [polarInner_legSum, normSq_sum_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc : (((x m : ℂ) * polarMoment a m) * star ((x n : ℂ) * polarMoment a n)).re
      = x m * x n * ((polarMoment a m) * star (polarMoment a n)).re := by
    have h1 : ((x m : ℂ) * polarMoment a m) * star ((x n : ℂ) * polarMoment a n)
        = (((x m * x n : ℝ)) : ℂ) * (polarMoment a m * star (polarMoment a n)) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hc]
  ring
theorem polarMatrix_self (a : ℝ) (n : ℕ) :
    polarMatrix a n n = RHLean.polarFormRescaled a (phiC n) := by
  rw [Y7Matrix.polarFormRescaled_phiC]
  unfold polarMatrix
  have h : ((polarMoment a n) * star (polarMoment a n)).re = ‖polarMoment a n‖ ^ 2 := by
    have hmul : (polarMoment a n) * star (polarMoment a n) = Complex.normSq (polarMoment a n) := by
      simpa only [Complex.star_def] using Complex.mul_conj (polarMoment a n)
    rw [hmul, Complex.sq_norm]
    simp
  rw [h]
lemma normSq_legSum (x : ℕ → ℝ) (s : Finset ℕ) (y : ℝ) :
    ‖legSum x s y‖ ^ 2 =
      ∑ m ∈ s, ∑ n ∈ s,
        x m * x n *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) := by
  have hcast : legSum x s y =
      ((∑ n ∈ s, x n * (Y7Legendre.phi n).eval y : ℝ) : ℂ) := by
    simp only [legSum, phiC, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hcast, Complex.sq_norm, Complex.normSq_ofReal]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring
lemma integral_phi_mul_phi (m n : ℕ) :
    (∫ y in Set.Ioo (-1 : ℝ) 1,
        (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) =
      if m = n then 1 else 0 := by
  apply Complex.ofReal_injective
  have hc : ((∫ y in Set.Ioo (-1 : ℝ) 1,
        (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y : ℝ) : ℂ) =
      Y7Matrix.innerC m n := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← intervalIntegral.integral_ofReal]
    unfold Y7Matrix.innerC
    apply intervalIntegral.integral_congr
    intro y _
    simp only [phiC]
    rw [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  rw [hc, Y7Matrix.innerC_eq_ite]
  split_ifs <;> simp
lemma integral_normSq_legSum (x : ℕ → ℝ) (s : Finset ℕ) :
    (∫ y in Set.Ioo (-1 : ℝ) 1, ‖legSum x s y‖ ^ 2) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n *
        (∫ y in Set.Ioo (-1 : ℝ) 1,
          (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) := by
  have hpt : (fun y => ‖legSum x s y‖ ^ 2) =
      fun y => ∑ m ∈ s, ∑ n ∈ s,
        x m * x n *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) := by
    funext y
    rw [normSq_legSum]
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [← MeasureTheory.integral_const_mul]
    · intro n hn
      have hcont : Continuous (fun y : ℝ =>
          x m * x n * ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) := by
        fun_prop
      exact (integrableOn_Icc_iff_integrableOn_Ioo).mp hcont.integrableOn_Icc
  · intro m hm
    apply integrable_finsetSum
    intro n hn
    have hcont : Continuous (fun y : ℝ =>
        x m * x n * ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) := by
      fun_prop
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mp hcont.integrableOn_Icc
noncomputable def gammaMatrix (a : ℝ) (m n : ℕ) : ℝ :=
  ∫ x : ℝ in Set.Ioo (-1) 1, ∫ y : ℝ in Set.Ioo (-1) 1,
    RHLean.gammaKernelRescaled a ‖x - y‖ *
      ((Y7Legendre.phi m).eval x * (Y7Legendre.phi n).eval y)
noncomputable def shiftOperatorMatrix (a : ℝ) (m n : ℕ) : ℝ :=
  ∑ k ∈ RHLean.arithSupport a, RHLean.arithCoeff k *
    shiftGram m n (RHLean.shiftLengthRescaled a k)
noncomputable def rescaledOperatorM (a : ℝ) (m n : ℕ) : ℝ :=
  (if m = n then harmonicR m else 0)
    + RHLean.c0 a * (if m = n then 1 else 0)
    + potentialMatrix m n
    - gammaMatrix a m n
    - polarMatrix a m n
    - shiftOperatorMatrix a m n
def ArchDiagonalRep : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.archFormRescaled (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * (if m = n then harmonicR m else 0)
def C0Rep (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.c0 a * (∫ y in Set.Ioo (-1) 1, ‖legSum x s y‖ ^ 2) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * (RHLean.c0 a * (if m = n then 1 else 0))
def PotentialRep : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.potentialFormRescaled (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * potentialMatrix m n
def GammaRep (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.gammaFormRescaled a (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * gammaMatrix a m n
def PolarRep (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.polarFormRescaled a (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * polarMatrix a m n
def ShiftRep (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.shiftFormRescaled a (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * shiftOperatorMatrix a m n
def FormMatrixRep (a : ℝ) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → ℝ),
    RHLean.localizedFormRescaled a (legSum x s) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n * rescaledOperatorM a m n
theorem polarRep (a : ℝ) : PolarRep a :=
  fun s x => polarFormRescaled_legSum a s x
theorem c0Rep (a : ℝ) : C0Rep a := by
  intro s x
  rw [integral_normSq_legSum]
  simp_rw [integral_phi_mul_phi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring
lemma intervalIntegrable_V_mul_phi_mul_phi (m n : ℕ) :
    IntervalIntegrable (fun y : ℝ => RHLean.rescaledPotential y *
      ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) volume (-1) 1 := by
  have hcont : Continuous (fun y : ℝ =>
      (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) :=
    (Y7Legendre.phi m).continuous.mul (Y7Legendre.phi n).continuous
  refine (Y7Matrix.intervalIntegrable_rescaledPotential_mul_pow 0).continuousOn_mul
    hcont.continuousOn |>.congr_uIoo ?_
  intro y _
  ring
theorem potentialRep : PotentialRep := by
  intro s x
  rw [RHLean.potentialFormRescaled]
  have hpt : (fun y => RHLean.rescaledPotential y * ‖legSum x s y‖ ^ 2) =
      fun y => ∑ m ∈ s, ∑ n ∈ s, x m * x n *
        (RHLean.rescaledPotential y *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) := by
    funext y
    rw [normSq_legSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hpt]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [show potentialMatrix m n = ∫ y in Set.Ioo (-1 : ℝ) 1,
          RHLean.rescaledPotential y *
            ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y) from rfl]
      rw [← MeasureTheory.integral_const_mul]
    · intro n hn
      have hV : IntervalIntegrable (fun y : ℝ => RHLean.rescaledPotential y *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) volume (-1) 1 :=
        intervalIntegrable_V_mul_phi_mul_phi m n
      have hIoo : IntegrableOn (fun y : ℝ => RHLean.rescaledPotential y *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) (Set.Ioo (-1) 1) :=
        (integrableOn_Ioc_iff_integrableOn_Ioo).mp
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hV)
      exact hIoo.const_mul (x m * x n)
  · intro m hm
    apply integrable_finsetSum
    intro n hn
    have hV : IntervalIntegrable (fun y : ℝ => RHLean.rescaledPotential y *
        ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) volume (-1) 1 :=
      intervalIntegrable_V_mul_phi_mul_phi m n
    have hIoo : IntegrableOn (fun y : ℝ => RHLean.rescaledPotential y *
        ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval y)) (Set.Ioo (-1) 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mp
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp hV)
    exact hIoo.const_mul (x m * x n)
lemma sum_comm_mul (A s : Finset ℕ) (c x : ℕ → ℝ) (I : ℕ → ℕ → ℕ → ℝ) :
    (∑ k ∈ A, c k * (∑ m ∈ s, ∑ n ∈ s, x m * x n * I k m n))
      = ∑ m ∈ s, ∑ n ∈ s, x m * x n * (∑ k ∈ A, c k * I k m n) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro k hk
  ring
lemma shiftLengthRescaled_lt_two {a : ℝ} {k : ℕ} (hk : k ∈ RHLean.arithSupport a) :
    RHLean.shiftLengthRescaled a k < 2 := by
  rw [RHLean.arithSupport, Finset.mem_Icc] at hk
  obtain ⟨hk2, hkU⟩ := hk
  have ha_pos : 0 < a := by
    by_contra h
    push_neg at h
    have hx1 : Real.exp (2 * a) ≤ 1 := by
      calc Real.exp (2 * a) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hc : Nat.ceil (Real.exp (2 * a)) ≤ 1 := Nat.ceil_le.mpr (by simpa using hx1)
    omega
  have hk_lt : (k : ℝ) < Real.exp (2 * a) := by
    have h1 : k + 1 ≤ Nat.ceil (Real.exp (2 * a)) := by omega
    have h2 : (Nat.ceil (Real.exp (2 * a)) : ℝ) < Real.exp (2 * a) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h3 : (k : ℝ) + 1 ≤ (Nat.ceil (Real.exp (2 * a)) : ℝ) := by exact_mod_cast h1
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog : Real.log k < 2 * a := by
    rw [← Real.log_exp (2 * a)]
    exact Real.log_lt_log hkpos hk_lt
  rw [RHLean.shiftLengthRescaled, div_lt_iff₀ ha_pos]
  linarith
lemma shiftLengthRescaled_pos {a : ℝ} {k : ℕ} (hk : k ∈ RHLean.arithSupport a) :
    0 < RHLean.shiftLengthRescaled a k := by
  rw [RHLean.arithSupport, Finset.mem_Icc] at hk
  obtain ⟨hk2, hkU⟩ := hk
  have ha_pos : 0 < a := by
    by_contra h
    push_neg at h
    have hx1 : Real.exp (2 * a) ≤ 1 := by
      calc Real.exp (2 * a) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    have hc : Nat.ceil (Real.exp (2 * a)) ≤ 1 := Nat.ceil_le.mpr (by simpa using hx1)
    omega
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hlog : 0 < Real.log k := Real.log_pos hk1
  rw [RHLean.shiftLengthRescaled]
  exact div_pos hlog ha_pos
private lemma shift_expansion_Ioo (s : Finset ℕ) (x : ℕ → ℝ)
    {a b r : ℝ} :
    (∫ y in Set.Ioo a b, legSum x s y * star (legSum x s (y + r))).re
      = ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          (∫ y in Set.Ioo a b,
            (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y + r)) := by
  have hpt : (fun y => legSum x s y *
        star (legSum x s (y + r))) =
      fun y => (((∑ m ∈ s, x m * (Y7Legendre.phi m).eval y) *
          (∑ n ∈ s, x n * (Y7Legendre.phi n).eval (y + r)) : ℝ) : ℂ) := by
    funext y
    have h1 : legSum x s y =
        ((∑ m ∈ s, x m * (Y7Legendre.phi m).eval y : ℝ) : ℂ) := by
      simp only [legSum, Y7Matrix.phiC, Complex.ofReal_sum, Complex.ofReal_mul]
    have h2 : star (legSum x s (y + r)) =
        ((∑ n ∈ s, x n * (Y7Legendre.phi n).eval (y + r) : ℝ) : ℂ) := by
      rw [show legSum x s (y + r) =
          ((∑ n ∈ s, x n * (Y7Legendre.phi n).eval (y + r) : ℝ) : ℂ) from by
        simp only [legSum, Y7Matrix.phiC, Complex.ofReal_sum, Complex.ofReal_mul]]
      simp only [Complex.star_def, Complex.conj_ofReal]
    rw [h1, h2]
    push_cast
    ring
  rw [hpt, integral_complex_ofReal, Complex.ofReal_re]
  have hpt2 : (fun y => (∑ m ∈ s, x m * (Y7Legendre.phi m).eval y) *
        (∑ n ∈ s, x n * (Y7Legendre.phi n).eval (y + r))) =
      fun y => ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y + r)) := by
    funext y
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hpt2]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [← MeasureTheory.integral_const_mul]
    · intro n hn
      have hcont : Continuous (fun y : ℝ => x m * x n *
          ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y + r))) := by
        fun_prop
      exact (integrableOn_Icc_iff_integrableOn_Ioo).mp
        hcont.integrableOn_Icc
  · intro m hm
    apply integrable_finsetSum
    intro n hn
    have hcont : Continuous (fun y : ℝ => x m * x n *
        ((Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y + r))) := by
      fun_prop
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mp
      hcont.integrableOn_Icc
theorem shiftRep (a : ℝ) (s : Finset ℕ) (x : ℕ → ℝ) :
    RHLean.shiftFormRescaled a (legSum x s)
      = ∑ m ∈ s, ∑ n ∈ s, x m * x n * shiftOperatorMatrix a m n := by
  have hplus : ∀ k ∈ RHLean.arithSupport a,
      (∫ y in Set.Ioo (-1 : ℝ) (1 - RHLean.shiftLengthRescaled a k),
          legSum x s y * star (legSum x s (y + RHLean.shiftLengthRescaled a k))).re
        = ∑ m ∈ s, ∑ n ∈ s, x m * x n *
            (∫ y in Set.Ioo (-1 : ℝ) (1 - RHLean.shiftLengthRescaled a k),
              (Y7Legendre.phi m).eval y *
                (Y7Legendre.phi n).eval (y + RHLean.shiftLengthRescaled a k)) := by
    intro k hk
    exact shift_expansion_Ioo s x
  have hminus : ∀ k ∈ RHLean.arithSupport a,
      (∫ y in Set.Ioo (-1 + RHLean.shiftLengthRescaled a k) 1,
          legSum x s y * star (legSum x s (y - RHLean.shiftLengthRescaled a k))).re
        = ∑ m ∈ s, ∑ n ∈ s, x m * x n *
            (∫ y in Set.Ioo (-1 + RHLean.shiftLengthRescaled a k) 1,
              (Y7Legendre.phi m).eval y *
                (Y7Legendre.phi n).eval (y - RHLean.shiftLengthRescaled a k)) := by
    intro k hk
    have h := shift_expansion_Ioo s x (a := -1 + RHLean.shiftLengthRescaled a k) (b := 1)
      (r := -RHLean.shiftLengthRescaled a k)
    simpa only [sub_eq_add_neg] using h
  have hgram : ∀ k ∈ RHLean.arithSupport a, ∀ m n : ℕ,
      (∫ y in Set.Ioo (-1 : ℝ) (1 - RHLean.shiftLengthRescaled a k),
          (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y + RHLean.shiftLengthRescaled a k))
        + (∫ y in Set.Ioo (-1 + RHLean.shiftLengthRescaled a k) 1,
          (Y7Legendre.phi m).eval y * (Y7Legendre.phi n).eval (y - RHLean.shiftLengthRescaled a k))
        = shiftGram m n (RHLean.shiftLengthRescaled a k) := by
    intro k hk m n
    have hr := shiftLengthRescaled_lt_two hk
    have h1 : (-1 : ℝ) ≤ 1 - RHLean.shiftLengthRescaled a k := by linarith
    have h2 : (-1 + RHLean.shiftLengthRescaled a k) ≤ 1 := by linarith
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h1,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h2]
    rw [shiftOverlap_phi m n, shiftOverlapNeg_phi m n]
    unfold shiftGram
    ring
  have hterm : ∀ k ∈ RHLean.arithSupport a,
      ((∫ y in Set.Ioo (-1 : ℝ) (1 - RHLean.shiftLengthRescaled a k),
          legSum x s y * star (legSum x s (y + RHLean.shiftLengthRescaled a k)))
        + (∫ y in Set.Ioo (-1 + RHLean.shiftLengthRescaled a k) 1,
          legSum x s y * star (legSum x s (y - RHLean.shiftLengthRescaled a k)))).re
        = ∑ m ∈ s, ∑ n ∈ s, x m * x n * shiftGram m n
            (RHLean.shiftLengthRescaled a k) := by
    intro k hk
    rw [Complex.add_re, hplus k hk, hminus k hk, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_add, hgram k hk m n]
  unfold RHLean.shiftFormRescaled shiftOperatorMatrix
  have hL : (∑ n ∈ RHLean.arithSupport a, RHLean.arithCoeff n *
      ((∫ y in Set.Ioo (-1 : ℝ) (1 - RHLean.shiftLengthRescaled a n),
          legSum x s y * star (legSum x s (y + RHLean.shiftLengthRescaled a n)))
        + (∫ y in Set.Ioo (-1 + RHLean.shiftLengthRescaled a n) 1,
          legSum x s y * star (legSum x s (y - RHLean.shiftLengthRescaled a n)))).re)
      = ∑ n ∈ RHLean.arithSupport a, RHLean.arithCoeff n *
          (∑ m ∈ s, ∑ m' ∈ s, x m * x m' * shiftGram m m'
            (RHLean.shiftLengthRescaled a n)) :=
    Finset.sum_congr rfl (fun n hn => by rw [hterm n hn])
  rw [hL]
  exact sum_comm_mul (RHLean.arithSupport a) s RHLean.arithCoeff x
    (fun k m n => shiftGram m n (RHLean.shiftLengthRescaled a k))
set_option maxHeartbeats 1000000 in
private lemma abs_gammaKernelRescaled_le {a M z : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M)
    (hz : z ∈ Set.Icc 0 M) :
    |RHLean.gammaKernelRescaled a z|
      ≤ a * (Real.exp (a * M) / 2 + Real.exp (a * M / 2) / 4) := by
  unfold RHLean.gammaKernelRescaled
  rw [abs_mul, abs_of_nonneg ha]
  refine mul_le_mul_of_nonneg_left ?_ ha
  exact RHLean.GateII.Collar.gammaKernel_abs_le (mul_nonneg ha hM)
    ⟨mul_nonneg ha hz.1, mul_le_mul_of_nonneg_left hz.2 ha⟩
private lemma measurable_gammaKernelRescaled_comp (a x : ℝ) :
    Measurable (fun y : ℝ => RHLean.gammaKernelRescaled a ‖x - y‖) := by
  unfold RHLean.gammaKernelRescaled
  exact measurable_const.mul
    (RHLean.GateII.Collar.measurable_gammaKernel.comp
      (measurable_const.mul ((continuous_const.sub continuous_id).norm.measurable)))
private lemma integrableOn_gammaKernel_phi {a : ℝ} (ha : 0 ≤ a) (m n : ℕ) {x' : ℝ}
    (hx' : x' ∈ Set.Ioo (-1 : ℝ) 1) :
    IntegrableOn (fun y : ℝ => RHLean.gammaKernelRescaled a ‖x' - y‖ *
      ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y))
      (Set.Ioo (-1 : ℝ) 1) := by
  obtain ⟨Cn, hCn⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (Y7Legendre.phi n).continuous.continuousOn
  set K := a * (Real.exp (a * 2) / 2 + Real.exp (a * 2 / 2) / 4) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg ha (by positivity)
  refine IntegrableOn.of_bound ?hfin ?hmeas (|(Y7Legendre.phi m).eval x'| * K * Cn) ?hbound
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  · have hcont : Continuous (fun y : ℝ =>
        (Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y) := by fun_prop
    exact ((measurable_gammaKernelRescaled_comp a x').mul hcont.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hx1 : |x'| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hy1 : |y| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hdist : ‖x' - y‖ ≤ 2 := by
      calc ‖x' - y‖ ≤ ‖x'‖ + ‖y‖ := norm_sub_le _ _
        _ = |x'| + |y| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 2 := by linarith
    have hkb := abs_gammaKernelRescaled_le ha (by norm_num : (0 : ℝ) ≤ 2)
      ⟨norm_nonneg _, hdist⟩
    have hyb : ‖(Y7Legendre.phi n).eval y‖ ≤ Cn :=
      hCn y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |RHLean.gammaKernelRescaled a ‖x' - y‖| *
          (|(Y7Legendre.phi m).eval x'| * |(Y7Legendre.phi n).eval y|)
        ≤ K * (|(Y7Legendre.phi m).eval x'| * Cn) :=
          mul_le_mul hkb
            (mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hyb)
              (abs_nonneg _))
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK0
      _ = |(Y7Legendre.phi m).eval x'| * K * Cn := by ring
private lemma integrableOn_gammaKernel_phi_integral {a : ℝ} (ha : 0 ≤ a) (m n : ℕ) :
    IntegrableOn (fun x' : ℝ => ∫ y in Set.Ioo (-1 : ℝ) 1,
      RHLean.gammaKernelRescaled a ‖x' - y‖ *
        ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y))
      (Set.Ioo (-1 : ℝ) 1) := by
  obtain ⟨Cm, hCm⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (Y7Legendre.phi m).continuous.continuousOn
  obtain ⟨Cn, hCn⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (Y7Legendre.phi n).continuous.continuousOn
  have Cm0 : 0 ≤ Cm := le_trans (norm_nonneg _) (hCm 0 ⟨by norm_num, by norm_num⟩)
  have Cn0 : 0 ≤ Cn := le_trans (norm_nonneg _) (hCn 0 ⟨by norm_num, by norm_num⟩)
  set K := a * (Real.exp (a * 2) / 2 + Real.exp (a * 2 / 2) / 4) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg ha (by positivity)
  refine IntegrableOn.of_bound ?hfin ?hmeas (K * Cm * Cn * 2) ?hbound
  · rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  · have hmeas : Measurable (fun p : ℝ × ℝ =>
        RHLean.gammaKernelRescaled a ‖p.1 - p.2‖ *
          ((Y7Legendre.phi m).eval p.1 * (Y7Legendre.phi n).eval p.2)) := by
      refine Measurable.mul ?_ ?_
      · unfold RHLean.gammaKernelRescaled
        exact measurable_const.mul
          (RHLean.GateII.Collar.measurable_gammaKernel.comp
            (measurable_const.mul ((continuous_fst.sub continuous_snd).norm.measurable)))
      · have hcont : Continuous (fun p : ℝ × ℝ =>
            (Y7Legendre.phi m).eval p.1 * (Y7Legendre.phi n).eval p.2) := by fun_prop
        exact hcont.measurable
    have hf : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        RHLean.gammaKernelRescaled a ‖p.1 - p.2‖ *
          ((Y7Legendre.phi m).eval p.1 * (Y7Legendre.phi n).eval p.2))
        (volume.prod (volume.restrict (Set.Ioo (-1 : ℝ) 1))) :=
      hmeas.aestronglyMeasurable
    simpa only using (hf.integral_prod_right').mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x' hx'
    have hx1 : |x'| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hCm_x : ‖(Y7Legendre.phi m).eval x'‖ ≤ Cm :=
      hCm x' ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩
    have hC : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        ‖RHLean.gammaKernelRescaled a ‖x' - y‖ *
          ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y)‖ ≤ K * Cm * Cn := by
      intro y hy
      have hy1 : |y| ≤ 1 := by
        rw [abs_le]
        exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have hdist : ‖x' - y‖ ≤ 2 := by
        calc ‖x' - y‖ ≤ ‖x'‖ + ‖y‖ := norm_sub_le _ _
          _ = |x'| + |y| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 2 := by linarith
      have hkb := abs_gammaKernelRescaled_le ha (by norm_num : (0 : ℝ) ≤ 2)
        ⟨norm_nonneg _, hdist⟩
      have hyb : ‖(Y7Legendre.phi n).eval y‖ ≤ Cn :=
        hCn y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |RHLean.gammaKernelRescaled a ‖x' - y‖| *
            (|(Y7Legendre.phi m).eval x'| * |(Y7Legendre.phi n).eval y|)
          ≤ K * (Cm * Cn) :=
            mul_le_mul hkb
              (mul_le_mul (by simpa [Real.norm_eq_abs] using hCm_x)
                (by simpa [Real.norm_eq_abs] using hyb) (abs_nonneg _) Cm0)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK0
        _ = K * Cm * Cn := by ring
    have hfin : volume (Set.Ioo (-1 : ℝ) 1) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hvol : (volume (Set.Ioo (-1 : ℝ) 1)).toReal = 2 := by
      rw [Real.volume_Ioo,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - (-1))]
      norm_num
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) hfin hC
    rw [measureReal_def, hvol] at hb
    simpa only [mul_assoc] using hb
theorem gammaRep (a : ℝ) (ha : 0 ≤ a) : GammaRep a := by
  intro s x
  have hpt : ∀ x' y : ℝ,
      (legSum x s x' * star (legSum x s y)).re =
        ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y) := by
    intro x' y
    have h1 : legSum x s x' =
        ((∑ m ∈ s, x m * (Y7Legendre.phi m).eval x' : ℝ) : ℂ) := by
      simp only [legSum, phiC, Complex.ofReal_sum, Complex.ofReal_mul]
    have h2 : star (legSum x s y) =
        ((∑ n ∈ s, x n * (Y7Legendre.phi n).eval y : ℝ) : ℂ) := by
      rw [show legSum x s y =
          ((∑ n ∈ s, x n * (Y7Legendre.phi n).eval y : ℝ) : ℂ) from by
        simp only [legSum, phiC, Complex.ofReal_sum, Complex.ofReal_mul]]
      simp only [Complex.star_def, Complex.conj_ofReal]
    rw [h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hinner : ∀ x' ∈ Set.Ioo (-1 : ℝ) 1,
      (∫ y in Set.Ioo (-1 : ℝ) 1, RHLean.gammaKernelRescaled a ‖x' - y‖ *
        (legSum x s x' * star (legSum x s y)).re) =
      ∑ m ∈ s, ∑ n ∈ s, x m * x n *
        (∫ y in Set.Ioo (-1 : ℝ) 1, RHLean.gammaKernelRescaled a ‖x' - y‖ *
          ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y)) := by
    intro x' hx'
    have hpt' : (fun y : ℝ => RHLean.gammaKernelRescaled a ‖x' - y‖ *
          (legSum x s x' * star (legSum x s y)).re) =
        fun y => ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          (RHLean.gammaKernelRescaled a ‖x' - y‖ *
            ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y)) := by
      funext y
      rw [hpt x' y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hpt']
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [← MeasureTheory.integral_const_mul]
      · intro n hn
        exact Integrable.const_mul (integrableOn_gammaKernel_phi ha m n hx') (x m * x n)
    · intro m hm
      apply integrable_finsetSum
      intro n hn
      exact Integrable.const_mul (integrableOn_gammaKernel_phi ha m n hx') (x m * x n)
  unfold RHLean.gammaFormRescaled gammaMatrix
  have houter : (∫ x' in Set.Ioo (-1 : ℝ) 1,
        ∫ y in Set.Ioo (-1 : ℝ) 1, RHLean.gammaKernelRescaled a ‖x' - y‖ *
          (legSum x s x' * star (legSum x s y)).re) =
      ∫ x' in Set.Ioo (-1 : ℝ) 1,
        ∑ m ∈ s, ∑ n ∈ s, x m * x n *
          (∫ y in Set.Ioo (-1 : ℝ) 1, RHLean.gammaKernelRescaled a ‖x' - y‖ *
            ((Y7Legendre.phi m).eval x' * (Y7Legendre.phi n).eval y)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x' hx'
    exact hinner x' hx'
  rw [houter]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [← MeasureTheory.integral_const_mul]
    · intro n hn
      exact Integrable.const_mul (integrableOn_gammaKernel_phi_integral ha m n)
        (x m * x n)
  · intro m hm
    apply integrable_finsetSum
    intro n hn
    exact Integrable.const_mul (integrableOn_gammaKernel_phi_integral ha m n)
      (x m * x n)
theorem formMatrixRep_of_parts (a : ℝ) (harch : ArchDiagonalRep)
    (hgamma : GammaRep a) : FormMatrixRep a := by
  intro s x
  unfold RHLean.localizedFormRescaled rescaledOperatorM
  rw [harch s x, c0Rep a s x, potentialRep s x, hgamma s x, polarRep a s x, shiftRep a s x]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
theorem form_nonneg_of_matrixRep (a : ℝ) (hrep : FormMatrixRep a)
    (hpos : ∀ (s : Finset ℕ) (x : ℕ → ℝ),
      0 ≤ ∑ m ∈ s, ∑ n ∈ s, x m * x n * rescaledOperatorM a m n) :
    ∀ (s : Finset ℕ) (x : ℕ → ℝ),
      0 ≤ RHLean.localizedFormRescaled a (legSum x s) := by
  intro s x
  rw [hrep s x]
  exact hpos s x
end Y7Op
end
end Inline_Y7_Operator
