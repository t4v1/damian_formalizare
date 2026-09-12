import MorseFloer.Basic

/-!
# The Morse lemma in every finite dimension

This file proves Theorem 1.3.1 of Audin–Damian (the Morse lemma) for a function
`f : E → ℝ` on an arbitrary finite-dimensional real normed space, analytic near a
nondegenerate critical point `c`:

`MorseFloer.morse_lemma_general` : there is a chart `φ`, a homeomorphism from an
open neighbourhood of `c` onto an open set, with `φ c = 0` and
`f y = f c + ½ · d²f_c (φ y, φ y)` on its source.

Only three derivatives are used: `MorseFloer.morse_lemma_of_contDiffAt` is the same
statement for `f` merely `C³` at `c`, and the analytic version is derived from it.

The book argues by induction on the dimension.  We follow instead the analyst's
route, which needs no induction and — because the conclusion only asks for a
*homeomorphism* — no smooth dependence on parameters beyond a Lipschitz bound.

1. **Hadamard's lemma** (`hadamard_eq`).  Put
   `Q x = ∫₀¹ (1 − t) d²f_{c + t x} dt`, a bilinear form depending on `x`.  Along the
   segment, `g t = f (c + t x)` satisfies `((1 − t) g' + g)' = (1 − t) g''`, so the
   fundamental theorem of calculus gives `f (c + x) = f c + df_c x + Q x (x, x)`.
   Moreover `Q 0 = ½ d²f_c` (`hadamardQ_zero`), and `Q` is Lipschitz near `0`
   because `d²f` is (`hadamardQ_lipschitz`).  No differentiation under the
   integral sign is needed.
2. **A Lipschitz square root** (`exists_sqrt`).  Let `B = d²f_c`, symmetric and
   nondegenerate, and let `S` be the space of `B`-self-adjoint operators
   (`selfAdj B`).  The map `A ↦ ½ A ∘ A` sends `S` to `S` and has derivative the
   identity at `A = id`, so the inverse function theorem, applied *inside* `S`,
   yields a local inverse `R` near `½ id`, Lipschitz there, whose values are again
   `B`-self-adjoint.  Working in `S` rather than in all of `End E` is what makes
   `B (A v, A v) = B (A² v, v)` available.
3. **The family `T`** (`exists_family`).  With `e : E ≃ E*` induced by `B`, the
   operator `T x = e⁻¹ ∘ sym (Q x)` is `B`-self-adjoint, `T 0 = ½ id`, `T` is
   Lipschitz near `0`, and `Q x (x, x) = B (T x x, x)`.
4. **The chart** (`morse_of_family`).  With `A x = R (T x)`, one has
   `½ A x ∘ A x = T x`, hence `f (c + x) = f c + ½ B (A x x, A x x)`.  The map
   `ψ x = A x x` has strict derivative `id` at `0` (`hasStrictFDerivAt_apply_self`):
   `ψ u − ψ v − (u − v) = (A u − id)(u − v) + (A u − A v) v`, and both terms are
   `o(‖u − v‖)` since `A` is Lipschitz with `A 0 = id`.  The inverse function
   theorem turns `y ↦ ψ (y − c)` into the chart.
-/

open scoped ContDiff Topology NNReal
open Filter Set Metric

namespace MorseFloer

namespace MorseLemma

/-! ## Derivatives along a segment -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The segment `s ↦ c + s x` has velocity `x`. -/
theorem hasDerivAt_segment (c x : E) (t : ℝ) : HasDerivAt (fun s : ℝ => c + s • x) x t :=
  (((hasDerivAt_id' t).smul_const x).const_add c).congr_deriv (one_smul ℝ x)

/-- At a point where `f` is `C²`, the differential of `df` is `d²f`. -/
theorem hasFDerivAt_fderiv_of_contDiffAt {f : E → ℝ} {y : E} (hy : ContDiffAt ℝ 2 f y) :
    HasFDerivAt (fderiv ℝ f) (sndFDeriv f y) y :=
  ((hy.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

/-- The first derivative of `s ↦ f (c + s x)`. -/
theorem hasDerivAt_comp_segment {f : E → ℝ} {c x : E} {t : ℝ}
    (hy : ContDiffAt ℝ 2 f (c + t • x)) :
    HasDerivAt (fun s : ℝ => f (c + s • x)) (fderiv ℝ f (c + t • x) x) t :=
  (hy.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_segment c x t)

/-- The derivative of `s ↦ df_{c + s x}` is `d²f_{c + s x} (x, ·)`. -/
theorem hasDerivAt_fderiv_comp_segment {f : E → ℝ} {c x : E} {t : ℝ}
    (hy : ContDiffAt ℝ 2 f (c + t • x)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (c + s • x)) (sndFDeriv f (c + t • x) x) t :=
  (hasFDerivAt_fderiv_of_contDiffAt hy).comp_hasDerivAt t (hasDerivAt_segment c x t)

/-- The second derivative of `s ↦ f (c + s x)` is `d²f_{c + s x} (x, x)`. -/
theorem hasDerivAt_fderiv_apply_segment {f : E → ℝ} {c x : E} {t : ℝ}
    (hy : ContDiffAt ℝ 2 f (c + t • x)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (c + s • x) x) (sndFDeriv f (c + t • x) x x) t :=
  ((hasDerivAt_fderiv_comp_segment hy).clm_apply (hasDerivAt_const t x)).congr_deriv (by simp)

/-- Along the segment `s ↦ c + s x`, the function `(1 − s) g'(s) + g(s)`, where
`g s = f (c + s x)`, has derivative `(1 − s) g''(s)`. -/
theorem hasDerivAt_taylor_aux {f : E → ℝ} {c x : E} {t : ℝ}
    (hy : ContDiffAt ℝ 2 f (c + t • x)) :
    HasDerivAt (fun s : ℝ => (1 - s) * fderiv ℝ f (c + s • x) x + f (c + s • x))
      ((1 - t) * sndFDeriv f (c + t • x) x x) t :=
  ((((hasDerivAt_id' t).const_sub 1).mul (hasDerivAt_fderiv_apply_segment hy)).add
    (hasDerivAt_comp_segment hy)).congr_deriv (by ring)

end Segment

/- Mathlib builds itself with `maxSynthPendingDepth := 3` (see its `lakefile.lean`); this
project uses Lean's default of `1`, at which instance synthesis fails on iterated spaces of
operators such as `E →L[ℝ] E →L[ℝ] ℝ` (e.g. `NormSMulClass`, or the `ENormedAddMonoid`
behind `IntervalIntegrable`).  From here on we use Mathlib's own setting.  The segment
computations above stay at the default: at depth `3` the unifier times out on
`hasDerivAt_fderiv_apply_segment`. -/
set_option maxSynthPendingDepth 3

/-! ## Operators self-adjoint for a bilinear form, and their square roots -/

section SquareRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The operators `A` that are self-adjoint for the bilinear form `B`:
`B (A v) w = B v (A w)` for all `v, w`. -/
def selfAdj (B : E →L[ℝ] E →L[ℝ] ℝ) : Submodule ℝ (E →L[ℝ] E) where
  carrier := {A | ∀ v w, B (A v) w = B v (A w)}
  add_mem' {A A'} hA hA' v w := by simp [hA v w, hA' v w]
  zero_mem' v w := by simp
  smul_mem' r A hA v w := by simp [hA v w]

theorem mem_selfAdj {B : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] E} :
    A ∈ selfAdj B ↔ ∀ v w, B (A v) w = B v (A w) := Iff.rfl

/-- The identity, as a `B`-self-adjoint operator. -/
def oneS (B : E →L[ℝ] E →L[ℝ] ℝ) : selfAdj B :=
  ⟨ContinuousLinearMap.id ℝ E, fun _ _ => rfl⟩

theorem halfSq_mem {B : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] E} (hA : A ∈ selfAdj B) :
    (1 / 2 : ℝ) • A.comp A ∈ selfAdj B := by
  intro v w
  simp [hA (A v) w, hA v (A w)]

/-- Half the square `A ↦ ½ A ∘ A`, as a self-map of the `B`-self-adjoint operators. -/
noncomputable def halfSq (B : E →L[ℝ] E →L[ℝ] ℝ) (A : selfAdj B) : selfAdj B :=
  ⟨(1 / 2 : ℝ) • (A : E →L[ℝ] E).comp (A : E →L[ℝ] E), halfSq_mem A.2⟩

theorem coe_halfSq (B : E →L[ℝ] E →L[ℝ] ℝ) (A : selfAdj B) :
    (halfSq B A : E →L[ℝ] E) = (1 / 2 : ℝ) • (A : E →L[ℝ] E).comp (A : E →L[ℝ] E) := rfl

/-- On all operators, `A ↦ ½ A ∘ A` has strict derivative the identity at `A = id`. -/
theorem hasStrictFDerivAt_halfSq_full :
    HasStrictFDerivAt (fun A : E →L[ℝ] E => (1 / 2 : ℝ) • A.comp A)
      (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) (ContinuousLinearMap.id ℝ E) := by
  have h := ((hasStrictFDerivAt_id (𝕜 := ℝ) (ContinuousLinearMap.id ℝ E)).clm_comp
    (hasStrictFDerivAt_id (ContinuousLinearMap.id ℝ E))).fun_const_smul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext A v
  simp only [ContinuousLinearMap.id_apply, id_eq, smul_apply, add_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  module

/-- Restricted to the `B`-self-adjoint operators, `A ↦ ½ A ∘ A` still has strict
derivative the identity at `A = id`: the norm of `selfAdj B` is the operator norm. -/
theorem hasStrictFDerivAt_halfSq (B : E →L[ℝ] E →L[ℝ] ℝ) :
    HasStrictFDerivAt (halfSq B)
      ((ContinuousLinearEquiv.refl ℝ (selfAdj B) : selfAdj B ≃L[ℝ] selfAdj B) :
        selfAdj B →L[ℝ] selfAdj B) (oneS B) := by
  have hfull := (hasStrictFDerivAt_halfSq_full (E := E)).isLittleO
  rw [Asymptotics.isLittleO_iff] at hfull
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have ht : Tendsto (fun p : selfAdj B × selfAdj B => ((p.1 : E →L[ℝ] E), (p.2 : E →L[ℝ] E)))
      (𝓝 (oneS B, oneS B)) (𝓝 (ContinuousLinearMap.id ℝ E, ContinuousLinearMap.id ℝ E)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).tendsto _
  filter_upwards [ht.eventually (hfull hε)] with p hp
  simpa [coe_halfSq] using hp

/-- **A Lipschitz square root near `½ id`.**  The inverse function theorem applied to
`halfSq` inside the `B`-self-adjoint operators. -/
theorem exists_sqrt [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∃ R : selfAdj B → selfAdj B, R (halfSq B (oneS B)) = oneS B ∧
      (∀ᶠ T in 𝓝 (halfSq B (oneS B)), halfSq B (R T) = T) ∧
      ∃ K, ∃ s ∈ 𝓝 (halfSq B (oneS B)), LipschitzOnWith K R s := by
  have h := hasStrictFDerivAt_halfSq B
  exact ⟨h.localInverse _ _ _, h.localInverse_apply_image, h.eventually_right_inverse,
    h.to_localInverse.exists_lipschitzOnWith⟩

end SquareRoot

/-! ## Hadamard's lemma -/

section Hadamard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hadamard remainder `Q x = ∫₀¹ (1 − t) d²f_{c + t x} dt`. -/
noncomputable def hadamardQ (f : E → ℝ) (c x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) • sndFDeriv f (c + t • x)

/-- Evaluation of a bilinear form at `(v, w)`, as a continuous linear functional. -/
noncomputable def evalAt (v w : E) : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)

@[simp]
theorem evalAt_apply (v w : E) (P : E →L[ℝ] E →L[ℝ] ℝ) : evalAt v w P = P v w := rfl

theorem line_mem_ball {c x : E} {ρ t : ℝ} (hx : ‖x‖ < ρ) (ht : t ∈ Icc (0 : ℝ) 1) :
    c + t • x ∈ ball c ρ := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  calc t * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)
    _ < ρ := by rwa [one_mul]

theorem continuousOn_hadamard_integrand {f : E → ℝ} {c x : E} {ρ : ℝ}
    (hC : ContinuousOn (sndFDeriv f) (ball c ρ)) (hx : ‖x‖ < ρ) :
    ContinuousOn (fun t : ℝ => (1 - t) • sndFDeriv f (c + t • x)) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  have hline : Continuous (fun t : ℝ => c + t • x) := by fun_prop
  exact (continuousOn_const.sub continuousOn_id).smul
    (hC.comp hline.continuousOn fun t ht => line_mem_ball hx ht)

/-- **Hadamard's lemma**, the integral form of Taylor's formula to order two:
`f (c + x) = f c + df_c x + Q x (x, x)` as long as the segment `[c, c + x]` stays in a
ball on which `f` is `C²`. -/
theorem hadamard_eq {f : E → ℝ} {c x : E} {ρ : ℝ}
    (hf : ∀ y ∈ ball c ρ, ContDiffAt ℝ 2 f y) (hC : ContinuousOn (sndFDeriv f) (ball c ρ))
    (hx : ‖x‖ < ρ) :
    f (c + x) = f c + fderiv ℝ f c x + hadamardQ f c x x x := by
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) • sndFDeriv f (c + t • x))
      MeasureTheory.volume 0 1 :=
    (continuousOn_hadamard_integrand hC hx).intervalIntegrable
  -- Pull the evaluation at `(x, x)` out of the integral.
  have heval : hadamardQ f c x x x
      = ∫ t in (0 : ℝ)..1, (1 - t) * sndFDeriv f (c + t • x) x x := by
    have h := (evalAt x x).intervalIntegral_comp_comm hint
    show evalAt x x (hadamardQ f c x) = _
    rw [hadamardQ, ← h]
    simp
  have hint' : IntervalIntegrable (fun t : ℝ => (1 - t) * sndFDeriv f (c + t • x) x x)
      MeasureTheory.volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    have h := (evalAt x x).continuous.comp_continuousOn (continuousOn_hadamard_integrand hC hx)
    refine h.congr fun t _ => ?_
    simp
  -- The derivative of `(1 − t) g'(t) + g(t)` along the segment.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (1 - s) * fderiv ℝ f (c + s • x) x + f (c + s • x))
        ((1 - t) * sndFDeriv f (c + t • x) x x) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact hasDerivAt_taylor_aux (hf _ (line_mem_ball hx ht))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint'
  rw [heval, hFTC]
  simp only [one_smul, zero_smul, add_zero, sub_self, zero_mul, sub_zero, one_mul, zero_add]
  ring

theorem integral_one_sub : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
  have h : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s - s * s / 2) (1 - t) t := by
    intro t _
    have h1 := (hasDerivAt_id' t).sub (((hasDerivAt_id' t).mul (hasDerivAt_id' t)).div_const 2)
    exact h1.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((continuous_const.sub continuous_id).intervalIntegrable 0 1)]
  norm_num

/-- At `x = 0` the Hadamard remainder is half the Hessian. -/
theorem hadamardQ_zero (f : E → ℝ) (c : E) :
    hadamardQ f c 0 = (1 / 2 : ℝ) • sndFDeriv f c := by
  simp only [hadamardQ, smul_zero, add_zero]
  rw [intervalIntegral.integral_smul_const, integral_one_sub]

/-- The Hadamard remainder inherits a Lipschitz bound from the second differential. -/
theorem hadamardQ_lipschitz {f : E → ℝ} {c : E} {ρ : ℝ} {K : ℝ≥0}
    (hL : LipschitzOnWith K (sndFDeriv f) (ball c ρ)) {y z : E} (hy : ‖y‖ < ρ)
    (hz : ‖z‖ < ρ) :
    ‖hadamardQ f c y - hadamardQ f c z‖ ≤ K * ‖y - z‖ := by
  have hC := hL.continuousOn
  rw [hadamardQ, hadamardQ, ← intervalIntegral.integral_sub
    (continuousOn_hadamard_integrand hC hy).intervalIntegrable
    (continuousOn_hadamard_integrand hC hz).intervalIntegrable]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * ‖y - z‖) ?_).trans
    (le_of_eq (by simp))
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  rw [← smul_sub, norm_smul]
  have h1 : ‖(1 : ℝ) - t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 - t by linarith [ht'.2])]
    linarith [ht'.1]
  have h2 : ‖sndFDeriv f (c + t • y) - sndFDeriv f (c + t • z)‖ ≤ K * ‖y - z‖ := by
    have h3 : ‖(c + t • y) - (c + t • z)‖ ≤ ‖y - z‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht'.1]
      calc t * ‖y - z‖ ≤ 1 * ‖y - z‖ := mul_le_mul_of_nonneg_right ht'.2 (norm_nonneg _)
        _ = ‖y - z‖ := one_mul _
    calc _ ≤ K * ‖(c + t • y) - (c + t • z)‖ :=
          hL.norm_sub_le (line_mem_ball hy ht') (line_mem_ball hz ht')
      _ ≤ K * ‖y - z‖ := mul_le_mul_of_nonneg_left h3 (NNReal.coe_nonneg K)
  calc ‖(1 : ℝ) - t‖ * ‖sndFDeriv f (c + t • y) - sndFDeriv f (c + t • z)‖
      ≤ 1 * (K * ‖y - z‖) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = K * ‖y - z‖ := one_mul _

/-- Near a point where `f` is `C³`, there is a ball on which `f` is `C²` and its
second differential is Lipschitz. -/
theorem exists_ball_regular {f : E → ℝ} {c : E} (hf3 : ContDiffAt ℝ 3 f c) :
    ∃ ρ > 0, ∃ K : ℝ≥0, (∀ y ∈ ball c ρ, ContDiffAt ℝ 2 f y) ∧
      LipschitzOnWith K (sndFDeriv f) (ball c ρ) := by
  have hev : ∀ᶠ y in 𝓝 c, ContDiffAt ℝ 2 f y := (hf3.of_le (by norm_num)).eventually (by simp)
  have h1 : ContDiffAt ℝ 1 (sndFDeriv f) c :=
    (hf3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, ht, hLt⟩ := h1.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (show ∀ᶠ y in 𝓝 c, y ∈ t from ht))
  exact ⟨ρ, hρ, K, fun y hy => (hball y hy).1, hLt.mono fun y hy => (hball y hy).2⟩

end Hadamard

/-! ## From the Hadamard family to a family of self-adjoint operators -/

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The symmetric part `½ (P + Pᵗ)` of a bilinear form. -/
noncomputable def symmPart (P : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (P + P.flip)

theorem symmPart_apply (P : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    symmPart P v w = (1 / 2 : ℝ) * (P v w + P w v) := by
  simp only [symmPart, smul_apply, add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

theorem symmPart_symm (P : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    symmPart P v w = symmPart P w v := by
  rw [symmPart_apply, symmPart_apply, add_comm]

theorem symmPart_of_symm {P : E →L[ℝ] E →L[ℝ] ℝ} (hP : ∀ v w, P v w = P w v) :
    symmPart P = P := by
  ext v w
  rw [symmPart_apply, hP w v]
  ring

theorem symmPart_norm_sub_le (P P' : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖symmPart P - symmPart P'‖ ≤ ‖P - P'‖ := by
  have h : symmPart P - symmPart P' = (1 / 2 : ℝ) • ((P - P') + (P - P').flip) := by
    ext v w
    simp only [sub_apply, symmPart_apply, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  rw [h, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h2 := norm_add_le (P - P') (P - P').flip
  rw [ContinuousLinearMap.opNorm_flip] at h2
  linarith

/-- A nondegenerate bilinear form on a finite-dimensional space identifies the space
with its dual. -/
theorem exists_equiv_of_injective [FiniteDimensional ℝ E] (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : Function.Injective B) : ∃ e : E ≃L[ℝ] (E →L[ℝ] ℝ), ∀ v, e v = B v := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq,
      Module.finrank_linearMap_self]
  exact ⟨(LinearMap.linearEquivOfInjective (B : E →ₗ[ℝ] E →L[ℝ] ℝ) hB
    hdim).toContinuousLinearEquiv, fun _ => rfl⟩

/-- The operator `e⁻¹ ∘ P` representing the bilinear form `P` through `e`. -/
noncomputable def toOp (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) (P : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  (e.symm : (E →L[ℝ] ℝ) →L[ℝ] E).comp P

theorem apply_toOp (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) (P : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    e (toOp e P v) = P v := by
  simp [toOp]

theorem toOp_mem {B : E →L[ℝ] E →L[ℝ] ℝ} {e : E ≃L[ℝ] (E →L[ℝ] ℝ)} (he : ∀ v, e v = B v)
    (hB : ∀ v w, B v w = B w v) {P : E →L[ℝ] E →L[ℝ] ℝ} (hP : ∀ v w, P v w = P w v) :
    toOp e P ∈ selfAdj B := by
  intro v w
  rw [hB v, ← he, ← he, apply_toOp, apply_toOp]
  exact hP v w

theorem toOp_norm_sub_le (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) (P P' : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖toOp e P - toOp e P'‖ ≤ ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * ‖P - P'‖ := by
  rw [toOp, toOp, ← ContinuousLinearMap.comp_sub]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- **Step 3.**  The Hadamard family, symmetrised and transported through `B`, is a
Lipschitz family `T` of `B`-self-adjoint operators with `T 0 = ½ id` and
`f (c + x) = f c + B (T x x, x)`. -/
theorem exists_family [FiniteDimensional ℝ E] {f : E → ℝ} {c : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hBsymm : ∀ v w, B v w = B w v) (hBinj : Function.Injective B)
    (Q : E → E →L[ℝ] E →L[ℝ] ℝ) {ρ K : ℝ}
    (hQ0 : Q 0 = (1 / 2 : ℝ) • B)
    (hQL : ∀ y z, ‖y‖ < ρ → ‖z‖ < ρ → ‖Q y - Q z‖ ≤ K * ‖y - z‖)
    (hfQ : ∀ x, ‖x‖ < ρ → f (c + x) = f c + Q x x x) :
    ∃ T : E → selfAdj B, ∃ K' : ℝ, T 0 = halfSq B (oneS B) ∧
      (∀ y z, ‖y‖ < ρ → ‖z‖ < ρ → ‖T y - T z‖ ≤ K' * ‖y - z‖) ∧
      (∀ x, ‖x‖ < ρ → f (c + x) = f c + B ((T x : E →L[ℝ] E) x) x) := by
  obtain ⟨e, he⟩ := exists_equiv_of_injective B hBinj
  refine ⟨fun x => ⟨toOp e (symmPart (Q x)), toOp_mem he hBsymm (symmPart_symm _)⟩,
    ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * K, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show toOp e (symmPart (Q 0))
      = (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)
    have hsym : ∀ v w, ((1 / 2 : ℝ) • B) v w = ((1 / 2 : ℝ) • B) w v := fun v w => by
      simp only [smul_apply, smul_eq_mul, hBsymm v w]
    rw [hQ0, symmPart_of_symm hsym]
    ext v
    simp [toOp, ← he]
  · intro y z hy hz
    have h1 : ‖toOp e (symmPart (Q y)) - toOp e (symmPart (Q z))‖
        ≤ ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * ‖symmPart (Q y) - symmPart (Q z)‖ :=
      toOp_norm_sub_le e _ _
    have h2 := symmPart_norm_sub_le (Q y) (Q z)
    have h3 := hQL y z hy hz
    have h4 : 0 ≤ ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ := norm_nonneg _
    calc _ = ‖toOp e (symmPart (Q y)) - toOp e (symmPart (Q z))‖ := rfl
      _ ≤ ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * ‖symmPart (Q y) - symmPart (Q z)‖ := h1
      _ ≤ ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * (K * ‖y - z‖) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) h4
      _ = ‖(e.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * K * ‖y - z‖ := by ring
  · intro x hx
    rw [hfQ x hx]
    congr 1
    show Q x x x = B (toOp e (symmPart (Q x)) x) x
    rw [← he, apply_toOp, symmPart_apply]
    ring

end Family

/-! ## The chart -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A map with a Lipschitz bound near `0` is continuous at `0`. -/
theorem tendsto_of_norm_sub_le {F : Type*} [SeminormedAddCommGroup F] {g : E → F} {ρ K : ℝ}
    (hρ : 0 < ρ) (hg : ∀ y z, ‖y‖ < ρ → ‖z‖ < ρ → ‖g y - g z‖ ≤ K * ‖y - z‖) :
    Tendsto g (𝓝 0) (𝓝 (g 0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun u => K * ‖u‖) ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (0 : E) hρ] with u hu
    have h := hg u 0 (mem_ball_zero_iff.mp hu) (by rwa [norm_zero])
    rwa [sub_zero] at h
  · have h := (tendsto_norm_zero : Tendsto (fun a : E => ‖a‖) (𝓝 0) (𝓝 0)).const_mul K
    rwa [mul_zero] at h

/-- **The chart has derivative the identity.**  If `A` is Lipschitz near `0` with
`A 0 = id`, then `u ↦ A u u` has strict derivative `id` at `0`. -/
theorem hasStrictFDerivAt_apply_self {A : E → E →L[ℝ] E} {δ L : ℝ} (hδ : 0 < δ)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAL : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖A u - A v‖ ≤ L * ‖u - v‖) :
    HasStrictFDerivAt (fun u => A u u) (ContinuousLinearMap.id ℝ E) 0 := by
  refine HasStrictFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr fun ε hε => ?_)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |L| + 1 := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; positivity
  have hLM : L ≤ M := by rw [hM]; linarith [le_abs_self L]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min δ (ε / (2 * M)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; exact lt_min hδ (div_pos hε (mul_pos two_pos hMpos))
  have h1 : ∀ᶠ p : E × E in 𝓝 ((0 : E), (0 : E)), p.1 ∈ ball (0 : E) η :=
    (continuous_fst.tendsto ((0 : E), (0 : E))).eventually_mem (ball_mem_nhds _ hηpos)
  have h2 : ∀ᶠ p : E × E in 𝓝 ((0 : E), (0 : E)), p.2 ∈ ball (0 : E) η :=
    (continuous_snd.tendsto ((0 : E), (0 : E))).eventually_mem (ball_mem_nhds _ hηpos)
  filter_upwards [h1, h2] with p hp1 hp2
  obtain ⟨u, v⟩ := p
  rw [mem_ball_zero_iff] at hp1 hp2
  have hηδ : η ≤ δ := by rw [hη]; exact min_le_left _ _
  have hηε : η ≤ ε / (2 * M) := by rw [hη]; exact min_le_right _ _
  have hu : ‖u‖ < δ := hp1.trans_le hηδ
  have hv : ‖v‖ < δ := hp2.trans_le hηδ
  have hid : A u u - A v v - ContinuousLinearMap.id ℝ E (u - v)
      = (A u - A 0) (u - v) + (A u - A v) v := by
    rw [hA0]
    simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  show ‖A u u - A v v - ContinuousLinearMap.id ℝ E (u - v)‖ ≤ ε * ‖u - v‖
  rw [hid]
  have hA1 : ‖A u - A 0‖ ≤ M * ‖u‖ := by
    have h := hAL u 0 hu (by rwa [norm_zero])
    rw [sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))
  have hA2 : ‖A u - A v‖ ≤ M * ‖u - v‖ :=
    (hAL u v hu hv).trans (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))
  have hsmall : M * (‖u‖ + ‖v‖) ≤ ε := by
    have e1 : ‖u‖ * (2 * M) < ε := (lt_div_iff₀ (mul_pos two_pos hMpos)).mp (hp1.trans_le hηε)
    have e2 : ‖v‖ * (2 * M) < ε := (lt_div_iff₀ (mul_pos two_pos hMpos)).mp (hp2.trans_le hηε)
    nlinarith
  calc ‖(A u - A 0) (u - v) + (A u - A v) v‖
      ≤ ‖A u - A 0‖ * ‖u - v‖ + ‖A u - A v‖ * ‖v‖ :=
        (norm_add_le _ _).trans (add_le_add ((A u - A 0).le_opNorm _) ((A u - A v).le_opNorm _))
    _ ≤ (M * ‖u‖) * ‖u - v‖ + (M * ‖u - v‖) * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hA1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hA2 (norm_nonneg _))
    _ = (M * (‖u‖ + ‖v‖)) * ‖u - v‖ := by ring
    _ ≤ ε * ‖u - v‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

/-- **Step 4.**  From a Lipschitz family `T` of `B`-self-adjoint operators with
`T 0 = ½ id` and `f (c + x) = f c + B (T x x, x)`, the square root `A x` of `2 T x`
produces the Morse chart `y ↦ A (y − c) (y − c)`. -/
theorem morse_of_family [CompleteSpace E] [FiniteDimensional ℝ E] {f : E → ℝ} {c : E}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (T : E → selfAdj B) {ρ K : ℝ} (hρ : 0 < ρ)
    (hT0 : T 0 = halfSq B (oneS B))
    (hTL : ∀ y z, ‖y‖ < ρ → ‖z‖ < ρ → ‖T y - T z‖ ≤ K * ‖y - z‖)
    (hfT : ∀ x, ‖x‖ < ρ → f (c + x) = f c + B ((T x : E →L[ℝ] E) x) x) :
    ∃ φ : OpenPartialHomeomorph E E, c ∈ φ.source ∧ φ c = 0 ∧
      ∀ y ∈ φ.source, f y = f c + (1 / 2 : ℝ) * B (φ y) (φ y) := by
  obtain ⟨R, hR1, hRinv, KR, s, hs, hRL⟩ := exists_sqrt B
  have hTt : Tendsto T (𝓝 0) (𝓝 (halfSq B (oneS B))) := by
    rw [← hT0]
    exact tendsto_of_norm_sub_le hρ hTL
  have hev : ∀ᶠ u in 𝓝 (0 : E), ‖u‖ < ρ ∧ T u ∈ s ∧ halfSq B (R (T u)) = T u := by
    have h0 : ∀ᶠ u in 𝓝 (0 : E), ‖u‖ < ρ := by
      filter_upwards [Metric.ball_mem_nhds (0 : E) hρ] with u hu
      exact mem_ball_zero_iff.mp hu
    exact h0.and ((hTt.eventually_mem hs).and (hTt.eventually hRinv))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- The operator family `A u = R (T u)`.
  obtain ⟨A, hAdef⟩ : ∃ A : E → E →L[ℝ] E, A = fun u => (R (T u) : E →L[ℝ] E) := ⟨_, rfl⟩
  have hA0 : A 0 = ContinuousLinearMap.id ℝ E := by
    rw [hAdef]
    show (R (T 0) : E →L[ℝ] E) = _
    rw [hT0, hR1]
    rfl
  have hAL : ∀ u v, ‖u‖ < δ → ‖v‖ < δ → ‖A u - A v‖ ≤ (KR * K) * ‖u - v‖ := by
    intro u v hu hv
    have hu' := hball u (mem_ball_zero_iff.mpr hu)
    have hv' := hball v (mem_ball_zero_iff.mpr hv)
    have h1 : ‖R (T u) - R (T v)‖ ≤ KR * ‖T u - T v‖ := hRL.norm_sub_le hu'.2.1 hv'.2.1
    have h2 := hTL u v hu'.1 hv'.1
    rw [hAdef]
    calc ‖(R (T u) : E →L[ℝ] E) - R (T v)‖ = ‖R (T u) - R (T v)‖ := rfl
      _ ≤ KR * ‖T u - T v‖ := h1
      _ ≤ KR * (K * ‖u - v‖) := mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg KR)
      _ = (KR * K) * ‖u - v‖ := by ring
  have hψ0 : HasStrictFDerivAt (fun u => A u u) (ContinuousLinearMap.id ℝ E) 0 :=
    hasStrictFDerivAt_apply_self hδ hA0 hAL
  have hψ : HasStrictFDerivAt (fun y => A (y - c) (y - c))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) c := by
    have hsub : HasStrictFDerivAt (fun y : E => y - c) (ContinuousLinearMap.id ℝ E) c :=
      hasStrictFDerivAt_sub_const c
    have h0 : HasStrictFDerivAt (fun u => A u u) (ContinuousLinearMap.id ℝ E) (c - c) := by
      rw [sub_self]
      exact hψ0
    rw [ContinuousLinearEquiv.coe_refl]
    exact (HasStrictFDerivAt.comp c (f := fun y : E => y - c) h0 hsub).congr_fderiv
      (ContinuousLinearMap.id_comp _)
  -- An open neighbourhood of `c` on which the construction is valid.
  have hev' : ∀ᶠ y in 𝓝 c, y - c ∈ ball (0 : E) δ := by
    have ht : Tendsto (fun y : E => y - c) (𝓝 c) (𝓝 (c - c)) :=
      (continuous_id.sub continuous_const).tendsto c
    rw [sub_self] at ht
    exact ht.eventually_mem (Metric.ball_mem_nhds 0 hδ)
  obtain ⟨V, hVsub, hVopen, hcV⟩ := _root_.mem_nhds_iff.mp hev'
  refine ⟨(hψ.toOpenPartialHomeomorph _).restrOpen V hVopen, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.mem_inter hψ.mem_toOpenPartialHomeomorph_source hcV
  · simp only [OpenPartialHomeomorph.coe_restrOpen,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    simp
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    obtain ⟨hyρ, -, hsq⟩ := hball (y - c) (hVsub hy.2)
    simp only [OpenPartialHomeomorph.coe_restrOpen,
      HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    have hsq' : (1 / 2 : ℝ) • (A (y - c)).comp (A (y - c)) = (T (y - c) : E →L[ℝ] E) := by
      rw [hAdef]
      exact congrArg Subtype.val hsq
    have hself : ∀ v w, B (A (y - c) v) w = B v (A (y - c) w) := by
      rw [hAdef]
      exact mem_selfAdj.mp (R (T (y - c))).2
    have hf' := hfT (y - c) hyρ
    rw [show c + (y - c) = y by abel] at hf'
    rw [hf', ← hsq']
    simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
    rw [hself (A (y - c) (y - c)) (y - c)]

end Chart

end MorseLemma

open MorseLemma in
/-- **The Morse lemma for a `C³` function.**

Near a nondegenerate critical point `c` of a function `f` that is `C³` at `c`, there
is a chart `φ` centred at `c` in which `f` is exactly its quadratic model:
`f y = f c + ½ · d²f_c (φ y, φ y)` on the source of `φ`.

The proof combines Hadamard's lemma (`hadamard_eq`), a Lipschitz square root of a
`d²f_c`-self-adjoint operator near `½ id` (`exists_sqrt`), and the inverse function
theorem (`morse_of_family`); see the module docstring.  Three derivatives are all it
uses: they make the second differential Lipschitz near `c`. -/
theorem morse_lemma_of_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → ℝ} {c : E}
    (hf : ContDiffAt ℝ 3 f c) (hcrit : fderiv ℝ f c = 0)
    (hnd : IsNondegenerate (sndFDeriv f c)) :
    ∃ φ : OpenPartialHomeomorph E E, c ∈ φ.source ∧ φ c = 0 ∧
      ∀ y ∈ φ.source, f y = f c + (1 / 2 : ℝ) * sndFDeriv f c (φ y) (φ y) := by
  obtain ⟨ρ, hρ, K, hC2, hL⟩ := exists_ball_regular hf
  have hBsymm : ∀ v w, sndFDeriv f c v w = sndFDeriv f c w v :=
    sndFDeriv_symm (hf.of_le (by norm_num))
  have hBinj := (isNondegenerate_iff_injective _).mp hnd
  obtain ⟨T, K', hT0, hTL, hfT⟩ := exists_family (f := f) (c := c) hBsymm hBinj
    (hadamardQ f c) (hadamardQ_zero f c) (fun y z hy hz => hadamardQ_lipschitz hL hy hz)
    (fun x hx => by
      rw [hadamard_eq hC2 hL.continuousOn hx, hcrit]
      simp)
  exact morse_of_family T hρ hT0 hTL hfT

/-- **Theorem 1.3.1 (the Morse lemma), in every finite dimension.**

Near a nondegenerate critical point `c` of a function `f` analytic at `c`, there is
a chart `φ` centred at `c` in which `f` is exactly its quadratic model:
`f y = f c + ½ · d²f_c (φ y, φ y)` on the source of `φ`.  This is
`morse_lemma_of_contDiffAt`, which needs only three derivatives. -/
theorem morse_lemma_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → ℝ} {c : E}
    (hf : ContDiffAt ℝ ω f c) (hcrit : fderiv ℝ f c = 0)
    (hnd : IsNondegenerate (sndFDeriv f c)) :
    ∃ φ : OpenPartialHomeomorph E E, c ∈ φ.source ∧ φ c = 0 ∧
      ∀ y ∈ φ.source, f y = f c + (1 / 2 : ℝ) * sndFDeriv f c (φ y) (φ y) :=
  morse_lemma_of_contDiffAt (hf.of_le le_top) hcrit hnd

end MorseFloer
