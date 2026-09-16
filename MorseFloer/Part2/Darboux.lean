import MorseFloer.Part2.FlowC1

/-!
# Darboux's theorem in the local model (Theorem 5.3.2)

A closed nondegenerate `2`-form on a finite-dimensional real vector space is,
near any point, the pull-back of its value at that point by a local
diffeomorphism.  The proof is Moser's path method, as in the book.

The form is taken here as a `C¹` map `Ω : E → E →L[ℝ] E →L[ℝ] ℝ`, alternating
at every point, nondegenerate at the base point `x₀`, and closed:
`DΩ(u)(v, w) − DΩ(v)(u, w) + DΩ(w)(u, v) = 0`.  Chapter 5 restates the result
for its `IsSymplecticForm2`.

## The route

1. **The Poincaré lemma** (`poincare`, `poincare_d`).  For a closed alternating
   `β` the `1`-form `α_x = ∫₀¹ s·β_{x₀ + s(x − x₀)}(x − x₀) ds` satisfies
   `Dα(a)(b) − Dα(b)(a) = β_x(a, b)`: differentiating under the integral and
   using closedness, the integrand is `d/ds (s² β_{x₀+s(x−x₀)}(a, b))`.
2. **Moser's field.**  With `Ω₀ = Ω x₀` and `Ω_t = Ω + t (Ω₀ − Ω)`, apply the
   Poincaré lemma to `β = Ω − Ω₀` and solve `Ω_t(X_t) = α` where `Ω_t` is
   invertible, which is the case near `{x₀} × ℝ`.  A cut-off makes the suspended
   field `(x, t) ↦ (X_t x, 1)` globally Lipschitz, and `FlowC1.exists_flow`
   gives its `C¹` flow.
3. **Invariance.**  Along the flow `ψ_t`, the scalar
   `Ω_t(ψ_t x)(Dψ_t a, Dψ_t b)` has derivative zero: differentiating
   `Ω_t(X_t) = α` in space, the terms cancel by closedness, alternation and the
   Poincaré identity.  Hence `Ω₀(Dψ₁ a, Dψ₁ b) = Ω_x(a, b)`.
4. **The chart.**  `Dψ₁(x₀)` is injective by nondegeneracy, so the inverse
   function theorem makes `ψ₁` an open partial homeomorphism near `x₀`.
-/

open Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace MorseFloer
namespace Darboux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The Poincaré lemma for closed `2`-forms -/

section Poincare

-- instance search on the nested operator spaces `E →L[ℝ] E →L[ℝ] ℝ` needs this
set_option maxSynthPendingDepth 3

variable (β : E → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : E)

/-- The integrand of the homotopy formula, `s·β_{x₀+s(x−x₀)}(x − x₀)`. -/
noncomputable def poincareIntegrand (x : E) (s : ℝ) : E →L[ℝ] ℝ :=
  s • β (x₀ + s • (x - x₀)) (x - x₀)

/-- The derivative of `poincareIntegrand` in `x`. -/
noncomputable def poincareIntegrand' (x : E) (s : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  s • (s • (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (x - x₀)).comp
      (fderiv ℝ β (x₀ + s • (x - x₀))) + β (x₀ + s • (x - x₀)))

/-- The primitive `α` of `β` given by the homotopy formula. -/
noncomputable def poincare (x : E) : E →L[ℝ] ℝ :=
  ∫ s in (0:ℝ)..1, poincareIntegrand β x₀ x s

omit [FiniteDimensional ℝ E] in
theorem poincareIntegrand'_apply (x : E) (s : ℝ) (a b : E) :
    poincareIntegrand' β x₀ x s a b
      = s * (s * fderiv ℝ β (x₀ + s • (x - x₀)) a (x - x₀) b + β (x₀ + s • (x - x₀)) a b) := by
  simp only [poincareIntegrand', smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_poincareIntegrand (hβ : Differentiable ℝ β) (x : E) (s : ℝ) :
    HasFDerivAt (fun x => poincareIntegrand β x₀ x s) (poincareIntegrand' β x₀ x s) x := by
  have hy : HasFDerivAt (fun x : E => x₀ + s • (x - x₀)) (s • ContinuousLinearMap.id ℝ E) x :=
    (((hasFDerivAt_id x).sub_const x₀).const_smul s).const_add x₀
  have hc : HasFDerivAt (fun x => β (x₀ + s • (x - x₀)))
      ((fderiv ℝ β (x₀ + s • (x - x₀))).comp (s • ContinuousLinearMap.id ℝ E)) x :=
    (hβ (x₀ + s • (x - x₀))).hasFDerivAt.comp x hy
  have hu : HasFDerivAt (fun x : E => x - x₀) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const x₀
  have h := (hc.clm_apply hu).const_smul s
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  simp only [poincareIntegrand', smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
theorem continuous_poincareIntegrand (hβ : Continuous β) :
    Continuous fun p : E × ℝ => poincareIntegrand β x₀ p.1 p.2 := by
  have hy : Continuous fun p : E × ℝ => x₀ + p.2 • (p.1 - x₀) :=
    continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))
  exact continuous_snd.smul ((hβ.comp hy).clm_apply (continuous_fst.sub continuous_const))

omit [FiniteDimensional ℝ E] in
theorem continuous_poincareIntegrand' (hβ : ContDiff ℝ 1 β) :
    Continuous fun p : E × ℝ => poincareIntegrand' β x₀ p.1 p.2 := by
  have hy : Continuous fun p : E × ℝ => x₀ + p.2 • (p.1 - x₀) :=
    continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))
  have happ : Continuous fun p : E × ℝ => ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (p.1 - x₀) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)).continuous.comp (continuous_fst.sub continuous_const)
  exact continuous_snd.smul ((continuous_snd.smul
    (happ.clm_comp ((hβ.continuous_fderiv one_ne_zero).comp hy))).add (hβ.continuous.comp hy))

/-- **Differentiation under the integral sign** for the homotopy formula. -/
theorem hasFDerivAt_poincare (hβ : ContDiff ℝ 1 β) (z : E) :
    HasFDerivAt (poincare β x₀) (∫ s in (0:ℝ)..1, poincareIntegrand' β x₀ z s) z := by
  have hc := continuous_poincareIntegrand β x₀ hβ.continuous
  have hc' := continuous_poincareIntegrand' β x₀ hβ
  have hsec : ∀ x : E, Continuous fun s : ℝ => (x, s) := fun x =>
    continuous_const.prodMk continuous_id
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_Icc (a := (0:ℝ)) (b := 1))).exists_bound_of_continuousOn
    hc'.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (bound := fun _ => C) (ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall fun x => (hc.comp (hsec x)).aestronglyMeasurable)
    ((hc.comp (hsec z)).intervalIntegrable 0 1)
    ((hc'.comp (hsec z)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s hs x hx => ?_) intervalIntegrable_const
    (Filter.Eventually.of_forall fun s _ x _ =>
      hasFDerivAt_poincareIntegrand β x₀ (hβ.differentiable one_ne_zero) x s)
  rw [Set.uIoc_of_le zero_le_one] at hs
  exact hC (x, s) ⟨ball_subset_closedBall hx, Ioc_subset_Icc_self hs⟩

theorem contDiff_poincare (hβ : ContDiff ℝ 1 β) : ContDiff ℝ 1 (poincare β x₀) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun z => (hasFDerivAt_poincare β x₀ hβ z).differentiableAt, ?_⟩
  have h : fderiv ℝ (poincare β x₀) = fun z => ∫ s in (0:ℝ)..1, poincareIntegrand' β x₀ z s :=
    funext fun z => (hasFDerivAt_poincare β x₀ hβ z).fderiv
  rw [h]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z s => poincareIntegrand' β x₀ z s) (continuous_poincareIntegrand' β x₀ hβ) 0 1

omit [FiniteDimensional ℝ E] in
theorem poincare_self : poincare β x₀ x₀ = 0 := by
  simp [poincare, poincareIntegrand]

/-- **The Poincaré lemma**: `dα = β` for a closed alternating `β`. -/
theorem poincare_d (hβ : ContDiff ℝ 1 β) (halt : ∀ x v w, β x v w = -β x w v)
    (hclosed : ∀ x u v w,
      fderiv ℝ β x u v w - fderiv ℝ β x v u w + fderiv ℝ β x w u v = 0) (x a b : E) :
    fderiv ℝ (poincare β x₀) x a b - fderiv ℝ (poincare β x₀) x b a = β x a b := by
  rw [(hasFDerivAt_poincare β x₀ hβ x).fderiv]
  have hc' := continuous_poincareIntegrand' β x₀ hβ
  have hsec : Continuous fun s : ℝ => poincareIntegrand' β x₀ x s :=
    hc'.comp (continuous_const.prodMk continuous_id)
  have hint : IntervalIntegrable (fun s => poincareIntegrand' β x₀ x s) volume 0 1 :=
    hsec.intervalIntegrable 0 1
  have hinta : ∀ v, IntervalIntegrable (fun s => poincareIntegrand' β x₀ x s v) volume 0 1 :=
    fun v => (hsec.clm_apply continuous_const).intervalIntegrable 0 1
  have hintab : ∀ v w, IntervalIntegrable (fun s => poincareIntegrand' β x₀ x s v w) volume 0 1 :=
    fun v w => ((hsec.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hint a,
    ContinuousLinearMap.intervalIntegral_apply (hinta a) b,
    ContinuousLinearMap.intervalIntegral_apply hint b,
    ContinuousLinearMap.intervalIntegral_apply (hinta b) a,
    ← intervalIntegral.integral_sub (hintab a b) (hintab b a)]
  set y : ℝ → E := fun s => x₀ + s • (x - x₀) with hy
  have hyd : ∀ s, HasDerivAt y (x - x₀) s := fun s => by
    have h := ((hasDerivAt_id' s).smul_const (x - x₀)).const_add x₀
    rw [one_smul] at h
    exact h
  have hβd : Differentiable ℝ β := hβ.differentiable one_ne_zero
  have hβy : ∀ s, HasDerivAt (fun s => β (y s) a b) (fderiv ℝ β (y s) (x - x₀) a b) s :=
    fun s => by
      have h := (((hβd (y s)).hasFDerivAt.comp_hasDerivAt s (hyd s)).clm_apply
        (hasDerivAt_const s a)).clm_apply (hasDerivAt_const s b)
      simpa using h
  have hderiv : ∀ s, HasDerivAt (fun s => s * s * β (y s) a b)
      ((s + s) * β (y s) a b + s * s * fderiv ℝ β (y s) (x - x₀) a b) s := fun s => by
    exact (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).mul (hβy s)).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have hcontd : Continuous fun s =>
      (s + s) * β (y s) a b + s * s * fderiv ℝ β (y s) (x - x₀) a b := by
    have hyc : Continuous y := continuous_const.add (continuous_id.smul continuous_const)
    have h1 : Continuous fun s => β (y s) a b :=
      ((hβ.continuous.comp hyc).clm_apply continuous_const).clm_apply continuous_const
    have h2 : Continuous fun s => fderiv ℝ β (y s) (x - x₀) a b :=
      ((((hβ.continuous_fderiv one_ne_zero).comp hyc).clm_apply continuous_const).clm_apply
        continuous_const).clm_apply continuous_const
    exact ((continuous_id.add continuous_id).mul h1).add
      ((continuous_id.mul continuous_id).mul h2)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s _ => hderiv s) (hcontd.intervalIntegrable 0 1)
  calc ∫ s in (0:ℝ)..1, (poincareIntegrand' β x₀ x s a b - poincareIntegrand' β x₀ x s b a)
      = ∫ s in (0:ℝ)..1, ((s + s) * β (y s) a b + s * s * fderiv ℝ β (y s) (x - x₀) a b) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [poincareIntegrand'_apply]
        have h1 := hclosed (y s) (x - x₀) a b
        have h2 := halt (y s) b a
        show s * (s * fderiv ℝ β (y s) a (x - x₀) b + β (y s) a b)
            - s * (s * fderiv ℝ β (y s) b (x - x₀) a + β (y s) b a)
          = (s + s) * β (y s) a b + s * s * fderiv ℝ β (y s) (x - x₀) a b
        linear_combination (-(s * s)) * h1 - s * h2
    _ = β x a b := by
        rw [hftc]
        simp [hy]

end Poincare

/-! ### Moser's vector field -/

section Moser

set_option maxSynthPendingDepth 3

variable (Ω : E → E →L[ℝ] E →L[ℝ] ℝ) (x₀ : E)

/-- The linear path of forms `Ω_t(y) = Ω y + t (Ω x₀ − Ω y)`, as a function of
`p = (y, t)`. -/
noncomputable def pathForm (p : E × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  Ω p.1 + p.2 • (Ω x₀ - Ω p.1)

/-- The primitive `α` of `Ω − Ω x₀` given by the Poincaré lemma. -/
noncomputable def primitive : E → E →L[ℝ] ℝ :=
  poincare (fun y => Ω y - Ω x₀) x₀

/-- Moser's vector field `X_t(y) = Ω_t(y)⁻¹ α_y`. -/
noncomputable def moserField (p : E × ℝ) : E :=
  (pathForm Ω x₀ p).inverse (primitive Ω x₀ p.1)

/-- The set where `Ω_t(y)` is invertible. -/
def goodSet : Set (E × ℝ) := {p | (pathForm Ω x₀ p).IsInvertible}

omit [FiniteDimensional ℝ E] in
theorem pathForm_base (t : ℝ) : pathForm Ω x₀ (x₀, t) = Ω x₀ := by
  simp [pathForm]

omit [FiniteDimensional ℝ E] in
theorem pathForm_zero (y : E) : pathForm Ω x₀ (y, 0) = Ω y := by
  simp [pathForm]

omit [FiniteDimensional ℝ E] in
theorem pathForm_one (y : E) : pathForm Ω x₀ (y, 1) = Ω x₀ := by
  simp [pathForm]

omit [FiniteDimensional ℝ E] in
theorem contDiff_pathForm (hΩ : ContDiff ℝ 1 Ω) : ContDiff ℝ 1 (pathForm Ω x₀) :=
  (hΩ.comp contDiff_fst).add (contDiff_snd.smul (contDiff_const.sub (hΩ.comp contDiff_fst)))

theorem contDiff_primitive (hΩ : ContDiff ℝ 1 Ω) : ContDiff ℝ 1 (primitive Ω x₀) :=
  contDiff_poincare _ x₀ (hΩ.sub contDiff_const)

omit [FiniteDimensional ℝ E] in
theorem primitive_base : primitive Ω x₀ x₀ = 0 :=
  poincare_self _ x₀

/-- `dα = Ω − Ω x₀`. -/
theorem primitive_d (hΩ : ContDiff ℝ 1 Ω) (halt : ∀ y v w, Ω y v w = -Ω y w v)
    (hclosed : ∀ y u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0) (y a b : E) :
    fderiv ℝ (primitive Ω x₀) y a b - fderiv ℝ (primitive Ω x₀) y b a
      = Ω y a b - Ω x₀ a b := by
  have hd : ∀ z, fderiv ℝ (fun y => Ω y - Ω x₀) z = fderiv ℝ Ω z := fun z =>
    fderiv_sub_const (Ω x₀)
  have h := poincare_d (fun y => Ω y - Ω x₀) x₀ (hΩ.sub contDiff_const)
    (fun z v w => by
      simp only [sub_apply]
      linear_combination halt z v w - halt x₀ v w)
    (fun z u v w => by rw [hd]; exact hclosed z u v w) y a b
  simpa [primitive] using h

/-- `Ω x₀` is an isomorphism `E ≃ E*`, by nondegeneracy and finite dimension. -/
theorem exists_equiv_base (hnd : ∀ v, (∀ w, Ω x₀ v w = 0) → v = 0) :
    ∃ e : E ≃L[ℝ] (E →L[ℝ] ℝ), (e : E →L[ℝ] E →L[ℝ] ℝ) = Ω x₀ := by
  have hinj : Function.Injective (Ω x₀) := by
    intro v w h
    refine sub_eq_zero.mp (hnd (v - w) fun u => ?_)
    simp [h]
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq,
      Module.finrank_linearMap_self]
  refine ⟨(LinearMap.linearEquivOfInjective (Ω x₀ : E →ₗ[ℝ] (E →L[ℝ] ℝ)) hinj
    hdim).toContinuousLinearEquiv, ?_⟩
  ext v
  rfl

theorem isOpen_goodSet (hΩ : ContDiff ℝ 1 Ω) : IsOpen (goodSet Ω x₀) :=
  ContinuousLinearEquiv.isOpen.preimage (contDiff_pathForm Ω x₀ hΩ).continuous

omit [FiniteDimensional ℝ E] in
theorem base_mem_goodSet {e : E ≃L[ℝ] (E →L[ℝ] ℝ)}
    (he : (e : E →L[ℝ] E →L[ℝ] ℝ) = Ω x₀) (t : ℝ) : (x₀, t) ∈ goodSet Ω x₀ :=
  ⟨e, by rw [he, pathForm_base]⟩

omit [FiniteDimensional ℝ E] in
theorem pathForm_moserField {p : E × ℝ} (hp : p ∈ goodSet Ω x₀) :
    pathForm Ω x₀ p (moserField Ω x₀ p) = primitive Ω x₀ p.1 := by
  obtain ⟨A, hA⟩ := hp
  simp [moserField, ← hA]

omit [FiniteDimensional ℝ E] in
theorem moserField_base (t : ℝ) : moserField Ω x₀ (x₀, t) = 0 := by
  simp [moserField, primitive_base]

theorem contDiffAt_moserField (hΩ : ContDiff ℝ 1 Ω) {p : E × ℝ} (hp : p ∈ goodSet Ω x₀) :
    ContDiffAt ℝ 1 (moserField Ω x₀) p := by
  obtain ⟨A, hA⟩ := hp
  have h1 : ContDiffAt ℝ 1 (fun q => (pathForm Ω x₀ q).inverse) p := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := 1) A
    rw [hA] at h
    exact h.comp p (contDiff_pathForm Ω x₀ hΩ).contDiffAt
  exact h1.clm_apply ((contDiff_primitive Ω x₀ hΩ).comp contDiff_fst).contDiffAt

/-- A smooth function of time, `1` on `[−1/2, 3/2]` and `0` outside `[−1, 2]`. -/
noncomputable def timeCutoff (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t + 2) * Real.smoothTransition (4 - 2 * t)

theorem contDiff_timeCutoff : ContDiff ℝ 1 timeCutoff :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

theorem timeCutoff_eq_one {t : ℝ} (ht : t ∈ Icc (-1 / 2 : ℝ) (3 / 2)) : timeCutoff t = 1 := by
  rw [timeCutoff, Real.smoothTransition.one_of_one_le (show 1 ≤ 2 * t + 2 by linarith [ht.1]),
    Real.smoothTransition.one_of_one_le (show 1 ≤ 4 - 2 * t by linarith [ht.2]), one_mul]

theorem timeCutoff_eq_zero {t : ℝ} (ht : t ∉ Icc (-1 : ℝ) 2) : timeCutoff t = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [timeCutoff, Real.smoothTransition.zero_of_nonpos (show 2 * t + 2 ≤ 0 by linarith),
      zero_mul]
  · rw [timeCutoff, Real.smoothTransition.zero_of_nonpos (show 4 - 2 * t ≤ 0 by linarith),
      mul_zero]

/-- **The cut-off suspended Moser field.**  A globally Lipschitz `C¹` field `F` on
`E × ℝ` whose time component is `1`, which vanishes in space along `{x₀} × ℝ`,
and which is `(X_t, 1)` near every `(y, t)` with `y` close to `x₀` and
`t ∈ [0, 1]`. -/
theorem exists_vectorField (hΩ : ContDiff ℝ 1 Ω)
    (hnd : ∀ v, (∀ w, Ω x₀ v w = 0) → v = 0) :
    ∃ (F : E × ℝ → E × ℝ) (K : ℝ≥0) (ε : ℝ), 0 < ε ∧ ContDiff ℝ 1 F ∧ LipschitzWith K F ∧
      (∀ q, (F q).2 = 1) ∧ (∀ t, F (x₀, t) = (0, 1)) ∧
      ∀ y ∈ ball x₀ ε, ∀ t ∈ Icc (0:ℝ) 1,
        (y, t) ∈ goodSet Ω x₀ ∧ F =ᶠ[𝓝 (y, t)] fun q => (moserField Ω x₀ q, 1) := by
  obtain ⟨e, he⟩ := exists_equiv_base Ω x₀ hnd
  have hG := isOpen_goodSet Ω x₀ hΩ
  have hsub : ({x₀} : Set E) ×ˢ Icc (-1 : ℝ) 2 ⊆ goodSet Ω x₀ := by
    rintro ⟨y, t⟩ ⟨hy, -⟩
    have hy' : y = x₀ := hy
    rw [hy']
    exact base_mem_goodSet Ω x₀ he t
  obtain ⟨U, V, hU, hV, hxU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hG hsub
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x₀ (hxU (mem_singleton x₀))
  let χ₁ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hK : closedBall x₀ (r / 2) ×ˢ Icc (-1 : ℝ) 2 ⊆ goodSet Ω x₀ := fun q hq =>
    hUV ⟨hrU (closedBall_subset_ball (by linarith) hq.1), hIV hq.2⟩
  obtain ⟨g, hg⟩ : ∃ g : E × ℝ → E,
      ∀ q, g q = (χ₁ q.1 * timeCutoff q.2) • moserField Ω x₀ q := ⟨_, fun _ => rfl⟩
  have hχc : ContDiff ℝ 1 fun q : E × ℝ => χ₁ q.1 * timeCutoff q.2 :=
    (χ₁.contDiff.comp contDiff_fst).mul (contDiff_timeCutoff.comp contDiff_snd)
  have hzero : ∀ q ∉ closedBall x₀ (r / 2) ×ˢ Icc (-1 : ℝ) 2,
      χ₁ q.1 * timeCutoff q.2 = 0 := by
    intro q hq
    rw [mem_prod, not_and_or] at hq
    rcases hq with hq | hq
    · have h1 : χ₁ q.1 = 0 := χ₁.zero_of_le_dist (by
        rw [mem_closedBall, not_le] at hq
        exact hq.le)
      rw [h1, zero_mul]
    · rw [timeCutoff_eq_zero hq, mul_zero]
  have hgc : ContDiff ℝ 1 g := by
    refine contDiff_iff_contDiffAt.mpr fun q => ?_
    by_cases hq : q ∈ goodSet Ω x₀
    · rw [show g = fun q => (χ₁ q.1 * timeCutoff q.2) • moserField Ω x₀ q from funext hg]
      exact hχc.contDiffAt.smul (contDiffAt_moserField Ω x₀ hΩ hq)
    · have hq' : q ∉ closedBall x₀ (r / 2) ×ˢ Icc (-1 : ℝ) 2 := fun h => hq (hK h)
      have hcl : IsClosed (closedBall x₀ (r / 2) ×ˢ Icc (-1 : ℝ) 2) :=
        isClosed_closedBall.prod isClosed_Icc
      have hev : g =ᶠ[𝓝 q] fun _ => 0 := by
        filter_upwards [hcl.isOpen_compl.mem_nhds hq'] with z hz
        rw [hg, hzero z hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hgs : HasCompactSupport g :=
    HasCompactSupport.intro ((isCompact_closedBall x₀ (r / 2)).prod isCompact_Icc)
      fun q hq => by rw [hg, hzero q hq, zero_smul]
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgs hgc one_ne_zero
  refine ⟨fun q => (g q, 1), max C 0, r / 4, by positivity, hgc.prodMk contDiff_const,
    hC.prodMk (LipschitzWith.const 1), fun q => rfl, fun t => ?_, fun y hy t ht => ?_⟩
  · show (g (x₀, t), (1 : ℝ)) = (0, 1)
    rw [hg, moserField_base, smul_zero]
  · have hyt : (y, t) ∈ goodSet Ω x₀ :=
      hUV ⟨hrU (ball_subset_ball (by linarith) hy), hIV ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    refine ⟨hyt, ?_⟩
    have h1 : ∀ᶠ z in 𝓝 y, χ₁ z = 1 := χ₁.eventuallyEq_one_of_mem_ball hy
    have h2 : ∀ᶠ s in 𝓝 t, timeCutoff s = 1 := by
      filter_upwards [Ioo_mem_nhds (show (-1 / 2 : ℝ) < t by linarith [ht.1])
        (show t < 3 / 2 by linarith [ht.2])] with s hs
      exact timeCutoff_eq_one ⟨hs.1.le, hs.2.le⟩
    filter_upwards [h1.prod_nhds h2] with q hq
    simp only [hg, hq.1, hq.2, one_mul, one_smul]

/-! ### Invariance along Moser's flow -/

/-- **Moser's argument.**  There is a `C¹` map `ψ` with
`Ω x₀ (Dψ(x) a) (Dψ(x) b) = Ω x a b` for every `x` near `x₀`. -/
theorem exists_pullback (hΩ : ContDiff ℝ 1 Ω) (halt : ∀ y v w, Ω y v w = -Ω y w v)
    (hnd : ∀ v, (∀ w, Ω x₀ v w = 0) → v = 0)
    (hclosed : ∀ y u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0) :
    ∃ ψ : E → E, ContDiff ℝ 1 ψ ∧ ∃ ρ > 0, ∀ x ∈ ball x₀ ρ, ∀ a b : E,
      Ω x₀ (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = Ω x a b := by
  obtain ⟨F, K, ε, hε, hFc, hFl, hF2, hFbase, hFloc⟩ := exists_vectorField Ω x₀ hΩ hnd
  obtain ⟨Φ, hΦ0, hΦd, -, hΦc, hvar⟩ := FlowC1.exists_flow hFc hFl
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → E → E, ∀ t x, ψ t x = (Φ t (x, 0)).1 := ⟨_, fun _ _ => rfl⟩
  have hΩd : Differentiable ℝ Ω := hΩ.differentiable one_ne_zero
  have hΦcont : ∀ p, Continuous fun s => Φ s p := fun p =>
    continuous_iff_continuousAt.2 fun s => (hΦd s p).continuousAt
  -- the time coordinate of the flow is time
  have hsnd : ∀ t x, (Φ t (x, 0)).2 = t := by
    intro t x
    have hd : ∀ s, HasDerivAt (fun s => (Φ s (x, 0)).2 - s) 0 s := fun s =>
      ((hasFDerivAt_snd.comp_hasDerivAt s (hΦd s (x, 0))).sub (hasDerivAt_id' s)).congr_deriv
        (by simp [hF2])
    have h : (Φ t (x, 0)).2 - t = (Φ 0 (x, 0)).2 - 0 :=
      is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    simpa [hΦ0, sub_eq_zero] using h
  -- the orbit of the base point is `t ↦ (x₀, t)`
  have hbase : ∀ t, Φ t (x₀, 0) = (x₀, t) := fun t =>
    congrFun (FlowC1.eq_of_global hFl (α := fun s => Φ s (x₀, 0)) (β := fun s => (x₀, s))
      (fun s => hΦd s (x₀, 0))
      (fun s => by
        show HasDerivAt (fun s => (x₀, s)) (F (x₀, s)) s
        rw [hFbase]
        exact (hasDerivAt_const s x₀).prodMk (hasDerivAt_id' s))
      (t₀ := 0) (by simp [hΦ0])) t
  -- orbits starting near `x₀` stay near `x₀` up to time `1`
  have hlip : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, dist (ψ t x) x₀ ≤ dist x x₀ * Real.exp (K * t) := by
    intro t ht x
    have h := dist_le_of_trajectories_ODE (v := fun _ => F) (K := K) (a := 0) (b := 1)
      (fun _ => hFl) (hΦcont (x, 0)).continuousOn
      (fun s _ => (hΦd s (x, 0)).hasDerivWithinAt)
      (hΦcont (x₀, 0)).continuousOn (fun s _ => (hΦd s (x₀, 0)).hasDerivWithinAt)
      (le_refl (dist (Φ 0 (x, 0)) (Φ 0 (x₀, 0)))) t ht
    rw [hΦ0, hΦ0, hbase, sub_zero] at h
    calc dist (ψ t x) x₀ ≤ dist (Φ t (x, 0)) (x₀, t) := by
          rw [hψ, Prod.dist_eq]
          exact le_max_left _ _
      _ ≤ dist (x, (0:ℝ)) (x₀, 0) * Real.exp (K * t) := h
      _ ≤ dist x x₀ * Real.exp (K * t) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          rw [Prod.dist_eq]
          exact max_le le_rfl (by simp)
  set ρ : ℝ := ε / Real.exp K with hρ
  have hρpos : 0 < ρ := div_pos hε (Real.exp_pos _)
  have hstay : ∀ x ∈ ball x₀ ρ, ∀ t ∈ Icc (0:ℝ) 1, ψ t x ∈ ball x₀ ε := by
    intro x hx t ht
    rw [mem_ball] at hx ⊢
    have hKt : Real.exp (K * t) ≤ Real.exp K := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg
      linarith
    calc dist (ψ t x) x₀ ≤ dist x x₀ * Real.exp (K * t) := hlip t ht x
      _ ≤ dist x x₀ * Real.exp K := mul_le_mul_of_nonneg_left hKt dist_nonneg
      _ < ρ * Real.exp K := mul_lt_mul_of_pos_right hx (Real.exp_pos _)
      _ = ε := by rw [hρ]; field_simp
  refine ⟨ψ 1, ?_, ρ, hρpos, fun x hx a b => ?_⟩
  · rw [show ψ 1 = fun x => (Φ 1 (x, 0)).1 from funext (hψ 1)]
    exact contDiff_fst.comp ((hΦc 1).comp (contDiff_prodMk_left 0))
  -- the differential of the flow at `(x, 0)`, and of `ψ t` at `x`
  obtain ⟨M, hM⟩ : ∃ M : ℝ → (E × ℝ →L[ℝ] E × ℝ), ∀ t, M t = fderiv ℝ (Φ t) (x, 0) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ → (E →L[ℝ] E), ∀ t, A t = fderiv ℝ (ψ t) x := ⟨_, fun _ => rfl⟩
  have hΦdiff : ∀ t, Differentiable ℝ (Φ t) := fun t => (hΦc t).differentiable one_ne_zero
  have hψfd : ∀ t, HasFDerivAt (ψ t)
      ((ContinuousLinearMap.fst ℝ E ℝ).comp ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ))) x := by
    intro t
    rw [show ψ t = fun x => (Φ t (x, 0)).1 from funext (hψ t), hM]
    exact hasFDerivAt_fst.comp x
      ((hΦdiff t (x, 0)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x 0))
  have hAeq : ∀ t, A t
      = (ContinuousLinearMap.fst ℝ E ℝ).comp ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
    fun t => by rw [hA]; exact (hψfd t).fderiv
  have hMd : ∀ t, HasDerivAt M ((fderiv ℝ F (Φ t (x, 0))).comp (M t)) t := fun t => by
    rw [show M = fun s => fderiv ℝ (Φ s) (x, 0) from funext hM]
    exact hvar t (x, 0)
  -- the time component of the linearised flow stays zero
  have hFsnd : ∀ q, (ContinuousLinearMap.snd ℝ E ℝ).comp (fderiv ℝ F q) = 0 := fun q => by
    have h1 := hasFDerivAt_snd.comp q ((hFc.differentiable one_ne_zero) q).hasFDerivAt
    have h2 : HasFDerivAt (fun q => (F q).2) (0 : E × ℝ →L[ℝ] ℝ) q := by
      rw [show (fun q => (F q).2) = fun _ => (1 : ℝ) from funext hF2]
      exact hasFDerivAt_const 1 q
    exact h1.unique h2
  have hS : ∀ t,
      (ContinuousLinearMap.snd ℝ E ℝ).comp ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ)) = 0 := by
    have hSd : ∀ t, HasDerivAt (fun t => (ContinuousLinearMap.snd ℝ E ℝ).comp
        ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ))) 0 t := by
      intro t
      have h := (hasDerivAt_const t (ContinuousLinearMap.snd ℝ E ℝ)).clm_comp
        ((hMd t).clm_comp (hasDerivAt_const t (ContinuousLinearMap.inl ℝ E ℝ)))
      refine h.congr_deriv (ContinuousLinearMap.ext fun w => ?_)
      have hw := DFunLike.congr_fun (hFsnd (Φ t (x, 0))) (M t (w, 0))
      simpa using hw
    intro t
    have h : (ContinuousLinearMap.snd ℝ E ℝ).comp ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ))
        = (ContinuousLinearMap.snd ℝ E ℝ).comp ((M 0).comp (ContinuousLinearMap.inl ℝ E ℝ)) :=
      is_const_of_deriv_eq_zero (fun s => (hSd s).differentiableAt) (fun s => (hSd s).deriv) t 0
    rw [h, hM 0, show Φ 0 = id from funext hΦ0, fderiv_id]
    ext w
    simp
  have hMinl : ∀ t w, M t (w, 0) = (A t w, 0) := fun t w => by
    have h2 := DFunLike.congr_fun (hS t) w
    simp at h2
    refine Prod.ext ?_ h2
    rw [hAeq]
    simp
  have hAd : ∀ t, HasDerivAt A ((ContinuousLinearMap.fst ℝ E ℝ).comp
      ((fderiv ℝ F (Φ t (x, 0))).comp ((M t).comp (ContinuousLinearMap.inl ℝ E ℝ)))) t := by
    intro t
    have h := (hasDerivAt_const t (ContinuousLinearMap.fst ℝ E ℝ)).clm_comp
      ((hMd t).clm_comp (hasDerivAt_const t (ContinuousLinearMap.inl ℝ E ℝ)))
    rw [show A = fun s => (ContinuousLinearMap.fst ℝ E ℝ).comp
      ((M s).comp (ContinuousLinearMap.inl ℝ E ℝ)) from funext hAeq]
    refine h.congr_deriv (ContinuousLinearMap.ext fun w => ?_)
    simp
  have hq : ∀ t, Φ t (x, 0) = (ψ t x, t) := fun t => Prod.ext (hψ t x).symm (hsnd t x)
  -- the scalar `Ω_t(ψ_t x)(Dψ_t a, Dψ_t b)` has derivative zero on `[0, 1]`
  have hGd : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => pathForm Ω x₀ (ψ s x, s) (A s a) (A s b)) 0 t := by
    intro t ht
    obtain ⟨hgood, hloc⟩ := hFloc (ψ t x) (hstay x hx t ht) t ht
    have hXd : DifferentiableAt ℝ (moserField Ω x₀) (ψ t x, t) :=
      (contDiffAt_moserField Ω x₀ hΩ hgood).differentiableAt one_ne_zero
    -- the velocity of the flow is Moser's field
    have hv : HasDerivAt (fun s => ψ s x) (moserField Ω x₀ (ψ t x, t)) t := by
      have h := hasFDerivAt_fst.comp_hasDerivAt t (hΦd t (x, 0))
      rw [hq t, hloc.eq_of_nhds] at h
      rw [show (fun s => ψ s x) = fun s => (Φ s (x, 0)).1 from funext fun s => hψ s x]
      exact h
    -- the linearised field
    have hprod : fderiv ℝ F (ψ t x, t) = (fderiv ℝ (moserField Ω x₀) (ψ t x, t)).prod 0 := by
      rw [hloc.fderiv_eq]
      exact (hXd.hasFDerivAt.prodMk (hasFDerivAt_const (1:ℝ) (ψ t x, t))).fderiv
    have hAa : ∀ v, HasDerivAt (fun s => A s v)
        (fderiv ℝ (moserField Ω x₀) (ψ t x, t) (A t v, 0)) t := fun v => by
      have h := (hAd t).clm_apply (hasDerivAt_const t v)
      refine h.congr_deriv ?_
      simp [hMinl, hq, hprod]
    -- differentiating `Ω_t(X_t) = α` in space
    have hB : HasFDerivAt (fun y => moserField Ω x₀ (y, t))
        ((fderiv ℝ (moserField Ω x₀) (ψ t x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) (ψ t x) :=
      HasFDerivAt.comp (g := moserField Ω x₀) (f := fun y => (y, t)) (ψ t x) hXd.hasFDerivAt
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) (ψ t x) t)
    have hP : HasFDerivAt (fun y => pathForm Ω x₀ (y, t))
        (fderiv ℝ Ω (ψ t x) + t • (0 - fderiv ℝ Ω (ψ t x))) (ψ t x) :=
      (hΩd (ψ t x)).hasFDerivAt.add (((hasFDerivAt_const (Ω x₀) (ψ t x)).sub
        (hΩd (ψ t x)).hasFDerivAt).const_smul t)
    have hαfd : fderiv ℝ (primitive Ω x₀) (ψ t x)
        = (pathForm Ω x₀ (ψ t x, t)).comp
            ((fderiv ℝ (moserField Ω x₀) (ψ t x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
          + (fderiv ℝ Ω (ψ t x) + t • (0 - fderiv ℝ Ω (ψ t x))).flip
              (moserField Ω x₀ (ψ t x, t)) := by
      have hev : (fun y => pathForm Ω x₀ (y, t) (moserField Ω x₀ (y, t))) =ᶠ[𝓝 (ψ t x)]
          primitive Ω x₀ := by
        have hopen : (fun y => (y, t)) ⁻¹' goodSet Ω x₀ ∈ 𝓝 (ψ t x) :=
          (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
            ((isOpen_goodSet Ω x₀ hΩ).mem_nhds hgood)
        filter_upwards [hopen] with y hy
        exact pathForm_moserField Ω x₀ hy
      rw [← hev.fderiv_eq]
      exact (hP.clm_apply hB).fderiv
    have hstar : ∀ w v, fderiv ℝ (primitive Ω x₀) (ψ t x) w v
        = pathForm Ω x₀ (ψ t x, t) (fderiv ℝ (moserField Ω x₀) (ψ t x, t) (w, 0)) v
          + (fderiv ℝ Ω (ψ t x) w (moserField Ω x₀ (ψ t x, t)) v
            - t * fderiv ℝ Ω (ψ t x) w (moserField Ω x₀ (ψ t x, t)) v) := by
      intro w v
      rw [hαfd]
      simp
      ring
    have hPalt : ∀ v w, pathForm Ω x₀ (ψ t x, t) v w = -pathForm Ω x₀ (ψ t x, t) w v := by
      intro v w
      simp only [pathForm, add_apply, smul_apply, sub_apply, smul_eq_mul]
      linear_combination halt (ψ t x) v w + t * (halt x₀ v w - halt (ψ t x) v w)
    -- the time derivative of `Ω_t(ψ_t x)`
    have hΩψ : HasDerivAt (fun s => Ω (ψ s x))
        (fderiv ℝ Ω (ψ t x) (moserField Ω x₀ (ψ t x, t))) t :=
      (hΩd (ψ t x)).hasFDerivAt.comp_hasDerivAt t hv
    have hc : HasDerivAt (fun s => pathForm Ω x₀ (ψ s x, s))
        (fderiv ℝ Ω (ψ t x) (moserField Ω x₀ (ψ t x, t))
          + (t • (0 - fderiv ℝ Ω (ψ t x) (moserField Ω x₀ (ψ t x, t)))
            + (1:ℝ) • (Ω x₀ - Ω (ψ t x)))) t :=
      hΩψ.add ((hasDerivAt_id' t).smul ((hasDerivAt_const t (Ω x₀)).sub hΩψ))
    have hG := (hc.clm_apply (hAa a)).clm_apply (hAa b)
    refine hG.congr_deriv ?_
    have hs1 := hstar (A t a) (A t b)
    have hs2 := hstar (A t b) (A t a)
    have hal := hPalt (A t a) (fderiv ℝ (moserField Ω x₀) (ψ t x, t) (A t b, 0))
    have hcl := hclosed (ψ t x) (moserField Ω x₀ (ψ t x, t)) (A t a) (A t b)
    have hpo := primitive_d Ω x₀ hΩ halt hclosed (ψ t x) (A t a) (A t b)
    simp only [add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul, one_mul]
    linear_combination -hs1 + hs2 + hal + (1 - t) * hcl + hpo
  have hGcont : ContinuousOn (fun s => pathForm Ω x₀ (ψ s x, s) (A s a) (A s b)) (Icc 0 1) :=
    fun s hs => (hGd s hs).continuousAt.continuousWithinAt
  have hconst : pathForm Ω x₀ (ψ 1 x, 1) (A 1 a) (A 1 b)
      = pathForm Ω x₀ (ψ 0 x, 0) (A 0 a) (A 0 b) :=
    constant_of_has_deriv_right_zero hGcont
      (fun s hs => (hGd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  have hψ0 : ∀ y, ψ 0 y = y := fun y => by rw [hψ, hΦ0]
  have hA0 : A 0 = ContinuousLinearMap.id ℝ E := by
    rw [hA 0, show ψ 0 = id from funext hψ0, fderiv_id]
  rw [pathForm_one, hψ0 x, pathForm_zero, hA0, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.id_apply, hA 1] at hconst
  exact hconst

/-- **Darboux's theorem**, local model, for a `C¹` field of continuous bilinear
forms. -/
theorem darboux (hΩ : ContDiff ℝ 1 Ω) (halt : ∀ y v w, Ω y v w = -Ω y w v)
    (hnd : ∀ v, (∀ w, Ω x₀ v w = 0) → v = 0)
    (hclosed : ∀ y u v w,
      fderiv ℝ Ω y u v w - fderiv ℝ Ω y v u w + fderiv ℝ Ω y w u v = 0) :
    ∃ φ : OpenPartialHomeomorph E E, x₀ ∈ φ.source ∧
      ∀ x ∈ φ.source, ∀ u v : E, Ω x₀ (fderiv ℝ φ x u) (fderiv ℝ φ x v) = Ω x u v := by
  obtain ⟨ψ, hψc, ρ, hρ, hinv⟩ := exists_pullback Ω x₀ hΩ halt hnd hclosed
  have hinj : Function.Injective (fderiv ℝ ψ x₀) := by
    intro a a' h
    refine sub_eq_zero.mp (hnd (a - a') fun b => ?_)
    have h1 := hinv x₀ (mem_ball_self hρ) (a - a') b
    rw [map_sub, h, sub_self, map_zero, zero_apply] at h1
    exact h1.symm
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ ψ x₀ : E →ₗ[ℝ] E) hinj).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = fderiv ℝ ψ x₀ := ContinuousLinearMap.ext fun v => rfl
  have hstrict : HasStrictFDerivAt ψ (e : E →L[ℝ] E) x₀ := by
    rw [he]
    exact hψc.contDiffAt.hasStrictFDerivAt' ((hψc.differentiable one_ne_zero) x₀).hasFDerivAt
      one_ne_zero
  refine ⟨(hstrict.toOpenPartialHomeomorph ψ).restrOpen (ball x₀ ρ) isOpen_ball, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, mem_ball_self hρ⟩
  · intro x hx u v
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    simp only [OpenPartialHomeomorph.coe_restrOpen, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    exact hinv x hx.2 u v

end Moser

end Darboux
end MorseFloer
