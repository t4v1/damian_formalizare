import MorseFloer.Part2.Ch5
import MorseFloer.Part2.CauchyHolder

/-!
# Regularity for the Floer equation

`Part2/CauchyHolder.lean` proves elliptic regularity for a system `∂̄u_i = G_i (z, u)` on `ℂ`,
with `u : ℂ → ℂⁿ`.  Chapter 6 writes the Floer equation in real form, for
`u : ℝ → ℝ → ℝ^{2n}` with `∂u/∂s + J₀ ∂u/∂t + ∇H_t(u) = 0`.  This file is the dictionary
between the two: the identification `ℝ^{2n} ≅ ℂⁿ` under which `J₀` is multiplication by `i`,
and the passage from partial derivatives to Fréchet differentiability.

## Main results

* `contDiff_one_of_partials`: continuous partial derivatives give a `C¹` function of two real
  variables;
* `contDiff_infty_of_floer`: a `C¹` solution of the real Floer equation with a smooth
  nonlinearity is `C^∞`.
-/

open Filter Topology Metric Set
open scoped Real ContDiff

namespace MorseFloer
namespace FloerRegularity

open CauchyPompeiu CauchyHolder Chapter5

/-! ### From partial derivatives to `C¹` -/

theorem continuous_coprod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Continuous fun q : (ℝ →L[ℝ] F) × (ℝ →L[ℝ] F) => q.1.coprod q.2 := by
  refine LipschitzWith.continuous (K := 2) (LipschitzWith.of_dist_le_mul fun q q' => ?_)
  rw [dist_eq_norm, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have happ : (q.1.coprod q.2 - q'.1.coprod q'.2) h = (q.1 - q'.1) h.1 + (q.2 - q'.2) h.2 := by
    simp only [sub_apply, ContinuousLinearMap.coprod_apply]
    abel
  rw [happ]
  have h1 : ‖(q.1 - q'.1) h.1‖ ≤ ‖q.1 - q'.1‖ * ‖h‖ :=
    le_trans ((q.1 - q'.1).le_opNorm h.1)
      (mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_of_eq (Prod.norm_mk h.1 h.2).symm))
        (norm_nonneg _))
  have h2 : ‖(q.2 - q'.2) h.2‖ ≤ ‖q.2 - q'.2‖ * ‖h‖ :=
    le_trans ((q.2 - q'.2).le_opNorm h.2)
      (mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _)
        (le_of_eq (Prod.norm_mk h.1 h.2).symm)) (norm_nonneg _))
  have h3 : ‖q.1 - q'.1‖ ≤ max ‖q.1 - q'.1‖ ‖q.2 - q'.2‖ := le_max_left _ _
  have h4 : ‖q.2 - q'.2‖ ≤ max ‖q.1 - q'.1‖ ‖q.2 - q'.2‖ := le_max_right _ _
  have h5 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  calc ‖(q.1 - q'.1) h.1 + (q.2 - q'.2) h.2‖
      ≤ ‖(q.1 - q'.1) h.1‖ + ‖(q.2 - q'.2) h.2‖ := norm_add_le _ _
    _ ≤ ‖q.1 - q'.1‖ * ‖h‖ + ‖q.2 - q'.2‖ * ‖h‖ := by linarith
    _ ≤ 2 * max ‖q.1 - q'.1‖ ‖q.2 - q'.2‖ * ‖h‖ := by nlinarith

/-- **Continuous partial derivatives give a `C¹` function.** -/
theorem contDiff_one_of_partials {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u us ut : ℝ → ℝ → F}
    (hs : ∀ s t, HasDerivAt (fun σ => u σ t) (us s t) s)
    (ht : ∀ s t, HasDerivAt (u s) (ut s t) t)
    (hcs : Continuous fun p : ℝ × ℝ => us p.1 p.2)
    (hct : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    ContDiff ℝ 1 fun p : ℝ × ℝ => u p.1 p.2 := by
  have hsmul : Continuous fun v : F => (1 : ℝ →L[ℝ] ℝ).smulRight v :=
    (ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).continuous
  have hc₁ : Continuous fun p : ℝ × ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight (us p.1 p.2) :=
    hsmul.comp hcs
  have hc₂ : Continuous fun p : ℝ × ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight (ut p.1 p.2) :=
    hsmul.comp hct
  have hd : ∀ p : ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => u q.1 q.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (us p.1 p.2)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ut p.1 p.2))) p := by
    intro p
    have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := u)
      (f₁ := fun s t => (1 : ℝ →L[ℝ] ℝ).smulRight (us s t))
      (f₂ := fun s t => (1 : ℝ →L[ℝ] ℝ).smulRight (ut s t)) (u := p)
      (Eventually.of_forall fun v => (hs v.1 v.2).hasFDerivAt)
      (Eventually.of_forall fun v => (ht v.1 v.2).hasFDerivAt)
      hc₁.continuousAt hc₂.continuousAt
    exact h.hasFDerivAt
  refine contDiff_one_iff_fderiv.2 ⟨fun p => (hd p).differentiableAt, ?_⟩
  have hfd : fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2)
      = fun p : ℝ × ℝ => ((1 : ℝ →L[ℝ] ℝ).smulRight (us p.1 p.2)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ut p.1 p.2)) := funext fun p => (hd p).fderiv
  rw [hfd]
  exact continuous_coprod.comp (hc₁.prodMk hc₂)

/-- The derivative of a function of two real variables, in the two coordinate directions. -/
theorem fderiv_apply_of_partials {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u us ut : ℝ → ℝ → F}
    (hs : ∀ s t, HasDerivAt (fun σ => u σ t) (us s t) s)
    (ht : ∀ s t, HasDerivAt (u s) (ut s t) t)
    (hcs : Continuous fun p : ℝ × ℝ => us p.1 p.2)
    (hct : Continuous fun p : ℝ × ℝ => ut p.1 p.2) (p h : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) p h = h.1 • us p.1 p.2 + h.2 • ut p.1 p.2 := by
  have hsmul : Continuous fun v : F => (1 : ℝ →L[ℝ] ℝ).smulRight v :=
    (ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).continuous
  have hd : HasFDerivAt (fun q : ℝ × ℝ => u q.1 q.2)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (us p.1 p.2)).coprod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ut p.1 p.2))) p := by
    have h' := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := u)
      (f₁ := fun s t => (1 : ℝ →L[ℝ] ℝ).smulRight (us s t))
      (f₂ := fun s t => (1 : ℝ →L[ℝ] ℝ).smulRight (ut s t)) (u := p)
      (Eventually.of_forall fun v => (hs v.1 v.2).hasFDerivAt)
      (Eventually.of_forall fun v => (ht v.1 v.2).hasFDerivAt)
      (hsmul.comp hcs).continuousAt (hsmul.comp hct).continuousAt
    exact h'.hasFDerivAt
  rw [hd.fderiv]
  simp

/-! ### The identification `ℝ^{2n} ≅ ℂⁿ` -/

variable {l : Type*} [Fintype l] [DecidableEq l]

/-- The identification of `ℝ^{2n}` with `ℂⁿ`, as a linear map. -/
noncomputable def toCpxₗ : ((l ⊕ l) → ℝ) →ₗ[ℝ] (l → ℂ) where
  toFun X := fun i => (X (Sum.inl i) : ℂ) + (X (Sum.inr i) : ℂ) * Complex.I
  map_add' X Y := by
    funext i
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring
  map_smul' c X := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

/-- The identification of `ℝ^{2n}` with `ℂⁿ`, under which `J₀` is multiplication by `i`. -/
noncomputable def toCpxL : ((l ⊕ l) → ℝ) →L[ℝ] (l → ℂ) := LinearMap.toContinuousLinearMap toCpxₗ

omit [DecidableEq l] in
theorem toCpxL_apply (X : (l ⊕ l) → ℝ) (i : l) :
    toCpxL X i = (X (Sum.inl i) : ℂ) + (X (Sum.inr i) : ℂ) * Complex.I := rfl

/-- The inverse identification. -/
noncomputable def ofCpxₗ : (l → ℂ) →ₗ[ℝ] ((l ⊕ l) → ℝ) where
  toFun Y := Sum.elim (fun i => (Y i).re) fun i => (Y i).im
  map_add' Y Z := by
    funext j
    cases j with
    | inl i => simp
    | inr i => simp
  map_smul' c Y := by
    funext j
    cases j with
    | inl i => simp
    | inr i => simp

noncomputable def ofCpxL : (l → ℂ) →L[ℝ] ((l ⊕ l) → ℝ) := LinearMap.toContinuousLinearMap ofCpxₗ

omit [DecidableEq l] in
theorem ofCpxL_apply (Y : l → ℂ) :
    ofCpxL Y = Sum.elim (fun i => (Y i).re) fun i => (Y i).im := rfl

omit [DecidableEq l] in
@[simp]
theorem ofCpxL_toCpxL (X : (l ⊕ l) → ℝ) : ofCpxL (toCpxL X) = X := by
  funext j
  cases j with
  | inl i => simp [ofCpxL_apply, toCpxL_apply]
  | inr i => simp [ofCpxL_apply, toCpxL_apply]

omit [DecidableEq l] in
@[simp]
theorem toCpxL_ofCpxL (Y : l → ℂ) : toCpxL (ofCpxL Y) = Y := by
  funext i
  rw [toCpxL_apply, ofCpxL_apply]
  simp only [Sum.elim_inl, Sum.elim_inr]
  exact Complex.re_add_im (Y i)

/-- **The standard complex structure becomes multiplication by `i`.** -/
theorem toCpxL_stdJ (X : (l ⊕ l) → ℝ) (i : l) :
    toCpxL (stdJ l X) i = Complex.I * toCpxL X i := by
  have hX : X = Sum.elim (X ∘ Sum.inl) (X ∘ Sum.inr) := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => rfl
  have hmul : stdJ l X = Sum.elim (fun i => -(X (Sum.inr i))) fun i => X (Sum.inl i) := by
    rw [stdJ_apply, Matrix.J]
    conv_lhs => rw [hX]
    rw [Matrix.fromBlocks_mulVec]
    funext j
    cases j with
    | inl i => simp [Matrix.neg_mulVec]
    | inr i => simp
  rw [toCpxL_apply, toCpxL_apply, hmul]
  simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_neg]
  linear_combination (-(X (Sum.inr i) : ℂ)) * Complex.I_sq

/-! ### Regularity for the real Floer equation -/

/-- **A `C¹` solution of the Floer equation is `C^∞`.**  The equation
`∂u/∂s + J₀ ∂u/∂t + N_t(u) = 0` on `ℝ^{2n}` becomes, under the identification with `ℂⁿ`, the
system `∂̄u_i = G_i (z, u)` on `ℂ`, to which the elliptic bootstrap applies. -/
theorem contDiff_infty_of_floer {u us ut : ℝ → ℝ → ((l ⊕ l) → ℝ)}
    {N : ℝ → ((l ⊕ l) → ℝ) → ((l ⊕ l) → ℝ)}
    (hs : ∀ s t, HasDerivAt (fun σ => u σ t) (us s t) s)
    (ht : ∀ s t, HasDerivAt (u s) (ut s t) t)
    (hcs : Continuous fun p : ℝ × ℝ => us p.1 p.2)
    (hct : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hN : ContDiff ℝ ∞ fun p : ℝ × ((l ⊕ l) → ℝ) => N p.1 p.2)
    (heq : ∀ s t, us s t + stdJ l (ut s t) + N t (u s t) = 0) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ => u p.1 p.2 := by
  have huC1 : ContDiff ℝ 1 fun p : ℝ × ℝ => u p.1 p.2 := contDiff_one_of_partials hs ht hcs hct
  have hEc : ContDiff ℝ 1 fun z : ℂ => ((z.re, z.im) : ℝ × ℝ) :=
    (Complex.reCLM.prod Complex.imCLM).contDiff
  have hcomp : ContDiff ℝ 1 fun z : ℂ => u z.re z.im := huC1.comp hEc
  -- the complexified solution
  have hUC1 : ∀ i : l, ContDiff ℝ 1 fun z : ℂ => toCpxL (u z.re z.im) i := by
    intro i
    exact (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l => ℂ) i).comp toCpxL)).comp hcomp
  -- the derivative of the complexified solution
  have hfd : ∀ (i : l) (z v : ℂ), fderiv ℝ (fun z : ℂ => toCpxL (u z.re z.im) i) z v
      = toCpxL (v.re • us z.re z.im + v.im • ut z.re z.im) i := by
    intro i z v
    have hE : HasFDerivAt (fun z : ℂ => ((z.re, z.im) : ℝ × ℝ))
        (Complex.reCLM.prod Complex.imCLM) z :=
      (Complex.reCLM.prod Complex.imCLM).hasFDerivAt
    have hu' : HasFDerivAt (fun q : ℝ × ℝ => u q.1 q.2)
        (fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) (z.re, z.im)) (z.re, z.im) :=
      ((huC1.differentiable one_ne_zero) _).hasFDerivAt
    have h1' := hu'.comp z hE
    have h1 : HasFDerivAt (fun z : ℂ => u z.re z.im)
        ((fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) (z.re, z.im)).comp
          (Complex.reCLM.prod Complex.imCLM)) z := h1'
    have hchain0 := (ContinuousLinearMap.hasFDerivAt
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l => ℂ) i).comp toCpxL)).comp z h1
    have hchain : HasFDerivAt (fun z : ℂ => toCpxL (u z.re z.im) i)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l => ℂ) i).comp toCpxL).comp
          ((fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) (z.re, z.im)).comp
            (Complex.reCLM.prod Complex.imCLM))) z := hchain0
    rw [hchain.fderiv]
    show ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l => ℂ) i).comp toCpxL)
      (fderiv ℝ (fun q : ℝ × ℝ => u q.1 q.2) (z.re, z.im) ((v.re, v.im) : ℝ × ℝ)) = _
    rw [fderiv_apply_of_partials hs ht hcs hct (z.re, z.im) ((v.re, v.im) : ℝ × ℝ)]
    rfl
  have hdbar : ∀ (i : l) (z : ℂ),
      dbar (fun z : ℂ => toCpxL (u z.re z.im) i) z = -(toCpxL (N z.im (u z.re z.im)) i) := by
    intro i z
    rw [dbar, hfd i z 1, hfd i z Complex.I]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, one_smul, zero_smul,
      add_zero, zero_add]
    have hJ : toCpxL (stdJ l (ut z.re z.im)) i = Complex.I * toCpxL (ut z.re z.im) i :=
      toCpxL_stdJ _ i
    have hsum : toCpxL (us z.re z.im) i + Complex.I * toCpxL (ut z.re z.im) i
        = toCpxL (us z.re z.im + stdJ l (ut z.re z.im)) i := by
      rw [← hJ, map_add]
      rfl
    rw [hsum]
    have hz : us z.re z.im + stdJ l (ut z.re z.im) = -(N z.im (u z.re z.im)) := by
      have h := heq z.re z.im
      linear_combination (norm := abel) h
    rw [hz, map_neg]
    rfl
  -- the right-hand side as a smooth function of the point and the values
  have hGsmooth : ∀ i : l, ContDiff ℝ ∞ fun p : ℂ × (l → ℂ) =>
      -(toCpxL (N p.1.im (ofCpxL p.2)) i) := by
    intro i
    have h1 : ContDiff ℝ ∞ fun p : ℂ × (l → ℂ) =>
        ((p.1.im, ofCpxL p.2) : ℝ × ((l ⊕ l) → ℝ)) :=
      ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ (l → ℂ))).prod
        (ofCpxL.comp (ContinuousLinearMap.snd ℝ ℂ (l → ℂ)))).contDiff
    exact ((ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l => ℂ) i).comp toCpxL)).comp
        (hN.comp h1)).neg
  have heq' : ∀ (i : l) (z : ℂ),
      dbar (fun z : ℂ => toCpxL (u z.re z.im) i) z
        = -(toCpxL (N z.im (ofCpxL fun j => toCpxL (u z.re z.im) j)) i) := by
    intro i z
    rw [hdbar i z]
    have h : (fun j => toCpxL (u z.re z.im) j) = toCpxL (u z.re z.im) := rfl
    rw [h, ofCpxL_toCpxL]
  have hUsmooth : ∀ i : l, ContDiff ℝ ∞ fun z : ℂ => toCpxL (u z.re z.im) i := fun i =>
    contDiff_infty_of_dbar_system
      (G := fun (i : l) (z : ℂ) (Y : l → ℂ) => -(toCpxL (N z.im (ofCpxL Y)) i))
      hUC1 hGsmooth heq' i
  -- back to the real picture
  have hemb : ContDiff ℝ ∞ fun p : ℝ × ℝ => ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) :=
    ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ))
      + Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))).contDiff
  have hback : (fun p : ℝ × ℝ => u p.1 p.2)
      = fun p : ℝ × ℝ => ofCpxL fun i =>
        (fun z : ℂ => toCpxL (u z.re z.im) i) ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) := by
    funext p
    dsimp only
    have hre : ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).re = p.1 := by simp
    have him : ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).im = p.2 := by simp
    rw [hre, him]
    have h : (fun i => toCpxL (u p.1 p.2) i) = toCpxL (u p.1 p.2) := rfl
    rw [h, ofCpxL_toCpxL]
  rw [hback]
  exact (ContinuousLinearMap.contDiff ofCpxL).comp
    (contDiff_pi.2 fun i => (hUsmooth i).comp hemb)

end FloerRegularity
end MorseFloer
