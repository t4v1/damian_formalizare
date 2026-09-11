import MorseFloer.Basic

/-!
# Squared distance functions are generically Morse (Proposition 1.2.1)

For a manifold `M` smoothly embedded in a Euclidean space `F` by `ι`, and for almost every
`p ∈ F`, the function `x ↦ ‖ι x - p‖²` is a Morse function on `M`.  This file proves that
statement with no assumption: `ae_isMorseFunction_distSq_general` below is sorry-free.

The book obtains it from Sard's theorem applied to the endpoint map `(x, ν) ↦ x + ν` of the
normal bundle.  Mathlib has neither the normal bundle nor Sard's theorem on manifolds, so we
run the same argument in local coordinates, where everything it needs exists.  The file is
organised along the five steps of that argument.

1. **The local normal frame** (`proj`, `contDiffAt_proj`, `exists_proj_eq`).  For an
   injective linear map `A : E →L F`, `proj A = 1 - A (A*A)⁻¹ A*` is the orthogonal
   projection onto `(range A)ᗮ`.  We write it without adjoints, through the linear form
   `coL A w = ⟪w, A ·⟫` and the Gram form `gram A`, which is invertible as a map to the
   dual; Mathlib's smoothness of inversion then makes `proj` smooth near every injective
   `A`.  Near a fixed `A₀`, `proj A` maps the *fixed* space `N = (range A₀)ᗮ` onto
   `(range A)ᗮ`: it is injective on `N` because it is close to `proj A₀ = 1` there, and the
   dimensions agree.
2. **The second differential of a squared distance** (`sndFDeriv_normSq_eq`).  If the
   points `q v` are such that `g v - q v` is normal to the image of `dg_v` for all `v` near
   `u`, then the second differential of `‖g - q u‖²` at `u` is `(a, b) ↦ 2⟪dq_u a, dg_u b⟫`.
   This replaces the book's second fundamental form computation.
3. **The endpoint map and Sard's theorem** (`measure_image_null`,
   `exists_nhds_ae_nondegenerate`).  In a chart, with `g = ι ∘ φ⁻¹`, the endpoint map is
   `Φ (u, w) = g u + proj (dg_u) w` on `U₀ × N`, a space of dimension `dim F`.  The
   equidimensional Sard theorem (Mathlib's Jacobian lemma transported along a linear
   isomorphism, as in `Chapter14.sard_of_finrank_eq`) makes the image of its critical set
   null.  If `u` is a critical point of `‖g - p‖²` then `p = Φ (u, w)` for some `w ∈ N`;
   if the Hessian at `u` has a kernel vector `a`, step 2 applied to `q = Φ (·, w)` shows that
   `d(Φ(·, w))_u a` is normal, hence equal to `proj (dg_u) w₀` for some `w₀ ∈ N`, and then
   `(a, -w₀)` lies in the kernel of `dΦ`.  So `p` is a critical value of `Φ`.  Covering an
   open set by countably many such `U₀` gives `ae_nondegenerate_of_isOpen`.
4. **From an immersion to injective differentials** (`injective_fderiv_of_isImmersion`).
   Mathlib defines immersions by a local normal form `u ↦ (u, 0)` in some pair of charts; the
   differential of `ι` read in any chart is injective because it differs from the normal
   form by invertible changes of coordinates.
5. **Back to the manifold** (`isNondegenerate_hessian_of_chart`,
   `ae_isMorseFunction_of_isSmoothEmbedding`).  The embedding makes `M` second countable, so
   countably many preferred charts cover it.  The Hessian at a critical point `y` is
   computed in the chart at `y`, not in the chart used for the Sard argument; the two are
   related by a change of coordinates with invertible differential, and
   `sndFDeriv_comp_of_critical` from `MorseFloer.Basic` shows nondegeneracy is transported.

Only the equidimensional case of Sard is used, and it is used for a map that is merely
differentiable along the set in question, so none of the Morse–Sard machinery assumed in
Chapter 14 is needed.
-/

open scoped Manifold ContDiff RealInnerProductSpace
open ContinuousLinearMap Filter Topology Set MeasureTheory Module

namespace MorseFloer
namespace DistSqMorse

/-! ## The local normal frame -/

section Frame

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The real inner product, as a continuous bilinear map. -/
noncomputable def innerR : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem innerR_apply (v w : F) : innerR v w = ⟪v, w⟫ := rfl

/-- `coL A w` is the linear form `b ↦ ⟪w, A b⟫`; it vanishes exactly when `w` is
orthogonal to the range of `A`. -/
noncomputable def coL : (E →L[ℝ] F) →L[ℝ] F →L[ℝ] E →L[ℝ] ℝ :=
  ((compL ℝ F (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).flip innerR).comp (compL ℝ E F ℝ).flip

@[simp] theorem coL_apply (A : E →L[ℝ] F) (w : F) (b : E) : coL A w b = ⟪w, A b⟫ := rfl

/-- The Gram form `(a, b) ↦ ⟪A a, A b⟫` of a linear map `A`. -/
noncomputable def gram (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ := (coL A).comp A

theorem gram_apply (A : E →L[ℝ] F) (a b : E) : gram A a b = ⟪A a, A b⟫ := rfl

/-- A finite-dimensional space and its (continuous) dual have the same dimension. -/
theorem finrank_dual_eq [FiniteDimensional ℝ E] : finrank ℝ (E →L[ℝ] ℝ) = finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- The Gram form of an injective map is injective, as a map from `E` to its dual. -/
theorem gram_injective {A : E →L[ℝ] F} (hA : Function.Injective A) :
    Function.Injective (gram A) := by
  intro a a' h
  have h1 : gram A (a - a') = 0 := by rw [map_sub, h, sub_self]
  have h2 : ⟪A (a - a'), A (a - a')⟫ = 0 := by
    rw [← gram_apply, h1, zero_apply]
  have h3 : A (a - a') = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp h2
  rw [map_sub, sub_eq_zero] at h3
  exact hA h3

/-- The Gram form of an injective map is invertible, as a map from `E` to its dual. -/
theorem gram_isInvertible [FiniteDimensional ℝ E] {A : E →L[ℝ] F}
    (hA : Function.Injective A) : (gram A).IsInvertible := by
  have hinj := gram_injective hA
  have hsurj : Function.Surjective (gram A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_dual_eq.symm
      (f := (gram A : E →ₗ[ℝ] E →L[ℝ] ℝ))).mp hinj
  exact ⟨(LinearEquiv.ofBijective (gram A : E →ₗ[ℝ] E →L[ℝ] ℝ)
    ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ => rfl⟩

/-- The orthogonal projection onto the orthogonal complement of the range of `A`, written
as `1 - A (A*A)⁻¹ A*` with the adjoint replaced by `coL A` and `A*A` by the Gram form.  It
is a smooth function of `A` near every injective `A`. -/
noncomputable def proj (A : E →L[ℝ] F) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F - A.comp ((gram A).inverse.comp (coL A))

theorem proj_apply (A : E →L[ℝ] F) (w : F) :
    proj A w = w - A ((gram A).inverse (coL A w)) := rfl

/-- `proj A w` is orthogonal to the range of `A`. -/
theorem coL_proj [FiniteDimensional ℝ E] {A : E →L[ℝ] F} (hA : Function.Injective A)
    (w : F) : coL A (proj A w) = 0 := by
  have h : coL A (A ((gram A).inverse (coL A w))) = coL A w :=
    (gram_isInvertible hA).self_apply_inverse (coL A w)
  rw [proj_apply, map_sub, h, sub_self]

theorem inner_proj [FiniteDimensional ℝ E] {A : E →L[ℝ] F} (hA : Function.Injective A)
    (w : F) (b : E) : ⟪proj A w, A b⟫ = 0 := by
  rw [← coL_apply, coL_proj hA, zero_apply]

/-- `proj A` fixes the vectors orthogonal to the range of `A`. -/
theorem proj_of_coL_eq_zero {A : E →L[ℝ] F} {w : F} (h : coL A w = 0) : proj A w = w := by
  rw [proj_apply, h, map_zero, map_zero, sub_zero]

/-- The projection `proj A` depends smoothly on `A` near an injective `A`: it is built from
`A` by compositions and one inversion, of the Gram form, which is invertible there. -/
theorem contDiffAt_proj [FiniteDimensional ℝ E] {A : E →L[ℝ] F} (hA : Function.Injective A)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n proj A := by
  obtain ⟨e, he⟩ := gram_isInvertible hA
  have hcoL : ContDiff ℝ n (fun B : E →L[ℝ] F => coL B) := ContinuousLinearMap.contDiff _
  have hgram : ContDiff ℝ n (fun B : E →L[ℝ] F => gram B) := hcoL.clm_comp contDiff_id
  have hinv0 : ContDiffAt ℝ n ContinuousLinearMap.inverse (gram A) := by
    rw [← he]
    exact contDiffAt_map_inverse e
  have hinv : ContDiffAt ℝ n (fun B : E →L[ℝ] F => (gram B).inverse) A :=
    hinv0.comp A hgram.contDiffAt
  have h1 : ContDiffAt ℝ n (fun B : E →L[ℝ] F => (gram B).inverse.comp (coL B)) A :=
    hinv.clm_comp hcoL.contDiffAt
  have h2 : ContDiffAt ℝ n
      (fun B : E →L[ℝ] F => B.comp ((gram B).inverse.comp (coL B))) A :=
    contDiffAt_id.clm_comp h1
  exact contDiffAt_const.sub h2

/-- Near an injective `A₀`, the projection attached to `A` maps the normal space of `A₀`
onto that of `A`. -/
theorem exists_proj_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {A A₀ : E →L[ℝ] F}
    (hA : Function.Injective A) (hA₀ : Function.Injective A₀)
    (hclose : ‖proj A - proj A₀‖ < 1) {ν : F} (hν : coL A ν = 0) :
    ∃ w ∈ (LinearMap.range (A₀ : E →ₗ[ℝ] F))ᗮ, proj A w = ν := by
  set N := (LinearMap.range (A₀ : E →ₗ[ℝ] F))ᗮ
  set K := (LinearMap.range (A : E →ₗ[ℝ] F))ᗮ with hK
  have hid : ∀ w ∈ N, proj A₀ w = w := fun w hw => proj_of_coL_eq_zero (by
    ext b
    rw [coL_apply, zero_apply]
    exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ b) hw)
  set L : N →ₗ[ℝ] F := (proj A : F →ₗ[ℝ] F) ∘ₗ N.subtype
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : proj A w = 0 := hw
    have h1 : ‖(w : F)‖ ≤ ‖proj A - proj A₀‖ * ‖(w : F)‖ := by
      calc ‖(w : F)‖ = ‖(proj A - proj A₀) w‖ := by
              rw [sub_apply, hw', hid w w.2, zero_sub, norm_neg]
        _ ≤ ‖proj A - proj A₀‖ * ‖(w : F)‖ := le_opNorm _ _
    have h2 : ‖(w : F)‖ = 0 := by nlinarith [norm_nonneg (w : F)]
    exact Submodule.coe_eq_zero.mp (norm_eq_zero.mp h2)
  have hle : LinearMap.range L ≤ K := by
    rintro _ ⟨w, rfl⟩
    rw [hK, Submodule.mem_orthogonal]
    rintro _ ⟨b, rfl⟩
    rw [real_inner_comm]
    exact inner_proj hA w b
  have hdimN : finrank ℝ N = finrank ℝ K := by
    have h1 : finrank ℝ (LinearMap.range (A₀ : E →ₗ[ℝ] F)) + finrank ℝ N = finrank ℝ F :=
      Submodule.finrank_add_finrank_orthogonal _
    have h2 : finrank ℝ (LinearMap.range (A : E →ₗ[ℝ] F)) + finrank ℝ K = finrank ℝ F :=
      Submodule.finrank_add_finrank_orthogonal _
    rw [LinearMap.finrank_range_of_inj hA₀] at h1
    rw [LinearMap.finrank_range_of_inj hA] at h2
    omega
  have heq : LinearMap.range L = K :=
    Submodule.eq_of_le_of_finrank_eq hle ((LinearMap.finrank_range_of_inj hinj).trans hdimN)
  have hνK : ν ∈ K := by
    rw [hK, Submodule.mem_orthogonal]
    rintro _ ⟨b, rfl⟩
    rw [real_inner_comm, ContinuousLinearMap.coe_coe, ← coL_apply, hν, zero_apply]
  rw [← heq] at hνK
  obtain ⟨w, hw⟩ := hνK
  exact ⟨w, w.2, hw⟩

end Frame

/-! ## The second differential of a squared distance -/

section Hessian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The differential of `v ↦ ‖g v - p‖²`, obtained from the bilinearity of the inner
product. -/
theorem hasFDerivAt_normSq_sub {g : E → F} {p : F} {v : E} (hg : DifferentiableAt ℝ g v) :
    HasFDerivAt (fun y => ‖g y - p‖ ^ 2)
      (innerR.precompR E (g v - p) (fderiv ℝ g v) +
        innerR.precompL E (fderiv ℝ g v) (g v - p)) v := by
  have hf : HasFDerivAt (fun y => g y - p) (fderiv ℝ g v) v := hg.hasFDerivAt.sub_const p
  have h := innerR.hasFDerivAt_of_bilinear hf hf
  have heq : (fun y => ‖g y - p‖ ^ 2) = fun y => innerR (g y - p) (g y - p) := by
    funext y
    rw [innerR_apply, real_inner_self_eq_norm_sq]
  rw [heq]
  exact h

/-- The differential of `v ↦ ‖g v - p‖²` is `b ↦ 2⟪g v - p, dg_v b⟫`. -/
theorem fderiv_normSq_sub_apply {g : E → F} {p : F} {v : E} (hg : DifferentiableAt ℝ g v)
    (b : E) : fderiv ℝ (fun y => ‖g y - p‖ ^ 2) v b = 2 * ⟪g v - p, fderiv ℝ g v b⟫ := by
  rw [(hasFDerivAt_normSq_sub hg).fderiv]
  simp only [add_apply, precompR_apply, compL_apply, comp_apply, precompL_apply, innerR_apply]
  rw [real_inner_comm (fderiv ℝ g v b)]
  ring

/-- At a critical point `u` of `‖g - p‖²`, the vector `g u - p` is orthogonal to the image
of `dg_u`. -/
theorem inner_eq_zero_of_fderiv_normSq {g : E → F} {p : F} {u : E}
    (hg : DifferentiableAt ℝ g u) (h : fderiv ℝ (fun y => ‖g y - p‖ ^ 2) u = 0) (b : E) :
    ⟪g u - p, fderiv ℝ g u b⟫ = 0 := by
  have h1 := fderiv_normSq_sub_apply (p := p) hg b
  rw [h, zero_apply] at h1
  linarith

/-- **The Hessian of a squared distance at a critical point.**  If `q` is a
differentiable family of points with `q u = p`, such that `g v - q v` stays orthogonal to
the image of `dg_v`, then the second differential of `‖g - p‖²` at `u` is
`(a, b) ↦ 2 ⟪dq_u a, dg_u b⟫`.  This is the identity that ties degeneracy of the Hessian
to non-injectivity of the endpoint map. -/
theorem sndFDeriv_normSq_eq {g q : E → F} {u : E} {p : F} (hg : ContDiffAt ℝ 2 g u)
    (hq : DifferentiableAt ℝ q u) (hqu : q u = p)
    (horth : ∀ᶠ v in 𝓝 u, ∀ b, ⟪g v - q v, fderiv ℝ g v b⟫ = 0) (a b : E) :
    sndFDeriv (fun v => ‖g v - p‖ ^ 2) u a b = 2 * ⟪fderiv ℝ q u a, fderiv ℝ g u b⟫ := by
  have hdiff : ∀ᶠ v in 𝓝 u, DifferentiableAt ℝ g v :=
    (hg.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hc : HasFDerivAt (fun v => innerR (q v - p)) (innerR.comp (fderiv ℝ q u)) u :=
    innerR.hasFDerivAt.comp u (hq.hasFDerivAt.sub_const p)
  have hd : HasFDerivAt (fderiv ℝ g) (sndFDeriv g u) u :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hSd := (hc.clm_comp hd).const_smul (2 : ℝ)
  have key : fderiv ℝ (fun v => ‖g v - p‖ ^ 2) =ᶠ[𝓝 u]
      fun v => (2 : ℝ) • (innerR (q v - p)).comp (fderiv ℝ g v) := by
    filter_upwards [hdiff, horth] with v hv hov
    ext b
    rw [fderiv_normSq_sub_apply hv b]
    have := hov b
    simp only [smul_apply, comp_apply, innerR_apply, smul_eq_mul]
    rw [inner_sub_left] at this ⊢
    rw [inner_sub_left]
    linarith
  rw [sndFDeriv_def, key.fderiv_eq, show fderiv ℝ
    (fun v => (2 : ℝ) • (innerR (q v - p)).comp (fderiv ℝ g v)) u = _ from hSd.fderiv]
  simp [hqu]

end Hessian

/-! ## Sard's theorem between spaces of equal dimension -/

section Sard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- For an endomorphism of a finite-dimensional space, vanishing determinant is failure of
surjectivity. -/
theorem det_eq_zero_iff_not_surjective (A : F →L[ℝ] F) :
    A.det = 0 ↔ ¬ Function.Surjective A := by
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq,
    LinearMap.ker_eq_bot, LinearMap.injective_iff_surjective]
  rfl

/-- **Sard's theorem between spaces of equal dimension**, for a map that need only be
differentiable at the points of the set considered.  Mathlib's Jacobian lemma transported
along a linear isomorphism, as in `Chapter14.sard_of_finrank_eq`. -/
theorem measure_image_null [MeasurableSpace F] [BorelSpace F] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (μ : Measure F) [μ.IsAddHaarMeasure]
    {Φ : X → F} {s : Set X} (hd : ∀ z ∈ s, DifferentiableAt ℝ Φ z)
    (hcrit : ∀ z ∈ s, ¬ Function.Surjective (fderiv ℝ Φ z))
    (hdim : finrank ℝ X = finrank ℝ F) : μ (Φ '' s) = 0 := by
  set e : X ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hdim
  set g' : F → F →L[ℝ] F := fun y => (fderiv ℝ Φ (e.symm y)).comp (e.symm : F →L[ℝ] X)
  have himg : Φ '' s = (Φ ∘ e.symm) '' (e '' s) := by simp [Set.image_image]
  rw [himg]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ (f' := g') ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    have hz' : e.symm (e z) ∈ s := by simpa using hz
    exact ((hd _ hz').hasFDerivAt.comp (e z) e.symm.hasFDerivAt).hasFDerivWithinAt
  · rintro y ⟨z, hz, rfl⟩
    rw [det_eq_zero_iff_not_surjective]
    simp only [g', ContinuousLinearEquiv.symm_apply_apply]
    intro hsurj
    rw [ContinuousLinearMap.coe_comp] at hsurj
    exact hcrit z hz hsurj.of_comp

end Sard

/-! ## The endpoint map of the normal frame -/

section Endpoint

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **The local statement.**  Near any point `u₀` of an open set on which `g` is `C²` with
injective differential, almost every `p` has the property that every critical point of
`‖g - p‖²` is nondegenerate. -/
theorem exists_nhds_ae_nondegenerate (μ : Measure F) [μ.IsAddHaarMeasure] {g : E → F}
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hinj : ∀ u ∈ U, Function.Injective (fderiv ℝ g u)) {u₀ : E} (hu₀ : u₀ ∈ U) :
    ∃ U₀ ∈ 𝓝 u₀, ∀ᵐ p ∂μ, ∀ u ∈ U₀, fderiv ℝ (fun v => ‖g v - p‖ ^ 2) u = 0 →
      IsNondegenerate (sndFDeriv (fun v => ‖g v - p‖ ^ 2) u) := by
  have hgd : ∀ v ∈ U, ContDiffAt ℝ 2 g v := fun v hv => hg.contDiffAt (hU.mem_nhds hv)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by norm_num)
  have hPc : ∀ v ∈ U, ContDiffAt ℝ 1 (fun v => proj (fderiv ℝ g v)) v := fun v hv =>
    (contDiffAt_proj (hinj v hv)).comp v (hD1.contDiffAt (hU.mem_nhds hv))
  set N : Submodule ℝ F := (LinearMap.range (fderiv ℝ g u₀ : E →ₗ[ℝ] F))ᗮ
  set U₀ : Set E := U ∩ (fun v => proj (fderiv ℝ g v)) ⁻¹'
    Metric.ball (proj (fderiv ℝ g u₀)) 1
  have hU₀n : U₀ ∈ 𝓝 u₀ := inter_mem (hU.mem_nhds hu₀)
    ((hPc u₀ hu₀).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos))
  refine ⟨U₀, hU₀n, ?_⟩
  -- the endpoint map of the normal frame
  set Φ : E × N → F := fun z => g z.1 + proj (fderiv ℝ g z.1) (z.2 : F)
  have hΦd : ∀ z : E × N, z.1 ∈ U → DifferentiableAt ℝ Φ z := by
    intro z hz
    have h1 : DifferentiableAt ℝ (fun z : E × N => g z.1) z :=
      ((hgd z.1 hz).differentiableAt (by simp)).comp z differentiableAt_fst
    have h2 : DifferentiableAt ℝ (fun z : E × N => proj (fderiv ℝ g z.1)) z :=
      ((hPc z.1 hz).differentiableAt (by simp)).comp z differentiableAt_fst
    have h3 : DifferentiableAt ℝ (fun z : E × N => (z.2 : F)) z :=
      (ContinuousLinearMap.differentiableAt N.subtypeL).comp z differentiableAt_snd
    exact h1.add (h2.clm_apply h3)
  have hdim : finrank ℝ (E × N) = finrank ℝ F := by
    rw [Module.finrank_prod, ← LinearMap.finrank_range_of_inj (hinj u₀ hu₀),
      Submodule.finrank_add_finrank_orthogonal]
  set s : Set (E × N) := {z | z.1 ∈ U₀ ∧ ¬ Function.Surjective (fderiv ℝ Φ z)}
  have hnull : μ (Φ '' s) = 0 :=
    measure_image_null μ (fun z hz => hΦd z hz.1.1) (fun z hz => hz.2) hdim
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro p hp
  simp only [Set.mem_ofPred_eq, not_forall] at hp
  obtain ⟨u, hu, hcrit, hdeg⟩ := hp
  have huU : u ∈ U := hu.1
  have hclose : ‖proj (fderiv ℝ g u) - proj (fderiv ℝ g u₀)‖ < 1 := by
    have h := hu.2
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hgu : DifferentiableAt ℝ g u := (hgd u huU).differentiableAt (by simp)
  have hν : coL (fderiv ℝ g u) (p - g u) = 0 := by
    ext b
    have := inner_eq_zero_of_fderiv_normSq hgu hcrit b
    rw [coL_apply, zero_apply, ← neg_sub, inner_neg_left, this, neg_zero]
  obtain ⟨w, hwN, hw⟩ := exists_proj_eq (hinj u huU) (hinj u₀ hu₀) hclose hν
  have hΦz : Φ (u, ⟨w, hwN⟩) = p := by
    change g u + proj (fderiv ℝ g u) w = p
    rw [hw]
    abel
  refine ⟨(u, ⟨w, hwN⟩), ⟨hu, ?_⟩, hΦz⟩
  intro hsurj
  have hinjΦ : Function.Injective (fderiv ℝ Φ (u, ⟨w, hwN⟩)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv ℝ Φ (u, ⟨w, hwN⟩) : E × N →ₗ[ℝ] F))).mpr hsurj
  apply hdeg
  intro a ha
  -- the curve of endpoints obtained by freezing the normal coordinate
  have hΦzd : HasFDerivAt Φ (fderiv ℝ Φ (u, ⟨w, hwN⟩)) (u, ⟨w, hwN⟩) :=
    (hΦd (u, ⟨w, hwN⟩) huU).hasFDerivAt
  have hqd' := hΦzd.comp u (hasFDerivAt_prodMk_left (𝕜 := ℝ) u (⟨w, hwN⟩ : N))
  have hqu : (Φ ∘ fun v : E => (v, (⟨w, hwN⟩ : N))) u = p := hΦz
  have hqorth : ∀ᶠ v in 𝓝 u, ∀ b,
      ⟪g v - (Φ ∘ fun v : E => (v, (⟨w, hwN⟩ : N))) v, fderiv ℝ g v b⟫ = 0 := by
    filter_upwards [hU.mem_nhds huU] with v hv b
    change ⟪g v - (g v + proj (fderiv ℝ g v) w), fderiv ℝ g v b⟫ = 0
    have h1 : g v - (g v + proj (fderiv ℝ g v) w) = -proj (fderiv ℝ g v) w := by abel
    rw [h1, inner_neg_left, inner_proj (hinj v hv), neg_zero]
  have hH := sndFDeriv_normSq_eq (hgd u huU) hqd'.differentiableAt hqu hqorth a
  have hν' : coL (fderiv ℝ g u)
      (fderiv ℝ (Φ ∘ fun v : E => (v, (⟨w, hwN⟩ : N))) u a) = 0 := by
    ext b
    have h1 := ha b
    rw [hH b] at h1
    rw [coL_apply, zero_apply]
    linarith
  obtain ⟨w₀, hw₀N, hw₀⟩ := exists_proj_eq (hinj u huU) (hinj u₀ hu₀) hclose hν'
  have h1 : fderiv ℝ Φ (u, ⟨w, hwN⟩) (a, 0) =
      fderiv ℝ (Φ ∘ fun v : E => (v, (⟨w, hwN⟩ : N))) u a := by
    rw [hqd'.fderiv]
    rfl
  have hr : HasFDerivAt (Φ ∘ fun y : N => (u, y)) ((proj (fderiv ℝ g u)).comp N.subtypeL)
      ⟨w, hwN⟩ :=
    (ContinuousLinearMap.hasFDerivAt ((proj (fderiv ℝ g u)).comp N.subtypeL)).const_add (g u)
  have hr' := hΦzd.comp (⟨w, hwN⟩ : N) (hasFDerivAt_prodMk_right (𝕜 := ℝ) u (⟨w, hwN⟩ : N))
  have h2 : fderiv ℝ Φ (u, ⟨w, hwN⟩) (0, ⟨w₀, hw₀N⟩) = proj (fderiv ℝ g u) w₀ := by
    have := congrArg (fun L : N →L[ℝ] F => L ⟨w₀, hw₀N⟩) (hr'.unique hr)
    exact this
  have h3 : fderiv ℝ Φ (u, ⟨w, hwN⟩) (a, -⟨w₀, hw₀N⟩) = 0 := by
    have : ((a, -⟨w₀, hw₀N⟩) : E × N) = (a, 0) - (0, ⟨w₀, hw₀N⟩) := by ext <;> simp
    rw [this, map_sub, h1, h2, hw₀, sub_self]
  have h4 := hinjΦ (h3.trans (map_zero _).symm)
  simpa using congrArg Prod.fst h4

/-- **The statement on an open set.**  If `g` is `C²` with injective differential on an
open set `U`, then for almost every `p`, every critical point of `‖g - p‖²` in `U` is
nondegenerate.  A countable union of the local statements: `E` is second countable. -/
theorem ae_nondegenerate_of_isOpen (μ : Measure F) [μ.IsAddHaarMeasure] {g : E → F}
    {U : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hinj : ∀ u ∈ U, Function.Injective (fderiv ℝ g u)) :
    ∀ᵐ p ∂μ, ∀ u ∈ U, fderiv ℝ (fun v => ‖g v - p‖ ^ 2) u = 0 →
      IsNondegenerate (sndFDeriv (fun v => ‖g v - p‖ ^ 2) u) := by
  have hloc := fun u (hu : u ∈ U) => exists_nhds_ae_nondegenerate μ hU hg hinj hu
  choose! W hW hWae using hloc
  obtain ⟨t, htU, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (fun u hu => mem_nhdsWithin_of_mem_nhds (hW u hu))
  have hall : ∀ᵐ p ∂μ, ∀ u ∈ t, ∀ v ∈ W u, fderiv ℝ (fun v => ‖g v - p‖ ^ 2) v = 0 →
      IsNondegenerate (sndFDeriv (fun v => ‖g v - p‖ ^ 2) v) :=
    (ae_ball_iff htc).mpr fun u hu => hWae u (htU hu)
  filter_upwards [hall] with p hp u hu
  obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.mp (hcover hu)
  exact hp v hv u huv

end Endpoint

/-! ## From charts to the manifold -/

section Charts

open IsManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A change of coordinates between two charts of the maximal atlas of a boundaryless
manifold is `Cⁿ` near every point of its (open) domain, with invertible differential. -/
theorem coordChange_facts {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] (hn : n ≠ 0)
    {e e' : OpenPartialHomeomorph M E} (he : e ∈ maximalAtlas 𝓘(ℝ, E) n M)
    (he' : e' ∈ maximalAtlas 𝓘(ℝ, E) n M) {x : E}
    (hx : x ∈ (𝓘(ℝ, E).extendCoordChange e e').source) :
    (𝓘(ℝ, E).extendCoordChange e e').source ∈ 𝓝 x ∧
      ContDiffAt ℝ n (𝓘(ℝ, E).extendCoordChange e e') x ∧
      (fderiv ℝ (𝓘(ℝ, E).extendCoordChange e e') x).IsInvertible := by
  have hnhds : (𝓘(ℝ, E).extendCoordChange e e').source ∈ 𝓝 x := by
    have := 𝓘(ℝ, E).extendCoordChange_source_mem_nhdsWithin hx
    rwa [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at this
  refine ⟨hnhds, (𝓘(ℝ, E).contDiffOn_extendCoordChange he he').contDiffAt hnhds, ?_⟩
  have := 𝓘(ℝ, E).isInvertible_fderivWithin_extendCoordChange hn he he' hx
  rwa [fderivWithin_of_mem_nhds hnhds] at this

/-- **Transfer of nondegeneracy from a chart.**  If `y` lies in the domain of the chart at
`x₀`, the Hessian of `f` at a critical point `y` (computed in the preferred chart at `y`)
is nondegenerate as soon as the second differential of `f` read in the chart at `x₀` is.
This is `sndFDeriv_comp_of_critical` applied to the change of coordinates. -/
theorem isNondegenerate_hessian_of_chart [IsManifold 𝓘(ℝ, E) ω M] {f : M → ℝ} {x₀ y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) x₀).source) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) f y)
    (hh : ContDiffAt ℝ 2 (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y))
    (hcrit : IsCriticalPoint 𝓘(ℝ, E) f y)
    (hgood : fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y) = 0 →
      IsNondegenerate
        (sndFDeriv (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y))) :
    IsNondegenerate (hessian 𝓘(ℝ, E) f y) := by
  have hy' : y ∈ (chartAt E x₀).source := by rwa [extChartAt_source] at hy
  have hsrc : extChartAt 𝓘(ℝ, E) y y ∈
      (𝓘(ℝ, E).extendCoordChange (chartAt E y) (chartAt E x₀)).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    exact mem_image_of_mem _ ⟨mem_chart_source E y, hy'⟩
  obtain ⟨hnhds, hτd, hτinv⟩ := coordChange_facts (n := ω) WithTop.top_ne_zero
    (chart_mem_maximalAtlas y) (chart_mem_maximalAtlas x₀) hsrc
  set τ := 𝓘(ℝ, E).extendCoordChange (chartAt E y) (chartAt E x₀)
  have hτy : τ (extChartAt 𝓘(ℝ, E) y y) = extChartAt 𝓘(ℝ, E) x₀ y := by
    change extChartAt 𝓘(ℝ, E) x₀ ((extChartAt 𝓘(ℝ, E) y).symm (extChartAt 𝓘(ℝ, E) y y)) = _
    rw [extChartAt_to_inv]
  have heq : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) y f =ᶠ[𝓝 (extChartAt 𝓘(ℝ, E) y y)]
      (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) ∘ τ := by
    filter_upwards [hnhds] with v hv
    have hv2 : (extChartAt 𝓘(ℝ, E) y).symm v ∈ (extChartAt 𝓘(ℝ, E) x₀).source := hv.2
    change extChartAt 𝓘(ℝ) (f y) (f ((extChartAt 𝓘(ℝ, E) y).symm v)) =
      f ((extChartAt 𝓘(ℝ, E) x₀).symm
        (extChartAt 𝓘(ℝ, E) x₀ ((extChartAt 𝓘(ℝ, E) y).symm v)))
    rw [(extChartAt 𝓘(ℝ, E) x₀).left_inv hv2, extChartAt_model_space_eq_id]
    rfl
  have hh' : ContDiffAt ℝ 2 (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm)
      (τ (extChartAt 𝓘(ℝ, E) y y)) := by
    rw [hτy]; exact hh
  have hτ2 : ContDiffAt ℝ 2 τ (extChartAt 𝓘(ℝ, E) y y) := hτd.of_le (OrderTop.le_top _)
  have hcomp : fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) y f) (extChartAt 𝓘(ℝ, E) y y) =
      (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y)).comp
        (fderiv ℝ τ (extChartAt 𝓘(ℝ, E) y y)) := by
    rw [heq.fderiv_eq, fderiv_comp _ (hh'.differentiableAt (by simp))
      (hτ2.differentiableAt (by simp)), hτy]
  have hcrit' : fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) y f)
      (extChartAt 𝓘(ℝ, E) y y) = 0 := by
    have h1 := hf.mfderiv
    unfold IsCriticalPoint at hcrit
    rw [hcrit, ModelWithCorners.range_eq_univ, fderivWithin_univ] at h1
    exact h1.symm
  have hcritx : fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y) = 0 := by
    rw [hcomp] at hcrit'
    ext v
    obtain ⟨a, rfl⟩ := hτinv.surjective v
    have := congrArg (fun L => L a) hcrit'
    simpa using this
  have hcritτ : fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (τ (extChartAt 𝓘(ℝ, E) y y)) = 0 := by
    rw [hτy]; exact hcritx
  have hhess : ∀ a b, hessian 𝓘(ℝ, E) f y a b =
      sndFDeriv (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ y)
        (fderiv ℝ τ (extChartAt 𝓘(ℝ, E) y y) a) (fderiv ℝ τ (extChartAt 𝓘(ℝ, E) y y) b) := by
    intro a b
    have h1 : hessian 𝓘(ℝ, E) f y =
        sndFDeriv ((f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) ∘ τ) (extChartAt 𝓘(ℝ, E) y y) := by
      change sndFDeriv (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) y f) (extChartAt 𝓘(ℝ, E) y y) = _
      rw [sndFDeriv_def, sndFDeriv_def]
      exact heq.fderiv.fderiv_eq
    rw [h1, sndFDeriv_comp_of_critical hh' hτ2 hcritτ, hτy]
  have hnd := hgood hcritx
  intro a ha
  have h2 : fderiv ℝ τ (extChartAt 𝓘(ℝ, E) y y) a = 0 := by
    apply hnd
    intro w
    obtain ⟨b, rfl⟩ := hτinv.surjective w
    rw [← hhess]
    exact ha b
  exact hτinv.injective (h2.trans (map_zero _).symm)

/-- A smooth map read in a chart is smooth on the chart's target. -/
theorem contDiffOn_comp_extChartAt_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsManifold 𝓘(ℝ, E) ω M] {ι : M → F} (hι : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω ι) (x₀ : M) :
    ContDiffOn ℝ ω (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀).target :=
  (hι.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀)).contDiffOn

/-- **An immersion has injective differential**, read in any chart of the source.  Mathlib
defines immersions through a local normal form `u ↦ (u, 0)`; this recovers injectivity of
the differential from it, through the change of coordinates to the normal-form chart. -/
theorem injective_fderiv_of_isImmersion {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [IsManifold 𝓘(ℝ, E) ω M] {ι : M → F} (hι : Manifold.IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ω ι)
    (x₀ : M) {u : E} (hu : u ∈ (extChartAt 𝓘(ℝ, E) x₀).target)
    (hd : DifferentiableAt ℝ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) u) :
    Function.Injective (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) u) := by
  have h := hι.isImmersionAt ((extChartAt 𝓘(ℝ, E) x₀).symm u)
  have hy₀ : (extChartAt 𝓘(ℝ, E) x₀).symm u ∈ (chartAt E x₀).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, E))]
    exact (extChartAt 𝓘(ℝ, E) x₀).map_target hu
  have hsrc : u ∈ (𝓘(ℝ, E).extendCoordChange (chartAt E x₀) h.domChart).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    exact ⟨(extChartAt 𝓘(ℝ, E) x₀).symm u, ⟨hy₀, h.mem_domChart_source⟩,
      (extChartAt 𝓘(ℝ, E) x₀).right_inv hu⟩
  obtain ⟨hnhds, hτd, hτinv⟩ := coordChange_facts (n := ω) WithTop.top_ne_zero
    (chart_mem_maximalAtlas x₀) h.domChart_mem_maximalAtlas hsrc
  set τ := 𝓘(ℝ, E).extendCoordChange (chartAt E x₀) h.domChart
  have hcod : DifferentiableAt ℝ (h.codChart.extend 𝓘(ℝ, F))
      (ι ((extChartAt 𝓘(ℝ, E) x₀).symm u)) :=
    ((OpenPartialHomeomorph.contMDiffAt_extend h.codChart_mem_maximalAtlas
      h.mem_codChart_source).contDiffAt).differentiableAt WithTop.top_ne_zero
  have heq : (h.codChart.extend 𝓘(ℝ, F)) ∘ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) =ᶠ[𝓝 u]
      (h.equiv ∘ fun a => (a, (0 : h.complement))) ∘ τ := by
    filter_upwards [hnhds] with v hv
    have hv2 : (extChartAt 𝓘(ℝ, E) x₀).symm v ∈ (h.domChart.extend 𝓘(ℝ, E)).source := hv.2
    have hmem : τ v ∈ (h.domChart.extend 𝓘(ℝ, E)).target :=
      (h.domChart.extend 𝓘(ℝ, E)).map_source hv2
    calc (h.codChart.extend 𝓘(ℝ, F) ∘ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm)) v
        = ((h.codChart.extend 𝓘(ℝ, F)) ∘ ι ∘ (h.domChart.extend 𝓘(ℝ, E)).symm) (τ v) := by
          change h.codChart.extend 𝓘(ℝ, F) (ι ((extChartAt 𝓘(ℝ, E) x₀).symm v)) =
            h.codChart.extend 𝓘(ℝ, F) (ι ((h.domChart.extend 𝓘(ℝ, E)).symm
              (h.domChart.extend 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm v))))
          rw [(h.domChart.extend 𝓘(ℝ, E)).left_inv hv2]
      _ = ((h.equiv ∘ fun a => (a, (0 : h.complement))) ∘ τ) v := h.writtenInCharts hmem
  have hL : HasFDerivAt ((h.codChart.extend 𝓘(ℝ, F)) ∘ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm))
      ((fderiv ℝ (h.codChart.extend 𝓘(ℝ, F)) (ι ((extChartAt 𝓘(ℝ, E) x₀).symm u))).comp
        (fderiv ℝ (ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) u)) u :=
    hcod.hasFDerivAt.comp u hd.hasFDerivAt
  have hR : HasFDerivAt ((h.equiv ∘ fun a => (a, (0 : h.complement))) ∘ τ)
      (((h.equiv : E × h.complement →L[ℝ] F).comp (inl ℝ E h.complement)).comp
        (fderiv ℝ τ u)) u :=
    (h.equiv.hasFDerivAt.comp (τ u) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (τ u) (0 : h.complement))).comp
      u (hτd.differentiableAt WithTop.top_ne_zero).hasFDerivAt
  have hEq := (hL.congr_of_eventuallyEq heq.symm).unique hR
  have hinjR : Function.Injective
      (((h.equiv : E × h.complement →L[ℝ] F).comp (inl ℝ E h.complement)).comp
        (fderiv ℝ τ u)) := by
    intro a b hab
    simp only [coe_comp, Function.comp_apply, inl_apply, ContinuousLinearEquiv.coe_coe] at hab
    have := h.equiv.injective hab
    exact hτinv.injective (congrArg Prod.fst this)
  rw [← hEq, coe_comp] at hinjR
  exact hinjR.of_comp

variable [FiniteDimensional ℝ E]

/-- **Proposition 1.2.1, for a smooth embedding into a Euclidean space.**  For almost
every `p`, the squared distance to `p` is a Morse function on `M`. -/
theorem ae_isMorseFunction_of_isSmoothEmbedding {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] [IsManifold 𝓘(ℝ, E) ω M]
    (ι : M → F) (hι : Manifold.IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ω ι) :
    ∀ᵐ p ∂μ, IsMorseFunction 𝓘(ℝ, E) (fun x : M => ‖ι x - p‖ ^ 2) := by
  have : SecondCountableTopology M := hι.isEmbedding.secondCountableTopology
  have hsmooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω ι := hι.contMDiff
  obtain ⟨s, hsc, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M => extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x)
  have hgood : ∀ x₀ ∈ s, ∀ᵐ p ∂μ, ∀ u ∈ (extChartAt 𝓘(ℝ, E) x₀).target,
      fderiv ℝ (fun v => ‖(ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) v - p‖ ^ 2) u = 0 →
      IsNondegenerate
        (sndFDeriv (fun v => ‖(ι ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) v - p‖ ^ 2) u) := by
    intro x₀ _
    have hg := contDiffOn_comp_extChartAt_symm hsmooth x₀
    have hopen := isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀
    refine ae_nondegenerate_of_isOpen μ hopen (hg.of_le (OrderTop.le_top _)) fun u hu => ?_
    exact injective_fderiv_of_isImmersion hι.isImmersion x₀ hu
      ((hg.contDiffAt (hopen.mem_nhds hu)).differentiableAt WithTop.top_ne_zero)
  filter_upwards [(ae_ball_iff hsc).mpr hgood] with p hp
  intro y hcrit
  have hy : y ∈ ⋃ x ∈ s, (extChartAt 𝓘(ℝ, E) x).source := by
    rw [hcover]; exact mem_univ y
  obtain ⟨x₀, hx₀, hyx⟩ := mem_iUnion₂.mp hy
  have hq : ContDiff ℝ ω (fun w : F => ‖w - p‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hg := contDiffOn_comp_extChartAt_symm hsmooth x₀
  have hopen := isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀
  have hmem : extChartAt 𝓘(ℝ, E) x₀ y ∈ (extChartAt 𝓘(ℝ, E) x₀).target :=
    (extChartAt 𝓘(ℝ, E) x₀).map_source hyx
  refine isNondegenerate_hessian_of_chart hyx ?_ ?_ hcrit (hp x₀ hx₀ _ hmem)
  · exact (hq.contMDiff.comp hsmooth).mdifferentiableAt WithTop.top_ne_zero
  · exact (hq.contDiffAt.comp _ (hg.contDiffAt (hopen.mem_nhds hmem))).of_le
      (OrderTop.le_top _)

end Charts

end DistSqMorse

/-- **Proposition 1.2.1.**  For almost every `p ∈ ℝⁿ`, the squared distance
`x ↦ ‖ι x − p‖²` on a smoothly embedded manifold `V ⊆ ℝⁿ` is a Morse function. -/
theorem ae_isMorseFunction_distSq_general {d n : ℕ}
    {V : Type*} [TopologicalSpace V] [ChartedSpace (EuclideanSpace ℝ (Fin d)) V]
    [IsManifold (𝓡 d) ω V] (ι : V → EuclideanSpace ℝ (Fin n))
    (hι : Manifold.IsSmoothEmbedding (𝓡 d) (𝓡 n) ω ι) :
    ∀ᵐ p : EuclideanSpace ℝ (Fin n),
      IsMorseFunction (𝓡 d) (fun x : V => ‖ι x - p‖ ^ 2) :=
  DistSqMorse.ae_isMorseFunction_of_isSmoothEmbedding volume ι hι

end MorseFloer
