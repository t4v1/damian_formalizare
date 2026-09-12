import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# The flow of a vector field on a compact manifold

Mathlib proves that a `C¹` vector field on a manifold has local integral curves,
that they are unique, and (`exists_isMIntegralCurve_of_isMIntegralCurveOn`) that
they are global once a uniform existence time is known. It does not assemble
them into a *flow* continuous in the initial point. This file supplies that on a
compact boundaryless manifold, for use in Reeb's theorem (Corollary 2.1.9).

## The route

1. **Reading a chart curve on the manifold.**
   `hasMFDerivAt_extChartAt_symm_comp`: if a curve `g` in the model space solves
   the coordinate expression of `v` in the extended chart at `x₀`, and stays in
   the interior of the chart's target, then `(extChartAt I x₀).symm ∘ g` is
   tangent to `v`. This is the translation step of Mathlib's local existence
   theorem, isolated so that it can be used for a whole family of curves.
2. **A local flow in one chart.** `exists_localFlow`: the coordinate field is
   `C¹` near `extChartAt I x₀ x₀`, so Picard–Lindelöf, in the form that also
   gives continuity of the solution in the initial point, yields curves for all
   initial points in a closed ball, on a common time interval, depending
   continuously on `(initial point, time)`. Shrinking the ball and the interval
   keeps the solutions inside the chart. Pulled back to `M`, this is a map
   `β : ℝ → M → M`, continuous on `(-ρ, ρ) × U` for an open `U ∋ x₀`, whose
   curves `t ↦ β t x` are integral curves of `v` starting at `x`.
3. **A uniform time.** Compactness of `M` (through
   `IsCompact.eventually_forall_of_forall_eventually`) turns the local existence
   times into a single `ε > 0` valid at every point; Mathlib's uniform-time
   lemma then gives a global integral curve through each point, and `Φ t x` is
   the value at time `t` of the one through `x`.
4. **The group law** is uniqueness of global integral curves applied to the
   translated curve `s ↦ Φ (s + t) x`, which starts at `Φ t x`.
5. **Continuity.** On `(-ρ, ρ) × U`, uniqueness identifies `Φ` with the local
   flow `β` of step 2, so `Φ` is jointly continuous near every `(0, y)`, and
   compactness again gives one `a > 0` with `Φ` continuous at every `(t, y)`
   with `|t| < a`. The group law `Φ t = Φ (t/2) ∘ Φ (t/2)` doubles that range,
   and induction reaches every time.
-/

open Set Function
open scoped Manifold Topology

namespace MorseFloer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- **A chart solution is an integral curve.** Let `g : ℝ → E` have, at time `t`,
the velocity prescribed by `v` read in the extended chart at `x₀` (the vector
`v` at the point `(extChartAt I x₀).symm (g t)`, transported into that chart by
the tangent coordinate change), and let `g t` lie in the interior of the chart's
target. Then the pulled-back curve `(extChartAt I x₀).symm ∘ g` is tangent to `v`
at `t`. -/
theorem hasMFDerivAt_extChartAt_symm_comp [IsManifold I 1 M]
    {v : (x : M) → TangentSpace I x} {x₀ : M} {g : ℝ → E} {t : ℝ}
    (hg : HasDerivAt g (tangentCoordChange I ((extChartAt I x₀).symm (g t)) x₀
      ((extChartAt I x₀).symm (g t)) (v ((extChartAt I x₀).symm (g t)))) t)
    (hgt : g t ∈ interior (extChartAt I x₀).target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ g) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (((extChartAt I x₀).symm ∘ g) t))) := by
  let xₜ : M := (extChartAt I x₀).symm (g t)
  have hf3' := mem_of_mem_of_subset hgt interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source (I := I) xₜ
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp hg.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ g) (v xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hg
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hgt⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

open Metric in
/-- **A local flow around each point.** For a `C¹` vector field on a boundaryless
manifold modelled on a finite-dimensional space, every point `x₀` has an open
neighbourhood `U` and a time `ρ > 0` carrying a map `β : ℝ → M → M` such that,
for `x ∈ U`, the curve `t ↦ β t x` starts at `x` and is an integral curve of `v`
on `(-ρ, ρ)`, and `(t, x) ↦ β t x` is continuous on `(-ρ, ρ) × U`. It is the
Picard–Lindelöf flow of the coordinate expression of `v` in the chart at `x₀`. -/
theorem exists_localFlow [IsManifold I 1 M] [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧ ∃ β : ℝ → M → M,
      (∀ x ∈ U, β 0 x = x ∧ IsMIntegralCurveOn (β · x) v (Ioo (-ρ) ρ)) ∧
      ContinuousOn (uncurry β) (Ioo (-ρ) ρ ×ˢ U) := by
  set e := extChartAt I x₀
  set f : E → E := fun y ↦ tangentCoordChange I (e.symm y) x₀ (e.symm y) (v (e.symm y))
  -- the coordinate expression of `v` is `C¹` at the centre of the chart
  have hf : ContDiffAt ℝ 1 f (e x₀) := by
    have h := hv x₀
    rw [contMDiffAt_iff] at h
    exact (h.2.contDiffAt
      (range_mem_nhds_isInteriorPoint BoundarylessManifold.isInteriorPoint)).snd
  -- Picard–Lindelöf, with continuous dependence on the initial point
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα, hαc⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hα0 : ∀ y ∈ closedBall (e x₀) r, α (y, 0) = y := fun y hy ↦ (hα y hy).1
  have hαd : ∀ y ∈ closedBall (e x₀) r, ∀ t ∈ Icc (0 - ε) (0 + ε),
      HasDerivWithinAt (fun s ↦ α (y, s)) (f (α (y, t))) (Icc (0 - ε) (0 + ε)) t :=
    fun y hy ↦ (hα y hy).2
  set S := closedBall (e x₀) r ×ˢ Icc (0 - ε) (0 + ε)
  have hS : S ∈ 𝓝 (e x₀, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds _ hr') (Icc_mem_nhds (by linarith) (by linarith))
  have hT : interior e.target ∈ 𝓝 (α (e x₀, 0)) := by
    rw [hα0 _ (mem_closedBall_self hr'.le)]
    exact isOpen_interior.mem_nhds
      ((I.isInteriorPoint_iff).mp BoundarylessManifold.isInteriorPoint)
  -- shrink the ball and the interval so that the solutions stay inside the chart
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem hS ((hαc.continuousAt hS).preimage_mem_nhds hT))
  rw [← ball_prod_same] at hball
  have key : ∀ y ∈ ball (e x₀) ρ, ∀ s ∈ ball (0 : ℝ) ρ,
      (y ∈ closedBall (e x₀) r ∧ s ∈ Icc (0 - ε) (0 + ε)) ∧ α (y, s) ∈ interior e.target :=
    fun y hy s hs ↦ hball (show (y, s) ∈ ball (e x₀) ρ ×ˢ ball (0 : ℝ) ρ from ⟨hy, hs⟩)
  have hIoo : ∀ s ∈ Ioo (-ρ) ρ, s ∈ ball (0 : ℝ) ρ := fun s hs ↦ by
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
    exact hs
  set U : Set M := e.source ∩ e ⁻¹' ball (e x₀) ρ
  refine ⟨ρ, hρ, U,
    (continuousOn_extChartAt x₀).isOpen_inter_preimage (isOpen_extChartAt_source x₀) isOpen_ball,
    ⟨mem_extChartAt_source x₀, mem_ball_self hρ⟩, fun t x ↦ e.symm (α (e x, t)), ?_, ?_⟩
  · intro x hx
    have hxr := (key _ hx.2 0 (mem_ball_self hρ)).1.1
    refine ⟨?_, fun t ht ↦ ?_⟩
    · show e.symm (α (e x, 0)) = x
      rw [hα0 _ hxr, e.left_inv hx.1]
    · have hk := key _ hx.2 t (hIoo t ht)
      have hd : HasDerivAt (fun s ↦ α (e x, s)) (f (α (e x, t))) t :=
        (hαd _ hxr t hk.1.2).hasDerivAt (Filter.mem_of_superset
          (isOpen_ball.mem_nhds (hIoo t ht)) fun s hs ↦ (key _ hx.2 s hs).1.2)
      exact (hasMFDerivAt_extChartAt_symm_comp (x₀ := x₀) hd hk.2).hasMFDerivWithinAt
  · have h1 : ContinuousOn (fun p : ℝ × M ↦ (e p.2, p.1)) (Ioo (-ρ) ρ ×ˢ U) := by
      refine ContinuousOn.prodMk ?_ continuous_fst.continuousOn
      exact (continuousOn_extChartAt x₀).comp continuous_snd.continuousOn
        (fun p (hp : p ∈ Ioo (-ρ) ρ ×ˢ U) ↦ hp.2.1)
    have h2 : MapsTo (fun p : ℝ × M ↦ (e p.2, p.1)) (Ioo (-ρ) ρ ×ˢ U)
        (S ∩ α ⁻¹' interior e.target) :=
      fun p hp ↦ key _ hp.2.2 _ (hIoo _ hp.1)
    exact (continuousOn_extChartAt_symm x₀).comp ((hαc.mono inter_subset_left).comp h1 h2)
      fun p hp ↦ interior_subset (h2 hp).2

/-- **The flow of a `C¹` vector field on a compact boundaryless manifold.**  There
is a map `Φ : ℝ → M → M`, jointly continuous, with `Φ 0 = id`, every
`t ↦ Φ t x` an integral curve of `v`, and the group law
`Φ (s + t) = Φ s ∘ Φ t`. -/
theorem exists_flow [IsManifold I 1 M] [T2Space M] [CompactSpace M]
    [BoundarylessManifold I M] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M))) :
    ∃ Φ : ℝ → M → M, Continuous (uncurry Φ) ∧ (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) := by
  -- a uniform existence time, by compactness
  have hunif : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ (univ : Set M),
      ∃ γ : ℝ → M, γ 0 = y ∧ IsMIntegralCurveOn γ v (Ioo (-t) t) := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun y _ ↦ ?_
    obtain ⟨ρ, hρ, U, hU, hyU, β, hβ, -⟩ := exists_localFlow hv y
    filter_upwards [prod_mem_nhds (Ioo_mem_nhds (show -ρ < (0 : ℝ) by linarith) hρ)
      (hU.mem_nhds hyU)] with p hp
    exact ⟨(β · p.2), (hβ p.2 hp.2).1, (hβ p.2 hp.2).2.mono
      (Ioo_subset_Ioo (neg_le_neg hp.1.2.le) hp.1.2.le)⟩
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hunif
  have hδ2 : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-(δ / 2)) (δ / 2)) :=
    fun x ↦ hδ' (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith) x
      (mem_univ x)
  -- global integral curves through every point
  choose γ hγ0 hγ using fun x ↦
    exists_isMIntegralCurve_of_isMIntegralCurveOn hv (half_pos hδ) hδ2 x
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ → M → M, ∀ t x, Φ t x = γ x t := ⟨fun t x ↦ γ x t, fun _ _ ↦ rfl⟩
  have hΦ0 : ∀ x, Φ 0 x = x := fun x ↦ by rw [hΦ, hγ0]
  have hΦc : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v := fun x ↦ by
    have h : (fun t ↦ Φ t x) = γ x := funext fun t ↦ hΦ t x
    rw [h]
    exact hγ x
  -- the group law, by uniqueness of integral curves
  have hΦg : ∀ s t x, Φ (s + t) x = Φ s (Φ t x) := by
    intro s t x
    have h := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv
      ((hγ x).comp_add t) (hγ (γ x t)) (by simp only [comp_apply, zero_add, hγ0])
    simp only [hΦ]
    exact congrFun h s
  -- near each `(0, y)`, `Φ` coincides with a local chart flow, hence is continuous there
  have hloc : ∀ y : M, ∀ᶠ p : ℝ × M in 𝓝 ((0 : ℝ), y),
      ContinuousAt (uncurry Φ) (p.1, p.2) := by
    intro y
    obtain ⟨ρ, hρ, U, hU, hyU, β, hβ, hβc⟩ := exists_localFlow hv y
    have hO : IsOpen (Ioo (-ρ) ρ ×ˢ U) := isOpen_Ioo.prod hU
    have h0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have heq : EqOn (uncurry Φ) (uncurry β) (Ioo (-ρ) ρ ×ˢ U) := by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0 hv
        ((hΦc x).isMIntegralCurveOn _) (hβ x hx).2
        (by simp only [hΦ0, (hβ x hx).1]) ht
    filter_upwards [hO.mem_nhds (⟨h0, hyU⟩ : ((0 : ℝ), y) ∈ Ioo (-ρ) ρ ×ˢ U)] with p hp
    exact (hβc.congr heq).continuousAt (hO.mem_nhds hp)
  -- a uniform time of continuity, by compactness
  have hunifc : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y ∈ (univ : Set M), ContinuousAt (uncurry Φ) (t, y) :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ ↦ hloc y
  obtain ⟨a, ha, hca⟩ := Metric.eventually_nhds_iff.mp hunifc
  -- doubling the time of continuity with the group law
  have hdouble : ∀ n : ℕ, ∀ t : ℝ, |t| < 2 ^ n * a → ∀ y, ContinuousAt (uncurry Φ) (t, y) := by
    intro n
    induction n with
    | zero =>
      intro t ht y
      refine hca ?_ y (mem_univ y)
      rw [Real.dist_eq, sub_zero]
      simpa using ht
    | succ n ih =>
      intro t ht y
      have ht2 : |t / 2| < 2 ^ n * a := by
        rw [abs_div, abs_two]
        rw [pow_succ] at ht
        linarith
      have hsplit : uncurry Φ =
          fun p : ℝ × M ↦ uncurry Φ (p.1 / 2, uncurry Φ (p.1 / 2, p.2)) := by
        funext ⟨t', x⟩
        show Φ t' x = Φ (t' / 2) (Φ (t' / 2) x)
        rw [← hΦg, add_halves]
      rw [hsplit]
      have hin : ContinuousAt (fun p : ℝ × M ↦ (p.1 / 2, uncurry Φ (p.1 / 2, p.2))) (t, y) :=
        (continuous_fst.div_const 2).continuousAt.prodMk
          ((ih _ ht2 y).comp_of_eq
            ((continuous_fst.div_const 2).prodMk continuous_snd).continuousAt rfl)
      exact (ih _ ht2 (uncurry Φ (t / 2, y))).comp_of_eq hin rfl
  have hcont : Continuous (uncurry Φ) := by
    refine continuous_iff_continuousAt.mpr fun p ↦ ?_
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|p.1| / a) one_lt_two
    exact hdouble n p.1 (by rwa [div_lt_iff₀ ha] at hn) p.2
  exact ⟨Φ, hcont, hΦ0, hΦc, hΦg⟩

end MorseFloer
