import MorseFloer.Basic
import MorseFloer.Part1.MorseLemma
import MorseFloer.Part1.ManifoldFlow

/-!
# Reeb's theorem (Corollary 2.1.9)

A compact manifold carrying a Morse function with exactly two critical points is
homeomorphic to a sphere.  This file proves it as `MorseFloer.reeb_general`.

The proof is the classical one, organised so that the manifold enters in as few
places as possible.

1. **The two critical points.**  On a compact manifold `f` has a minimum `m` and a
   maximum `M`, and extrema are critical.  In positive dimension `f` cannot be
   constant (every point would be critical, and a manifold of positive dimension is
   not finite), so `m ≠ M`, the critical set is `{m, M}`, and `m`, `M` are the only
   points at the levels `f m`, `f M`.  Dimension zero is handled directly: there
   `V` has two points.
2. **A gradient-like vector field.**  In the chart at `x₀`, the vector
   `Σᵢ ∂ᵢ(f ∘ φ⁻¹) eᵢ`, carried to the tangent space by the tangent coordinate
   change, pairs with `df` to `Σᵢ (∂ᵢ(f ∘ φ⁻¹))²`: nonnegative, and positive away from
   the critical points.  Mathlib's partition-of-unity theorem for sections with
   values in convex sets (`exists_contMDiffSection_forall_mem_convex_of_local`)
   glues these local fields into a global `C¹` field `v` with `df(v) > 0` off the
   critical points.
3. **Flow lines.**  `exists_flow` provides the flow `Φ` of `v`.  From here on
   everything is point-set topology plus one-variable calculus, packaged in the
   structure `GradientLikeFlow`: `f` is nondecreasing along flow lines, `m` and
   `M` are fixed, and along any other flow line `f` increases strictly from `f m`
   (as `t → -∞`) to `f M` (as `t → +∞`); a cluster point of a flow line is a
   point where `f` is constant along the flow, hence is `m` or `M`.  So every
   such flow line crosses each intermediate level exactly once, at a time `τ`
   depending continuously on the starting point.
4. **The Morse chart at the minimum.**  The Morse lemma
   (`morse_lemma_of_contDiffAt`) writes `f = f m + ½ B(ψ, ψ)` near `m`, with `B`
   the Hessian.  Since `m` is a minimum, `B` is nonnegative; being nondegenerate,
   it is positive definite.  A level `c` slightly above `f m` then lies inside
   the chart, where it is the ellipsoid `B(ψ, ψ) = 2(c - f m)`, and the radial
   projection `ψ / ‖ψ‖` identifies it with the unit sphere `Sⁿ⁻¹`.
5. **Assembly.**  With `σ x ∈ f⁻¹(c)` the point where the flow line of `x`
   crosses the level `c`, and `θ x ∈ [0, π]` the rescaled height of `x`, the map
   `x ↦ (sin θ · u(σ x), -cos θ) ∈ Sⁿ ⊆ ℝⁿ × ℝ` is continuous (also at `m` and `M`,
   where `sin θ → 0`) and bijective; `V` is compact, so it is a homeomorphism.
-/

open Set Function Filter Topology Metric Bundle
open scoped Manifold ContDiff

namespace MorseFloer

namespace Reeb

/-! ## Coordinates on `ℝⁿ⁺¹ = ℝⁿ × ℝ` -/

section Join

variable {n : ℕ}

/-- The point of `ℝⁿ⁺¹` whose first `n` coordinates are those of `w` and whose last
coordinate is `t`. -/
noncomputable def join (w : EuclideanSpace ℝ (Fin n)) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => w i) t)

@[simp]
theorem join_castSucc (w : EuclideanSpace ℝ (Fin n)) (t : ℝ) (i : Fin n) :
    join w t i.castSucc = w i := by
  simp [join]

@[simp]
theorem join_last (w : EuclideanSpace ℝ (Fin n)) (t : ℝ) : join w t (Fin.last n) = t := by
  simp [join]

theorem join_inj {w w' : EuclideanSpace ℝ (Fin n)} {t t' : ℝ} (h : join w t = join w' t') :
    w = w' ∧ t = t' := by
  refine ⟨?_, by simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) h⟩
  ext i
  simpa using congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i.castSucc) h

theorem exists_eq_join (z : EuclideanSpace ℝ (Fin (n + 1))) : ∃ w t, z = join w t := by
  refine ⟨WithLp.toLp 2 (fun i => z i.castSucc), z (Fin.last n), ?_⟩
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem norm_join_sq (w : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖join w t‖ ^ 2 = ‖w‖ ^ 2 + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

theorem continuous_join :
    Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => join p.1 p.2) := by
  show Continuous fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
    WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => p.1 i) p.2)
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  induction i using Fin.lastCases with
  | last => simpa using continuous_snd
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (PiLp.continuous_apply 2 _ j).comp continuous_fst

end Join

/-! ## Flow lines of a gradient-like flow -/

/-- The data extracted from a Morse function with two critical points and the flow of a
gradient-like vector field: a flow `Φ`, along which `f` has derivative `D ≥ 0`, strictly
positive away from the minimum `m` and the maximum `M`, which are the only points at
their levels.  Everything after the construction of the flow uses only this. -/
structure GradientLikeFlow (X : Type*) [TopologicalSpace X] where
  /-- The function. -/
  f : X → ℝ
  /-- The flow. -/
  Φ : ℝ → X → X
  /-- The derivative of `f` along the flow. -/
  D : X → ℝ
  /-- The minimum. -/
  m : X
  /-- The maximum. -/
  M : X
  continuous_f : Continuous f
  continuous_Φ : Continuous (uncurry Φ)
  Φ_zero : ∀ x, Φ 0 x = x
  Φ_add : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)
  hasDerivAt : ∀ x t, HasDerivAt (fun s => f (Φ s x)) (D (Φ t x)) t
  D_nonneg : ∀ x, 0 ≤ D x
  D_pos : ∀ x, x ≠ m → x ≠ M → 0 < D x
  min_le : ∀ x, f m ≤ f x
  le_max : ∀ x, f x ≤ f M
  eq_m : ∀ x, f x = f m → x = m
  eq_M : ∀ x, f x = f M → x = M
  lt : f m < f M

namespace GradientLikeFlow

variable {X : Type*} [TopologicalSpace X] (F : GradientLikeFlow X)

theorem continuous_Φ_left (x : X) : Continuous fun t => F.Φ t x :=
  F.continuous_Φ.comp (continuous_id.prodMk continuous_const)

theorem continuous_Φ_right (t : ℝ) : Continuous (F.Φ t) :=
  F.continuous_Φ.comp (continuous_const.prodMk continuous_id)

theorem Φ_neg_Φ (t : ℝ) (x : X) : F.Φ (-t) (F.Φ t x) = x := by
  rw [← F.Φ_add, neg_add_cancel, F.Φ_zero]

theorem Φ_Φ_neg (t : ℝ) (x : X) : F.Φ t (F.Φ (-t) x) = x := by
  rw [← F.Φ_add, add_neg_cancel, F.Φ_zero]

/-- `f` is nondecreasing along every flow line. -/
theorem monotone (x : X) : Monotone fun t => F.f (F.Φ t x) :=
  monotone_of_deriv_nonneg (fun t => (F.hasDerivAt x t).differentiableAt)
    fun t => by rw [(F.hasDerivAt x t).deriv]; exact F.D_nonneg _

/-- The minimum is a fixed point of the flow. -/
theorem Φ_m (t : ℝ) : F.Φ t F.m = F.m := by
  have key : ∀ s ≤ (0 : ℝ), F.Φ s F.m = F.m := by
    intro s hs
    refine F.eq_m _ (le_antisymm ?_ (F.min_le _))
    have h : F.f (F.Φ s F.m) ≤ F.f (F.Φ 0 F.m) := F.monotone F.m hs
    rwa [F.Φ_zero] at h
  rcases le_or_gt t 0 with ht | ht
  · exact key t ht
  · calc F.Φ t F.m = F.Φ t (F.Φ (-t) F.m) := by rw [key (-t) (by linarith)]
      _ = F.m := F.Φ_Φ_neg t F.m

/-- The maximum is a fixed point of the flow. -/
theorem Φ_M (t : ℝ) : F.Φ t F.M = F.M := by
  have key : ∀ s, (0 : ℝ) ≤ s → F.Φ s F.M = F.M := by
    intro s hs
    refine F.eq_M _ (le_antisymm (F.le_max _) ?_)
    have h : F.f (F.Φ 0 F.M) ≤ F.f (F.Φ s F.M) := F.monotone F.M hs
    rwa [F.Φ_zero] at h
  rcases le_or_gt 0 t with ht | ht
  · exact key t ht
  · calc F.Φ t F.M = F.Φ t (F.Φ (-t) F.M) := by rw [key (-t) (by linarith)]
      _ = F.M := F.Φ_Φ_neg t F.M

theorem Φ_ne_m {x : X} (hm : x ≠ F.m) (t : ℝ) : F.Φ t x ≠ F.m := fun h =>
  hm (by rw [← F.Φ_neg_Φ t x, h, F.Φ_m])

theorem Φ_ne_M {x : X} (hM : x ≠ F.M) (t : ℝ) : F.Φ t x ≠ F.M := fun h =>
  hM (by rw [← F.Φ_neg_Φ t x, h, F.Φ_M])

/-- Away from `m` and `M`, `f` is strictly increasing along the flow line. -/
theorem strictMono {x : X} (hm : x ≠ F.m) (hM : x ≠ F.M) :
    StrictMono fun t => F.f (F.Φ t x) :=
  strictMono_of_deriv_pos fun t => by
    rw [(F.hasDerivAt x t).deriv]
    exact F.D_pos _ (F.Φ_ne_m hm t) (F.Φ_ne_M hM t)

theorem lt_f {x : X} (hm : x ≠ F.m) : F.f F.m < F.f x :=
  lt_of_le_of_ne (F.min_le x) fun h => hm (F.eq_m x h.symm)

theorem f_lt {x : X} (hM : x ≠ F.M) : F.f x < F.f F.M :=
  lt_of_le_of_ne (F.le_max x) fun h => hM (F.eq_M x h)

theorem ne_m_of_lt {x : X} (h : F.f F.m < F.f x) : x ≠ F.m := by
  rintro rfl
  exact lt_irrefl _ h

theorem ne_M_of_lt {x : X} (h : F.f x < F.f F.M) : x ≠ F.M := by
  rintro rfl
  exact lt_irrefl _ h

/-- If `f` has limit `ℓ` along a flow line (towards `+∞` or `-∞`), then `ℓ` is `f m` or
`f M`: `f` is constant along the flow line of any cluster point, which must therefore
be `m` or `M`. -/
theorem limit_eq [T2Space X] {x z : X} {l : Filter ℝ} {ℓ : ℝ}
    (hl : ∀ s : ℝ, Tendsto (fun t => s + t) l l)
    (hlim : Tendsto (fun t => F.f (F.Φ t x)) l (𝓝 ℓ))
    (hz : MapClusterPt z l fun t => F.Φ t x) : ℓ = F.f F.m ∨ ℓ = F.f F.M := by
  have hval : ∀ s, F.f (F.Φ s z) = ℓ := by
    intro s
    have h1 : MapClusterPt ((F.f ∘ F.Φ s) z) l ((F.f ∘ F.Φ s) ∘ fun t => F.Φ t x) :=
      hz.continuousAt_comp (F.continuous_f.comp (F.continuous_Φ_right s)).continuousAt
    have h2 : Tendsto ((F.f ∘ F.Φ s) ∘ fun t => F.Φ t x) l (𝓝 ℓ) := by
      have heq : ((F.f ∘ F.Φ s) ∘ fun t => F.Φ t x) = (fun t => F.f (F.Φ t x)) ∘ fun t => s + t := by
        funext t
        simp only [Function.comp_apply, F.Φ_add]
      rw [heq]
      exact hlim.comp (hl s)
    exact eq_of_nhds_neBot (h1.clusterPt.mono h2).neBot
  by_cases hm : z = F.m
  · left
    rw [← hval 0, F.Φ_zero, hm]
  by_cases hM : z = F.M
  · right
    rw [← hval 0, F.Φ_zero, hM]
  exfalso
  have h : F.f (F.Φ 0 z) < F.f (F.Φ 1 z) := F.strictMono hm hM (zero_lt_one' ℝ)
  rw [hval 0, hval 1] at h
  exact lt_irrefl _ h

/-- The time at which the flow line of `x` crosses the level `c`. -/
noncomputable def τ (c : ℝ) (x : X) : ℝ := Classical.epsilon fun t => F.f (F.Φ t x) = c

/-- The point where the flow line of `x` crosses the level `c`. -/
noncomputable def σ (c : ℝ) (x : X) : X := F.Φ (F.τ c x) x

section Compact

variable [CompactSpace X] [T2Space X]

/-- Along a flow line other than `m`, `M`, `f` tends to `f M` as `t → +∞`. -/
theorem tendsto_atTop {x : X} (hm : x ≠ F.m) :
    Tendsto (fun t => F.f (F.Φ t x)) atTop (𝓝 (F.f F.M)) := by
  have hbdd : BddAbove (range fun t => F.f (F.Φ t x)) :=
    ⟨F.f F.M, by rintro _ ⟨t, rfl⟩; exact F.le_max _⟩
  have hlim := tendsto_atTop_ciSup (F.monotone x) hbdd
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (map (fun t => F.Φ t x) atTop)
  rcases F.limit_eq (fun s => tendsto_atTop_add_const_left atTop s tendsto_id) hlim hz with h | h
  · exfalso
    have h1 : F.f (F.Φ 0 x) ≤ ⨆ t, F.f (F.Φ t x) := le_ciSup hbdd 0
    rw [F.Φ_zero, h] at h1
    exact absurd h1 (not_le.mpr (F.lt_f hm))
  · rwa [h] at hlim

/-- Along a flow line other than `m`, `M`, `f` tends to `f m` as `t → -∞`. -/
theorem tendsto_atBot {x : X} (hM : x ≠ F.M) :
    Tendsto (fun t => F.f (F.Φ t x)) atBot (𝓝 (F.f F.m)) := by
  have hbdd : BddBelow (range fun t => F.f (F.Φ t x)) :=
    ⟨F.f F.m, by rintro _ ⟨t, rfl⟩; exact F.min_le _⟩
  have hlim := tendsto_atBot_ciInf (F.monotone x) hbdd
  obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace (map (fun t => F.Φ t x) atBot)
  rcases F.limit_eq (fun s => tendsto_atBot_add_const_left atBot s tendsto_id) hlim hz with h | h
  · rwa [h] at hlim
  · exfalso
    have h1 : ⨅ t, F.f (F.Φ t x) ≤ F.f (F.Φ 0 x) := ciInf_le hbdd 0
    rw [F.Φ_zero, h] at h1
    exact absurd h1 (not_le.mpr (F.f_lt hM))

/-- Every flow line other than `m`, `M` crosses every intermediate level. -/
theorem exists_level {x : X} (hm : x ≠ F.m) (hM : x ≠ F.M) {c : ℝ}
    (hc₁ : F.f F.m < c) (hc₂ : c < F.f F.M) : ∃ t, F.f (F.Φ t x) = c := by
  obtain ⟨t₁, ht₁⟩ := ((F.tendsto_atBot hM).eventually (eventually_lt_nhds hc₁)).exists
  obtain ⟨t₂, ht₂⟩ := ((F.tendsto_atTop hm).eventually (eventually_gt_nhds hc₂)).exists
  have hle : t₁ ≤ t₂ := by
    by_contra h
    have h' : F.f (F.Φ t₂ x) ≤ F.f (F.Φ t₁ x) := F.monotone x (not_le.mp h).le
    linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc hle
    (F.continuous_f.comp (F.continuous_Φ_left x)).continuousOn ⟨ht₁.le, ht₂.le⟩
  exact ⟨t, ht⟩

section Level

variable {c : ℝ} (hc₁ : F.f F.m < c) (hc₂ : c < F.f F.M)
include hc₁ hc₂

theorem f_Φ_τ {x : X} (hm : x ≠ F.m) (hM : x ≠ F.M) : F.f (F.Φ (F.τ c x) x) = c :=
  Classical.epsilon_spec (F.exists_level hm hM hc₁ hc₂)

theorem f_σ {x : X} (hm : x ≠ F.m) (hM : x ≠ F.M) : F.f (F.σ c x) = c :=
  F.f_Φ_τ hc₁ hc₂ hm hM

theorem τ_eq {x : X} (hm : x ≠ F.m) (hM : x ≠ F.M) {t : ℝ} (ht : F.f (F.Φ t x) = c) :
    F.τ c x = t :=
  (F.strictMono hm hM).injective ((F.f_Φ_τ hc₁ hc₂ hm hM).trans ht.symm)

/-- The crossing time depends continuously on the starting point. -/
theorem continuousAt_τ {x₀ : X} (hm : x₀ ≠ F.m) (hM : x₀ ≠ F.M) : ContinuousAt (F.τ c) x₀ := by
  have hreg := (eventually_ne_nhds hm).and (eventually_ne_nhds hM)
  have hτ₀ := F.f_Φ_τ hc₁ hc₂ hm hM
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun a' ha' => ?_, fun b' hb' => ?_⟩
  · have h1 : F.f (F.Φ a' x₀) < c := by
      have h : F.f (F.Φ a' x₀) < F.f (F.Φ (F.τ c x₀) x₀) := F.strictMono hm hM ha'
      rwa [hτ₀] at h
    have h2 : ∀ᶠ x in 𝓝 x₀, F.f (F.Φ a' x) < c :=
      ((F.continuous_f.comp (F.continuous_Φ_right a')).tendsto x₀).eventually
        (eventually_lt_nhds h1)
    filter_upwards [h2, hreg] with x hx hxr
    by_contra hle
    have h3 : F.f (F.Φ (F.τ c x) x) ≤ F.f (F.Φ a' x) := F.monotone x (not_lt.mp hle)
    rw [F.f_Φ_τ hc₁ hc₂ hxr.1 hxr.2] at h3
    linarith
  · have h1 : c < F.f (F.Φ b' x₀) := by
      have h : F.f (F.Φ (F.τ c x₀) x₀) < F.f (F.Φ b' x₀) := F.strictMono hm hM hb'
      rwa [hτ₀] at h
    have h2 : ∀ᶠ x in 𝓝 x₀, c < F.f (F.Φ b' x) :=
      ((F.continuous_f.comp (F.continuous_Φ_right b')).tendsto x₀).eventually
        (eventually_gt_nhds h1)
    filter_upwards [h2, hreg] with x hx hxr
    by_contra hle
    have h3 : F.f (F.Φ b' x) ≤ F.f (F.Φ (F.τ c x) x) := F.monotone x (not_lt.mp hle)
    rw [F.f_Φ_τ hc₁ hc₂ hxr.1 hxr.2] at h3
    linarith

theorem continuousAt_σ {x₀ : X} (hm : x₀ ≠ F.m) (hM : x₀ ≠ F.M) : ContinuousAt (F.σ c) x₀ :=
  F.continuous_Φ.continuousAt.comp ((F.continuousAt_τ hc₁ hc₂ hm hM).prodMk continuousAt_id)

end Level

end Compact

/-! ## Assembly -/

/-- A level `c` strictly between the extreme values, together with a map `u` identifying
the level set `f = c` with the unit sphere of `ℝⁿ`. -/
structure LevelSphere (n : ℕ) where
  /-- The level. -/
  c : ℝ
  /-- The identification of the level set with the unit sphere. -/
  u : X → EuclideanSpace ℝ (Fin n)
  lt_c : F.f F.m < c
  c_lt : c < F.f F.M
  continuousOn : ContinuousOn u {x | F.f x = c}
  norm_eq : ∀ x, F.f x = c → ‖u x‖ = 1
  injOn : InjOn u {x | F.f x = c}
  surj : ∀ w, ‖w‖ = 1 → ∃ x, F.f x = c ∧ u x = w

/-- The height of `x`, rescaled to an angle in `[0, π]`. -/
noncomputable def angle (x : X) : ℝ := Real.pi * ((F.f x - F.f F.m) / (F.f F.M - F.f F.m))

theorem continuous_angle : Continuous F.angle :=
  continuous_const.mul ((F.continuous_f.sub continuous_const).div_const _)

theorem angle_m : F.angle F.m = 0 := by simp [angle]

theorem angle_M : F.angle F.M = Real.pi := by
  rw [angle, div_self (sub_ne_zero.mpr F.lt.ne'), mul_one]

theorem angle_mem (x : X) : F.angle x ∈ Icc 0 Real.pi := by
  have hba : 0 < F.f F.M - F.f F.m := sub_pos.mpr F.lt
  have h1 : 0 ≤ (F.f x - F.f F.m) / (F.f F.M - F.f F.m) :=
    div_nonneg (sub_nonneg.mpr (F.min_le x)) hba.le
  have h2 : (F.f x - F.f F.m) / (F.f F.M - F.f F.m) ≤ 1 :=
    (div_le_one hba).mpr (by linarith [F.le_max x])
  refine ⟨mul_nonneg Real.pi_pos.le h1, ?_⟩
  rw [angle]
  have := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  linarith

theorem angle_pos {x : X} (hm : x ≠ F.m) : 0 < F.angle x :=
  mul_pos Real.pi_pos (div_pos (sub_pos.mpr (F.lt_f hm)) (sub_pos.mpr F.lt))

theorem angle_lt_pi {x : X} (hM : x ≠ F.M) : F.angle x < Real.pi := by
  have hba : 0 < F.f F.M - F.f F.m := sub_pos.mpr F.lt
  have h2 : (F.f x - F.f F.m) / (F.f F.M - F.f F.m) < 1 :=
    (div_lt_one hba).mpr (by linarith [F.f_lt hM])
  have := mul_lt_mul_of_pos_left h2 Real.pi_pos
  rwa [mul_one] at this

theorem f_eq_of_angle_eq {x y : X} (h : F.angle x = F.angle y) : F.f x = F.f y := by
  have h1 := mul_left_cancel₀ Real.pi_ne_zero h
  have h2 := (div_left_inj' (sub_ne_zero.mpr F.lt.ne')).mp h1
  linarith

section Assembly

variable [CompactSpace X] [T2Space X] {F} {n : ℕ} (L : F.LevelSphere n)

/-- The map to the sphere: `x ↦ (sin θ · u(σ x), -cos θ)` with `θ` the rescaled height of
`x`.  At `m` and `M` the first component vanishes, whatever the junk value of `σ`. -/
noncomputable def sphereMap (x : X) : EuclideanSpace ℝ (Fin (n + 1)) :=
  join (Real.sin (F.angle x) • L.u (F.σ L.c x)) (-Real.cos (F.angle x))

theorem norm_first (x : X) :
    ‖Real.sin (F.angle x) • L.u (F.σ L.c x)‖ = |Real.sin (F.angle x)| := by
  by_cases hm : x = F.m
  · rw [hm, F.angle_m, Real.sin_zero, zero_smul, norm_zero, abs_zero]
  by_cases hM : x = F.M
  · rw [hM, F.angle_M, Real.sin_pi, zero_smul, norm_zero, abs_zero]
  rw [norm_smul, Real.norm_eq_abs, L.norm_eq _ (F.f_σ L.lt_c L.c_lt hm hM), mul_one]

theorem norm_sphereMap (x : X) : ‖sphereMap L x‖ = 1 := by
  have h : ‖sphereMap L x‖ ^ 2 = 1 ^ 2 := by
    rw [sphereMap, norm_join_sq, norm_first, sq_abs, neg_sq, Real.sin_sq_add_cos_sq, one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h

theorem continuousAt_first (x : X) :
    ContinuousAt (fun y => Real.sin (F.angle y) • L.u (F.σ L.c y)) x := by
  have hsin : Continuous fun y => Real.sin (F.angle y) :=
    Real.continuous_sin.comp F.continuous_angle
  by_cases hreg : x ≠ F.m ∧ x ≠ F.M
  · have hσ := F.continuousAt_σ L.lt_c L.c_lt hreg.1 hreg.2
    have hev : ∀ᶠ y in 𝓝 x, F.σ L.c y ∈ {y | F.f y = L.c} := by
      filter_upwards [(eventually_ne_nhds hreg.1).and (eventually_ne_nhds hreg.2)] with y hy
      exact F.f_σ L.lt_c L.c_lt hy.1 hy.2
    have hu : ContinuousAt (fun y => L.u (F.σ L.c y)) x :=
      (L.continuousOn _ (F.f_σ L.lt_c L.c_lt hreg.1 hreg.2)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hσ, hev⟩)
    exact hsin.continuousAt.smul hu
  · have hsin0 : Real.sin (F.angle x) = 0 := by
      rcases not_and_or.mp hreg with h | h
      · rw [not_not.mp h, F.angle_m, Real.sin_zero]
      · rw [not_not.mp h, F.angle_M, Real.sin_pi]
    have hlim : Tendsto (fun y => |Real.sin (F.angle y)|) (𝓝 x)
        (𝓝 (|Real.sin (F.angle x)|)) := (continuous_abs.comp hsin).tendsto x
    rw [hsin0, abs_zero] at hlim
    simp only [ContinuousAt, hsin0, zero_smul]
    exact squeeze_zero_norm (fun y => (norm_first L y).le) hlim

theorem continuous_sphereMap : Continuous (sphereMap L) :=
  continuous_iff_continuousAt.mpr fun x =>
    continuous_join.continuousAt.comp ((continuousAt_first L x).prodMk
      (continuous_neg.comp (Real.continuous_cos.comp F.continuous_angle)).continuousAt)

theorem sphereMap_injective : Injective (sphereMap L) := by
  intro x y hxy
  obtain ⟨h1, h2⟩ := join_inj hxy
  have hθ : F.angle x = F.angle y :=
    Real.injOn_cos (F.angle_mem x) (F.angle_mem y) (neg_inj.mp h2)
  have hf : F.f x = F.f y := F.f_eq_of_angle_eq hθ
  by_cases hxm : x = F.m
  · rw [hxm] at hf ⊢
    exact (F.eq_m y hf.symm).symm
  by_cases hxM : x = F.M
  · rw [hxM] at hf ⊢
    exact (F.eq_M y hf.symm).symm
  have hym : y ≠ F.m := fun h => hxm (F.eq_m x (by rw [hf, h]))
  have hyM : y ≠ F.M := fun h => hxM (F.eq_M x (by rw [hf, h]))
  have hsin : Real.sin (F.angle y) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (F.angle_pos hym) (F.angle_lt_pi hyM)).ne'
  rw [hθ] at h1
  have hu : L.u (F.σ L.c x) = L.u (F.σ L.c y) := smul_right_injective _ hsin h1
  have hpx := F.f_σ L.lt_c L.c_lt hxm hxM
  have hσ : F.σ L.c x = F.σ L.c y := L.injOn hpx (F.f_σ L.lt_c L.c_lt hym hyM) hu
  have hpm : F.σ L.c x ≠ F.m := F.ne_m_of_lt (by rw [hpx]; exact L.lt_c)
  have hpM : F.σ L.c x ≠ F.M := F.ne_M_of_lt (by rw [hpx]; exact L.c_lt)
  have hx' : F.Φ (-F.τ L.c x) (F.σ L.c x) = x := F.Φ_neg_Φ _ _
  have hy' : F.Φ (-F.τ L.c y) (F.σ L.c x) = y := by rw [hσ]; exact F.Φ_neg_Φ _ _
  have ht : -F.τ L.c x = -F.τ L.c y :=
    (F.strictMono hpm hpM).injective (show F.f (F.Φ (-F.τ L.c x) (F.σ L.c x)) =
      F.f (F.Φ (-F.τ L.c y) (F.σ L.c x)) by rw [hx', hy', hf])
  calc x = F.Φ (-F.τ L.c x) (F.σ L.c x) := hx'.symm
    _ = F.Φ (-F.τ L.c y) (F.σ L.c x) := by rw [ht]
    _ = y := hy'

theorem sphereMap_surjective (z : EuclideanSpace ℝ (Fin (n + 1))) (hz : ‖z‖ = 1) :
    ∃ x, sphereMap L x = z := by
  obtain ⟨w, t, rfl⟩ := exists_eq_join z
  have hnorm := norm_join_sq w t
  rw [hz, one_pow] at hnorm
  have hw2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  have ht₁ : -1 ≤ t := by nlinarith
  have ht₂ : t ≤ 1 := by nlinarith
  have hw0 : t ^ 2 = 1 → w = 0 := fun h => by
    have : ‖w‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  rcases ht₁.eq_or_lt with h | h
  · refine ⟨F.m, ?_⟩
    rw [hw0 (by rw [← h]; norm_num), ← h, sphereMap, F.angle_m, Real.sin_zero, zero_smul,
      Real.cos_zero]
  rcases ht₂.eq_or_lt with h' | h'
  · refine ⟨F.M, ?_⟩
    rw [hw0 (by rw [h']; norm_num), h', sphereMap, F.angle_M, Real.sin_pi, zero_smul,
      Real.cos_pi, neg_neg]
  -- the generic case `-1 < t < 1`
  set θ₀ := Real.arccos (-t) with hθ₀
  have hθ₀pos : 0 < θ₀ := Real.arccos_pos.mpr (by linarith)
  have hθ₀lt : θ₀ < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hcos : Real.cos θ₀ = -t := Real.cos_arccos (by linarith) (by linarith)
  have hsin : Real.sin θ₀ = ‖w‖ := by
    rw [hθ₀, Real.sin_arccos, show 1 - (-t) ^ 2 = ‖w‖ ^ 2 by linear_combination hnorm]
    exact Real.sqrt_sq (norm_nonneg w)
  have hwpos : 0 < ‖w‖ := by
    rw [← hsin]
    exact Real.sin_pos_of_pos_of_lt_pi hθ₀pos hθ₀lt
  obtain ⟨y, hyc, hyu⟩ := L.surj (‖w‖⁻¹ • w)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne'])
  have hym : y ≠ F.m := F.ne_m_of_lt (by rw [hyc]; exact L.lt_c)
  have hyM : y ≠ F.M := F.ne_M_of_lt (by rw [hyc]; exact L.c_lt)
  have hba : 0 < F.f F.M - F.f F.m := sub_pos.mpr F.lt
  have hq₁ : 0 < θ₀ / Real.pi := div_pos hθ₀pos Real.pi_pos
  have hq₂ : θ₀ / Real.pi < 1 := (div_lt_one Real.pi_pos).mpr hθ₀lt
  have hc'₁ : F.f F.m < F.f F.m + (F.f F.M - F.f F.m) * (θ₀ / Real.pi) := by
    have := mul_pos hba hq₁
    linarith
  have hc'₂ : F.f F.m + (F.f F.M - F.f F.m) * (θ₀ / Real.pi) < F.f F.M := by
    have := mul_lt_mul_of_pos_left hq₂ hba
    linarith
  obtain ⟨s, hs⟩ := F.exists_level hym hyM hc'₁ hc'₂
  have hxm : F.Φ s y ≠ F.m := F.Φ_ne_m hym s
  have hxM : F.Φ s y ≠ F.M := F.Φ_ne_M hyM s
  have hτ : F.τ L.c (F.Φ s y) = -s :=
    F.τ_eq L.lt_c L.c_lt hxm hxM (by rw [F.Φ_neg_Φ]; exact hyc)
  have hσx : F.σ L.c (F.Φ s y) = y := by
    rw [σ, hτ, F.Φ_neg_Φ]
  have hθx : F.angle (F.Φ s y) = θ₀ := by
    rw [angle, hs, show F.f F.m + (F.f F.M - F.f F.m) * (θ₀ / Real.pi) - F.f F.m =
      (F.f F.M - F.f F.m) * (θ₀ / Real.pi) by ring, mul_div_cancel_left₀ _ hba.ne',
      ← mul_div_assoc, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  refine ⟨F.Φ s y, ?_⟩
  rw [sphereMap, hθx, hσx, hyu, hsin, hcos, neg_neg, smul_smul, mul_inv_cancel₀ hwpos.ne',
    one_smul]

include L in
/-- **The assembly.**  A gradient-like flow on a compact space, with a level set
identified with `Sⁿ⁻¹`, makes the space homeomorphic to `Sⁿ`. -/
theorem nonempty_homeomorph_sphere :
    Nonempty (X ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  let Ψ : X → sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun x => ⟨sphereMap L x, mem_sphere_zero_iff_norm.mpr (norm_sphereMap L x)⟩
  have hcont : Continuous Ψ := (continuous_sphereMap L).subtype_mk _
  have hbij : Bijective Ψ := by
    refine ⟨fun x y h => sphereMap_injective L (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨x, hx⟩ := sphereMap_surjective L z.1 (mem_sphere_zero_iff_norm.mp z.2)
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨(show Continuous (Equiv.ofBijective Ψ hbij) from hcont).homeoOfEquivCompactToT2⟩

end Assembly

end GradientLikeFlow

/-! ## Charts and critical points -/

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (E) in
/-- The differential of `f : M → ℝ` at `x`, as a linear form on the model space `E`, which
is explicit because `f` and `x` do not determine it. -/
noncomputable def dF (f : M → ℝ) (x : M) : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem isCriticalPoint_iff_dF {f : M → ℝ} {x : M} :
    IsCriticalPoint 𝓘(ℝ, E) f x ↔ dF E f x = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ E] in
/-- A smooth function read in a chart is smooth on the chart's target. -/
theorem contDiffOn_chart_comp {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (x₀ : M) :
    ContDiffOn ℝ ∞ (f ∘ (chartAt E x₀).symm) (chartAt E x₀).target :=
  (hf.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn

omit [FiniteDimensional ℝ E] in
theorem differentiableAt_chart_comp {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {x₀ y : M} (hy : y ∈ (chartAt E x₀).source) :
    DifferentiableAt ℝ (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y) :=
  ((contDiffOn_chart_comp hf x₀).contDiffAt ((chartAt E x₀).open_target.mem_nhds
    ((chartAt E x₀).map_source hy))).differentiableAt (by simp)

omit [FiniteDimensional ℝ E] in
/-- The differential of `f` at `y`, computed in the chart at `x₀`: it is the differential
of `f ∘ φ⁻¹` precomposed with the tangent coordinate change from the preferred chart at
`y` to the chart at `x₀`. -/
theorem mfderiv_apply_eq {f : M → ℝ} {x₀ y : M} (hy : y ∈ (chartAt E x₀).source)
    (hg : DifferentiableAt ℝ (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) (w : E) :
    dF E f y w = fderiv ℝ (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)
        (tangentCoordChange 𝓘(ℝ, E) y x₀ y w) := by
  have heq : f =ᶠ[𝓝 y] (f ∘ (chartAt E x₀).symm) ∘ chartAt E x₀ := by
    filter_upwards [(chartAt E x₀).open_source.mem_nhds hy] with z hz
    simp only [Function.comp_apply, (chartAt E x₀).left_inv hz]
  have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x₀) y :=
    mdifferentiableAt_atlas (chart_mem_atlas E x₀) hy
  have h3 := (hg.hasFDerivAt.hasMFDerivAt.comp y hc.hasMFDerivAt).congr_of_eventuallyEq heq
  have h4 := congrArg (fun L : E →L[ℝ] ℝ => L w) h3.mfderiv
  have h5 := congrArg (fun L : E →L[ℝ] E =>
    fderiv ℝ (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y) (L w))
    (mfderiv_chartAt_eq_tangentCoordChange (I := 𝓘(ℝ, E)) hy)
  exact h4.trans h5

omit [FiniteDimensional ℝ E] in
/-- A point where `f ∘ φ⁻¹` has vanishing differential (in its own chart) is critical. -/
theorem isCriticalPoint_of_fderiv {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {x : M}
    (h : fderiv ℝ (f ∘ (chartAt E x).symm) (chartAt E x x) = 0) :
    IsCriticalPoint 𝓘(ℝ, E) f x := by
  rw [isCriticalPoint_iff_dF]
  ext w
  rw [mfderiv_apply_eq (mem_chart_source E x) (differentiableAt_chart_comp hf
    (mem_chart_source E x)), h, zero_apply, zero_apply]

omit [FiniteDimensional ℝ E] in
/-- At a critical point, `f ∘ φ⁻¹` has vanishing differential in the chart at the point. -/
theorem fderiv_eq_zero_of_isCriticalPoint {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {x : M} (h : IsCriticalPoint 𝓘(ℝ, E) f x) :
    fderiv ℝ (f ∘ (chartAt E x).symm) (chartAt E x x) = 0 := by
  rw [isCriticalPoint_iff_dF] at h
  ext w
  have h1 := mfderiv_apply_eq (mem_chart_source E x) (differentiableAt_chart_comp hf
    (mem_chart_source E x)) w
  rw [h, zero_apply, tangentCoordChange_self (mem_extChartAt_source (I := 𝓘(ℝ, E)) x)] at h1
  rw [← h1, zero_apply]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem isLocalMin_chart {f : M → ℝ} {x : M} (h : IsLocalMin f x) :
    IsLocalMin (f ∘ (chartAt E x).symm) (chartAt E x x) := by
  have h1 : IsLocalMin f ((chartAt E x).symm (chartAt E x x)) := by
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
    exact h
  exact h1.comp_continuous
    ((chartAt E x).continuousAt_symm ((chartAt E x).map_source (mem_chart_source E x)))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem isLocalMax_chart {f : M → ℝ} {x : M} (h : IsLocalMax f x) :
    IsLocalMax (f ∘ (chartAt E x).symm) (chartAt E x x) := by
  have h1 : IsLocalMax f ((chartAt E x).symm (chartAt E x x)) := by
    rw [(chartAt E x).left_inv (mem_chart_source E x)]
    exact h
  exact h1.comp_continuous
    ((chartAt E x).continuousAt_symm ((chartAt E x).map_source (mem_chart_source E x)))

omit [FiniteDimensional ℝ E] in
/-- A local minimum is a critical point. -/
theorem isCriticalPoint_of_isLocalMin {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {x : M}
    (h : IsLocalMin f x) : IsCriticalPoint 𝓘(ℝ, E) f x :=
  isCriticalPoint_of_fderiv hf (isLocalMin_chart h).fderiv_eq_zero

omit [FiniteDimensional ℝ E] in
/-- A local maximum is a critical point. -/
theorem isCriticalPoint_of_isLocalMax {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {x : M}
    (h : IsLocalMax f x) : IsCriticalPoint 𝓘(ℝ, E) f x :=
  isCriticalPoint_of_fderiv hf (isLocalMax_chart h).fderiv_eq_zero

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The Hessian at `x` is the second differential of `f ∘ φ⁻¹` in the chart at `x`. -/
theorem hessian_eq (f : M → ℝ) (x : M) :
    hessian 𝓘(ℝ, E) f x = sndFDeriv (f ∘ (chartAt E x).symm) (chartAt E x x) := by
  have h1 : writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) x f = f ∘ (chartAt E x).symm := rfl
  have h2 : extChartAt 𝓘(ℝ, E) x x = chartAt E x x := by simp [mfld_simps]
  show sndFDeriv (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ) x f) (extChartAt 𝓘(ℝ, E) x x) = _
  rw [h1, h2]

end Charts

/-! ## A gradient-like vector field -/

section GradientLike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A coordinate gradient of `g : E → ℝ`: the vector `Σᵢ dg_p(bᵢ) bᵢ` for a fixed basis `b`
of `E`. -/
noncomputable def coordGrad (g : E → ℝ) (p : E) : E :=
  ∑ i, fderiv ℝ g p (Module.finBasis ℝ E i) • Module.finBasis ℝ E i

theorem fderiv_coordGrad (g : E → ℝ) (p : E) :
    fderiv ℝ g p (coordGrad g p) = ∑ i, (fderiv ℝ g p (Module.finBasis ℝ E i)) ^ 2 := by
  simp only [coordGrad, map_sum, map_smul, smul_eq_mul, sq]

theorem fderiv_coordGrad_pos {g : E → ℝ} {p : E} (h : fderiv ℝ g p ≠ 0) :
    0 < fderiv ℝ g p (coordGrad g p) := by
  rw [fderiv_coordGrad]
  by_contra hle
  apply h
  have hsum : ∑ i, (fderiv ℝ g p (Module.finBasis ℝ E i)) ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hz : ∀ i, fderiv ℝ g p (Module.finBasis ℝ E i) = 0 := fun i =>
    pow_eq_zero_iff two_ne_zero |>.mp
      ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp hsum i (Finset.mem_univ _))
  exact ContinuousLinearMap.coe_injective ((Module.finBasis ℝ E).ext fun i => by simp [hz i])

theorem contDiffOn_coordGrad {g : E → ℝ} {s : Set E} (hs : IsOpen s)
    (hg : ContDiffOn ℝ 2 g s) : ContDiffOn ℝ 1 (coordGrad g) s := by
  have hd : ContDiffOn ℝ 1 (fun p => fderiv ℝ g p) s := hg.fderiv_of_isOpen hs (by norm_num)
  show ContDiffOn ℝ 1 (fun p => ∑ i, fderiv ℝ g p (Module.finBasis ℝ E i) •
    Module.finBasis ℝ E i) s
  exact ContDiffOn.sum fun i _ => (hd.clm_apply contDiffOn_const).smul contDiffOn_const

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The local field.**  On the chart at `x₀`, the coordinate gradient of `f ∘ φ⁻¹`,
carried to the tangent spaces by the tangent coordinate change, is a `C¹` local section
along which `df` is positive at every non-critical point. -/
theorem exists_local_section {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ s : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiffOn 𝓘(ℝ, E) (ModelWithCorners.prod 𝓘(ℝ, E) 𝓘(ℝ, E)) 1
        (fun x => TotalSpace.mk' E x (s x)) U ∧
      ∀ y ∈ U, IsCriticalPoint 𝓘(ℝ, E) f y ∨ 0 < dF E f y (s y) := by
  have hg := contDiffOn_chart_comp hf x₀
  have hG : ContDiffOn ℝ 1 (coordGrad (f ∘ (chartAt E x₀).symm)) (chartAt E x₀).target :=
    contDiffOn_coordGrad (chartAt E x₀).open_target (hg.of_le (by norm_cast))
  refine ⟨(chartAt E x₀).source, (chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀),
    fun y => tangentCoordChange 𝓘(ℝ, E) x₀ y y
      (coordGrad (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)), ?_, ?_⟩
  · have hbase : (chartAt E x₀).source ⊆
        (trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x₀).baseSet := fun _ h => h
    refine ((trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x₀).contMDiffOn_section_iff
      (chartAt E x₀).open_source hbase).mpr ?_
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
        (fun y => coordGrad (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)) (chartAt E x₀).source :=
      hG.contMDiffOn.comp contMDiffOn_chart fun y hy => (chartAt E x₀).map_source hy
    refine h1.congr fun y hy => ?_
    have hy' : y ∈ (extChartAt 𝓘(ℝ, E) x₀).source := by rwa [extChartAt_source]
    change tangentCoordChange 𝓘(ℝ, E) y x₀ y (tangentCoordChange 𝓘(ℝ, E) x₀ y y
      (coordGrad (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y))) =
      coordGrad (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)
    rw [tangentCoordChange_comp ⟨⟨hy', mem_extChartAt_source (I := 𝓘(ℝ, E)) y⟩, hy'⟩,
      tangentCoordChange_self hy']
  · intro y hy
    show IsCriticalPoint 𝓘(ℝ, E) f y ∨ 0 < dF E f y (tangentCoordChange 𝓘(ℝ, E) x₀ y y
        (coordGrad (f ∘ (chartAt E x₀).symm) (chartAt E x₀ y)))
    by_cases hc : IsCriticalPoint 𝓘(ℝ, E) f y
    · exact Or.inl hc
    refine Or.inr ?_
    have hy' : y ∈ (extChartAt 𝓘(ℝ, E) x₀).source := by rwa [extChartAt_source]
    have hd := differentiableAt_chart_comp hf hy
    rw [mfderiv_apply_eq hy hd, tangentCoordChange_comp
      ⟨⟨hy', mem_extChartAt_source (I := 𝓘(ℝ, E)) y⟩, hy'⟩, tangentCoordChange_self hy']
    refine fderiv_coordGrad_pos fun h0 => hc ?_
    rw [isCriticalPoint_iff_dF]
    ext w
    rw [mfderiv_apply_eq hy hd, h0, zero_apply, zero_apply]

/-- **A gradient-like vector field.**  On a σ-compact Hausdorff manifold, a smooth
function admits a `C¹` vector field `v` with `df(v) > 0` at every non-critical point. -/
theorem exists_gradientLike_field [T2Space M] [SigmaCompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    ∃ v : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (ModelWithCorners.tangent 𝓘(ℝ, E)) 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ x, ¬ IsCriticalPoint 𝓘(ℝ, E) f x → 0 < dF E f x (v x) := by
  let t : ∀ x : M, Set (TangentSpace 𝓘(ℝ, E) x) := fun x =>
    {w | IsCriticalPoint 𝓘(ℝ, E) f x ∨ 0 < dF E f x w}
  have hlin : ∀ (x : M) (a b : ℝ) (u u' : E),
      dF E f x (a • u + b • u') = a * dF E f x u + b * dF E f x u' := by
    intro x a b u u'
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : IsCriticalPoint 𝓘(ℝ, E) f x
    · have : t x = univ := eq_univ_of_forall fun w => Or.inl hx
      rw [this]
      exact convex_univ
    · intro w₁ h₁ w₂ h₂ α β hα hβ hαβ
      have h₁' : 0 < dF E f x w₁ := Or.resolve_left h₁ hx
      have h₂' : 0 < dF E f x w₂ := Or.resolve_left h₂ hx
      refine Or.inr (lt_of_lt_of_eq ?_ (hlin x α β w₁ w₂).symm)
      rcases hα.eq_or_lt with hα' | hα'
      · rw [← hα', zero_add] at hαβ
        rw [← hα', hαβ]
        linarith
      · have := mul_pos hα' h₁'
        have := mul_nonneg hβ h₂'.le
        linarith
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local 𝓘(ℝ, E) (n := 1)
    (F_fiber := E)
    (TangentSpace 𝓘(ℝ, E) : M → Type _) t ht fun x₀ => exists_local_section hf x₀
  exact ⟨fun x => s x, s.contMDiff, fun x hx => Or.resolve_left (hs x) hx⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Along an integral curve of `v`, the derivative of `f` is `df(v)`. -/
theorem hasDerivAt_comp_integralCurve {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {γ : ℝ → M} {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (dF E f (γ t) (v (γ t))) t := by
  have h1 : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ) f (γ t) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (γ t)) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 := h1.comp t (hγ t)
  rw [hasMFDerivAt_iff_hasFDerivAt] at h2
  -- restated with the model-space types, so that `hasDerivAt` finds the instances on `ℝ`
  -- rather than on the tangent spaces
  have h3 : HasFDerivAt (f ∘ γ) ((dF E f (γ t)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t :=
    h2
  refine h3.hasDerivAt.congr_deriv (congrArg (dF E f (γ t)) ?_)
  show (1 : ℝ →L[ℝ] ℝ) 1 • v (γ t) = v (γ t)
  exact one_smul ℝ (v (γ t))

end GradientLike

/-! ## The Morse chart at the minimum -/

section MorseChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A nonnegative, nondegenerate symmetric bilinear form is positive definite. -/
theorem pos_of_nonneg_of_nondegenerate {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ v w, B v w = B w v) (hnn : ∀ v, 0 ≤ B v v) (hnd : IsNondegenerate B)
    {v : E} (hv : v ≠ 0) : 0 < B v v := by
  refine (hnn v).lt_of_ne fun h => hv (hnd v fun w => ?_)
  have key : ∀ t : ℝ, 0 ≤ 2 * t * B v w + t ^ 2 * B w w := by
    intro t
    have e1 : B (v + t • w) (v + t • w) = B v v + 2 * t * B v w + t ^ 2 * B w w := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [hsymm w v]
      ring
    have := hnn (v + t • w)
    rw [e1, ← h] at this
    linarith
  have hγ : 0 ≤ B w w := hnn w
  have hne : B w w + 1 ≠ 0 := by linarith
  have hu : (B w w + 1) * (B w w + 1)⁻¹ = 1 := mul_inv_cancel₀ hne
  have h2 : 0 ≤ (B w w + 1) ^ 2 * (2 * (-(B v w) / (B w w + 1)) * B v w +
      (-(B v w) / (B w w + 1)) ^ 2 * B w w) :=
    mul_nonneg (sq_nonneg _) (key _)
  have h3 : (B w w + 1) ^ 2 * (2 * (-(B v w) / (B w w + 1)) * B v w +
      (-(B v w) / (B w w + 1)) ^ 2 * B w w) = -(B v w ^ 2 * (B w w + 2)) := by
    linear_combination (B v w ^ 2 * B w w * ((B w w + 1) * (B w w + 1)⁻¹) -
      B v w ^ 2 * (B w w + 2)) * hu
  rw [h3] at h2
  have h4 : B v w ^ 2 = 0 := by
    nlinarith [sq_nonneg (B v w), mul_nonneg (sq_nonneg (B v w)) hγ]
  exact pow_eq_zero_iff two_ne_zero |>.mp h4

omit [FiniteDimensional ℝ E] in
theorem apply_smul_smul (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (z : E) :
    B (r • z) (r • z) = r ^ 2 * B z z := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
/-- A bilinear form nonnegative on a ball about `0` is nonnegative. -/
theorem nonneg_of_ball {B : E →L[ℝ] E →L[ℝ] ℝ} {R : ℝ} (hR : 0 < R)
    (h : ∀ z ∈ ball (0 : E) R, 0 ≤ B z z) (z : E) : 0 ≤ B z z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hr : 0 < R / 2 / ‖z‖ := div_pos (half_pos hR) hz'
  have hmem : (R / 2 / ‖z‖) • z ∈ ball (0 : E) R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le, div_mul_cancel₀ _ hz'.ne']
    linarith
  have h1 := h _ hmem
  rw [apply_smul_smul] at h1
  by_contra hneg
  have := mul_neg_of_pos_of_neg (pow_pos hr 2) (not_le.mp hneg)
  linarith

/-- **The level set near a nondegenerate minimum, abstractly.**  Suppose that on an open
set `N` the function `f` is `a + ½ B(h, h)` for an injective continuous `h` whose image
contains a ball about `0`, with `B` positive definite, and that `f ≥ a + δ₀` off `N`.
Then some level `c` slightly above `a` is identified with the unit sphere of `E` by
`x ↦ h x / ‖h x‖`. -/
theorem exists_level_sphere_of_chart {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    {N : Set X} {h : X → E} {B : E →L[ℝ] E →L[ℝ] ℝ} {a b R δ₀ : ℝ} (hR : 0 < R)
    (hδ₀ : 0 < δ₀) (hab : a < b) (hh : ContinuousOn h N) (hinj : InjOn h N)
    (hball : ball (0 : E) R ⊆ h '' N) (hBpos : ∀ z, z ≠ 0 → 0 < B z z)
    (hfN : ∀ x ∈ N, f x = a + (1 / 2) * B (h x) (h x)) (hout : ∀ x, x ∉ N → a + δ₀ ≤ f x)
    (w₀ : E) (hw₀ : ‖w₀‖ = 1) :
    ∃ c, a < c ∧ c < b ∧ ∃ u : X → E, ContinuousOn u {x | f x = c} ∧
      (∀ x, f x = c → ‖u x‖ = 1) ∧ InjOn u {x | f x = c} ∧
      ∀ w : E, ‖w‖ = 1 → ∃ x, f x = c ∧ u x = w := by
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn (f := fun z => B z z)
    ⟨w₀, mem_sphere_zero_iff_norm.mpr hw₀⟩
    (B.continuous.clm_apply continuous_id).continuousOn
  have hz₁ne : z₁ ≠ 0 := by
    rintro rfl
    simp at hz₁
  have hβ : 0 < B z₁ z₁ := hBpos z₁ hz₁ne
  have hβle : ∀ w : E, ‖w‖ = 1 → B z₁ z₁ ≤ B w w := fun w hw =>
    isMinOn_iff.mp hmin w (mem_sphere_zero_iff_norm.mpr hw)
  have hBR : 0 < B z₁ z₁ * R ^ 2 / 2 := div_pos (mul_pos hβ (pow_pos hR 2)) two_pos
  have hmpos : 0 < min (min δ₀ (B z₁ z₁ * R ^ 2 / 2)) (b - a) :=
    lt_min (lt_min hδ₀ hBR) (by linarith)
  have hm1 := min_le_left (min δ₀ (B z₁ z₁ * R ^ 2 / 2)) (b - a)
  have hm2 := min_le_right (min δ₀ (B z₁ z₁ * R ^ 2 / 2)) (b - a)
  have hm3 := min_le_left δ₀ (B z₁ z₁ * R ^ 2 / 2)
  have hm4 := min_le_right δ₀ (B z₁ z₁ * R ^ 2 / 2)
  obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < δ₀ ∧ 2 * ε < B z₁ z₁ * R ^ 2 ∧
      ε < b - a :=
    ⟨min (min δ₀ (B z₁ z₁ * R ^ 2 / 2)) (b - a) / 2, by linarith, by linarith, by linarith,
      by linarith⟩
  have hL : ∀ x, f x = a + ε → x ∈ N ∧ B (h x) (h x) = 2 * ε := by
    intro x hx
    have hxN : x ∈ N := by
      by_contra hxN
      have := hout x hxN
      linarith
    refine ⟨hxN, ?_⟩
    have := hfN x hxN
    linarith
  have hne : ∀ x, f x = a + ε → h x ≠ 0 := by
    intro x hx h0
    have := (hL x hx).2
    rw [h0] at this
    simp at this
    linarith
  have hunit : ∀ x, f x = a + ε → ‖‖h x‖⁻¹ • h x‖ = 1 := fun x hx => by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne x hx))]
  refine ⟨a + ε, by linarith, by linarith, fun x => ‖h x‖⁻¹ • h x, ?_, hunit, ?_, ?_⟩
  · have hh' : ContinuousOn h {x | f x = a + ε} := hh.mono fun x hx => (hL x hx).1
    exact (hh'.norm.inv₀ fun x hx => norm_ne_zero_iff.mpr (hne x hx)).smul hh'
  · intro x hx y hy hxy
    have hx' : f x = a + ε := hx
    have hy' : f y = a + ε := hy
    have hxy' : ‖h x‖⁻¹ • h x = ‖h y‖⁻¹ • h y := hxy
    obtain ⟨U, hU⟩ : ∃ U, U = ‖h x‖⁻¹ • h x := ⟨_, rfl⟩
    have hUne : U ≠ 0 := fun h0 => by
      have := hunit x hx'
      rw [← hU, h0, norm_zero] at this
      exact zero_ne_one this
    have hxU : h x = ‖h x‖ • U := by
      rw [hU, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne x hx')), one_smul]
    have hyU : h y = ‖h y‖ • U := by
      rw [hU, hxy', smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne y hy')), one_smul]
    have e1 := (hL x hx').2
    have e2 := (hL y hy').2
    rw [hxU, apply_smul_smul] at e1
    rw [hyU, apply_smul_smul] at e2
    have hpos := hBpos U hUne
    have hsq : ‖h x‖ ^ 2 = ‖h y‖ ^ 2 := by
      have := e1.trans e2.symm
      exact mul_right_cancel₀ hpos.ne' this
    have hn : ‖h x‖ = ‖h y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    exact hinj (hL x hx').1 (hL y hy').1 (by rw [hxU, hyU, hn])
  · intro w hw
    have hBw : 0 < B w w := hBpos w (by rintro rfl; simp at hw)
    have hle := hβle w hw
    set r := Real.sqrt (2 * ε / B w w) with hr
    have hr2 : r ^ 2 = 2 * ε / B w w := Real.sq_sqrt (div_nonneg (by linarith) hBw.le)
    have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos (by linarith) hBw)
    have hrR : r < R := by
      rw [hr, Real.sqrt_lt' hR, div_lt_iff₀ hBw]
      linarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R)]
    have hmem : r • w ∈ ball (0 : E) R := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hrpos.le, hw, mul_one]
      exact hrR
    obtain ⟨x, hxN, hxw⟩ := hball hmem
    have hfx : f x = a + ε := by
      rw [hfN x hxN, hxw, apply_smul_smul, hr2, div_mul_cancel₀ _ hBw.ne']
      ring
    refine ⟨x, hfx, ?_⟩
    show ‖h x‖⁻¹ • h x = w
    rw [hxw, norm_smul, Real.norm_of_nonneg hrpos.le, hw, mul_one, smul_smul,
      inv_mul_cancel₀ hrpos.ne', one_smul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **The level set near the minimum.**  At a nondegenerate critical point `m` which is
the unique minimum of `f`, the Morse lemma identifies a level set slightly above `f m`
with the unit sphere of the model space. -/
theorem exists_level_sphere [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {m : M} (hcrit : IsCriticalPoint 𝓘(ℝ, E) f m)
    (hnd : IsNondegenerate (hessian 𝓘(ℝ, E) f m)) (hmin : ∀ x, f m ≤ f x)
    (hunique : ∀ x, f x = f m → x = m) {b : ℝ} (hb : f m < b) (w₀ : E) (hw₀ : ‖w₀‖ = 1) :
    ∃ c, f m < c ∧ c < b ∧ ∃ u : M → E, ContinuousOn u {x | f x = c} ∧
      (∀ x, f x = c → ‖u x‖ = 1) ∧ InjOn u {x | f x = c} ∧
      ∀ w : E, ‖w‖ = 1 → ∃ x, f x = c ∧ u x = w := by
  have hp₀ : chartAt E m m ∈ (chartAt E m).target :=
    (chartAt E m).map_source (mem_chart_source E m)
  have hg3 : ContDiffAt ℝ 3 (f ∘ (chartAt E m).symm) (chartAt E m m) :=
    ((contDiffOn_chart_comp hf m).contDiffAt ((chartAt E m).open_target.mem_nhds hp₀)).of_le
      (by norm_cast)
  have hcrit' := fderiv_eq_zero_of_isCriticalPoint hf hcrit
  have hnd' : IsNondegenerate (sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m)) := by
    rwa [hessian_eq] at hnd
  obtain ⟨ψ, hψsrc, hψ0, hψ⟩ := morse_lemma_of_contDiffAt hg3 hcrit' hnd'
  have hgm : (f ∘ (chartAt E m).symm) (chartAt E m m) = f m := by
    simp only [Function.comp_apply, (chartAt E m).left_inv (mem_chart_source E m)]
  have hBsymm : ∀ v w, sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m) v w =
      sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m) w v :=
    sndFDeriv_symm (hg3.of_le (by norm_num))
  have hSopen : IsOpen (ψ.source ∩ (chartAt E m).target) :=
    ψ.open_source.inter (chartAt E m).open_target
  have hNopen : IsOpen ((chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target)) :=
    (chartAt E m).isOpen_inter_preimage hSopen
  have hmN : m ∈ (chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target) :=
    ⟨mem_chart_source E m, hψsrc, hp₀⟩
  have hfN : ∀ x ∈ (chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target),
      f x = f m + (1 / 2) * sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m)
        (ψ (chartAt E m x)) (ψ (chartAt E m x)) := by
    intro x hx
    have h1 := hψ (chartAt E m x) hx.2.1
    rw [hgm] at h1
    rw [← h1]
    simp only [Function.comp_apply, (chartAt E m).left_inv hx.1]
  have hinj : InjOn (fun x => ψ (chartAt E m x))
      ((chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target)) :=
    fun x hx y hy hxy => (chartAt E m).injOn hx.1 hy.1 (ψ.injOn hx.2.1 hy.2.1 hxy)
  have hcont : ContinuousOn (fun x => ψ (chartAt E m x))
      ((chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target)) :=
    ψ.continuousOn.comp ((chartAt E m).continuousOn.mono inter_subset_left)
      fun x hx => hx.2.1
  obtain ⟨R, hR, hball⟩ : ∃ R > 0, ball (0 : E) R ⊆ (fun x => ψ (chartAt E m x)) ''
      ((chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target)) := by
    have h1 : ψ '' (ψ.source ∩ (chartAt E m).target) ∈ 𝓝 (ψ (chartAt E m m)) :=
      ψ.image_mem_nhds hψsrc (hSopen.mem_nhds ⟨hψsrc, hp₀⟩)
    rw [hψ0] at h1
    obtain ⟨R, hR, hR'⟩ := Metric.mem_nhds_iff.mp h1
    refine ⟨R, hR, hR'.trans ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(chartAt E m).symm p, ⟨(chartAt E m).map_target hp.2, ?_⟩, ?_⟩
    · rw [mem_preimage, (chartAt E m).right_inv hp.2]
      exact hp
    · simp only [(chartAt E m).right_inv hp.2]
  have hnn : ∀ z, 0 ≤ sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m) z z :=
    nonneg_of_ball hR fun z hz => by
      obtain ⟨x, hx, rfl⟩ := hball hz
      show 0 ≤ sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m) (ψ (chartAt E m x))
        (ψ (chartAt E m x))
      have h1 := hfN x hx
      have h2 := hmin x
      linarith
  have hBpos : ∀ z, z ≠ 0 → 0 < sndFDeriv (f ∘ (chartAt E m).symm) (chartAt E m m) z z :=
    fun z hz => pos_of_nonneg_of_nondegenerate hBsymm hnn hnd' hz
  obtain ⟨δ₀, hδ₀, hout⟩ : ∃ δ₀ > 0, ∀ x, x ∉ (chartAt E m).source ∩
      chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target) → f m + δ₀ ≤ f x := by
    rcases ((chartAt E m).source ∩ chartAt E m ⁻¹' (ψ.source ∩ (chartAt E m).target))ᶜ.eq_empty_or_nonempty with hK | hK
    · refine ⟨1, one_pos, fun x hx => absurd ?_ hx⟩
      rw [compl_empty_iff.mp hK]
      exact mem_univ x
    · obtain ⟨x₁, hx₁, hmin₁⟩ := hNopen.isClosed_compl.isCompact.exists_isMinOn hK
        hf.continuous.continuousOn
      refine ⟨f x₁ - f m, ?_, fun x hx => ?_⟩
      · have hne : x₁ ≠ m := fun h' => hx₁ (by rw [h']; exact hmN)
        have := lt_of_le_of_ne (hmin x₁) fun h' => hne (hunique x₁ h'.symm)
        linarith
      · have := isMinOn_iff.mp hmin₁ x hx
        linarith
  exact exists_level_sphere_of_chart hR hδ₀ hb hcont hinj hball hBpos hfN hout w₀ hw₀

end MorseChart

/-! ## The theorem -/

/-- In positive dimension, no point of a manifold is open. -/
theorem not_isOpen_singleton_of_pos {n : ℕ} (hn : 0 < n) {V : Type*} [TopologicalSpace V]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) V] (x : V) : ¬ IsOpen ({x} : Set V) := by
  intro h
  have h1 : IsOpen ((chartAt (EuclideanSpace ℝ (Fin n)) x) '' {x}) :=
    (chartAt _ x).isOpen_image_of_subset_source h
      (singleton_subset_iff.mpr (mem_chart_source _ x))
  rw [image_singleton] at h1
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, 0, fun h0 => by
      have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) h0
      simp at this⟩⟩
  have := Module.punctured_nhds_neBot ℝ (EuclideanSpace ℝ (Fin n))
    (chartAt (EuclideanSpace ℝ (Fin n)) x x)
  exact not_isOpen_singleton _ h1

/-- Reeb's theorem in dimension zero: `V` has exactly two points. -/
theorem reeb_zero {V : Type*} [TopologicalSpace V] [T2Space V] [CompactSpace V]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) V] (f : V → ℝ)
    (hcard : {x : V | IsCriticalPoint (𝓡 0) f x}.ncard = 2) :
    Nonempty (V ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (0 + 1))) 1) := by
  classical
  have hzero : ∀ w : EuclideanSpace ℝ (Fin 0), w = 0 := fun w => by
    ext i
    exact i.elim0
  have hall : {x : V | IsCriticalPoint (𝓡 0) f x} = univ := eq_univ_of_forall fun x => by
    show mfderiv (𝓡 0) 𝓘(ℝ) f x = 0
    ext w
    rw [show w = 0 from hzero w, map_zero, map_zero]
  rw [hall] at hcard
  obtain ⟨x, y, hxy, huniv⟩ := Set.ncard_eq_two.mp hcard
  have hmem : ∀ z : V, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set V) := by
      rw [← huniv]
      exact mem_univ z
    simpa using this
  have : Finite V := Set.finite_univ_iff.mp (by rw [huniv]; exact Set.toFinite _)
  let F : GradientLikeFlow V :=
    { f := fun z => if z = x then 0 else 1
      Φ := fun _ z => z
      D := fun _ => 0
      m := x
      M := y
      continuous_f := continuous_of_discreteTopology
      continuous_Φ := continuous_snd
      Φ_zero := fun _ => rfl
      Φ_add := fun _ _ _ => rfl
      hasDerivAt := fun _ t => hasDerivAt_const t _
      D_nonneg := fun _ => le_rfl
      D_pos := fun z h1 h2 => ((hmem z).elim h1 h2).elim
      min_le := fun z => by by_cases h : z = x <;> simp [h]
      le_max := fun z => by by_cases h : z = x <;> simp [h, hxy.symm]
      eq_m := fun z hz => by
        by_contra h
        simp [h] at hz
      eq_M := fun z hz => by
        rcases hmem z with h | h
        · rw [h] at hz
          simp [hxy.symm] at hz
        · exact h
      lt := by simp [hxy.symm] }
  have hlevel : ∀ z : V, F.f z ≠ 1 / 2 := fun z => by
    change (if z = x then (0 : ℝ) else 1) ≠ 1 / 2
    by_cases h : z = x <;> norm_num [h]
  exact GradientLikeFlow.nonempty_homeomorph_sphere (F := F) (n := 0)
    { c := 1 / 2
      u := fun _ => 0
      lt_c := by
        change (if x = x then (0 : ℝ) else 1) < 1 / 2
        norm_num
      c_lt := by
        change (1 : ℝ) / 2 < if y = x then 0 else 1
        norm_num [hxy.symm]
      continuousOn := continuousOn_const
      norm_eq := fun z hz => absurd hz (hlevel z)
      injOn := fun z hz _ _ _ => absurd hz (hlevel z)
      surj := fun w hw => absurd hw (by rw [hzero w, norm_zero]; norm_num) }

end Reeb

open Reeb in
/-- **Corollary 2.1.9 (Reeb's theorem).**  A compact Hausdorff manifold carrying a smooth
Morse function with exactly two critical points is homeomorphic to a sphere.

See the module docstring for the route: a gradient-like flow (`exists_gradientLike_field`,
`exists_flow`) carries every non-extremal point to a level set that the Morse lemma at
the minimum identifies with `Sⁿ⁻¹` (`exists_level_sphere`), and the height together with
that point gives the homeomorphism (`GradientLikeFlow.nonempty_homeomorph_sphere`). -/
theorem reeb_general {n : ℕ} {V : Type*} [TopologicalSpace V] [T2Space V] [CompactSpace V]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) V] [IsManifold (𝓡 n) ω V]
    (f : V → ℝ) (hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ f) (hf : IsMorseFunction (𝓡 n) f)
    (hcard : {x : V | IsCriticalPoint (𝓡 n) f x}.ncard = 2) :
    Nonempty (V ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact reeb_zero f hcard
  -- the two critical points
  have hfin : {x : V | IsCriticalPoint (𝓡 n) f x}.Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨x₀, -⟩ := Set.nonempty_of_ncard_ne_zero
    (s := {x : V | IsCriticalPoint (𝓡 n) f x}) (by omega)
  have : Nonempty V := ⟨x₀⟩
  obtain ⟨m, -, hm⟩ := isCompact_univ.exists_isMinOn univ_nonempty hsmooth.continuous.continuousOn
  obtain ⟨M, -, hM⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hsmooth.continuous.continuousOn
  have hmin : ∀ x, f m ≤ f x := fun x => isMinOn_iff.mp hm x (mem_univ x)
  have hmax : ∀ x, f x ≤ f M := fun x => isMaxOn_iff.mp hM x (mem_univ x)
  have hcm : IsCriticalPoint (𝓡 n) f m :=
    isCriticalPoint_of_isLocalMin hsmooth (Eventually.of_forall hmin)
  have hcM : IsCriticalPoint (𝓡 n) f M :=
    isCriticalPoint_of_isLocalMax hsmooth (Eventually.of_forall hmax)
  have hlt : f m < f M := by
    by_contra hle
    have hconst : ∀ x, f x = f m := fun x =>
      le_antisymm ((hmax x).trans (not_lt.mp hle)) (hmin x)
    have hall : {x : V | IsCriticalPoint (𝓡 n) f x} = univ := eq_univ_of_forall fun x =>
      isCriticalPoint_of_isLocalMin hsmooth
        (Eventually.of_forall fun y => by rw [hconst x, hconst y])
    rw [hall] at hfin
    have : Finite V := Set.finite_univ_iff.mp hfin
    exact not_isOpen_singleton_of_pos hn x₀ (isOpen_discrete {x₀})
  have hmM : m ≠ M := fun h => by
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hsub : ({m, M} : Set V) ⊆ {x | IsCriticalPoint (𝓡 n) f x} := by
    rintro x (rfl | rfl)
    · exact hcm
    · exact hcM
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hmM]) hfin
  have hcrit_iff : ∀ x, IsCriticalPoint (𝓡 n) f x → x = m ∨ x = M := fun x hx => by
    have : x ∈ ({m, M} : Set V) := by
      rw [heq]
      exact hx
    simpa using this
  have eq_m : ∀ x, f x = f m → x = m := by
    intro x hx
    have hc := isCriticalPoint_of_isLocalMin hsmooth
      (Eventually.of_forall fun y => by rw [hx]; exact hmin y)
    rcases hcrit_iff x hc with h | h
    · exact h
    · rw [h] at hx
      exact absurd hx (ne_of_gt hlt)
  have eq_M : ∀ x, f x = f M → x = M := by
    intro x hx
    have hc := isCriticalPoint_of_isLocalMax hsmooth
      (Eventually.of_forall fun y => by rw [hx]; exact hmax y)
    rcases hcrit_iff x hc with h | h
    · rw [h] at hx
      exact absurd hx.symm (ne_of_gt hlt)
    · exact h
  -- the gradient-like flow
  obtain ⟨v, hv, hvpos⟩ := exists_gradientLike_field hsmooth
  obtain ⟨Φ, hΦc, hΦ0, hΦint, hΦadd⟩ := exists_flow hv
  let F : GradientLikeFlow V :=
    { f := f
      Φ := Φ
      D := fun x => dF (EuclideanSpace ℝ (Fin n)) f x (v x)
      m := m
      M := M
      continuous_f := hsmooth.continuous
      continuous_Φ := hΦc
      Φ_zero := hΦ0
      Φ_add := hΦadd
      hasDerivAt := fun x t => hasDerivAt_comp_integralCurve hsmooth (hΦint x) t
      D_nonneg := fun x => by
        show 0 ≤ dF (EuclideanSpace ℝ (Fin n)) f x (v x)
        by_cases hx : IsCriticalPoint (𝓡 n) f x
        · rw [isCriticalPoint_iff_dF.mp hx]
          exact (zero_apply (v x)).symm.le
        · exact (hvpos x hx).le
      D_pos := fun x h1 h2 => hvpos x fun hx => (hcrit_iff x hx).elim h1 h2
      min_le := hmin
      le_max := hmax
      eq_m := eq_m
      eq_M := eq_M
      lt := hlt }
  -- the level set near the minimum
  have hw₀ : ‖EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ = 1 := by simp
  obtain ⟨c, hc₁, hc₂, u, hu_cont, hu_norm, hu_inj, hu_surj⟩ :=
    exists_level_sphere hsmooth hcm (hf m hcm) hmin eq_m hlt _ hw₀
  exact GradientLikeFlow.nonempty_homeomorph_sphere (F := F)
    { c := c, u := u, lt_c := hc₁, c_lt := hc₂, continuousOn := hu_cont, norm_eq := hu_norm,
      injOn := hu_inj, surj := hu_surj }

end MorseFloer
