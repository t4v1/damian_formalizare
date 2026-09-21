import Mathlib

/-!
# Approximate periodic orbits converge to periodic orbits

A helper for Proposition 6.5.7 of Audin–Damian.  The book extracts, from a
finite-energy solution `u` of the Floer equation, a sequence `s_k → ±∞` along
which the loops `u(s_k, ·)` solve Hamilton's equation up to an error that tends
to `0` in `L²`, and then invokes Ascoli's theorem and an elliptic bootstrap to
produce a limiting periodic orbit.

Neither is needed.  A loop that solves `ẋ = X_t(x)` up to an error small in `L¹`
stays close to any other such loop with a nearby starting point, by Grönwall's
inequality applied to the difference *minus the integrated errors*.  So once the
starting points converge the loops form a Cauchy sequence at every time, and the
pointwise limit solves the integral equation — dominated convergence — hence is
a genuine periodic orbit.

The file is independent of the rest of the project: it is about a bounded,
uniformly Lipschitz, `1`-periodic time-dependent vector field on a Banach space.

* `exists_seq_atTop`, `exists_seq_atBot`: an integrable nonnegative function on
  the line tends to `0` along some sequence going to `+∞`, and to `-∞`;
* `tendsto_window`: the integral of an integrable function over a moving window of
  fixed length tends to `0` at both ends;
* `tendsto_atTop_of_antitone_of_seq`, `tendsto_atBot_of_antitone_of_seq`: an
  antitone function converging along one such sequence converges;
* `norm_sub_le_of_approx`: the Grönwall comparison of two approximate solutions;
* `exists_orbit_of_approx`: the limiting periodic orbit.
-/

open Filter Topology MeasureTheory Set

namespace MorseFloer
namespace ApproxOrbit

/-! ## Sequences along which an integrable function is small -/

/-- An integrable nonnegative function on the line is small somewhere beyond any
given point; otherwise a positive constant would be integrable on a half-line. -/
theorem exists_seq_atTop {g : ℝ → ℝ} (hg : Integrable g) (h0 : ∀ s, 0 ≤ g s) :
    ∃ s : ℕ → ℝ, Tendsto s atTop atTop ∧ Tendsto (fun k => g (s k)) atTop (𝓝 0) := by
  have key : ∀ k : ℕ, ∃ s : ℝ, (k : ℝ) < s ∧ g s < 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    push Not at hcon
    have hpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hc : IntegrableOn (fun _ : ℝ => (1 / ((k : ℝ) + 1) : ℝ)) (Ioi (k : ℝ)) := by
      refine Integrable.mono' hg.integrableOn aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_of_nonneg hpos.le]
      exact hcon s hs
    rw [integrableOn_const_iff] at hc
    rcases hc with hc | hc
    · exact hpos.ne' (enorm_eq_zero.mp hc)
    · rw [Real.volume_Ioi] at hc
      exact lt_irrefl _ hc
  choose s hs1 hs2 using key
  refine ⟨s, tendsto_atTop_mono (fun k => (hs1 k).le) tendsto_natCast_atTop_atTop, ?_⟩
  exact squeeze_zero (fun k => h0 _) (fun k => (hs2 k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The same towards `-∞`. -/
theorem exists_seq_atBot {g : ℝ → ℝ} (hg : Integrable g) (h0 : ∀ s, 0 ≤ g s) :
    ∃ s : ℕ → ℝ, Tendsto s atTop atBot ∧ Tendsto (fun k => g (s k)) atTop (𝓝 0) := by
  have key : ∀ k : ℕ, ∃ s : ℝ, s < -(k : ℝ) ∧ g s < 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    push Not at hcon
    have hpos : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hc : IntegrableOn (fun _ : ℝ => (1 / ((k : ℝ) + 1) : ℝ)) (Iio (-(k : ℝ))) := by
      refine Integrable.mono' hg.integrableOn aestronglyMeasurable_const ?_
      refine (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_of_nonneg hpos.le]
      exact hcon s hs
    rw [integrableOn_const_iff] at hc
    rcases hc with hc | hc
    · exact hpos.ne' (enorm_eq_zero.mp hc)
    · rw [Real.volume_Iio] at hc
      exact lt_irrefl _ hc
  choose s hs1 hs2 using key
  refine ⟨s, tendsto_atBot_mono (fun k => (hs1 k).le)
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop), ?_⟩
  exact squeeze_zero (fun k => h0 _) (fun k => (hs2 k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The integral of an integrable function over a moving window of fixed length tends to
zero** at both ends of the line. -/
theorem tendsto_window {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun a : ℝ => ∫ s in (a - 1 / 2)..(a + 1 / 2), g s) atTop (𝓝 0) ∧
      Tendsto (fun a : ℝ => ∫ s in (a - 1 / 2)..(a + 1 / 2), g s) atBot (𝓝 0) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable
  constructor
  · have h1 : Tendsto (fun a : ℝ => ∫ s in (0:ℝ)..(a + 1 / 2), g s) atTop
        (𝓝 (∫ s in Ioi (0:ℝ), g s)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn
        (tendsto_atTop_add_const_right _ _ tendsto_id)
    have h2 : Tendsto (fun a : ℝ => ∫ s in (0:ℝ)..(a - 1 / 2), g s) atTop
        (𝓝 (∫ s in Ioi (0:ℝ), g s)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hg.integrableOn
        (tendsto_atTop_add_const_right _ (-(1 / 2)) tendsto_id)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    refine h3.congr fun a => ?_
    exact intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)
  · have h1 : Tendsto (fun a : ℝ => ∫ s in (a - 1 / 2)..(0:ℝ), g s) atBot
        (𝓝 (∫ s in Iic (0:ℝ), g s)) :=
      intervalIntegral_tendsto_integral_Iic 0 hg.integrableOn
        (tendsto_atBot_add_const_right _ (-(1 / 2)) tendsto_id)
    have h2 : Tendsto (fun a : ℝ => ∫ s in (a + 1 / 2)..(0:ℝ), g s) atBot
        (𝓝 (∫ s in Iic (0:ℝ), g s)) :=
      intervalIntegral_tendsto_integral_Iic 0 hg.integrableOn
        (tendsto_atBot_add_const_right _ _ tendsto_id)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    refine h3.congr fun a => ?_
    have := intervalIntegral.integral_add_adjacent_intervals (hii (a - 1 / 2) (a + 1 / 2))
      (hii (a + 1 / 2) 0)
    linarith

/-- `c · x/(c+1) < x`: the elementary inequality behind every "choose the parameter so that
this term is below a third of `η`". -/
theorem mul_div_add_one_lt {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) : c * (x / (c + 1)) < x := by
  rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
  nlinarith

/-! ## Antitone functions converging along a sequence -/

/-- An antitone function which converges along a sequence going to `+∞` converges
at `+∞`, to the same limit. -/
theorem tendsto_atTop_of_antitone_of_seq {f : ℝ → ℝ} (hf : Antitone f) {s : ℕ → ℝ} {a : ℝ}
    (hs : Tendsto s atTop atTop) (hfs : Tendsto (fun k => f (s k)) atTop (𝓝 a)) :
    Tendsto f atTop (𝓝 a) := by
  have hbdd : BddBelow (range f) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨σ, rfl⟩
    refine le_of_tendsto hfs ?_
    filter_upwards [hs.eventually_ge_atTop σ] with k hk using hf hk
  have h1 := tendsto_atTop_ciInf hf hbdd
  have h2 : Tendsto (fun k => f (s k)) atTop (𝓝 (⨅ i, f i)) := h1.comp hs
  rw [tendsto_nhds_unique hfs h2]
  exact h1

/-- The same at `-∞`. -/
theorem tendsto_atBot_of_antitone_of_seq {f : ℝ → ℝ} (hf : Antitone f) {s : ℕ → ℝ} {a : ℝ}
    (hs : Tendsto s atTop atBot) (hfs : Tendsto (fun k => f (s k)) atTop (𝓝 a)) :
    Tendsto f atBot (𝓝 a) := by
  have hbdd : BddAbove (range f) := by
    refine ⟨a, ?_⟩
    rintro _ ⟨σ, rfl⟩
    refine ge_of_tendsto hfs ?_
    filter_upwards [hs.eventually_le_atBot σ] with k hk using hf hk
  have h1 := tendsto_atBot_ciSup hf hbdd
  have h2 : Tendsto (fun k => f (s k)) atTop (𝓝 (⨆ i, f i)) := h1.comp hs
  rw [tendsto_nhds_unique hfs h2]
  exact h1

/-! ## The sup norm against the Euclidean one -/

/-- The sup norm of a vector is at most its Euclidean norm. -/
theorem norm_le_sqrt_dotProduct {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ≤ Real.sqrt (v ⬝ᵥ v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have h : v i * v i ≤ v ⬝ᵥ v :=
    Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
      (Finset.mem_univ i)
  calc v i ^ 2 = v i * v i := sq _
    _ ≤ v ⬝ᵥ v := h

/-- The arithmetic–geometric form in which an `L²` bound yields an `L¹` bound without the
Cauchy–Schwarz inequality: `‖v‖ ≤ δ/2 + |v|²/(2δ)`. -/
theorem norm_le_add_dotProduct {ι : Type*} [Fintype ι] (v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖v‖ ≤ δ / 2 + (v ⬝ᵥ v) / (2 * δ) := by
  have hq : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
  have h1 : ‖v‖ ^ 2 ≤ v ⬝ᵥ v := by
    calc ‖v‖ ^ 2 ≤ Real.sqrt (v ⬝ᵥ v) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_sqrt_dotProduct v) 2
      _ = v ⬝ᵥ v := Real.sq_sqrt hq
  have h2 : 2 * δ * ‖v‖ ≤ δ ^ 2 + v ⬝ᵥ v := by nlinarith [sq_nonneg (‖v‖ - δ)]
  have h3 : δ / 2 + (v ⬝ᵥ v) / (2 * δ) = (δ ^ 2 + v ⬝ᵥ v) / (2 * δ) := by
    field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  linarith

/-! ## Periodic functions -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a `1`-periodic function is `1`-periodic. -/
theorem periodic_deriv {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hper : Function.Periodic f 1) : Function.Periodic f' 1 := by
  intro t
  have h1 : HasDerivAt (fun τ => f (τ + 1)) (f' (t + 1)) t := (hf (t + 1)).comp_add_const t 1
  have h2 : (fun τ => f (τ + 1)) = f := funext hper
  rw [h2] at h1
  exact h1.unique (hf t)

/-- A `1`-periodic function takes at `t` the value it takes at the fractional part. -/
theorem periodic_eq_fract {α : Type*} {f : ℝ → α} (hper : Function.Periodic f 1) (t : ℝ) :
    f t = f (Int.fract t) := by
  have h := hper.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one, Int.self_sub_floor] at h
  exact h.symm

/-- The integral of a nonnegative `1`-periodic function over an interval of length at
most `1` is at most its integral over a period. -/
theorem integral_le_of_periodic {e : ℝ → ℝ} (hc : Continuous e) (h0 : ∀ t, 0 ≤ e t)
    (hper : Function.Periodic e 1) {a t : ℝ} (hat : a ≤ t) (hta : t ≤ a + 1) :
    ∫ τ in a..t, e τ ≤ ∫ τ in (0:ℝ)..1, e τ := by
  have h1 : ∫ τ in a..t, e τ ≤ ∫ τ in a..(a + 1), e τ :=
    intervalIntegral.integral_mono_interval le_rfl hat hta (Eventually.of_forall h0)
      (hc.intervalIntegrable _ _)
  have h2 : ∫ τ in a..(a + 1), e τ = ∫ τ in (0:ℝ)..(0 + 1), e τ :=
    hper.intervalIntegral_add_eq a 0
  rw [h2, zero_add] at h1
  exact h1

/-! ## The Grönwall comparison -/

variable [CompleteSpace E]

/-- **Two approximate solutions stay close.**  If `f` and `g` solve `ẋ = X_t(x)` up to
errors whose `L¹` norms over `[0, 1]` are `η_f` and `η_g`, then on `[0, 1]` they stay within
`(‖f 0 - g 0‖ + 2 (η_f + η_g)) e^K` of one another.  Grönwall's inequality is applied not to
`f - g`, whose derivative is controlled only in `L¹`, but to `f - g` minus the integral of the
difference of the errors, whose derivative is `X_t(f) - X_t(g)` exactly. -/
theorem norm_sub_le_of_approx {X : ℝ → E → E} {K : ℝ} (hK : 0 < K)
    (hXlip : ∀ t a b, ‖X t a - X t b‖ ≤ K * ‖a - b‖)
    {f g f' g' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hef : Continuous fun t => f' t - X t (f t)) (heg : Continuous fun t => g' t - X t (g t))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖f t - g t‖ ≤ (‖f 0 - g 0‖ + 2 * ((∫ τ in (0:ℝ)..1, ‖f' τ - X τ (f τ)‖)
      + ∫ τ in (0:ℝ)..1, ‖g' τ - X τ (g τ)‖)) * Real.exp K := by
  set ef : ℝ → E := fun t => f' t - X t (f t) with hef_def
  set eg : ℝ → E := fun t => g' t - X t (g t) with heg_def
  set η : ℝ := (∫ τ in (0:ℝ)..1, ‖ef τ‖) + ∫ τ in (0:ℝ)..1, ‖eg τ‖ with hη_def
  have hdc : Continuous fun τ => ef τ - eg τ := hef.sub heg
  have hnc : Continuous fun τ => ‖ef τ‖ + ‖eg τ‖ := hef.norm.add heg.norm
  have hη0 : 0 ≤ η := add_nonneg
    (intervalIntegral.integral_nonneg zero_le_one fun τ _ => norm_nonneg _)
    (intervalIntegral.integral_nonneg zero_le_one fun τ _ => norm_nonneg _)
  -- the integrated error
  set I : ℝ → E := fun t => ∫ τ in (0:ℝ)..t, (ef τ - eg τ) with hI_def
  have hI : ∀ t, HasDerivAt I (ef t - eg t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hdc.intervalIntegrable _ _)
      (hdc.stronglyMeasurableAtFilter _ _) hdc.continuousAt
  have hIle : ∀ t ∈ Icc (0:ℝ) 1, ‖I t‖ ≤ η := by
    intro t ht
    calc ‖I t‖ ≤ ∫ τ in (0:ℝ)..t, ‖ef τ - eg τ‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ τ in (0:ℝ)..t, (‖ef τ‖ + ‖eg τ‖) :=
          intervalIntegral.integral_mono_on ht.1 (hdc.norm.intervalIntegrable _ _)
            (hnc.intervalIntegrable _ _) fun τ _ => norm_sub_le _ _
      _ ≤ ∫ τ in (0:ℝ)..1, (‖ef τ‖ + ‖eg τ‖) :=
          intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun τ => add_nonneg (norm_nonneg _) (norm_nonneg _))
            (hnc.intervalIntegrable _ _)
      _ = η := intervalIntegral.integral_add (hef.norm.intervalIntegrable _ _)
            (heg.norm.intervalIntegrable _ _)
  -- the corrected difference
  set w : ℝ → E := fun t => f t - g t - I t with hw_def
  have hw : ∀ t, HasDerivAt w (X t (f t) - X t (g t)) t := fun t => by
    have h := ((hf t).sub (hg t)).sub (hI t)
    refine h.congr_deriv ?_
    simp only [hef_def, heg_def]
    abel
  have hw0 : w 0 = f 0 - g 0 := by
    simp only [hw_def, hI_def, intervalIntegral.integral_same, sub_zero]
  have hbound : ∀ τ ∈ Ico (0:ℝ) 1, ‖X τ (f τ) - X τ (g τ)‖ ≤ K * ‖w τ‖ + K * η := by
    intro τ hτ
    have h1 : f τ - g τ = w τ + I τ := by simp only [hw_def]; abel
    calc ‖X τ (f τ) - X τ (g τ)‖ ≤ K * ‖f τ - g τ‖ := hXlip _ _ _
      _ = K * ‖w τ + I τ‖ := by rw [h1]
      _ ≤ K * (‖w τ‖ + η) := by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact hIle τ (Ico_subset_Icc_self hτ))
      _ = K * ‖w τ‖ + K * η := by ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (f := w)
    (f' := fun τ => X τ (f τ) - X τ (g τ)) (δ := ‖f 0 - g 0‖) (K := K) (ε := K * η)
    (a := 0) (b := 1)
    (fun τ _ => (hw τ).continuousAt.continuousWithinAt)
    (fun τ _ => (hw τ).hasDerivWithinAt) (by rw [hw0]) hbound t ht
  rw [gronwallBound_of_K_ne_0 hK.ne', sub_zero] at hgron
  have hKη : K * η / K = η := by field_simp
  rw [hKη] at hgron
  have hexp1 : Real.exp (K * t) ≤ Real.exp K := by
    apply Real.exp_le_exp.2
    nlinarith [ht.1, ht.2]
  have hexp0 : 1 ≤ Real.exp K := Real.one_le_exp hK.le
  have hexpt : 0 < Real.exp (K * t) := Real.exp_pos _
  have hd0 : 0 ≤ ‖f 0 - g 0‖ := norm_nonneg _
  have hwt : ‖w t‖ ≤ (‖f 0 - g 0‖ + η) * Real.exp K := by
    calc ‖w t‖ ≤ ‖f 0 - g 0‖ * Real.exp (K * t) + η * (Real.exp (K * t) - 1) := hgron
      _ ≤ ‖f 0 - g 0‖ * Real.exp K + η * Real.exp K := by
          gcongr
          linarith
      _ = (‖f 0 - g 0‖ + η) * Real.exp K := by ring
  have h1 : f t - g t = w t + I t := by simp only [hw_def]; abel
  calc ‖f t - g t‖ = ‖w t + I t‖ := by rw [h1]
    _ ≤ ‖w t‖ + ‖I t‖ := norm_add_le _ _
    _ ≤ (‖f 0 - g 0‖ + η) * Real.exp K + η := add_le_add hwt (hIle t ht)
    _ ≤ (‖f 0 - g 0‖ + η) * Real.exp K + η * Real.exp K := by
        gcongr
        exact le_mul_of_one_le_right hη0 hexp0
    _ = (‖f 0 - g 0‖ + 2 * η) * Real.exp K := by ring

/-! ## The limiting orbit -/

/-- **Approximate periodic orbits converge to a periodic orbit.**  Let `X` be a
time-dependent vector field, continuous, bounded, uniformly Lipschitz in the point and
`1`-periodic in time.  If the `1`-periodic `C¹` loops `y k` solve `ẋ = X_t(x)` up to errors
tending to `0` in `L¹` over a period, and their starting points converge, then they converge
at every time, and the limit is a `1`-periodic orbit of `X`. -/
theorem exists_orbit_of_approx {X : ℝ → E → E} {K M : ℝ}
    (hXc : Continuous fun q : ℝ × E => X q.1 q.2)
    (hXlip : ∀ t a b, ‖X t a - X t b‖ ≤ K * ‖a - b‖)
    (hXbd : ∀ t a, ‖X t a‖ ≤ M)
    {y y' : ℕ → ℝ → E}
    (hy : ∀ k t, HasDerivAt (y k) (y' k t) t)
    (hy'c : ∀ k, Continuous (y' k))
    (hper : ∀ k, Function.Periodic (y k) 1)
    (heper : ∀ k, Function.Periodic (fun t => ‖y' k t - X t (y k t)‖) 1)
    (hE : Tendsto (fun k => ∫ t in (0:ℝ)..1, ‖y' k t - X t (y k t)‖) atTop (𝓝 0))
    {p : E} (hp : Tendsto (fun k => y k 0) atTop (𝓝 p)) :
    ∃ x : ℝ → E, (∀ t, HasDerivAt x (X t (x t)) t) ∧ Function.Periodic x 1 ∧
      ∀ t, Tendsto (fun k => y k t) atTop (𝓝 (x t)) := by
  -- a positive Lipschitz constant
  set K' : ℝ := |K| + 1 with hK'_def
  have hK' : 0 < K' := by positivity
  have hXlip' : ∀ t a b, ‖X t a - X t b‖ ≤ K' * ‖a - b‖ := fun t a b =>
    (hXlip t a b).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self K).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _))
  have hyc : ∀ k, Continuous (y k) := fun k =>
    continuous_iff_continuousAt.2 fun t => (hy k t).continuousAt
  have hec : ∀ k, Continuous fun t => y' k t - X t (y k t) := fun k =>
    (hy'c k).sub (hXc.comp (continuous_id.prodMk (hyc k)))
  set η : ℕ → ℝ := fun k => ∫ t in (0:ℝ)..1, ‖y' k t - X t (y k t)‖ with hη_def
  have hη0 : ∀ k, 0 ≤ η k := fun k =>
    intervalIntegral.integral_nonneg zero_le_one fun τ _ => norm_nonneg _
  -- the loops are a Cauchy sequence at every time of `[0, 1]`
  have hcauchy01 : ∀ t ∈ Icc (0:ℝ) 1, CauchySeq fun k => y k t := by
    intro t ht
    rw [Metric.cauchySeq_iff']
    intro ε hε
    set ε₁ : ℝ := ε / (6 * Real.exp K') with hε₁_def
    have hε₁ : 0 < ε₁ := by positivity
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hp.cauchySeq ε₁ hε₁
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_order.1 hE).2 ε₁ hε₁)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn1 : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn2 : N₂ ≤ n := (le_max_right _ _).trans hn
    have h0 : ‖y n 0 - y (max N₁ N₂) 0‖ < ε₁ := by
      rw [← dist_eq_norm]
      exact hN₁ n hn1 _ (le_max_left _ _)
    have hηn : η n < ε₁ := hN₂ n hn2
    have hηN : η (max N₁ N₂) < ε₁ := hN₂ _ (le_max_right _ _)
    have hcmp := norm_sub_le_of_approx hK' hXlip' (hy n) (hy (max N₁ N₂)) (hec n)
      (hec (max N₁ N₂)) ht
    have hexp : 0 < Real.exp K' := Real.exp_pos _
    rw [dist_eq_norm]
    calc ‖y n t - y (max N₁ N₂) t‖
        ≤ (‖y n 0 - y (max N₁ N₂) 0‖ + 2 * (η n + η (max N₁ N₂))) * Real.exp K' := hcmp
      _ < (ε₁ + 2 * (ε₁ + ε₁)) * Real.exp K' := by
          apply mul_lt_mul_of_pos_right _ hexp
          linarith
      _ = 5 / 6 * ε := by
          rw [hε₁_def]
          field_simp
          ring
      _ < ε := by linarith
  -- hence at every time, by periodicity
  have hcauchy : ∀ t, CauchySeq fun k => y k t := by
    intro t
    have h := hcauchy01 (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    have he : (fun k => y k t) = fun k => y k (Int.fract t) :=
      funext fun k => periodic_eq_fract (hper k) t
    rw [he]
    exact h
  choose x hx using fun t => cauchySeq_tendsto_of_complete (hcauchy t)
  have hxper : Function.Periodic x 1 := by
    intro t
    have he : (fun k => y k (t + 1)) = fun k => y k t := funext fun k => hper k t
    have h := hx (t + 1)
    rw [he] at h
    exact tendsto_nhds_unique h (hx t)
  have hXt : ∀ τ, Continuous (X τ) := fun τ =>
    hXc.comp (continuous_const.prodMk continuous_id)
  -- the limit solves the integral equation on every interval of length at most `1`
  have hint : ∀ a t, a ≤ t → t ≤ a + 1 → x t - x a = ∫ τ in a..t, X τ (x τ) := by
    intro a t hat hta
    have hXyc : ∀ k, Continuous fun τ => X τ (y k τ) := fun k =>
      hXc.comp (continuous_id.prodMk (hyc k))
    have h1 : ∀ k, (∫ τ in a..t, X τ (y k τ))
        = (y k t - y k a) - ∫ τ in a..t, (y' k τ - X τ (y k τ)) := by
      intro k
      have hftc : ∫ τ in a..t, y' k τ = y k t - y k a :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hy k τ)
          ((hy'c k).intervalIntegrable a t)
      rw [← hftc, ← intervalIntegral.integral_sub ((hy'c k).intervalIntegrable a t)
        ((hec k).intervalIntegrable a t)]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp
    have lim2 : Tendsto (fun k => ∫ τ in a..t, (y' k τ - X τ (y k τ))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) hE
      calc ‖∫ τ in a..t, (y' k τ - X τ (y k τ))‖
          ≤ ∫ τ in a..t, ‖y' k τ - X τ (y k τ)‖ :=
            intervalIntegral.norm_integral_le_integral_norm hat
        _ ≤ ∫ τ in (0:ℝ)..1, ‖y' k τ - X τ (y k τ)‖ :=
            integral_le_of_periodic (hec k).norm (fun τ => norm_nonneg _) (heper k) hat hta
    have lim1 : Tendsto (fun k => ∫ τ in a..t, X τ (y k τ)) atTop (𝓝 (x t - x a - 0)) := by
      have := ((hx t).sub (hx a)).sub lim2
      refine this.congr fun k => ?_
      rw [h1 k]
    have lim3 : Tendsto (fun k => ∫ τ in a..t, X τ (y k τ)) atTop
        (𝓝 (∫ τ in a..t, X τ (x τ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
        (Eventually.of_forall fun k => (hXyc k).aestronglyMeasurable)
        (Eventually.of_forall fun k => Eventually.of_forall fun τ _ => hXbd _ _)
        intervalIntegrable_const
        (Eventually.of_forall fun τ _ => ((hXt τ).tendsto (x τ)).comp (hx τ))
    have := tendsto_nhds_unique lim1 lim3
    rw [sub_zero] at this
    exact this
  -- so it is locally Lipschitz, hence continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hXbd 0 0)
  have hlip1 : ∀ a t, a ≤ t → t ≤ a + 1 → ‖x t - x a‖ ≤ M * |t - a| := by
    intro a t hat hta
    rw [hint a t hat hta]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => hXbd _ _
  have hlip : ∀ t₀ t, |t - t₀| ≤ 1 → ‖x t - x t₀‖ ≤ M * |t - t₀| := by
    intro t₀ t h
    rcases le_total t₀ t with hle | hle
    · exact hlip1 t₀ t hle (by linarith [(abs_le.1 h).2])
    · rw [norm_sub_rev, abs_sub_comm]
      exact hlip1 t t₀ hle (by linarith [(abs_le.1 h).1])
  have hxc : Continuous x := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hcont : Continuous fun t : ℝ => M * |t - t₀| := by fun_prop
    have h0 : Tendsto (fun t : ℝ => M * |t - t₀|) (𝓝 t₀) (𝓝 0) := by
      have := hcont.tendsto t₀
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ h0
    filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    exact hlip t₀ t ht
  -- and differentiable, by the fundamental theorem of calculus
  have hgc : Continuous fun τ => X τ (x τ) := hXc.comp (continuous_id.prodMk hxc)
  refine ⟨x, fun t₀ => ?_, hxper, hx⟩
  have hF : HasDerivAt (fun t => x (t₀ - 1 / 2) + ∫ τ in (t₀ - 1 / 2)..t, X τ (x τ))
      (X t₀ (x t₀)) t₀ :=
    (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt).const_add _
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show t₀ - 1 / 2 < t₀ by linarith)
    (show t₀ < t₀ - 1 / 2 + 1 by linarith)] with t ht
  exact eq_add_of_sub_eq' (hint (t₀ - 1 / 2) t ht.1.le ht.2.le)

end ApproxOrbit
end MorseFloer
