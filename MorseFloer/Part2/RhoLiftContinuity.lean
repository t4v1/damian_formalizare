import MorseFloer.Part2.RhoLift

/-!
# Lemma 7.1.6: the lift of `ρ` is continuous on `Sp(2n)⋆`

The lift `ρ̃` of `Part2/RhoLift.lean` is continuous on `Sp(2n)⋆`, the symplectic matrices without
the eigenvalue `1` (`continuousOn_rhoLift`); together with `exp(i ρ̃) = ρ` on `Sp(2n)⁺` and
`exp(i(ρ̃ + π)) = ρ` on `Sp(2n)⁻` this is **Lemma 7.1.6** (`exists_lift_plus`,
`exists_lift_minus`).

The proof follows that of the continuity of `ρ` in `Part2/Rho.lean`: at `A₀`, small disjoint
discs about the distinct eigenvalues capture the spectrum of nearby `A`, `ρ̃(A)` is the sum of
the local sums over the discs, and each local sum tends to the local term of the centre
`c₀`.  Below the real axis the local sum is `0`; above it and off the circle it is `π m(D)`;
at a real `c₀ ≠ ±1` it is `(π/2) m(D)`, the non-real eigenvalues in the disc coming in
conjugate pairs; at `c₀ = -1` the identity `2π m₋(μ) + σ(μ) arg μ = π m(μ) + σ(μ) arg(-μ)`
reduces it to `(π/2) m(D)` plus a sum of bounded weights against `arg(-μ) → 0`; and on the
upper half of the circle it is `2π m₋(V_D) + ∑ σ(μ) arg μ`, where the negative index of the
sum `V_D` of the eigenspaces of the disc is locally constant (`Part2/SignatureContinuity.lean`),
`∑ σ(μ) = σ(c₀)` (Corollary 7.3.9) and `arg` is continuous at `c₀`.
-/

open Polynomial Matrix Module Filter Topology

namespace MorseFloer
namespace Rho

open Chapter7 SymplecticEigen SymplecticSpectrum EigenDecomp EigenMult HermitianIndex
  SignatureContinuity

/-! ### Weighted sums of values close to a limit -/

/-- If the finsets `s x` have at most `N` elements, the integer weights are bounded by `N`, and
the values `v μ` are eventually within `ε` of `v₀` on `s x` for every `ε`, the weighted sum of
`v μ - v₀` tends to `0`. -/
theorem tendsto_sum_weighted {X : Type*} {F : Filter X} (N : ℕ) (s : X → Finset ℂ)
    (e : X → ℂ → ℤ) (v : ℂ → ℝ) (v₀ : ℝ) (hcard : ∀ x, (s x).card ≤ N)
    (he : ∀ x, ∀ μ ∈ s x, (e x μ).natAbs ≤ N)
    (hv : ∀ ε > 0, ∀ᶠ x in F, ∀ μ ∈ s x, |v μ - v₀| < ε) :
    Tendsto (fun x => ∑ μ ∈ s x, (e x μ : ℝ) * (v μ - v₀)) F (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hε : 0 < δ / (N * N + 1) := by positivity
  filter_upwards [hv _ hε] with x hx
  rw [dist_zero_right, Real.norm_eq_abs]
  calc |∑ μ ∈ s x, (e x μ : ℝ) * (v μ - v₀)| ≤ ∑ μ ∈ s x, |(e x μ : ℝ) * (v μ - v₀)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _μ ∈ s x, (N : ℝ) * (δ / (N * N + 1)) := by
        refine Finset.sum_le_sum fun μ hμ => ?_
        rw [abs_mul]
        refine mul_le_mul ?_ (hx μ hμ).le (abs_nonneg _) (by positivity)
        rw [← Int.cast_abs, Int.abs_eq_natAbs]
        exact_mod_cast he x μ hμ
    _ = (s x).card * ((N : ℝ) * (δ / (N * N + 1))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * ((N : ℝ) * (δ / (N * N + 1))) := by
        gcongr
        exact_mod_cast hcard x
    _ < δ := by
        have h4 : (N : ℝ) * (N * (δ / (N * N + 1))) = δ * (N * N / (N * N + 1)) := by ring
        rw [h4]
        exact mul_lt_of_lt_one_right hδ ((div_lt_one (by positivity)).2 (by linarith))

/-! ### The local sums -/

variable {l : Type*} [DecidableEq l] [Fintype l]

open Classical in
/-- The local sum: the terms of the eigenvalues in the disc. -/
noncomputable def localSum (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (c₀ : ℂ) (r : ℝ) : ℝ :=
  ∑ μ ∈ discRoots M c₀ r, liftTerm M μ

open Classical in
theorem rhoLiftC_eq_sum_localSum (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (R : Finset ℂ) (r : ℝ)
    (hcover : ∀ z ∈ M.charpoly.roots, ∃ c ∈ R, dist z c < r)
    (hdisj : ∀ c ∈ R, ∀ c' ∈ R, c ≠ c' → 2 * r ≤ dist c c') :
    rhoLiftC M = ∑ c ∈ R, localSum M c r := by
  have e : M.charpoly.roots.toFinset = R.biUnion fun c => discRoots M c r := by
    ext z
    simp only [Finset.mem_biUnion, mem_discRoots, Multiset.mem_toFinset]
    constructor
    · intro hz
      obtain ⟨c, hc, h⟩ := hcover z hz
      exact ⟨c, hc, hz, h⟩
    · rintro ⟨c, -, hz, -⟩
      exact hz
  rw [rhoLiftC, e, Finset.sum_biUnion]
  · rfl
  intro c hc c' hc' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro z hz hz'
  rw [mem_discRoots] at hz hz'
  have := dist_triangle c z c'
  rw [dist_comm c z] at this
  linarith [hdisj c hc c' hc' hne, hz.2, hz'.2]

open Classical in
theorem localSum_self {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} (hc₀ : c₀ ∈ M.charpoly.roots)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ z ∈ M.charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) :
    localSum M c₀ r = liftTerm M c₀ := by
  have e : discRoots M c₀ r = {c₀} := by
    ext z
    rw [mem_discRoots, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hzr⟩
      by_contra hne
      have := hsep z hz hne
      linarith
    · intro hz
      rw [hz]
      exact ⟨hc₀, by rw [dist_self]; exact hr⟩
  rw [localSum, e, Finset.sum_singleton]

/-- A four-way split of a sum over the distinct eigenvalues. -/
theorem sum_split4 (T : Finset ℂ) (f : ℂ → ℝ) :
    ∑ μ ∈ T, f μ
      = (∑ μ ∈ T.filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), f μ)
        + ((∑ μ ∈ T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im), f μ)
        + ((∑ μ ∈ T.filter (fun z => z.im = 0), f μ)
        + ∑ μ ∈ T.filter (fun z => z.im < 0), f μ)) := by
  have e3 : ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter (fun z => ¬0 < z.im)).filter
      (fun z => z.im = 0) = T.filter (fun z => z.im = 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h0, -⟩, -⟩, h⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨⟨h0, fun h' => by rw [h] at h'; exact lt_irrefl _ h'.2⟩, by rw [h]; exact lt_irrefl _⟩, h⟩
  have e4 : ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter (fun z => ¬0 < z.im)).filter
      (fun z => ¬z.im = 0) = T.filter (fun z => z.im < 0) := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨h0, -⟩, h1⟩, h2⟩
      exact ⟨h0, lt_of_le_of_ne (not_lt.1 h1) h2⟩
    · rintro ⟨h0, h⟩
      exact ⟨⟨⟨h0, fun h' => by linarith [h'.2]⟩, by linarith⟩, h.ne⟩
  rw [← Finset.sum_filter_add_sum_filter_not T (fun z => ‖z‖ = 1 ∧ 0 < z.im),
    ← Finset.sum_filter_add_sum_filter_not (T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)))
      (fun z => 0 < z.im),
    ← Finset.sum_filter_add_sum_filter_not ((T.filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im))).filter
      (fun z => ¬0 < z.im)) (fun z => z.im = 0), e3, e4, Finset.filter_filter]

open Classical in
/-- On the upper circle, `2π m₋(μ) + σ(μ) arg μ = π m(μ) + σ(μ) arg(-μ)`. -/
theorem liftTerm_circle_eq {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {μ : ℂ} (h : ‖μ‖ = 1 ∧ 0 < μ.im) :
    liftTerm M μ = Real.pi * (M.charpoly.roots.count μ : ℝ)
      + (sigma M μ : ℝ) * Complex.arg (-μ) := by
  rw [liftTerm_of_circle h, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h.2]
  have : (sigma M μ : ℝ) = 2 * (mPos M μ : ℝ) - (M.charpoly.roots.count μ : ℝ) := by
    rw [sigma]
    push_cast
    ring
  rw [this]
  ring

/-! ### The eventual facts -/

open Classical in
/-- The eigenvalues of the disc, counted along the four kinds. -/
theorem count_disc_split {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} {c₀ : ℂ} (hc₀ : c₀.im = 0) (r : ℝ) :
    Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z c₀ < r)
      = Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im = 0)
        + 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z c₀ < r ∧ 0 < z.im) := by
  have hconj : ∀ z : ℂ, dist (starRingEnd ℂ z) c₀ < r ↔ dist z c₀ < r := by
    intro z
    have e : c₀ = starRingEnd ℂ c₀ := (Complex.conj_eq_iff_im.2 hc₀).symm
    conv_lhs => rw [e]
    rw [Complex.dist_conj_conj]
  rw [← card_filter_im_ne_zero A (fun z => dist z c₀ < r) hconj]
  exact card_filter_eq_add _ _ _ _ (fun z _ => by tauto) (fun z _ => by tauto)

open Classical in
theorem sum_count_upper_split (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (c₀ : ℂ) (r : ℝ) :
    Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ 0 < z.im)
      = ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), M.charpoly.roots.count μ
        + ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im),
            M.charpoly.roots.count μ := by
  rw [discRoots, Finset.filter_filter, Finset.filter_filter, sum_count_filter, sum_count_filter]
  refine card_filter_eq_add _ _ _ _ (fun z _ => ?_) (fun z _ h => h.2.2.1 h.1.2)
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : ‖z‖ = 1
    · exact Or.inl ⟨h1, h, h2⟩
    · exact Or.inr ⟨h1, fun h' => h h'.1, h2⟩
  · rintro (⟨h1, -, h2⟩ | ⟨h1, -, h2⟩) <;> exact ⟨h1, h2⟩

open Classical in
/-- **The negative index of the disc is locally constant**: near `A₀`, for a circle eigenvalue
`c₀`, `dim V_D - m₊(V_D) = m(c₀) - m₊(c₀)`. -/
theorem eventually_negIndex {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ) {c₀ : ℂ} (hc₀n : ‖c₀‖ = 1) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀) :
    ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀,
      (finrank ℂ (discSpace c₀ r (cpx A)) : ℝ) - (posIndex GForm (discSpace c₀ r (cpx A)) : ℝ)
        = ((cpx A₀).charpoly.roots.count c₀ : ℝ) - (mPos (cpx A₀) c₀ : ℝ) := by
  set M₀ := cpx A₀ with hM₀
  have hcirc : ∀ z ∈ M₀.charpoly.roots, dist z c₀ ≠ r := by
    intro z hz h
    by_cases hne : z = c₀
    · rw [hne, dist_self] at h
      linarith
    · have := hsep z hz hne
      linarith
  have hnd : ∀ v ∈ discSpace c₀ r M₀, (∀ w ∈ discSpace c₀ r M₀, GForm v w = 0) → v = 0 := by
    intro v hv h
    rw [discSpace, fPoly_eq_fS] at hv h
    refine eq_zero_of_mem_kerAeval_fS_of_forall (fun z => dist z c₀ < r) (HForm_cpx hA₀)
      ?_ hv fun w hw => ?_
    · intro z hz hzr
      have hz' : z = c₀ := by
        by_contra hne
        have := hsep z hz hne
        linarith
      rw [hz', inv_conj_of_norm_one hc₀n, dist_self]
      exact hr
    · rw [← GForm_eq_zero_iff]
      exact h w hw
  have hpos := (continuous_cpx.tendsto A₀).eventually (eventually_posIndex_eq c₀ r M₀ hcirc hnd)
  filter_upwards [eventually_facts c₀ hr hsep hr le_rfl, hpos.filter_mono nhdsWithin_le_nhds]
    with A hA hApos
  obtain ⟨-, -, hcount, -⟩ := hA
  rw [hApos, discSpace_self hr hsep, discSpace, fPoly_eq_fS, finrank_kerAeval_fS, hcount, mPos]

/-! ### The local limits -/

open Classical in
/-- **Below the real axis**: the local sum vanishes. -/
theorem localSum_eq_zero {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} {r : ℝ}
    (hD : ∀ z : ℂ, dist z c₀ < r → z.im < 0) : localSum M c₀ r = 0 :=
  Finset.sum_eq_zero fun μ hμ => liftTerm_of_lower (hD μ (mem_discRoots.1 hμ).2)

open Classical in
/-- **Above the real axis, off the circle**: the local sum is `π m(D)`. -/
theorem localSum_eq_of_upper {M : Matrix (l ⊕ l) (l ⊕ l) ℂ} {c₀ : ℂ} {r : ℝ}
    (hD : ∀ z : ℂ, dist z c₀ < r → 0 < z.im ∧ ‖z‖ ≠ 1) :
    localSum M c₀ r = Real.pi * Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r) := by
  rw [localSum, ← sum_count_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  obtain ⟨h1, h2⟩ := hD μ (Finset.mem_filter.1 hμ).2
  rw [liftTerm_of_upper (fun h => h2 h.1) h1]

open Classical in
/-- **At a real `c₀ ≠ ±1`**: the local sum is `(π/2) m(D)`. -/
theorem localSum_eq_of_real {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} {c₀ : ℂ} (hc₀ : c₀.im = 0) {r : ℝ}
    (hD : ∀ z : ℂ, dist z c₀ < r → ‖z‖ ≠ 1) :
    localSum (cpx A) c₀ r
      = Real.pi / 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z c₀ < r) := by
  set M := cpx A with hM
  rw [localSum, sum_split4, count_disc_split hc₀, sum_count_upper_split]
  have h1 : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), liftTerm M μ = 0 := by
    refine Finset.sum_eq_zero fun μ hμ => ?_
    rw [Finset.mem_filter, mem_discRoots] at hμ
    exact absurd hμ.2.1 (hD μ hμ.1.2)
  have h1' : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im),
      M.charpoly.roots.count μ = 0 := by
    refine Finset.sum_eq_zero fun μ hμ => ?_
    rw [Finset.mem_filter, mem_discRoots] at hμ
    exact absurd hμ.2.1 (hD μ hμ.1.2)
  have h2 : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im),
      liftTerm M μ = Real.pi * ∑ μ ∈ (discRoots M c₀ r).filter
        (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im), (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [liftTerm_of_upper hμ.2.1 hμ.2.2]
  have h3 : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => z.im = 0), liftTerm M μ
      = Real.pi / 2 * ∑ μ ∈ (discRoots M c₀ r).filter (fun z => z.im = 0),
          (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [liftTerm_of_real hμ.2]
  have h4 : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => z.im < 0), liftTerm M μ = 0 :=
    Finset.sum_eq_zero fun μ hμ => liftTerm_of_lower (Finset.mem_filter.1 hμ).2
  have h5 : Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r ∧ z.im = 0)
      = ∑ μ ∈ (discRoots M c₀ r).filter (fun z => z.im = 0), M.charpoly.roots.count μ := by
    rw [discRoots, Finset.filter_filter, sum_count_filter]
  rw [h1, h2, h3, h4, h5, h1']
  push_cast
  ring

open Classical in
/-- **At `c₀ = -1`**: the local sum is `(π/2) m(D)` plus a sum of bounded weights against
`arg(-μ)`, which tends to `0`. -/
theorem localSum_eq_of_neg_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} {r : ℝ} :
    localSum (cpx A) (-1) r
      = Real.pi / 2 * Multiset.card ((cpx A).charpoly.roots.filter fun z => dist z (-1) < r)
        + ∑ μ ∈ (discRoots (cpx A) (-1) r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im),
            (sigma (cpx A) μ : ℝ) * (Complex.arg (-μ) - Complex.arg (-(-1 : ℂ))) := by
  set M := cpx A with hM
  have hc₀ : (-1 : ℂ).im = 0 := by simp
  rw [localSum, sum_split4, count_disc_split hc₀, sum_count_upper_split]
  have h1 : ∑ μ ∈ (discRoots M (-1) r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im), liftTerm M μ
      = Real.pi * ∑ μ ∈ (discRoots M (-1) r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im),
          (M.charpoly.roots.count μ : ℝ)
        + ∑ μ ∈ (discRoots M (-1) r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im),
            (sigma M μ : ℝ) * (Complex.arg (-μ) - Complex.arg (-(-1 : ℂ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [liftTerm_circle_eq hμ.2, neg_neg, Complex.arg_one, sub_zero]
  have h2 : ∑ μ ∈ (discRoots M (-1) r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im),
      liftTerm M μ = Real.pi * ∑ μ ∈ (discRoots M (-1) r).filter
        (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im) ∧ 0 < z.im), (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [liftTerm_of_upper hμ.2.1 hμ.2.2]
  have h3 : ∑ μ ∈ (discRoots M (-1) r).filter (fun z => z.im = 0), liftTerm M μ
      = Real.pi / 2 * ∑ μ ∈ (discRoots M (-1) r).filter (fun z => z.im = 0),
          (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [liftTerm_of_real hμ.2]
  have h4 : ∑ μ ∈ (discRoots M (-1) r).filter (fun z => z.im < 0), liftTerm M μ = 0 :=
    Finset.sum_eq_zero fun μ hμ => liftTerm_of_lower (Finset.mem_filter.1 hμ).2
  have h5 : Multiset.card (M.charpoly.roots.filter fun z => dist z (-1) < r ∧ z.im = 0)
      = ∑ μ ∈ (discRoots M (-1) r).filter (fun z => z.im = 0), M.charpoly.roots.count μ := by
    rw [discRoots, Finset.filter_filter, sum_count_filter]
  rw [h1, h2, h3, h4, h5]
  push_cast
  ring

open Classical in
/-- **On the upper circle**: the local sum is `2π m₋(V_D) + ∑ σ(μ) arg μ`. -/
theorem localSum_eq_of_circle {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {c₀ : ℂ} {r : ℝ} (hD : ∀ z : ℂ, dist z c₀ < r → 0 < z.im)
    (hstab : ∀ z ∈ (cpx A).charpoly.roots, dist z c₀ < r →
      dist (starRingEnd ℂ z)⁻¹ c₀ < r) :
    localSum (cpx A) c₀ r
      = 2 * Real.pi * ((finrank ℂ (discSpace c₀ r (cpx A)) : ℝ)
          - (posIndex GForm (discSpace c₀ r (cpx A)) : ℝ))
        + ∑ μ ∈ circleRoots (cpx A) c₀ r, (sigma (cpx A) μ : ℝ) * Complex.arg μ := by
  set M := cpx A with hM
  -- the circle part and the off-circle part of the disc
  have hT : (discRoots M c₀ r).filter (fun z => ‖z‖ = 1 ∧ 0 < z.im) = circleRoots M c₀ r := by
    rw [discRoots, circleRoots, Finset.filter_filter]
    refine Finset.filter_congr fun z _ => ?_
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hD z h.1⟩⟩
  have hsum := sum_sigma_eq hA hstab
  have hfin : finrank ℂ (discSpace c₀ r M) = Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r) := by
    rw [discSpace, fPoly_eq_fS, finrank_kerAeval_fS, Multiset.countP_eq_card_filter]
  have hcount : Multiset.card (M.charpoly.roots.filter fun z => dist z c₀ < r)
      = ∑ μ ∈ circleRoots M c₀ r, M.charpoly.roots.count μ
        + ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)), M.charpoly.roots.count μ := by
    rw [circleRoots, discRoots, Finset.filter_filter, sum_count_filter, sum_count_filter]
    refine card_filter_eq_add _ _ _ _ (fun z _ => ?_) (fun z _ h => h.2.2 ⟨h.1.2, hD z h.1.1⟩)
    constructor
    · intro h
      by_cases h' : ‖z‖ = 1
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, fun h'' => h' h''.1⟩
    · rintro (h | h) <;> exact h.1
  rw [localSum, ← Finset.sum_filter_add_sum_filter_not (discRoots M c₀ r)
    (fun z => ‖z‖ = 1 ∧ 0 < z.im), hT]
  have h1 : ∑ μ ∈ circleRoots M c₀ r, liftTerm M μ
      = 2 * Real.pi * ∑ μ ∈ circleRoots M c₀ r, ((M.charpoly.roots.count μ : ℝ) - (mPos M μ : ℝ))
        + ∑ μ ∈ circleRoots M c₀ r, (sigma M μ : ℝ) * Complex.arg μ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [circleRoots, Finset.mem_filter] at hμ
    rw [liftTerm_of_circle ⟨hμ.2.2, hD μ hμ.2.1⟩]
  have h2 : ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)), liftTerm M μ
      = Real.pi * ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)),
          (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Finset.mem_filter, mem_discRoots] at hμ
    rw [liftTerm_of_upper hμ.2 (hD μ hμ.1.2)]
  have hσ : ∑ μ ∈ circleRoots M c₀ r, (sigma M μ : ℝ)
      = 2 * ∑ μ ∈ circleRoots M c₀ r, (mPos M μ : ℝ)
        - ∑ μ ∈ circleRoots M c₀ r, (M.charpoly.roots.count μ : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [sigma]
    push_cast
    ring
  have hsum' : ∑ μ ∈ circleRoots M c₀ r, (sigma M μ : ℝ)
      = 2 * (posIndex GForm (discSpace c₀ r M) : ℝ) - (finrank ℂ (discSpace c₀ r M) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hsum
    push_cast at this
    exact this
  have hfin' : (finrank ℂ (discSpace c₀ r M) : ℝ)
      = ∑ μ ∈ circleRoots M c₀ r, (M.charpoly.roots.count μ : ℝ)
        + ∑ μ ∈ (discRoots M c₀ r).filter (fun z => ¬(‖z‖ = 1 ∧ 0 < z.im)),
            (M.charpoly.roots.count μ : ℝ) := by
    rw [hfin, hcount]
    push_cast
    ring
  rw [h1, h2, Finset.sum_sub_distrib]
  linear_combination Real.pi * hσ - Real.pi * hsum' - Real.pi * hfin'

/-- The eventual closeness of `v ∘ shift` on the eigenvalues of the disc, from the continuity
of `v` at `shift c₀`. -/
theorem eventually_close_of_continuousAt {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} (c₀ : ℂ) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀)
    (v : ℂ → ℝ) (shift : ℂ → ℂ) (hshift : ∀ z, dist (shift z) (shift c₀) = dist z c₀)
    (hv : ContinuousAt v (shift c₀)) (P : ℂ → Prop) [DecidablePred P] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ A in 𝓝[Matrix.symplecticGroup l ℝ] A₀,
      ∀ μ ∈ (discRoots (cpx A) c₀ r).filter P, |v (shift μ) - v (shift c₀)| < ε := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hv ε hε
  rcases le_or_gt δ r with hδr | hδr
  · filter_upwards [eventually_facts c₀ hr hsep hδ hδr] with A hA μ hμ
    obtain ⟨-, hclose, -, -⟩ := hA
    rw [Finset.mem_filter, mem_discRoots] at hμ
    have := hδ' (show dist (shift μ) (shift c₀) < δ by rw [hshift]; exact hclose μ hμ.1.1 hμ.1.2)
    rwa [Real.dist_eq] at this
  · refine Eventually.of_forall fun A μ hμ => ?_
    rw [Finset.mem_filter, mem_discRoots] at hμ
    have := hδ' (show dist (shift μ) (shift c₀) < δ by rw [hshift]; exact hμ.1.2.trans hδr)
    rwa [Real.dist_eq] at this

/-- **The local sum converges to the local term of the centre**, for `A₀` symplectic without
the eigenvalue `1`. -/
theorem tendsto_localSum {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ) (h1 : (1 : ℂ) ∉ (cpx A₀).charpoly.roots)
    {c₀ : ℂ} (hc₀ : c₀ ∈ (cpx A₀).charpoly.roots) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c₀ → 3 * r ≤ dist z c₀)
    (hrb : r ≤ radiusBound c₀) :
    Tendsto (fun A => localSum (cpx A) c₀ r) (𝓝[Matrix.symplecticGroup l ℝ] A₀)
      (𝓝 (liftTerm (cpx A₀) c₀)) := by
  classical
  set N := Fintype.card (l ⊕ l) with hN
  have hr4 := radius_le_quarter hrb
  have hc₀0 : c₀ ≠ 0 := fun h => zero_notMem_roots hA₀ (h ▸ hc₀)
  rcases lt_trichotomy c₀.im 0 with him | him | him
  · -- below the real axis
    have hD : ∀ z : ℂ, dist z c₀ < r → z.im < 0 := fun z hz => by
      have h := disc_im hrb him.ne hz
      rcases lt_or_gt_of_ne h.2 with h' | h'
      · exact h'
      · exact absurd (h.1.1 h') (not_lt.2 him.le)
    rw [liftTerm_of_lower him]
    exact tendsto_const_nhds.congr fun A => (localSum_eq_zero hD).symm
  · -- the real axis
    by_cases hneg : c₀ = -1
    · subst hneg
      have hD : ∀ z : ℂ, dist z (-1) < r → z.re < 0 := fun z hz =>
        disc_re_neg_of_neg_one hrb rfl hz
      have hlim : Tendsto (fun A => ∑ μ ∈ (discRoots (cpx A) (-1) r).filter
          (fun z => ‖z‖ = 1 ∧ 0 < z.im), (sigma (cpx A) μ : ℝ)
            * (Complex.arg (-μ) - Complex.arg (-(-1 : ℂ))))
          (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 0) := by
        refine tendsto_sum_weighted N _ (fun A => sigma (cpx A)) (fun μ => Complex.arg (-μ))
          (Complex.arg (-(-1 : ℂ))) (fun A => ?_) (fun A μ _ => ?_) (fun ε hε => ?_)
        · exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans
            (card_toFinset_le _))
        · exact (natAbs_sigma_le _ _).trans (count_le_card _ _)
        · refine eventually_close_of_continuousAt (-1) hr hsep Complex.arg (fun z => -z)
            (fun z => by rw [dist_neg_neg]) ?_ _ hε
          rw [neg_neg]
          exact Complex.continuousAt_arg (by rw [Complex.mem_slitPlane_iff]; simp)
      have hconst : Tendsto (fun A => Real.pi / 2 * (((cpx A).charpoly.roots.filter
          fun z => dist z (-1) < r).card : ℝ)) (𝓝[Matrix.symplecticGroup l ℝ] A₀)
          (𝓝 (liftTerm (cpx A₀) (-1))) := by
        rw [liftTerm_of_real (by simp)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_facts (-1) hr hsep hr le_rfl] with A hA
        obtain ⟨-, -, hcount, -⟩ := hA
        rw [Multiset.countP_eq_card_filter] at hcount
        rw [hcount]
      have := hconst.add hlim
      rw [add_zero] at this
      exact this.congr fun A => (localSum_eq_of_neg_one).symm
    · -- a real eigenvalue other than `±1`
      have hne1 : c₀ ≠ 1 := fun h => h1 (h ▸ hc₀)
      have hnorm : ‖c₀‖ ≠ 1 := by
        intro h
        rcases eq_one_or_neg_one_of_im_eq_zero h him with h' | h'
        · exact hne1 h'
        · exact hneg h'
      have hD : ∀ z : ℂ, dist z c₀ < r → ‖z‖ ≠ 1 := fun z hz => (disc_norm hrb hnorm hz).2
      rw [liftTerm_of_real him]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_facts c₀ hr hsep hr le_rfl] with A hA
      obtain ⟨-, -, hcount, -⟩ := hA
      rw [Multiset.countP_eq_card_filter] at hcount
      rw [localSum_eq_of_real him hD, hcount]
  · -- above the real axis
    have hD : ∀ z : ℂ, dist z c₀ < r → 0 < z.im := fun z hz =>
      (disc_im hrb him.ne' hz).1.2 him
    by_cases hnorm : ‖c₀‖ = 1
    · -- the upper circle
      have hlim : Tendsto (fun A => ∑ μ ∈ (discRoots (cpx A) c₀ r).filter
          (fun z => ‖z‖ = 1 ∧ 0 < z.im), (sigma (cpx A) μ : ℝ)
            * (Complex.arg μ - Complex.arg c₀))
          (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 0) := by
        refine tendsto_sum_weighted N _ (fun A => sigma (cpx A)) Complex.arg (Complex.arg c₀)
          (fun A => ?_) (fun A μ _ => ?_) (fun ε hε => ?_)
        · exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans
            (card_toFinset_le _))
        · exact (natAbs_sigma_le _ _).trans (count_le_card _ _)
        · exact eventually_close_of_continuousAt c₀ hr hsep Complex.arg id (fun z => rfl)
            (Complex.continuousAt_arg (by rw [Complex.mem_slitPlane_iff]; exact Or.inr him.ne')) _ hε
      have hT : ∀ A : Matrix (l ⊕ l) (l ⊕ l) ℝ, (discRoots (cpx A) c₀ r).filter
          (fun z => ‖z‖ = 1 ∧ 0 < z.im) = circleRoots (cpx A) c₀ r := fun A => by
        rw [discRoots, circleRoots, Finset.filter_filter]
        refine Finset.filter_congr fun z _ => ?_
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hD z h.1⟩⟩
      simp_rw [hT] at hlim
      have hconst : Tendsto (fun A => 2 * Real.pi * ((finrank ℂ (discSpace c₀ r (cpx A)) : ℝ)
          - (posIndex GForm (discSpace c₀ r (cpx A)) : ℝ))
          + (∑ μ ∈ circleRoots (cpx A) c₀ r, (sigma (cpx A) μ : ℝ)) * Complex.arg c₀)
          (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 (liftTerm (cpx A₀) c₀)) := by
        rw [liftTerm_of_circle ⟨hnorm, him⟩]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_negIndex hA₀ hnorm hr hsep, eventually_sum_sigma hA₀ hnorm hr hsep hr4]
          with A hneg hsig
        rw [hneg]
        congr 2
        have := congrArg (fun x : ℤ => (x : ℝ)) hsig
        push_cast at this
        exact this.symm
      have := hconst.add hlim
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_facts c₀ hr hsep (by linarith : 0 < r / 2) (by linarith)]
        with A hA
      obtain ⟨hA, hclose, -, -⟩ := hA
      have hstab := stab_of_close hA hnorm hr4 hclose
      rw [localSum_eq_of_circle hA hD hstab, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    · -- above the real axis, off the circle
      have hD' : ∀ z : ℂ, dist z c₀ < r → 0 < z.im ∧ ‖z‖ ≠ 1 := fun z hz =>
        ⟨hD z hz, (disc_norm hrb hnorm hz).2⟩
      rw [liftTerm_of_upper (fun h => hnorm h.1) him]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_facts c₀ hr hsep hr le_rfl] with A hA
      obtain ⟨-, -, hcount, -⟩ := hA
      rw [Multiset.countP_eq_card_filter] at hcount
      rw [localSum_eq_of_upper hD', hcount]

/-! ### Continuity of the lift, and Lemma 7.1.6 -/

/-- **The lift is continuous at every symplectic matrix without the eigenvalue `1`.** -/
theorem tendsto_rhoLiftC {A₀ : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA₀ : A₀ ∈ Matrix.symplecticGroup l ℝ)
    (h1 : (1 : ℂ) ∉ (cpx A₀).charpoly.roots) :
    Tendsto (fun A => rhoLiftC (cpx A)) (𝓝[Matrix.symplecticGroup l ℝ] A₀)
      (𝓝 (rhoLiftC (cpx A₀))) := by
  classical
  set R := (cpx A₀).charpoly.roots.toFinset with hR
  obtain ⟨r, hr, hrb, hsep⟩ := exists_radius R
  have hsep' : ∀ c ∈ R, ∀ z ∈ (cpx A₀).charpoly.roots, z ≠ c → 3 * r ≤ dist z c :=
    fun c hc z hz hne => hsep z (Multiset.mem_toFinset.2 hz) c hc hne
  have hcover := (continuous_cpx.tendsto A₀).eventually (eventually_roots_near (cpx A₀) hr)
  have hloc : Tendsto (fun A => ∑ c ∈ R, localSum (cpx A) c r)
      (𝓝[Matrix.symplecticGroup l ℝ] A₀) (𝓝 (∑ c ∈ R, liftTerm (cpx A₀) c)) :=
    tendsto_finsetSum R fun c hc =>
      tendsto_localSum hA₀ h1 (Multiset.mem_toFinset.1 hc) hr (hsep' c hc) (hrb c hc)
  refine hloc.congr' ?_
  filter_upwards [hcover.filter_mono nhdsWithin_le_nhds] with A hA
  refine (rhoLiftC_eq_sum_localSum (cpx A) R r ?_ ?_).symm
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := hA z hz
    exact ⟨w, Multiset.mem_toFinset.2 hw, hzw⟩
  · intro c hc c' hc' hne
    linarith [hsep c hc c' hc' hne]

/-- **The lift is continuous on `Sp(2n)⋆`.** -/
theorem continuousOn_rhoLift (n : ℕ) :
    ContinuousOn (rhoLift n)
      {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ | A ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ (A - 1).det ≠ 0} := by
  intro A₀ hA₀
  have h1 : (1 : ℂ) ∉ (cpx A₀).charpoly.roots := (one_notMem_roots_iff A₀).2 hA₀.2
  exact (tendsto_rhoLiftC hA₀.1 h1).mono_left (nhdsWithin_mono _ fun A hA => hA.1)

/-- **Lemma 7.1.6 on `Sp(2n)⁺`.**  `ρ` admits a continuous real lift on `Sp(2n)⁺`. -/
theorem exists_lift_plus (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f {A | A ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ 0 < (A - 1).det} ∧
      ∀ A, A ∈ Matrix.symplecticGroup (Fin n) ℝ → 0 < (A - 1).det →
        Complex.exp (f A * Complex.I) = rho n A :=
  ⟨rhoLift n, (continuousOn_rhoLift n).mono fun _ hA => ⟨hA.1, hA.2.ne'⟩,
    fun _ hA hdet => exp_rhoLift_plus n hA hdet⟩

/-- **Lemma 7.1.6 on `Sp(2n)⁻`.**  `ρ` admits a continuous real lift on `Sp(2n)⁻`. -/
theorem exists_lift_minus (n : ℕ) :
    ∃ f : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ → ℝ,
      ContinuousOn f {A | A ∈ Matrix.symplecticGroup (Fin n) ℝ ∧ (A - 1).det < 0} ∧
      ∀ A, A ∈ Matrix.symplecticGroup (Fin n) ℝ → (A - 1).det < 0 →
        Complex.exp (f A * Complex.I) = rho n A :=
  ⟨fun A => rhoLift n A + Real.pi,
    ((continuousOn_rhoLift n).mono fun _ hA => ⟨hA.1, hA.2.ne⟩).add continuousOn_const,
    fun _ hA hdet => by
      have := exp_rhoLift_minus n hA hdet
      push_cast at this ⊢
      exact this⟩

end Rho
end MorseFloer
