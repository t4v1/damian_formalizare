import Mathlib

/-!
# A path along which a lattice-periodic map tends to zero converges to a zero

A helper for Theorem 6.5.6 of Audin–Damian.  Let `F` be a continuous map on `ℝⁿ`, invariant
under the lattice `ℤⁿ` — a map on the torus — whose zeros are finite in number in every
compact set.  If `q` is a continuous path with `F (q s) → 0` as `s → +∞`, then `q s`
converges to a zero of `F` (`tendsto_of_tendsto_zero`).

The book argues with the compactness of the space of solutions and the connectedness of the
image of a half-line.  The connectedness argument is the same here, but it is run in `ℝⁿ`:

* where `F` is small, the point is close to a zero — by compactness of the torus, that is,
  after translating a would-be counterexample into the unit cube (`exists_near_zero`);
* the zeros are uniformly separated — again by translating into the cube, where they are
  finitely many (`exists_separation`);
* so the path eventually lies in a union of pairwise disjoint balls about the zeros, and being
  connected it lies in one of them.
-/

open Filter Topology Metric Set

namespace MorseFloer
namespace LatticePath

variable {ι : Type*} [Fintype ι]

/-- Every point is within distance `1` of a lattice point. -/
theorem exists_lattice_near (q : ι → ℝ) : ∃ k : ι → ℤ, ‖q - fun i => (k i : ℝ)‖ ≤ 1 := by
  refine ⟨fun i => ⌊q i⌋, ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  show ‖q i - ⌊q i⌋‖ ≤ 1
  rw [Int.self_sub_floor, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one _).le

/-- A finite set in a metric space is uniformly discrete. -/
theorem exists_pos_of_finite {α : Type*} [MetricSpace α] {S : Set α} (hS : S.Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ S, ∀ b ∈ S, dist a b < ε → a = b := by
  classical
  rcases (hS.toFinset.offDiag).eq_empty_or_nonempty with hP | hP
  · refine ⟨1, one_pos, fun a ha b hb _ => ?_⟩
    by_contra hab
    have : (a, b) ∈ hS.toFinset.offDiag := by
      rw [Finset.mem_offDiag]
      exact ⟨hS.mem_toFinset.2 ha, hS.mem_toFinset.2 hb, hab⟩
    rw [hP] at this
    exact absurd this (Finset.notMem_empty _)
  · refine ⟨(hS.toFinset.offDiag).inf' hP fun ab => dist ab.1 ab.2, ?_, fun a ha b hb hab => ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro ab hab
      rw [Finset.mem_offDiag] at hab
      exact dist_pos.2 hab.2.2
    · by_contra hne
      have hmem : (a, b) ∈ hS.toFinset.offDiag := by
        rw [Finset.mem_offDiag]
        exact ⟨hS.mem_toFinset.2 ha, hS.mem_toFinset.2 hb, hne⟩
      have := Finset.inf'_le (fun ab : α × α => dist ab.1 ab.2) hmem
      exact absurd hab (not_lt.2 this)

variable {E' : Type*} [NormedAddCommGroup E']

/-- **Where `F` is small, a zero is near.** -/
theorem exists_near_zero {F : (ι → ℝ) → E'} (hF : Continuous F)
    (hlat : ∀ (k : ι → ℤ) (q : ι → ℝ), F (q + fun i => (k i : ℝ)) = F q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ q, ‖F q‖ < δ' → ∃ p, F p = 0 ∧ dist q p < δ := by
  by_contra hcon
  push Not at hcon
  have hex : ∀ n : ℕ, ∃ q, ‖F q‖ < 1 / ((n : ℝ) + 1) ∧ ∀ p, F p = 0 → δ ≤ dist q p :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq1 hq2 using hex
  choose k hk using fun n => exists_lattice_near (q n)
  have hFk : ∀ n, F (q n - fun i => (k n i : ℝ)) = F (q n) := fun n => by
    have := hlat (k n) (q n - fun i => (k n i : ℝ))
    rw [sub_add_cancel] at this
    exact this.symm
  obtain ⟨p, -, φ, hφ, hpφ⟩ := (isCompact_closedBall (0 : ι → ℝ) 1).tendsto_subseq
    (x := fun n => q n - fun i => (k n i : ℝ)) (fun n => mem_closedBall_zero_iff.2 (hk n))
  have hFp : F p = 0 := by
    have h1 : Tendsto (fun n => F (q (φ n) - fun i => (k (φ n) i : ℝ))) atTop (𝓝 (F p)) :=
      (hF.tendsto p).comp hpφ
    have h2 : Tendsto (fun n => F (q (φ n) - fun i => (k (φ n) i : ℝ))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      rw [hFk]
      exact (hq1 (φ n)).le
    exact tendsto_nhds_unique h1 h2
  have hle : ∀ n, δ ≤ dist (q (φ n) - fun i => (k (φ n) i : ℝ)) p := by
    intro n
    have hz : F (p + fun i => (k (φ n) i : ℝ)) = 0 := by rw [hlat, hFp]
    have := hq2 (φ n) _ hz
    rwa [dist_eq_norm, show q (φ n) - (p + fun i => (k (φ n) i : ℝ))
      = q (φ n) - (fun i => (k (φ n) i : ℝ)) - p by abel, ← dist_eq_norm] at this
  have hlim : Tendsto (fun n => dist (q (φ n) - fun i => (k (φ n) i : ℝ)) p) atTop (𝓝 0) := by
    have := (tendsto_iff_dist_tendsto_zero.1 hpφ)
    exact this
  have := ge_of_tendsto' hlim hle
  linarith

/-- **The zeros are uniformly separated.** -/
theorem exists_separation {F : (ι → ℝ) → E'}
    (hlat : ∀ (k : ι → ℤ) (q : ι → ℝ), F (q + fun i => (k i : ℝ)) = F q)
    (hfin : ∀ K : Set (ι → ℝ), IsCompact K → (K ∩ {p | F p = 0}).Finite) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ p p', F p = 0 → F p' = 0 → dist p p' < 2 * δ₀ → p = p' := by
  obtain ⟨ε, hε, hsep⟩ := exists_pos_of_finite (hfin _ (isCompact_closedBall (0 : ι → ℝ) 2))
  refine ⟨min ε 1 / 2, by positivity, fun p p' hp hp' hd => ?_⟩
  have hd' : dist p p' < min ε 1 := by linarith
  obtain ⟨k, hk⟩ := exists_lattice_near p
  have hz : ∀ a, F a = 0 → F (a - fun i => (k i : ℝ)) = 0 := fun a ha => by
    have := hlat k (a - fun i => (k i : ℝ))
    rw [sub_add_cancel] at this
    rw [← this, ha]
  have hdist : dist (p - fun i => (k i : ℝ)) (p' - fun i => (k i : ℝ)) = dist p p' :=
    dist_sub_right _ _ _
  have h1 : p - (fun i => (k i : ℝ)) ∈ closedBall (0 : ι → ℝ) 2 ∩ {p | F p = 0} :=
    ⟨mem_closedBall_zero_iff.2 (hk.trans (by norm_num)), hz p hp⟩
  have h2 : p' - (fun i => (k i : ℝ)) ∈ closedBall (0 : ι → ℝ) 2 ∩ {p | F p = 0} := by
    refine ⟨mem_closedBall_zero_iff.2 ?_, hz p' hp'⟩
    have h3 : ‖p' - fun i => (k i : ℝ)‖
        ≤ ‖p - fun i => (k i : ℝ)‖ + dist (p - fun i => (k i : ℝ)) (p' - fun i => (k i : ℝ)) := by
      rw [dist_eq_norm, ← norm_neg (p - (fun i => (k i : ℝ)) - (p' - fun i => (k i : ℝ)))]
      have e : p' - (fun i => (k i : ℝ)) = (p - fun i => (k i : ℝ))
          + -(p - (fun i => (k i : ℝ)) - (p' - fun i => (k i : ℝ))) := by abel
      calc ‖p' - fun i => (k i : ℝ)‖
          = ‖(p - fun i => (k i : ℝ))
              + -(p - (fun i => (k i : ℝ)) - (p' - fun i => (k i : ℝ)))‖ := by rw [← e]
        _ ≤ _ := norm_add_le _ _
    rw [hdist] at h3
    have : dist p p' < 1 := lt_of_lt_of_le hd' (min_le_right _ _)
    linarith
  have := hsep _ h1 _ h2 (by rw [hdist]; exact lt_of_lt_of_le hd' (min_le_left _ _))
  exact sub_left_injective this

/-- **A path along which `F` tends to zero converges to a zero of `F`.** -/
theorem tendsto_of_tendsto_zero {F : (ι → ℝ) → E'} (hF : Continuous F)
    (hlat : ∀ (k : ι → ℤ) (q : ι → ℝ), F (q + fun i => (k i : ℝ)) = F q)
    (hfin : ∀ K : Set (ι → ℝ), IsCompact K → (K ∩ {p | F p = 0}).Finite)
    {q : ℝ → (ι → ℝ)} (hq : Continuous q) (hFq : Tendsto (fun s => F (q s)) atTop (𝓝 0)) :
    ∃ p, F p = 0 ∧ Tendsto q atTop (𝓝 p) := by
  obtain ⟨δ₀, hδ₀, hsep⟩ := exists_separation hlat hfin
  -- for every small `δ` the path is eventually in the `δ`-ball of a single zero
  have hstep : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ (S : ℝ) (p : ι → ℝ), F p = 0 ∧ ∀ s, S ≤ s → dist (q s) p < δ := by
    intro δ hδ hδle
    obtain ⟨δ', hδ', hnear⟩ := exists_near_zero hF hlat hδ
    have hev : ∀ᶠ s in atTop, ‖F (q s)‖ < δ' := by
      have := (tendsto_zero_iff_norm_tendsto_zero.1 hFq)
      exact (tendsto_order.1 this).2 δ' hδ'
    obtain ⟨S, hS⟩ := eventually_atTop.1 hev
    obtain ⟨p, hp, hpS⟩ := hnear (q S) (hS S le_rfl)
    refine ⟨S, p, hp, fun s hs => ?_⟩
    have hconn : IsPreconnected (q '' Ici S) := isPreconnected_Ici.image q hq.continuousOn
    have hV : IsOpen (⋃ p' ∈ {p' | F p' = 0 ∧ p' ≠ p}, ball p' δ) :=
      isOpen_biUnion fun _ _ => isOpen_ball
    have hdisj : Disjoint (ball p δ) (⋃ p' ∈ {p' | F p' = 0 ∧ p' ≠ p}, ball p' δ) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [mem_iUnion₂] at hx'
      obtain ⟨p', ⟨hp'0, hp'ne⟩, hxp'⟩ := hx'
      rw [mem_ball] at hx hxp'
      refine hp'ne (hsep p' p hp'0 hp ?_)
      calc dist p' p ≤ dist p' x + dist x p := dist_triangle _ _ _
        _ < δ + δ := add_lt_add (by rw [dist_comm]; exact hxp') hx
        _ ≤ 2 * δ₀ := by linarith
    have hcover : q '' Ici S ⊆ ball p δ ∪ ⋃ p' ∈ {p' | F p' = 0 ∧ p' ≠ p}, ball p' δ := by
      rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨p', hp'0, hp'd⟩ := hnear (q σ) (hS σ hσ)
      by_cases hpp : p' = p
      · left
        rw [mem_ball, ← hpp]
        exact hp'd
      · right
        rw [mem_iUnion₂]
        exact ⟨p', ⟨hp'0, hpp⟩, mem_ball.2 hp'd⟩
    have hne : (q '' Ici S ∩ ball p δ).Nonempty :=
      ⟨q S, ⟨S, mem_Ici.2 le_rfl, rfl⟩, mem_ball.2 hpS⟩
    have hsub := hconn.subset_left_of_subset_union isOpen_ball hV hdisj hcover hne
    exact mem_ball.1 (hsub ⟨s, hs, rfl⟩)
  obtain ⟨S₀, p, hp, hpS₀⟩ := hstep δ₀ hδ₀ le_rfl
  refine ⟨p, hp, Metric.tendsto_atTop.2 fun η hη => ?_⟩
  obtain ⟨S, p', hp', hp'S⟩ := hstep (min η δ₀) (lt_min hη hδ₀) (min_le_right _ _)
  have hpp : p' = p := by
    refine hsep p' p hp' hp ?_
    have h1 := hp'S (max S S₀) (le_max_left _ _)
    have h2 := hpS₀ (max S S₀) (le_max_right _ _)
    calc dist p' p ≤ dist p' (q (max S S₀)) + dist (q (max S S₀)) p := dist_triangle _ _ _
      _ < min η δ₀ + δ₀ := add_lt_add (by rw [dist_comm]; exact h1) h2
      _ ≤ 2 * δ₀ := by linarith [min_le_right η δ₀]
  refine ⟨S, fun s hs => ?_⟩
  rw [← hpp]
  exact lt_of_lt_of_le (hp'S s hs) (min_le_left _ _)

end LatticePath
end MorseFloer
