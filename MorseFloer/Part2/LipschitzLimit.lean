import Mathlib

/-!
# Equi-Lipschitz sequences have locally uniformly convergent subsequences

A helper for Theorem 6.5.4 of Audin–Damian.  A sequence of maps `ℝ × ℝ → E`, `E` finite
dimensional, which are Lipschitz with a common constant and bounded at one point has a
subsequence converging uniformly on every compact set, to a Lipschitz limit
(`exists_subseq_tendstoUniformlyOn`).

This is the Arzelà–Ascoli theorem in the only form the compactness of the space of Floer
solutions needs, and it is proved directly.  The diagonal argument costs nothing: the sequence,
restricted to the countable set of rational points, lives in a product of closed balls, which
is compact and first countable, so it has a convergent subsequence there.  The Lipschitz bound
then makes the subsequence Cauchy at every point, and uniformly so on compact sets.
-/

open Filter Topology Metric Set

namespace MorseFloer
namespace LipschitzLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The rational points of the plane. -/
noncomputable def emb (q : ℚ × ℚ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

theorem exists_emb_near (p : ℝ × ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ q : ℚ × ℚ, ‖p - emb q‖ < δ := by
  obtain ⟨a, ha⟩ := exists_rat_near p.1 hδ
  obtain ⟨b, hb⟩ := exists_rat_near p.2 hδ
  refine ⟨(a, b), ?_⟩
  have e : p - emb (a, b) = (p.1 - a, p.2 - b) := rfl
  rw [e, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_lt ha hb

/-- **Equi-Lipschitz sequences have locally uniformly convergent subsequences.** -/
theorem exists_subseq_tendstoUniformlyOn {f : ℕ → ℝ × ℝ → E} {L R : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ n p q, ‖f n p - f n q‖ ≤ L * ‖p - q‖) (hbd : ∀ n, ‖f n 0‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (v : ℝ × ℝ → E), StrictMono φ ∧ (∀ p q, ‖v p - v q‖ ≤ L * ‖p - q‖) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → TendstoUniformlyOn (fun n => f (φ n)) v atTop K := by
  have hbd' : ∀ n p, ‖f n p‖ ≤ R + L * ‖p‖ := fun n p => by
    calc ‖f n p‖ = ‖f n 0 + (f n p - f n 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f n 0‖ + ‖f n p - f n 0‖ := norm_add_le _ _
      _ ≤ R + L * ‖p - 0‖ := add_le_add (hbd n) (hlip n p 0)
      _ = R + L * ‖p‖ := by rw [sub_zero]
  -- the sequence restricted to the rational points lives in a compact product
  have hSc : IsCompact (Set.pi (univ : Set (ℚ × ℚ)) fun q => closedBall (0 : E) (R + L * ‖emb q‖)) :=
    isCompact_univ_pi fun q => isCompact_closedBall _ _
  have hmem : ∀ n, (fun q => f n (emb q))
      ∈ Set.pi (univ : Set (ℚ × ℚ)) fun q => closedBall (0 : E) (R + L * ‖emb q‖) := by
    intro n
    rw [Set.mem_univ_pi]
    intro q
    rw [mem_closedBall_zero_iff]
    exact hbd' n (emb q)
  obtain ⟨a, -, φ, hφ, ha⟩ := hSc.tendsto_subseq hmem
  rw [tendsto_pi_nhds] at ha
  have ha' : ∀ q, Tendsto (fun n => f (φ n) (emb q)) atTop (𝓝 (a q)) := fun q => ha q
  have hL1 : 0 < L + 1 := by linarith
  -- Cauchy at every point
  have hcauchy : ∀ p, CauchySeq fun n => f (φ n) p := by
    intro p
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨q, hq⟩ := exists_emb_near p (δ := ε / (8 * (L + 1))) (by positivity)
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 (ha' q).cauchySeq) (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    have hkey : (L + 1) * (ε / (8 * (L + 1))) = ε / 8 := by
      field_simp
    have h2 : L * ‖p - emb q‖ ≤ ε / 8 := by
      calc L * ‖p - emb q‖ ≤ (L + 1) * (ε / (8 * (L + 1))) :=
            mul_le_mul (by linarith) hq.le (norm_nonneg _) hL1.le
        _ = ε / 8 := hkey
    calc ‖f (φ n) p - f (φ N) p‖
        = ‖(f (φ n) p - f (φ n) (emb q)) + (f (φ n) (emb q) - f (φ N) (emb q))
            + (f (φ N) (emb q) - f (φ N) p)‖ := by congr 1; abel
      _ ≤ ‖f (φ n) p - f (φ n) (emb q)‖ + ‖f (φ n) (emb q) - f (φ N) (emb q)‖
            + ‖f (φ N) (emb q) - f (φ N) p‖ := norm_add₃_le
      _ ≤ L * ‖p - emb q‖ + ε / 2 + L * ‖emb q - p‖ :=
          add_le_add (add_le_add (hlip _ _ _) h1.le) (hlip _ _ _)
      _ < ε := by rw [norm_sub_rev (emb q) p]; linarith
  choose v hv using fun p => cauchySeq_tendsto_of_complete (hcauchy p)
  have hvlip : ∀ p q, ‖v p - v q‖ ≤ L * ‖p - q‖ := fun p q =>
    le_of_tendsto (((hv p).sub (hv q)).norm) (Eventually.of_forall fun n => hlip _ _ _)
  refine ⟨φ, v, hφ, hvlip, fun K hK => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδpos : 0 < ε / (8 * (L + 1)) := by positivity
  obtain ⟨t, -, htfin, hcover⟩ := hK.finite_cover_balls hδpos
  choose qt hqt using fun x : ℝ × ℝ => exists_emb_near x hδpos
  have hev : ∀ᶠ n in atTop, ∀ x ∈ t, ‖f (φ n) (emb (qt x)) - v (emb (qt x))‖ < ε / 4 := by
    rw [Filter.eventually_all_finite htfin]
    intro x _
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 (hv (emb (qt x))))).2 _
      (by positivity)
  filter_upwards [hev] with n hn x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  rw [mem_ball, dist_eq_norm] at hxy
  have hyq := hqt y
  have hxq : ‖x - emb (qt y)‖ ≤ 2 * (ε / (8 * (L + 1))) := by
    calc ‖x - emb (qt y)‖ = ‖(x - y) + (y - emb (qt y))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - y‖ + ‖y - emb (qt y)‖ := norm_add_le _ _
      _ ≤ 2 * (ε / (8 * (L + 1))) := by linarith
  have hkey : (L + 1) * (ε / (8 * (L + 1))) = ε / 8 := by
    field_simp
  have h2 : L * ‖x - emb (qt y)‖ ≤ ε / 4 := by
    calc L * ‖x - emb (qt y)‖ ≤ (L + 1) * (2 * (ε / (8 * (L + 1)))) :=
          mul_le_mul (by linarith) hxq (norm_nonneg _) hL1.le
      _ = 2 * ((L + 1) * (ε / (8 * (L + 1)))) := by ring
      _ = ε / 4 := by rw [hkey]; ring
  have h3 := hn y hy
  rw [dist_eq_norm]
  calc ‖v x - f (φ n) x‖
      = ‖(v x - v (emb (qt y))) + (v (emb (qt y)) - f (φ n) (emb (qt y)))
          + (f (φ n) (emb (qt y)) - f (φ n) x)‖ := by congr 1; abel
    _ ≤ ‖v x - v (emb (qt y))‖ + ‖v (emb (qt y)) - f (φ n) (emb (qt y))‖
          + ‖f (φ n) (emb (qt y)) - f (φ n) x‖ := norm_add₃_le
    _ ≤ L * ‖x - emb (qt y)‖ + ε / 4 + L * ‖emb (qt y) - x‖ := by
        refine add_le_add (add_le_add (hvlip _ _) ?_) (hlip _ _ _)
        rw [norm_sub_rev]
        exact h3.le
    _ < ε := by rw [norm_sub_rev (emb (qt y)) x]; linarith

end LipschitzLimit
end MorseFloer
