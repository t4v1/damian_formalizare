# PR 2 — Morrey's inequality

**Branch name (suggested):** `halmaghi/morrey-inequality` (branched from PR 1's branch)
**Title:**

    feat(Analysis/FunctionalSpaces): prove Morrey's inequality

**Files touched:**
`Mathlib/Analysis/FunctionalSpaces/MorreyInequality.lean` (new),
`Mathlib.lean` (import line), `docs/references.bib` (`evans2010`, `liebLoss2001`).
**Opened:** https://github.com/leanprover-community/mathlib4/pull/43905 (2026-09-17), commit `fc6e22a`
**Workspace:** same clone as PR 1; committed on the branch
`halmaghi/morrey-inequality` created from PR 1's branch.

**Body:**

```
Morrey's inequality, the supercritical companion of the Gagliardo–Nirenberg–Sobolev
inequality of `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`. That file
bounds an `L^q` norm of a compactly supported `C¹` function by the `L^p` norm of its
derivative when `p < finrank ℝ E`; this one treats `finrank ℝ E < p`, where the
function is Hölder continuous of exponent `1 - n / p`:

* `enorm_sub_le_morreyConst_mul_rpow_mul_eLpNorm_fderiv`:
  `‖u x - u z‖ₑ ≤ morreyConst E μ p * ‖x - z‖ₑ ^ (1 - n / p) * eLpNorm (fderiv ℝ u) p μ`
  for `u` of class `C¹` (no support hypothesis is needed);
* `eLpNorm_top_le_eLpNorm_fderiv`: `eLpNorm u ⊤ μ ≤ C * eLpNorm (fderiv ℝ u) p μ` for
  `u` supported in a bounded set `s`, `C` depending on `s` through its diameter.

Both constants are explicit and homogeneous of the right degree in `μ`, so the
estimates are invariant under rescaling the Haar measure.

On the way: the exact value of the Riesz kernel integral on a ball,
`setLIntegral_ball_rpow_neg` (`∫⁻ y in ball x r, ‖y - x‖ₑ ^ (-a) ∂μ` equals
`n / (n - a) * μ (ball 0 1) * r ^ (n - a)` for `a < n`), its finiteness, and the Riesz
potential estimate `lintegral_ball_enorm_sub_le_lintegral_riesz` bounding the mean
oscillation of a `C¹` function on a ball by the Riesz potential of its derivative.
The proof is the classical one (Evans, PDE, §5.6.2; Lieb–Loss, Analysis, §8.4): polar
coordinates about the centre of a ball, the fundamental theorem of calculus along
rays, Hölder's inequality against the Riesz kernel, and a comparison of the averages
over `ball x d`, `ball z d` and `ball ((x + z)/2) (d/2)`.

The target space `F` is not assumed complete: the fundamental theorem of calculus is
applied in `UniformSpace.Completion F`.

The proofs were developed with the help of an LLM (Claude Code) and then checked and
edited by the author, who takes responsibility for every line.

- [ ] depends on: #43904 (polar coordinates for lintegral)
```

**Labels:** `t-analysis`, `LLM-generated`.

**Design points a reviewer may raise, with the prepared answer**

- *Why named constants (`morreyConst`, `rieszKernelConst`, …) rather than `∃ C`?*
  So that the statement is usable quantitatively and so that homogeneity in `μ` is
  visible; `SobolevInequality.lean` does the same with `SNormLESNormFDerivOneConst`.
  They are plain `def`s (the draft used `irreducible_def`; the style guide asks for a
  profiling justification, and there is none).
- *`p : ℝ≥0` with `(finrank ℝ E : ℝ≥0) < p`* mirrors `eLpNorm_le_eLpNorm_fderiv`'s
  hypothesis shape.
- *`[Nontrivial E]`* is needed: on the zero space `μ.toSphere = 0` and the polar
  formula is vacuous.
- *Naming:* `eLpNorm_top_le_eLpNorm_fderiv` follows `eLpNorm_le_eLpNorm_fderiv`;
  `setLIntegral_ball_rpow_neg` follows `setLIntegral_*`.

**Checklist before opening**

- [ ] `lake build Mathlib.Analysis.FunctionalSpaces.MorreyInequality` on master: green
- [ ] `lake exe lint-style`: clean; `lake exe runLinter Mathlib.Analysis.FunctionalSpaces.MorreyInequality`: clean
- [ ] `lake exe mk_all --check` (import registered in `Mathlib.lean`)
- [ ] `scripts/lint-bib.sh` (needs `bibtool`; CI runs it anyway)
- [ ] Zulip thread, same as PR 1
