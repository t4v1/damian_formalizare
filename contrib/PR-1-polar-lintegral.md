# PR 1 — polar coordinates for `lintegral`

**Branch name (suggested):** `halmaghi/lintegral-toSphere`
**Title (first line of the squash commit):**

    feat(MeasureTheory/Constructions/HaarToSphere): polar coordinates for lintegral

**Files touched:** `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` only.
**Opened:** https://github.com/leanprover-community/mathlib4/pull/43904 (2026-09-17)
**Zulip thread (2026-09-18):** https://leanprover.zulipchat.com/#narrow/channel/144837-PR-reviews/topic/.2343904.20.2343905.20polar.20coordinates.20for.20lintegral.2C.20Morrey.27s.20ineq/near/625097072
**Workspace:** `~/projects/mathlib4-master`, master commit `a218e50` (2026-09-17), branch
`halmaghi/lintegral-toSphere`, changes uncommitted.

**Body** (goes in the PR description box, above the `---` of the template):

```
`Measure.measurePreserving_homeomorphUnitSphereProd` represents an additive Haar
measure on a nontrivial finite-dimensional normed space `E` as the product of the
sphere measure `μ.toSphere` and Lebesgue measure on `(0, ∞)` with density
`r ^ (dim E - 1)`. The file exposes it only through the radial corollaries
`integrable_fun_norm_addHaar`, `integrableOn_fun_norm_addHaar` and
`integral_fun_norm_addHaar`, all for integrands of the form `f ‖x‖`.

This PR adds the general `lintegral` form, for an arbitrary measurable
`f : E → ℝ≥0∞`:

* `lintegral_addHaar_eq_lintegral_toSphere_lintegral_Ioi`:
  `∫⁻ x, f x ∂μ = ∫⁻ ω, ∫⁻ r in Ioi 0, ofReal (r ^ (dim E - 1)) * f (r • ω) ∂μ.toSphere`;
* `setLIntegral_ball_eq_lintegral_toSphere_lintegral_Ioo`: the same for
  `∫⁻ y in ball c R, f y ∂μ`, with the radial integral over `Ioo 0 R` and the rays
  emanating from `c`.

Both are needed for Morrey's inequality (follow-up PR), whose two analytic steps
integrate non-radial functions in polar coordinates; they are stated here on their
own because they are independent of it.

The proofs were developed with the help of an LLM (Claude Code) and then checked and
edited by the author, who takes responsibility for every line.
```

**Labels:** `t-measure-probability`, `LLM-generated` (the contribution guide requires
the label whenever an LLM wrote a substantial part of the code; it did).

**Checklist before opening**

- [ ] `lake build Mathlib.MeasureTheory.Constructions.HaarToSphere` on master: green
- [ ] `lake exe lint-style` on master: clean
- [ ] `lake exe runLinter Mathlib.MeasureTheory.Constructions.HaarToSphere`: clean
      (`unusedArguments`, `docBlame`, `unusedHavesSuffices`)
- [ ] Zulip: post in `#mathlib4 > polar coordinates for lintegral` linking the PR
- [ ] Do not squash the follow-up into this one: reviewers ask for small PRs
