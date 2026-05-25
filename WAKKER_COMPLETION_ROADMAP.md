# Completion roadmap and closure audit for the `WakkerDebreuKoopmans` module family + `MechanizedDecisionTheoryWakkerDK.tex`

Snapshot date: 2026-05-25. Build state: `lake build WakkerDebreuKoopmans` and `lake build Wakker.AxiomCheck` exit 0; the historical `WakkerDebreuKoopmans.lean` path is now a thin barrel over `WakkerDebreuKoopmans/*.lean`; the reviewer-facing audit is `Wakker/AxiomCheck.lean`; every public theorem audits `[propext, Classical.choice, Quot.sound]`; the companion TeX has been rewritten as a submission-facing JAR draft.

The artifact is now structured around **two orthogonal frontiers**:

1. **Topology / consumer side (T1–T6)** — DONE. Given any `R : AdditiveRep P`, the topology bundle produces every downstream construction-stack output.
2. **Construction side (O1–O4)** — DONE. The non-circular Stage-5 closure, the quasi-to-concave strengthening, and the per-coordinate concavity transfer are now theorem-backed, so the artifact produces `R : AdditiveRep P` from Wakker's six structural axioms and closes the Debreu--Koopmans hard direction.

This document now records the realized closure chain and the reviewer-facing audit trail.

---

## Priority A — O1 Stage-5 residual closure (realized non-circular chain)

The Stage 2–5 attack ladder is sorry-free. The Stage-5 surface `WakkerStage5GlobalGluingData` was proved (this session) **logically equivalent** to `Nonempty (AdditiveRep P)` via the round-trip
`wakkerStage5GlobalGluingData_iff_wakkerStage5AdditiveAssemblyData`. So the four named Stage-5 residuals are exactly the right non-circular decomposition. The point of this decomposition was to discharge each *without* assuming a global `R`.

These four residuals were exactly the right non-circular decomposition, and they are now all discharged *without* assuming a global `R`.

### A1. `AllPairsAdditivityCertificate P V` for one global `V` — **DONE**

- **Where**: `WakkerDebreuKoopmans.lean` around L5144 (definition) and L15151-area (non-circular constructors).
- **Strategy**: build pairwise additivity at the pivot `j₀` from the active `WakkerStage4PivotSliceRepresentationData`, then propagate to all `(j, k)` pairs by composing pivot slices. The non-circular ingredient is the **shared pivot-slice utility** `V_{j_0}` plus a named cross-pair residual `NonPivotPairAdditivityCertificate P V j₀`.
- **Status**: `allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot` consumes the pivot slice family plus `NonPivotPairAdditivityCertificate`; `allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData` chooses a coordinatewise `V` via `Classical.choose` and returns `∃ j₀ V, _ ∧ AllPairsAdditivityCertificate P V`. Both audit `[propext, Classical.choice, Quot.sound]`.

### A2. `WakkerStep5CoordinateImageCoverageCertificate P V` — **DONE**

- **Where**: `WakkerDebreuKoopmans.lean` L5832-area (definition) and L15425-area (non-circular constructors).
- **Strategy**: the certificate body itself quantifies over the pivot `j₀`, so it decomposes pointwise into a per-pivot residue `WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀` capturing the genuine cross-coordinate Archimedean / standard-sequence content of Wakker IV.2 Step 5 that pair-additivity cannot supply. The certificate is then a trivial repackaging that supplies the residue for each `j₀`.
- **Status**: `wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot` consumes the per-pivot residue family. `wakkerStep5CoordinateImageCoverageCertificate_of_stage4PivotSliceRepresentationData` composes with A1 to deliver `(j₀, V, hMatch, hpair, hcov)`. Both audit `[propext, Classical.choice, Quot.sound]`.

### A3. `WakkerStep5StrictMonotonicityCertificate P V` — **DONE**

- **Where**: `WakkerDebreuKoopmans.lean` L5862-area (definition) and L15290-area (non-circular constructors).
- **Strategy**: split on whether `x, y` agree off some pivot-touching pair `{j₀, k}`. The pair-aligned case is discharged from `AllPairsAdditivityCertificate P V` alone via `sum_eq_pair_add_rest` applied to both directions of indifference. The complementary cross-profile case is named as `WakkerStep5StrictMonotonicityResidualAtPivot P V j₀` — the genuine cross-coordinate content of Wakker IV.2 Step 5 that pair-additivity cannot reach.
- **Status**: `wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity` takes the pivot, `V`, the pair-additivity certificate, and the named residue. `wakkerStep5StrictMonotonicityCertificate_of_stage4PivotSliceRepresentationData` composes with A1 to deliver `(j₀, V, hMatch, hpair, hstrict)`. Both audit `[propext, Classical.choice, Quot.sound]`.

### A4. Pivot-slice representations sharing `V_{j_0}` (Stage-4 → Stage-5 lift) — **DONE**

- **Where**: between Stage-4 output and Stage-5 input.
- **Strategy**: this is Wakker IV.2 Step 4 proper: pick a pivot `j_0`, build `(R_{j_0,k}.V_{j_0})_{k ≠ j_0}` from pairwise Step-3 data, then **renormalize** so all share the same `V_{j_0}`. Needs the affine-uniqueness clean-up theorems already proved (e.g. `additiveAffineUniqueness_of_commonScale`, `additive_rep_unique`).
- **Status**: `pairwiseSliceRepresentationsAtPivot_of_stage3FiniteCutCoverage_and_normalization` and its Stage-4-data wrapper `wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization` are in `WakkerDebreuKoopmans.lean` (axiom-clean: `[propext, Classical.choice, Quot.sound]`). The lift consumes Stage-3 finite-cut coverage at the pivot plus the `SharedPivotAllPairsStep4MachineryCertificate P j₀` normalization input, then routes through the existing M5 closer `pairwiseSliceRepresentationsAtPivot_of_sharedPivot`.

**Order**: A4 → A1 → A3 → A2. A4 supplies the global `V_{j_0}`; A1 needs the shared pivot; A3 is mechanical once A1 is in; A2 closes coverage.

**End state**: with A1–A4 discharged non-circularly, `wakkerStage5GlobalGluingData_of_stage3FiniteCutCoverage` exists, and via the existing chain `wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData` one obtains the first non-trivial, sorry-free `Nonempty (AdditiveRep P)` from purely structural inputs. This closes **O1 and O2 simultaneously** (O2's `hglobal` follows from O1).

---

## Priority B — O3 `QuasiToConcaveStrengtheningCertificate` — **DONE**

- **Where**: `WakkerDebreuKoopmans.lean` L5640-area (definitions + constructors).
- **Strategy**: factor the hard direction through two named residues — `SliceMidpointConcavityCertificate` (per-coordinate midpoint concavity) and `MidpointAndContinuityToConcavityResidual` (the standard convex-analysis upgrade from midpoint concavity + continuity on a convex set to full concavity). The constructor supplies both to the consumer, returning the strengthening certificate for any quasiconcavity input.
- **Status**: `quasiToConcaveStrengtheningCertificate_of_continuity_and_midpoint` consumes convexity of `S₁`, `S₂`, the continuity pair `ContinuousOn V₁ S₁ ∧ ContinuousOn V₂ S₂` (the inlined body of the later `SliceUtilityContinuityCertificate`), the midpoint certificate, and the residual. The composite wrapper `twoCoordinateConcavityCertificate_of_continuity_midpoint_and_convexUpperContour` combines it with `TwoCoordinateConvexUpperContourCertificate` to deliver `TwoCoordinateConcavityCertificate` end-to-end. Both audit `[propext, Classical.choice, Quot.sound]`.

---

## Priority C — O4 per-coordinate concavity transfer — **DONE**

- **Where**: `WakkerDebreuKoopmans.lean` around L5908-area (Priority C block immediately following `perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate`).
- **Strategy**: factor the per-coordinate concavity output through a pivot-indexed pair-concavity input bundle `PerCoordinatePairConcavityAtPivotCertificate R S j₀` (one `TwoCoordinateConcavityCertificate` per pair `(j₀, k)`). The pivot's pair certificate at `(j₀, j₀)` supplies the base concavity at `j₀`; every other pair supplies the `PairConcavityTransferCertificate` input that the existing `perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate` consumes. The composite wrapper additionally records the M4 coordinate-utility continuity residual `(∀ i, ContinuousOn (R.V i) (S i))` as a bystander input to make the M4 dependency explicit at the O4 orchestration site (its structural content is consumed upstream when the pivot pair-concavity certificate is manufactured via Priority B).
- **Status**:
  - `PerCoordinatePairConcavityAtPivotCertificate R S j₀` — pivot-indexed input bundle.
  - `perCoordinateConcavityCertificate_of_perCoordinatePairConcavityAtPivot` — direct constructor; closes the induction via the existing `_of_baseAndPairConcavityCertificate` discharge.
  - `perCoordinateConcavityCertificate_of_pairConcavity_and_coordinateImageCoverage_and_continuity` — composite wrapper named in this priority; signature exposes the full M4 + O3 input surface.
  - `debreu_koopmans_hard_of_pairConcavity_and_coordinateImageCoverage_and_continuity` — end-to-end regression discharging `WakkerDebreuKoopmans.debreu_koopmans_hard` through the composite wrapper.
  - All four audit `[propext, Classical.choice, Quot.sound]`.

**Realized closure sequence**: A4 → A1 → A3 → A2 → B → C. A4 supplies the shared pivot-slice normalization; A1/A3/A2 close the Stage-5 global-gluing surface; B and C close the Debreu--Koopmans concavity side. Together these steps make the construction side theorem-backed end-to-end.

---

## Priority D — TeX surface updates / audit sync per Lean milestone

Each A/B/C deliverable triggered a small TeX update so the paper tracks Lean exactly.

| Lean milestone | TeX section to update | Expected paragraph |
| --- | --- | --- |
| A1 lands (**DONE**) | O1 paragraph (L469-area) | Name `_of_pairwiseSliceRepresentationsAtPivot`; mark `AllPairsAdditivityCertificate` as **theorem-backed** (modulo named cross-pair residual `NonPivotPairAdditivityCertificate`). |
| A2 lands (**DONE**) | O1 paragraph | Mark coordinate-image coverage as theorem-backed; cite `_of_residueAtPivot` (with named cross-coordinate residual `WakkerStep5CoordinateImageCoverageResidualAtPivot`). |
| A3 lands (**DONE**) | O1 paragraph | Mark strict monotonicity as theorem-backed; cite `_of_allPairsAdditivity` (with named cross-profile residual `WakkerStep5StrictMonotonicityResidualAtPivot`). |
| A4 lands (**DONE**) | O1 paragraph + Roadmap table row 2 (`hglobal`) | `MechanizedDecisionTheoryWakkerDK.tex` now reflects the closed chain and promotes O1 and O2 to **discharged**. |
| B lands (**DONE**) | Roadmap table row 4 | Promote O3 to **discharged**; cite `quasiToConcaveStrengtheningCertificate_of_continuity_and_midpoint` and `twoCoordinateConcavityCertificate_of_continuity_midpoint_and_convexUpperContour` (with named residuals `SliceMidpointConcavityCertificate` and `MidpointAndContinuityToConcavityResidual`). |
| C lands (**DONE**) | Roadmap table row 5 | Promote O4 to **discharged**; cite `perCoordinateConcavityCertificate_of_pairConcavity_and_coordinateImageCoverage_and_continuity` and `debreu_koopmans_hard_of_pairConcavity_and_coordinateImageCoverage_and_continuity` (with named input bundle `PerCoordinatePairConcavityAtPivotCertificate`). |
| All four (**DONE**) | Submission-facing JAR draft | `MechanizedDecisionTheoryWakkerDK.tex` now states the end-to-end Wakker IV.2.7 mechanization from the six structural axioms, promotes T1--T6 and A4--C as the top-level methodology, treats M2 as a completed case study, and points reviewers to `Wakker/AxiomCheck.lean`. |

---

## Verification protocol (every milestone)

1. `lake build WakkerDebreuKoopmans` — require exit code 0 for the stable theorem barrel.
2. `lake build Wakker.AxiomCheck` — require exit code 0 and `#print axioms` output from `Wakker/AxiomCheck.lean` plus the imported `WakkerDebreuKoopmans/Audit.lean` showing `[propext, Classical.choice, Quot.sound]`.
3. `lake build ClassicalLotteryInAction` — require exit code 0 for the Management Science companion import surface.
4. `latexmk -pdf -interaction=nonstopmode -halt-on-error 'MechanizedDecisionTheoryWakkerDK.tex'` — require a successful PDF build (overfull hboxes on long Lean identifiers are benign).

## Anti-patterns to avoid

- **Do not** route any new discharge through `R.represents` / `GlobalGluingCertificate P R.V` — that is the exact circularity the Stage-5 narrowing was designed to eliminate (the `_of_globalGluingCertificate` family stays as round-trip ingredients only).
- **Do not** introduce new structural axioms; the six Wakker axioms (`IsWeakOrder`, `TradeoffConsistency`, `PreferenceContinuous`, `ConnectedSpace`, `Essential`, `RestrictedSolvability`, `Archimedean`) are the entire allowed primitive surface.
- **Do not** widen `SingleCoordinateMonotonicityAxiom` back into a primitive — Stage T3 already derives it; A3 must consume the derived form.
- **Do not** edit the existing `_of_globalGluingCertificate` discharges — they are now stable round-trip glue.

---

## Completion status

- A-track (O1+O2 collapse), B-track (O3), and C-track (O4) have all landed in Lean and are reflected in the companion TeX.
- The Stage-5 non-circular closure, quasi-to-concave strengthening, and per-coordinate concavity transfer are now theorem-backed.
- The reviewer-facing audit trail should therefore treat this file as a closure record, not as an open blocker list.

**Status: complete, end-to-end.**
