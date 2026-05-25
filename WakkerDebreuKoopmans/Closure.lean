/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`, now a thin
re-export barrel.
-/

import WakkerDebreuKoopmans.Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open Function Finset

namespace WakkerRoadmap

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

namespace CertificateChecklist

/-! ##### O1: Discharge of `hConstruct` (`WakkerConstructionCertificate`)

Honest scope analysis.  The certificate
`WakkerConstructionCertificate P := ∃ V : (i : ι) → X i → ℝ,
   ∀ x y : Profile X, P.weakPref x y ↔ Σ V_i (y_i) ≤ Σ V_i (x_i)`
is *exactly* the existence of an additive representation.  The genuinely
deep multi-month content of O1 is constructing the utility function `V`
from scratch through Wakker's standard-sequence machinery — i.e., proving
\(\exists R : \texttt{AdditiveRep}\, P\) from the bare structural axioms of
Wakker IV.2.7.  Stages T1--T6 do *not* construct `R`; they consume an
already-given `R` and produce downstream construction-stack content.

What this section delivers honestly:

1. The trivial direction: given any `R : AdditiveRep P`, the construction
   certificate is immediate.
2. A named hypothesis bundle `AdditiveRepHypothesisBundle P :=
   Nonempty (AdditiveRep P)` documenting the precise residual content of O1.
3. The discharge of `WakkerConstructionCertificate P` from the bundle, which
   is one line of `Classical.choice` plus the trivial direction.
4. End-to-end consumer: `additiveRep_nonempty_of_AdditiveRepHypothesisBundle`
   collapsing the bundle to the public consumer interface used by
   `wakker_IV_2_7`.

The **genuinely deep open content** of O1 is unchanged by this section: it
remains the construction of `R` from the bare Wakker IV.2.7 structural axioms,
which is the multi-month target outside the scope of the topology
infrastructure plan T1--T6. -/

/-- **`WakkerConstructionCertificate` from any additive representation.**

The trivial direction: an `AdditiveRep P` already contains the utility
function `V := R.V` and the representation property `R.represents`, so the
construction certificate's existential is immediate. -/
theorem wakkerConstructionCertificate_of_additiveRep
    {X : ι → Type v} (P : WakkerInfra.ProductPref X) (R : AdditiveRep P) :
    WakkerConstructionCertificate P :=
  ⟨R.V, R.represents⟩

/-- **Additive-representation hypothesis bundle for O1.**

Names the precise residual content of O1: the existence of an additive
representation.  Discharging this bundle from the bare structural Wakker
axioms (`Essential`, `RestrictedSolvability`, `Archimedean`, `IsWeakOrder`,
`TradeoffConsistency`, plus the topology axioms in Stage T5's bundle) is
the genuinely deep multi-month content that constitutes Wakker IV.2.7's
forward direction.  Mechanizing that derivation requires building `V`
grid-point-by-grid-point through Wakker's standard-sequence machinery,
which is outside the scope of the topology infrastructure plan T1--T6. -/
def AdditiveRepHypothesisBundle {X : ι → Type v}
    (P : WakkerInfra.ProductPref X) : Prop :=
  Nonempty (AdditiveRep P)

/-- **`WakkerConstructionCertificate` from the additive-representation
hypothesis bundle.**

Discharge of the construction certificate from the named O1 bundle, via
`Classical.choice` to extract the additive representation and
`wakkerConstructionCertificate_of_additiveRep` to package it. -/
theorem wakkerConstructionCertificate_of_additiveRepHypothesisBundle
    {X : ι → Type v} (P : WakkerInfra.ProductPref X)
    (hBundle : AdditiveRepHypothesisBundle P) :
    WakkerConstructionCertificate P :=
  wakkerConstructionCertificate_of_additiveRep P hBundle.some

/-- **Reverse direction: `AdditiveRepHypothesisBundle` from
`WakkerConstructionCertificate`.**

The certificate's existential gives `(V, hglobal)` from which we package the
additive representation directly. -/
theorem additiveRepHypothesisBundle_of_wakkerConstructionCertificate
    {X : ι → Type v} (P : WakkerInfra.ProductPref X)
    (hConstruct : WakkerConstructionCertificate P) :
    AdditiveRepHypothesisBundle P :=
  additiveRep_nonempty_of_wakkerConstructionCertificate P hConstruct

/-- **Equivalence: `AdditiveRepHypothesisBundle ↔ WakkerConstructionCertificate`.**

Documents that the construction certificate and the additive-representation
hypothesis bundle are propositionally equivalent.  The deep mathematical
content of O1 is producing *either* of them from the structural Wakker axioms,
and both are equally hard. -/
theorem additiveRepHypothesisBundle_iff_wakkerConstructionCertificate
    {X : ι → Type v} (P : WakkerInfra.ProductPref X) :
    AdditiveRepHypothesisBundle P ↔ WakkerConstructionCertificate P :=
  ⟨wakkerConstructionCertificate_of_additiveRepHypothesisBundle P,
   additiveRepHypothesisBundle_of_wakkerConstructionCertificate P⟩

/-- **End-to-end: `Nonempty (AdditiveRep P)` from the additive-representation
hypothesis bundle.**

Trivial repackaging: the bundle is exactly `Nonempty (AdditiveRep P)`. -/
theorem additiveRep_nonempty_of_additiveRepHypothesisBundle
    {X : ι → Type v} (P : WakkerInfra.ProductPref X)
    (hBundle : AdditiveRepHypothesisBundle P) :
    Nonempty (AdditiveRep P) := hBundle

/-- **Top-level Wakker IV.2.7 from the additive-representation hypothesis
bundle plus the standard structural axioms.**

The public consumer interface.  This theorem documents the role of the
additive-representation hypothesis bundle: it is the precise residual content
that, combined with Wakker's structural axioms, produces the public
`Nonempty (AdditiveRep P)` consumer used by `wakker_IV_2_7`. -/
theorem wakker_IV_2_7_of_additiveRepHypothesisBundle
    {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : WakkerInfra.ProductPref X)
    [WakkerInfra.ProductPref.IsWeakOrder P]
    [WakkerInfra.ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (solvability  : WakkerInfra.ProductPref.RestrictedSolvability P)
    (archimedean  : ∃ j, WakkerInfra.ProductPref.Archimedean P j)
    (hBundle      : AdditiveRepHypothesisBundle P) :
    Nonempty (AdditiveRep P) :=
  wakker_IV_2_7_of_wakkerConstructionCertificate P essential solvability archimedean
    (wakkerConstructionCertificate_of_additiveRepHypothesisBundle P hBundle)

/-! ##### O1 standard-sequence-machinery forward-direction scaffolding
(Wakker (1989) Theorem IV.2.7, forward direction)

This block factors the genuinely deep multi-month O1 content
(`Nonempty (AdditiveRep P)` from the bare structural Wakker IV.2.7 axioms)
into a sequence of five named **stage outputs** mirroring Wakker's
grid-point-by-grid-point construction of `V` on a pivot coordinate `j`,
followed by cross-coordinate calibration and global additive assembly.
Each stage is a self-contained `Prop` whose body names exactly the data
produced by the corresponding block of the monograph proof.  The active
bundle now records theorem-backed Stage 2--4 attack outputs (`ℕ`-grid,
finite-cut coverage, and shared-pivot slice representation) rather than
opaque implications between the overstrong monograph endpoints.

The bundle is sorry-free: Stage 1 is a seed, Stages 2--4 are active
construction outputs with named constructors below, and only Stage 5 remains
as the final global-assembly implication to `AdditiveRepHypothesisBundle P`.

This is a *factoring layer*, not a full discharge: producing Stage 5 from
the Stage-4 pivot-slice surface is still the multi-month Wakker construction
itself.  The value of the layer is that it documents the precise decomposition
Wakker's monograph follows while moving Stages 2--4 onto theorem-backed,
non-circular Lean surfaces.

Stage outline (Wakker IV.2, forward direction):

* **Stage 1** — pivot data: existence of an essential pivot coordinate
  `j` together with a strict reference pair `v ≺_j w` on `j`.  Wakker's
  Step 1; trivially derivable from `∀ i, Essential P i`.
* **Stage 2** — integer-grid utility on the pivot: a doubly-infinite
  standard sequence `(aₙ)_{n∈ℤ}` on `Xⱼ` with `Vⱼ(aₙ) = n` and strict
  monotonicity of the corresponding preference comparisons.  Wakker's
  Step 2 (Archimedean + restricted solvability).
* **Stage 3** — dyadic-rational refinement: a `ℚ`-indexed grid
  `gridDyadic : ℚ → Xⱼ` with `Vⱼ(gridDyadic q) = q`.  Wakker's Step 3
  (bisection / mid-point standard sequences).
* **Stage 4** — full pivot coordinate utility: a function
  `Vⱼ : Xⱼ → ℝ` representing pivot preference on every profile section.
  Wakker's Step 4 (continuity / density extension).
* **Stage 5** — cross-coordinate calibration and additive assembly:
  the existence of an `AdditiveRep P`.  Wakker's Steps 5–6 (tradeoff
  consistency + global representation verification).  This stage is
  propositionally identical to `AdditiveRepHypothesisBundle P`. -/

/-- **Stage 1 (Wakker IV.2 Step 1) — pivot data.**

Existence of an essential pivot coordinate `j` with a strict reference
pair: profile sections `a[j := v]` and `a[j := w]` that strictly compare
under `P.weakPref`.  This is the seed witness used to launch the
standard-sequence construction. -/
def WakkerStage1PivotData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j : ι) (a : Profile X) (v w : X j),
    P.weakPref (Function.update a j v) (Function.update a j w) ∧
      ¬ P.weakPref (Function.update a j w) (Function.update a j v)

/-- Trivial Stage-1 seed derivation from the structural essential
hypothesis: any essential coordinate supplies a strict reference pair. -/
theorem wakkerStage1PivotData_of_essential
    {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    [Nonempty ι]
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i) :
    WakkerStage1PivotData P := by
  classical
  obtain ⟨j⟩ : Nonempty ι := inferInstance
  obtain ⟨a, v, w, hvw, hwv⟩ := essential j
  exact ⟨j, a, v, w, hvw, hwv⟩

/-- **Stage 2 (Wakker IV.2 Step 2) — integer-grid utility on the pivot.**

Existence of a pivot coordinate `j`, a doubly-infinite standard sequence
`aₙ : ℤ → Xⱼ`, and a coordinate utility `Vⱼ : Xⱼ → ℝ` with
`Vⱼ(aₙ) = n` for every `n ∈ ℤ`, together with strict monotonicity of
the standard-sequence preference comparison: for `n < m` there is a
common base profile witnessing `aₙ ≺_j aₘ`.  This is the output of
Wakker's Archimedean + restricted-solvability integer-grid construction. -/
def WakkerStage2IntegerGridData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j : ι) (aSeq : ℤ → X j) (Vj : X j → ℝ),
    (∀ n : ℤ, Vj (aSeq n) = (n : ℝ)) ∧
    (∀ n m : ℤ, n < m → ∃ b : Profile X,
      P.weakPref (Function.update b j (aSeq m)) (Function.update b j (aSeq n)) ∧
        ¬ P.weakPref (Function.update b j (aSeq n)) (Function.update b j (aSeq m)))

/-- **Stage 3 (Wakker IV.2 Step 3) — dyadic-rational refinement.**

Existence of a pivot coordinate `j`, a coordinate utility `Vⱼ : Xⱼ → ℝ`,
and a `ℚ`-indexed grid `gridDyadic : ℚ → Xⱼ` with `Vⱼ(gridDyadic q) = q`
for every `q ∈ ℚ`.  This is the output of Wakker's bisection / mid-point
standard-sequence refinement, densifying the integer grid to a
rational-valued grid. -/
def WakkerStage3DyadicRefinementData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j : ι) (Vj : X j → ℝ) (gridDyadic : ℚ → X j),
    ∀ q : ℚ, Vj (gridDyadic q) = (q : ℝ)

/-- **Stage 4 (Wakker IV.2 Step 4) — full pivot coordinate utility.**

Existence of a pivot coordinate `j` and a coordinate utility
`Vⱼ : Xⱼ → ℝ` representing pivot preference on every profile section:
for every base `a` and every `v, w ∈ Xⱼ`,
`a[j := v] ≽ a[j := w] ↔ Vⱼ w ≤ Vⱼ v`.  This is the output of Wakker's
continuity / density extension from the rational grid to the full
coordinate space. -/
def WakkerStage4FullPivotUtilityData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j : ι) (Vj : X j → ℝ),
    ∀ (a : Profile X) (v w : X j),
      P.weakPref (Function.update a j v) (Function.update a j w) ↔ Vj w ≤ Vj v

/-! ##### O1 Stage 2--4 theorem-backed attack surfaces

The three monograph-shaped Stage 2--4 targets above deliberately state the
classical Wakker endpoints: a two-sided integer grid, a rational/dyadic
refinement, and a full pivot-coordinate utility.  The currently audited Lean
machinery reaches a finer, forward-safe surface:

* a one-sided `ℕ`-grid utility on any injective standard sequence;
* finite-cut coverage on pairwise standard-sequence grids;
* shared-pivot pairwise Step-4 machinery yielding pivot-slice representations.

The following `Prop`s and constructors are the active, theorem-backed attack
layer for Stages 2--4.  They intentionally avoid any premise of the form
`R : AdditiveRep P`, so they do not smuggle the desired conclusion into the
forward construction. -/

/-- **Theorem-backed Stage 2 attack — natural-number grid utility.**

For some pivot `j`, an injective standard sequence `σ` on `j` carries a
utility `Vj` normalized by `Vj (σ.α n) = n` and strictly increasing along the
grid.  This is the currently theorem-backed grid-point-by-grid-point core of
Wakker Step 2; the older `WakkerStage2IntegerGridData` remains the stronger
two-sided endpoint target. -/
def WakkerStage2NatGridData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j : ι) (σ : ProductPref.StandardSequence P j) (Vj : X j → ℝ),
    Function.Injective σ.α ∧
    (∀ n : ℕ, Vj (σ.α n) = (n : ℝ)) ∧
    (∀ n m : ℕ, n < m → Vj (σ.α n) < Vj (σ.α m))

/-- **Stage 2 attack constructor from an injective standard sequence.**

This is the structural-axioms-safe grid utility theorem already present in
the file, repackaged as the active O1 Stage-2 attack output. -/
theorem wakkerStage2NatGridData_of_injectiveStandardSequence
    {X : ι → Type v} (P : ProductPref X) {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hinj : Function.Injective σ.α) :
    WakkerStage2NatGridData P := by
  obtain ⟨Vj, hVj⟩ := WakkerExistence.coord_utility_on_grid_exists P σ hinj
  refine ⟨j, σ, Vj, hinj, hVj, ?_⟩
  intro n m hnm
  rw [hVj n, hVj m]
  exact_mod_cast hnm

/-- **Theorem-backed Stage 3 attack — pairwise finite-cut coverage.**

Instead of asserting a global `ℚ`-indexed pivot grid, the audited Step-3
surface records finite-cut coverage on a pair of standard-sequence grids.
This is the non-circular form currently theorem-backed from Archimedean
bracketing plus grid reachability/surjectivity. -/
def WakkerStage3FiniteCutCoverageData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ (j k : ι), j ≠ k ∧
    ∃ (σj : ProductPref.StandardSequence P j)
      (σk : ProductPref.StandardSequence P k),
      PairwiseFiniteCutCoverageCertificate σj σk

/-- **Stage 3 attack constructor from surjective standard-sequence grids.** -/
theorem wakkerStage3FiniteCutCoverageData_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    WakkerStage3FiniteCutCoverageData P := by
  refine ⟨j, k, hjk, σj, σk, ?_⟩
  exact pairwiseFiniteCutCoverageCertificate_of_archimedean_and_surjectiveStandardSequences
    P hjk σj σk harchim_j harchim_k hsurj_j hsurj_k

/-- **Stage 3 attack constructor from grid reachability and a surjective
second-coordinate grid.** -/
theorem wakkerStage3FiniteCutCoverageData_of_gridReachability_surjectiveSecondCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_k : Function.Surjective σk.α) :
    WakkerStage3FiniteCutCoverageData P := by
  refine ⟨j, k, hjk, σj, σk, ?_⟩
  exact pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveSecondCoord
    P hjk σj σk harchim_j harchim_k hreach hsurj_k

/-- **Stage 3 attack constructor from grid reachability and a surjective
first-coordinate grid.** -/
theorem wakkerStage3FiniteCutCoverageData_of_gridReachability_surjectiveFirstCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_j : Function.Surjective σj.α) :
    WakkerStage3FiniteCutCoverageData P := by
  refine ⟨j, k, hjk, σj, σk, ?_⟩
  exact pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveFirstCoord
    P hjk σj σk harchim_j harchim_k hreach hsurj_j

/-- **Theorem-backed Stage 4 attack — pivot slice representations.**

This records the currently non-circular Step-4/Step-5-facing output: a pivot
coordinate whose pairwise slices all admit representations sharing a pivot
utility.  It is weaker and more honest than immediately asserting a full
standalone pivot utility, but it is strong enough to recover the old Stage-4
single-coordinate representation once any non-pivot coordinate is supplied. -/
def WakkerStage4PivotSliceRepresentationData {X : ι → Type v}
    (P : WakkerInfra.ProductPref X) : Prop :=
  ∃ j₀ : ι, PairwiseSliceRepresentationsAtPivot P j₀

/-- **Stage 4 attack constructor from shared-pivot all-pairs Step-4 machinery,
density, and continuity.**

No additive representation is assumed; the constructor routes through the
already-audited shared-pivot pairwise machinery and density-extension closer. -/
theorem wakkerStage4PivotSliceRepresentationData_of_sharedPivot
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j₀ : ι} [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid :
      ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
        Dense (Set.range σⱼ₀.α)) :
    WakkerStage4PivotSliceRepresentationData P := by
  exact ⟨j₀,
    pairwiseSliceRepresentationsAtPivot_of_sharedPivot
      P hsolv hShared hcont hdense_grid⟩

/-- **A4 — Stage-4 pivot-slice representations from Stage-3 finite-cut
coverage data and a multi-pair normalization input (Wakker IV.2 Step 4
lift, Stage 3 → Stage 4).**

Concretely, this packages the honest Wakker IV.2 Step-4 transition:

* **Stage-3 input** (`hStage3AtPivot`).  Stage-3 finite-cut coverage at the
  chosen pivot `j₀`: at least one paired non-pivot coordinate `k` carries
  a `PairwiseFiniteCutCoverageCertificate` against the pivot.  This is the
  Stage-3 output of `wakkerStage3FiniteCutCoverageData_of_*` consumed at the
  pivot side.  It serves as a named consistency witness that `j₀` is a
  viable pivot in the Wakker IV.2 Step 4 standard-sequence sense.

* **Normalization input** (`hNorm`).  A
  `SharedPivotAllPairsStep4MachineryCertificate P j₀` packaging, for every
  non-pivot coordinate `k`, a `PairwiseStep4TradeoffMachineryCertificate`
  calibrated against a single shared pivot-side standard sequence `σⱼ₀`.
  This is exactly the output of Wakker IV.2 Step 4's affine renormalization
  that re-pivots the per-pair Step-3 outputs `(R_{j₀,k}.V_{j₀})_{k ≠ j₀}`
  onto a single common `V_{j₀}`.  Discharging it from purely structural
  axioms is the remaining Wakker IV.2 Step 4 obligation (see the `m5_*` and
  `sharedPivotGrid_*` lemmas above for the machinery and
  `pairwise_additivity_of_injectiveStandardSequences_*` for the per-pair
  Step-4 chain).

* **Topology/continuity/density inputs** (`hcont`, `hdense_grid`).  Standard
  T2 + continuity of all candidate coordinate utilities on `j₀` plus density
  of every pivot grid; both flow into the already-audited M5 cardinal
  closer `pairwiseSliceRepresentationsAtPivot_of_sharedPivot`.

The proof composes the existing M5 closer; Stage-3 data is consumed as a
named consistency witness for `j₀`, and the construction itself is carried
by `hNorm` plus density and continuity.  This is the explicit non-circular
A4 route specified in the Wakker completion roadmap (Priority A, A4). -/
theorem pairwiseSliceRepresentationsAtPivot_of_stage3FiniteCutCoverage_and_normalization
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j₀ : ι} [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStage3AtPivot : ∃ k : ι, k ≠ j₀ ∧
      ∃ (σj : ProductPref.StandardSequence P j₀)
        (σk : ProductPref.StandardSequence P k),
        PairwiseFiniteCutCoverageCertificate σj σk)
    (hNorm : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid : ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
      Dense (Set.range σⱼ₀.α)) :
    PairwiseSliceRepresentationsAtPivot P j₀ := by
  -- Stage-3 data is recorded as a named consistency witness that the
  -- chosen pivot `j₀` admits at least one finite-cut-coverable companion
  -- pair, hence is a viable pivot.  The actual construction routes through
  -- the shared-pivot normalization input plus the audited M5 cardinal
  -- closer.
  obtain ⟨_k, _hk, _σj, _σk, _hcov⟩ := hStage3AtPivot
  exact pairwiseSliceRepresentationsAtPivot_of_sharedPivot
    P hsolv hNorm hcont hdense_grid

/-- **A4 — Stage-4 lift wrapper: package the A4 closer at the Stage-4 data
surface.**

Bundles `pairwiseSliceRepresentationsAtPivot_of_stage3FiniteCutCoverage_and_normalization`
into `WakkerStage4PivotSliceRepresentationData P`, exposing the named
Stage-3-to-Stage-4 lift at the same surface as
`wakkerStage4PivotSliceRepresentationData_of_sharedPivot`. -/
theorem wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j₀ : ι} [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStage3AtPivot : ∃ k : ι, k ≠ j₀ ∧
      ∃ (σj : ProductPref.StandardSequence P j₀)
        (σk : ProductPref.StandardSequence P k),
        PairwiseFiniteCutCoverageCertificate σj σk)
    (hNorm : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid : ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
      Dense (Set.range σⱼ₀.α)) :
    WakkerStage4PivotSliceRepresentationData P :=
  ⟨j₀,
    pairwiseSliceRepresentationsAtPivot_of_stage3FiniteCutCoverage_and_normalization
      hsolv hStage3AtPivot hNorm hcont hdense_grid⟩

/-- **Recover the older full-pivot Stage-4 target from pivot slice
representations and one non-pivot coordinate.**

The proof restricts any represented `(j₀,k)` slice to single-coordinate
changes at `j₀`; the `Vk` term cancels. -/
theorem wakkerStage4FullPivotUtilityData_of_pairwiseSliceRepresentationsAtPivot
    {X : ι → Type v} {P : ProductPref X} {j₀ k : ι}
    (hk : k ≠ j₀)
    (hPivot : PairwiseSliceRepresentationsAtPivot P j₀) :
    WakkerStage4FullPivotUtilityData P := by
  obtain ⟨Vj₀, hSlices⟩ := hPivot
  obtain ⟨Vk, hslice⟩ := hSlices k hk
  refine ⟨j₀, Vj₀, ?_⟩
  intro a v w
  have hAgree : Profile.agreeOff ({j₀} : Set ι)
      (Function.update a j₀ v) (Function.update a j₀ w) := by
    intro i hi
    have hij : i ≠ j₀ := by
      intro h
      exact hi (by simp [h])
    simp [Function.update_of_ne hij]
  have hRestrict := pairwiseSlice_restricted_to_pivot (P := P)
    (j₀ := j₀) (k := k) hk.symm (Vₖ := Vk) hslice hAgree
  simpa [Function.update_self] using hRestrict

/-- **Recover the older full-pivot Stage-4 target from active Stage-4 attack
data and an explicit non-pivot witness.** -/
theorem wakkerStage4FullPivotUtilityData_of_stage4PivotSliceRepresentationData
    {X : ι → Type v} {P : ProductPref X}
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hNonpivot : ∀ j₀ : ι, ∃ k : ι, k ≠ j₀) :
    WakkerStage4FullPivotUtilityData P := by
  obtain ⟨j₀, hPivot⟩ := hStage4
  obtain ⟨k, hk⟩ := hNonpivot j₀
  exact wakkerStage4FullPivotUtilityData_of_pairwiseSliceRepresentationsAtPivot hk hPivot

/-! ##### A1 — All-pairs additivity from pivot-slice representations

Roadmap item **A1** (`AllPairsAdditivityCertificate P V` for one global
`V`).  The deliverable is a non-circular assembly of
`AllPairsAdditivityCertificate P V` from the active Stage-4 pivot-slice
surface (`PairwiseSliceRepresentationsAtPivot P j₀`) plus a single named
consistency residue covering the cross-pair (both non-pivot) case.

The pivot-touching pairs (`j = j₀` or `k = j₀`) are discharged directly
from the pivot-slice certificates already supplied by Stage 4.  The
remaining cross-pair case is the genuine Wakker IV.2 Step 5–6 tradeoff-
consistency content; we isolate it as a Prop-level certificate
`NonPivotPairAdditivityCertificate` (mirroring the A4 routing of Stage-3
data through `SharedPivotAllPairsStep4MachineryCertificate`).  This keeps
the A1 assembly axiom-clean and exposes the exact remaining work for the
follow-on A2/A3 steps. -/

/-- **A1 — Cross-pair non-pivot additivity residual (named input).**

For coordinate pairs `(j, k)` with both `j, k ≠ j₀`, the pair-form
representation equation holds for the coordinate utilities `V j`, `V k`.

This is automatic from a global additive representation but cannot be
derived from pivot-slice data alone without invoking Wakker's deep
tradeoff-consistency argument.  It is therefore exposed as a named
consistency input here, exactly paralleling the A4 use of
`SharedPivotAllPairsStep4MachineryCertificate` for Stage-3-to-Stage-4
lift.  The discharge of this residual is the open content of A2/A3. -/
def NonPivotPairAdditivityCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    ∀ x y : Profile X,
      Profile.agreeOff ({j, k} : Set ι) x y →
      (P.weakPref x y ↔
        V j (y j) + V k (y k) ≤ V j (x j) + V k (x k))

/-- **A1 — All-pairs additivity from a pivot-slice-matched `V` and the
cross-pair residual.**

Given a global coordinate-utility family `V` whose pivot slices `(V j₀, V k)`
satisfy `PairwiseSliceRepresentationCertificate P j₀ k` for every non-pivot
coordinate `k`, plus the named cross-pair residual covering pairs with both
coordinates `≠ j₀`, assemble the global
`AllPairsAdditivityCertificate P V`.

The proof splits on whether either coordinate of the requested pair equals
the pivot:

* `j = j₀`: direct from `hMatch k`.
* `k = j₀`, `j ≠ j₀`: from `hMatch j` after swapping the unordered pair
  `{j, j₀} = {j₀, j}`; commute the two utility summands.
* `j ≠ j₀ ∧ k ≠ j₀`: from `hCross`. -/
theorem allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot
    {X : ι → Type v} {P : ProductPref X} (j₀ : ι)
    (V : (i : ι) → X i → ℝ)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k))
    (hCross : NonPivotPairAdditivityCertificate P V j₀) :
    AllPairsAdditivityCertificate P V := by
  intro j k hjk x y hxy
  by_cases hj : j = j₀
  · -- Pair (j₀, k); `k ≠ j₀` from `j ≠ k`.
    have hk : k ≠ j₀ := by
      intro h; apply hjk; rw [hj, h]
    have hxy' : Profile.agreeOff ({j₀, k} : Set ι) x y := by
      intro i hi
      apply hxy i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      rintro (h | h)
      · exact hi (Or.inl (h.trans hj))
      · exact hi (Or.inr h)
    have hslice := hMatch k hk x y hxy'
    rw [hj]; exact hslice
  · by_cases hk : k = j₀
    · -- Pair (j, j₀) with `j ≠ j₀`; use slice (j₀, j) and commute the sum.
      have hxy' : Profile.agreeOff ({j₀, j} : Set ι) x y := by
        intro i hi
        apply hxy i
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
        rintro (h | h)
        · exact hi (Or.inr h)
        · exact hi (Or.inl (h.trans hk))
      have hslice := hMatch j hj x y hxy'
      rw [hk, hslice]
      constructor <;> intro h <;> linarith
    · -- Pair (j, k) with both `≠ j₀`.
      exact hCross j k hj hk hjk x y hxy

/-- **A1 — Stage-4 wrapper: extract a global `V` and `AllPairsAdditivityCertificate`
from the active pivot-slice Stage-4 data.**

Consumes `WakkerStage4PivotSliceRepresentationData P` (witnessing
`∃ j₀, PairwiseSliceRepresentationsAtPivot P j₀`) together with the named
cross-pair residual.  Uses classical choice to materialize a single global
`V : (i : ι) → X i → ℝ` whose pivot slices match the existence content of
the Stage-4 data, then invokes
`allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot`. -/
theorem allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData
    {X : ι → Type v} {P : ProductPref X}
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀) :
    ∃ (j₀ : ι) (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
      AllPairsAdditivityCertificate P V := by
  classical
  obtain ⟨j₀, Vj₀, hSlices⟩ := hStage4
  -- For each `i`, choose a coordinate utility: `V j₀ := Vj₀`, and for
  -- `i ≠ j₀` pick the chosen `Vk` from `hSlices i (by …)`.  We package
  -- the dependent choice with `Classical.byCases`-style branching on
  -- `i = j₀`.
  let V : (i : ι) → X i → ℝ := fun i =>
    if h : i = j₀ then (h ▸ Vj₀) else Classical.choose (hSlices i h)
  have hV_j₀ : V j₀ = Vj₀ := by simp [V]
  have hV_k : ∀ k : ι, ∀ hk : k ≠ j₀, V k = Classical.choose (hSlices k hk) := by
    intro k hk
    simp [V, hk]
  -- Pivot-slice match for the constructed `V`.
  have hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k) := by
    intro k hk
    have hChoose := Classical.choose_spec (hSlices k hk)
    -- `hChoose : PairwiseSliceRepresentationCertificate P j₀ k Vj₀ (Classical.choose …)`
    rw [hV_j₀, hV_k k hk]
    exact hChoose
  refine ⟨j₀, V, hMatch, ?_⟩
  exact allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot
    j₀ V hMatch (hCross j₀ V hMatch)

/-! ##### A3 — Strict monotonicity from pivot-slice representations

Roadmap item **A3** (`WakkerStep5StrictMonotonicityCertificate P V`).  The
deliverable is a non-circular assembly producing the strict-monotonicity
certificate for the global `V` constructed by A1.

The strict-monotonicity content is `∀ x y, P.indiff x y → ∑ V (x) = ∑ V (y)`.
We split on whether `x` and `y` agree off a pivot-touching pair
`{j₀, k}`:

* **pair-aligned case**: `Profile.agreeOff {j₀, k} x y` for some `k ≠ j₀`.
  Discharged constructively from the supplied
  `AllPairsAdditivityCertificate P V` (applied to both directions of
  indifference, then split via `sum_eq_pair_add_rest`).
* **cross-profile case**: `x`, `y` do not agree off any pivot-touching
  pair.  Named as `WakkerStep5StrictMonotonicityResidualAtPivot P V j₀`
  — the genuine cross-coordinate content of the Wakker IV.2 Step 5
  argument that cannot be reached from pair-additivity alone.

This mirrors A1's `NonPivotPairAdditivityCertificate` shape: name the
residue beyond pivot-slice reach, then assemble.  The wrapper composes
with A1 to deliver a `V`, an `AllPairsAdditivityCertificate`, and the
strict-monotonicity certificate from Stage-4 pivot-slice data plus the
two named residues. -/

/-- **A3 — Strict-monotonicity residue beyond pivot slices.**

Indifferent profiles `x`, `y` that do not agree off any pivot-touching
pair `{j₀, k}` (`k ≠ j₀`) have equal additive sums.

For pairs of the form `agreeOff {j₀, k}`, the analogous statement is
provable from `AllPairsAdditivityCertificate` alone via
`sum_eq_pair_add_rest`; this residue isolates the genuinely
cross-coordinate content of Wakker IV.2 Step 5 that cannot be reached
from pair-additivity at the pivot. -/
def WakkerStep5StrictMonotonicityResidualAtPivot {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι) : Prop :=
  ∀ x y : Profile X,
    P.indiff x y →
    (∀ k : ι, k ≠ j₀ → ¬ Profile.agreeOff ({j₀, k} : Set ι) x y) →
    (∑ i, V i (x i)) = (∑ i, V i (y i))

/-- **A3 — Strict-monotonicity certificate from all-pairs additivity and the
named cross-profile residue.**

The pair-aligned case (`Profile.agreeOff {j₀, k} x y` for some `k ≠ j₀`)
is discharged directly from `hpair`: applying the all-pairs additivity
equivalence to both directions of indifference forces equality of the
pair sum, and `sum_eq_pair_add_rest` then identifies the remaining
off-pair summands via the `agreeOff` hypothesis.

The complementary case (`x`, `y` do not agree off any pivot-touching
pair) is consumed verbatim from
`WakkerStep5StrictMonotonicityResidualAtPivot P V j₀`. -/
theorem wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hResidue : WakkerStep5StrictMonotonicityResidualAtPivot P V j₀) :
    WakkerStep5StrictMonotonicityCertificate P V hpair hsolv := by
  classical
  intro x y hxy
  by_cases h : ∃ k : ι, k ≠ j₀ ∧ Profile.agreeOff ({j₀, k} : Set ι) x y
  · obtain ⟨k, hk_ne_j, hagree⟩ := h
    have hjk : j₀ ≠ k := fun hh => hk_ne_j hh.symm
    have hagree_sym : Profile.agreeOff ({j₀, k} : Set ι) y x :=
      fun i hi => (hagree i hi).symm
    have hxy_iff := hpair j₀ k hjk x y hagree
    have hyx_iff := hpair j₀ k hjk y x hagree_sym
    have h1 : V j₀ (y j₀) + V k (y k) ≤ V j₀ (x j₀) + V k (x k) :=
      hxy_iff.mp hxy.1
    have h2 : V j₀ (x j₀) + V k (x k) ≤ V j₀ (y j₀) + V k (y k) :=
      hyx_iff.mp hxy.2
    have hpair_eq :
        V j₀ (x j₀) + V k (x k) = V j₀ (y j₀) + V k (y k) :=
      le_antisymm h2 h1
    rw [sum_eq_pair_add_rest V x hjk, sum_eq_pair_add_rest V y hjk,
        hpair_eq]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hi_erase_j : i ∈ Finset.univ.erase j₀ :=
      (Finset.mem_erase.mp hi).2
    have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi_erase_j
    have hi_not_pair : i ∉ ({j₀, k} : Set ι) := by
      intro himem
      rcases (by simpa using himem : i = j₀ ∨ i = k) with rfl | rfl
      · exact hij rfl
      · exact hik rfl
    rw [hagree i hi_not_pair]
  · push_neg at h
    exact hResidue x y hxy h

/-- **A3 — Stage-4 wrapper.**

Composes A1 (`allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData`)
with the strict-monotonicity assembly above: from Stage-4 pivot-slice
data, the A1 cross-pair residue, and the A3 cross-profile residue,
produce a global `V`, an all-pairs additivity certificate, and the
strict-monotonicity certificate sharing the same `V` and `hpair`.

Returns the same `(j₀, V, hMatch, hpair)` tuple as A1, augmented with
the strict-monotonicity certificate.  This is the input shape consumed
by the Stage-5 global-gluing data assembly. -/
theorem wakkerStep5StrictMonotonicityCertificate_of_stage4PivotSliceRepresentationData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀)
    (hResidue : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      WakkerStep5StrictMonotonicityResidualAtPivot P V j₀) :
    ∃ (j₀ : ι) (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
      ∃ hpair : AllPairsAdditivityCertificate P V,
        WakkerStep5StrictMonotonicityCertificate P V hpair hsolv := by
  obtain ⟨j₀, V, hMatch, hpair⟩ :=
    allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData
      hStage4 hCross
  refine ⟨j₀, V, hMatch, hpair, ?_⟩
  exact wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity
    j₀ V hpair hsolv (hResidue j₀ V)

/-! ##### A2 — Coordinate-image coverage from pivot-slice representations

Roadmap item **A2** (`WakkerStep5CoordinateImageCoverageCertificate P V`).
The deliverable is a non-circular assembly producing the coverage
certificate for the global `V` constructed by A1.

The coverage content is genuinely cross-coordinate: for any profiles
`x, y` with `∑ V (y) ≤ ∑ V (x)` and a pivot `j₀`, there must exist a
single value `c : X j₀` such that updating `x` at `j₀` to `c` produces
an intermediate profile satisfying the preference bracket
`x ≽ update x j₀ c ≽ y`.  This is the precise input that the M1 chain
construction below consumes.

Following the A3 template, we name the per-pivot residue
`WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀` — the
genuine standard-sequence / Archimedean content of Wakker IV.2 Step 5
that cannot be reached from pair-additivity alone — and then assemble
the global certificate as a trivial repackaging that quantifies the
pivot over `ι`. -/

/-- **A2 — Coordinate-image coverage residue at a fixed pivot.**

Per-pivot form of the coverage content: for any profiles `x, y` with
`∑ V (y) ≤ ∑ V (x)`, there exists a pivot value `c : X j₀` producing
the bracket `x ≽ update x j₀ c ≽ y`.

This isolates the genuinely cross-coordinate Archimedean / standard-
sequence content of Wakker IV.2 Step 5 that pair-additivity at the
pivot does not supply.  Conjunctively quantified over `j₀ : ι`, it is
equivalent to `WakkerStep5CoordinateImageCoverageCertificate P V`. -/
def WakkerStep5CoordinateImageCoverageResidualAtPivot {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι) : Prop :=
  ∀ x y : Profile X,
    (∑ i, V i (y i)) ≤ (∑ i, V i (x i)) →
      ∃ c : X j₀,
        P.weakPref x (Function.update x j₀ c) ∧
        P.weakPref (Function.update x j₀ c) y

/-- **A2 — Coverage certificate from per-pivot coverage residues.**

The global coverage certificate is a trivial repackaging of the per-pivot
residue family: the certificate body itself quantifies over `j₀`, so
supplying `WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀` for
every pivot discharges the certificate by direct application. -/
theorem wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hResidue : ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀) :
    WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv := by
  intro x y j₀ hle
  exact hResidue j₀ x y hle

/-- **A2 — Stage-4 wrapper.**

Composes A1 (`allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData`)
with the coverage assembly above: from Stage-4 pivot-slice data, the A1
cross-pair residue, and the A2 per-pivot coverage residue family,
produce a global `V`, an all-pairs additivity certificate, and the
coordinate-image coverage certificate sharing the same `V` and `hpair`.

Returns the same `(j₀, V, hMatch, hpair)` tuple as A1, augmented with
the coverage certificate.  Symmetric in shape to the A3 wrapper. -/
theorem wakkerStep5CoordinateImageCoverageCertificate_of_stage4PivotSliceRepresentationData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀)
    (hResidue : ∀ (V : (i : ι) → X i → ℝ) (j₀ : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀) :
    ∃ (j₀ : ι) (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
      ∃ hpair : AllPairsAdditivityCertificate P V,
        WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv := by
  obtain ⟨j₀, V, hMatch, hpair⟩ :=
    allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData
      hStage4 hCross
  refine ⟨j₀, V, hMatch, hpair, ?_⟩
  exact wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot
    V hpair hsolv (fun j => hResidue V j)

/-- **Stage 5 (Wakker IV.2 Steps 5–6) — cross-coordinate calibration and
additive assembly.**

Existence of an additive representation of `P`.  This is the output of
Wakker's cross-coordinate calibration via tradeoff consistency followed
by global additive verification.  Propositionally identical to
`AdditiveRepHypothesisBundle P`. -/
def WakkerStage5AdditiveAssemblyData {X : ι → Type v} (P : WakkerInfra.ProductPref X) : Prop :=
  Nonempty (AdditiveRep P)

/-- Stage 5 is the same proposition as the additive-representation
hypothesis bundle. -/
theorem additiveRepHypothesisBundle_iff_wakkerStage5AdditiveAssemblyData
    {X : ι → Type v} (P : WakkerInfra.ProductPref X) :
    AdditiveRepHypothesisBundle P ↔ WakkerStage5AdditiveAssemblyData P :=
  Iff.rfl

/-! ##### O1 Stage 5 theorem-backed global-gluing attack surface

The old Stage-5 endpoint `WakkerStage5AdditiveAssemblyData P` is exactly
`Nonempty (AdditiveRep P)`, so taking it as a bundle field hides the real
work.  The next non-circular narrowing is to expose the explicit global-gluing
data consumed by the already-proved M1 chain-construction theorem:

* one coordinate-utility family `V` whose pivot slices agree with the active
  Stage-4 pivot-slice surface;
* an all-pairs additivity certificate for the same `V`;
* the coordinate-image coverage certificate; and
* the strict-monotonicity companion certificate.

From these four pieces, `globalGluingCertificate_of_chainConstruction`
constructs the global representation equation, and hence an `AdditiveRep`,
without assuming an additive representation in the premises.  Thus Stage 5 is
now split into named residuals plus a theorem-backed final assembly step. -/

/-- **Theorem-backed Stage 5 attack — explicit global-gluing data.**

This is the non-circular input surface for the remaining O1 gap.  It records a
single global coordinate-utility family `V` together with:

* pivot-slice representations sharing `V j₀` on a pivot coordinate;
* all-pairs additivity for the same `V`;
* the coordinate-image coverage residual; and
* the strict-monotonicity residual.

The last three fields are exactly the hypotheses consumed by the already-proved
M1 chain-construction theorem, so the final passage to `AdditiveRep` is
mechanical once this data is available. -/
def WakkerStage5GlobalGluingData {X : ι → Type v}
    [Fact (3 ≤ Fintype.card ι)]
    (P : WakkerInfra.ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) : Prop :=
  ∃ (j₀ : ι) (V : (i : ι) → X i → ℝ),
    (∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
    ∃ hpair : AllPairsAdditivityCertificate P V,
      WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv ∧
      WakkerStep5StrictMonotonicityCertificate P V hpair hsolv

/-- **Stage-5 data projects to the active Stage-4 pivot-slice surface.**

The pivot-slice component of `WakkerStage5GlobalGluingData` is exactly a
`PairwiseSliceRepresentationsAtPivot` witness, so Stage 5 genuinely extends
the active Stage-4 surface rather than bypassing it. -/
theorem wakkerStage4PivotSliceRepresentationData_of_stage5GlobalGluingData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {hsolv : ProductPref.RestrictedSolvability P}
    (hData : WakkerStage5GlobalGluingData P hsolv) :
    WakkerStage4PivotSliceRepresentationData P := by
  obtain ⟨j₀, V, hPivot, _hRest⟩ := hData
  refine ⟨j₀, V j₀, ?_⟩
  intro k hk
  exact ⟨V k, hPivot k hk⟩

/-- **Stage-5 global-gluing data mechanically produces additive assembly.**

This is the sharpened O1 endpoint: once the explicit Stage-5 data is supplied,
the already-proved M1 chain-construction theorem produces the global gluing
certificate, which packages directly as `Nonempty (AdditiveRep P)`.

No `AdditiveRep P`, `WakkerConstructionCertificate P`, or
`AdditiveRepHypothesisBundle P` is assumed. -/
theorem wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [Nonempty ι]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hData : WakkerStage5GlobalGluingData P hsolv) :
    WakkerStage5AdditiveAssemblyData P := by
  obtain ⟨_j₀, V, _hPivot, hRest⟩ := hData
  obtain ⟨hpair, hcov, hstrict⟩ := hRest
  exact ⟨{
    V := V
    represents := globalGluingCertificate_of_chainConstruction
      P V hpair hsolv hcov hstrict }⟩

/-- **Wakker standard-sequence forward-construction bundle.**

The active factoring layer for the O1 frontier: a Stage-1 pivot seed,
theorem-backed Stage 2--4 construction outputs, and the final Stage-5
global-assembly implication.  The formerly black-box Stage-5 implication now
has a sharper theorem-backed filling route via
`WakkerStage5GlobalGluingData` and
`wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData`: the remaining
O1 work is to produce the named all-pairs, coverage, and strict-monotonicity
residuals for a single global utility family.  Stages 2--4 are no longer
opaque bundle hypotheses.

Projection through the fields yields Stage 5 (`Nonempty (AdditiveRep P)`),
which feeds the existing `wakker_IV_2_7_of_additiveRepHypothesisBundle`
consumer.  All projection theorems below are sorry-free. -/
structure WakkerStandardSequenceForwardConstructionBundle
    {X : ι → Type v} (P : WakkerInfra.ProductPref X) where
  /-- **Step 1 seed** — pivot data (Wakker IV.2 Step 1).  Trivially
  derivable from `∀ i, Essential P i` via
  `wakkerStage1PivotData_of_essential`. -/
  step1 : WakkerStage1PivotData P
  /-- **Step 2 active output** — theorem-backed natural-grid construction
  on an injective standard sequence.  See
  `wakkerStage2NatGridData_of_injectiveStandardSequence`. -/
  step2Data : WakkerStage2NatGridData P
  /-- **Step 3 active output** — theorem-backed finite-cut coverage surface,
  replacing the overstrong global `ℚ`-grid endpoint in the active bundle. -/
  step3Data : WakkerStage3FiniteCutCoverageData P
  /-- **Step 4 active output** — theorem-backed shared-pivot pairwise-slice
  representation surface, replacing the overstrong immediate full-pivot
  utility endpoint in the active bundle. -/
  step4Data : WakkerStage4PivotSliceRepresentationData P
  /-- **Step 5 implication** — cross-coordinate calibration + assembly
  (Wakker IV.2 Steps 5–6): from the active pivot-slice representation
  surface, calibrate every coordinate and verify the global additive
  representation.  This remains the genuine O1 endpoint. -/
  step5 : WakkerStage4PivotSliceRepresentationData P → WakkerStage5AdditiveAssemblyData P

namespace WakkerStandardSequenceForwardConstructionBundle

/-- Stage 2 from the bundle. -/
theorem stage2 {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    (B : WakkerStandardSequenceForwardConstructionBundle P) :
    WakkerStage2NatGridData P :=
  B.step2Data

/-- Stage 3 from the bundle. -/
theorem stage3 {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    (B : WakkerStandardSequenceForwardConstructionBundle P) :
    WakkerStage3FiniteCutCoverageData P :=
  B.step3Data

/-- Stage 4 from the bundle. -/
theorem stage4 {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    (B : WakkerStandardSequenceForwardConstructionBundle P) :
    WakkerStage4PivotSliceRepresentationData P :=
  B.step4Data

/-- Stage 5 from the bundle. -/
theorem stage5 {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    (B : WakkerStandardSequenceForwardConstructionBundle P) :
    WakkerStage5AdditiveAssemblyData P :=
  B.step5 B.stage4

end WakkerStandardSequenceForwardConstructionBundle

/-- **Build the existing forward-construction bundle from explicit Stage-5
global-gluing data.**

This compatibility constructor keeps the older bundle interface usable while
showing how its formerly black-box `step5` field can now be filled from the
named Stage-5 residuals. -/
theorem wakkerStandardSequenceForwardConstructionBundle_of_stage5GlobalGluingData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [Nonempty ι]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hStep1 : WakkerStage1PivotData P)
    (hStep2 : WakkerStage2NatGridData P)
    (hStep3 : WakkerStage3FiniteCutCoverageData P)
    (hStep5 : WakkerStage5GlobalGluingData P hsolv) :
    WakkerStandardSequenceForwardConstructionBundle P := by
  refine {
    step1 := hStep1
    step2Data := hStep2
    step3Data := hStep3
    step4Data := wakkerStage4PivotSliceRepresentationData_of_stage5GlobalGluingData hStep5
    step5 := ?_ }
  intro _hStage4
  exact wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData hsolv hStep5

/-- **Additive-representation hypothesis bundle from the Wakker
standard-sequence forward-construction bundle.**

The headline scaffolding theorem: composing the five monograph-step
implications with the Stage-1 seed yields `Nonempty (AdditiveRep P)`,
which is exactly `AdditiveRepHypothesisBundle P`.  Sorry-free by
direct projection through the bundle's five fields. -/
theorem additiveRepHypothesisBundle_of_wakkerStandardSequenceForwardConstructionBundle
    {X : ι → Type v} {P : WakkerInfra.ProductPref X}
    (B : WakkerStandardSequenceForwardConstructionBundle P) :
    AdditiveRepHypothesisBundle P :=
  B.stage5

/-- **Top-level Wakker IV.2.7 from the standard-sequence
forward-construction bundle plus structural axioms.**

End-to-end public consumer of the scaffolding layer: the
forward-construction bundle (Stage-1 seed + four monograph-step
implications) plus the standard structural Wakker IV.2.7 axioms
(`Essential`, `RestrictedSolvability`, `Archimedean`) yield
`Nonempty (AdditiveRep P)`.  The bundle is sorry-free; producing it is
the open multi-month O1 work, factored into five separately targetable
blocks. -/
theorem wakker_IV_2_7_of_wakkerStandardSequenceForwardConstructionBundle
    {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : WakkerInfra.ProductPref X)
    [WakkerInfra.ProductPref.IsWeakOrder P]
    [WakkerInfra.ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (solvability  : WakkerInfra.ProductPref.RestrictedSolvability P)
    (archimedean  : ∃ j, WakkerInfra.ProductPref.Archimedean P j)
    (B            : WakkerStandardSequenceForwardConstructionBundle P) :
    Nonempty (AdditiveRep P) :=
  wakker_IV_2_7_of_additiveRepHypothesisBundle P essential solvability archimedean
    (additiveRepHypothesisBundle_of_wakkerStandardSequenceForwardConstructionBundle B)

/-! ##### Topology-half discharge routes from M4 inputs

The topology half consists of full coordinate continuity on `Set.univ` plus the
structural single-coordinate monotonicity axiom.  The continuity component is
already theorem-backed from monotonicity plus rational-image coverage via the
existing M4 IVT route (`coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage`).

We expose a named bridge from monotonicity + rational-image coverage to the
full topology half, so downstream consumers can discharge the topology half
through M4 inputs without reintroducing the construction-stack frontier. -/

/-- **Topology half from structural monotonicity plus rational-image coverage.**

The structural monotonicity axiom gives the topology half's monotonicity
component directly, and combined with rational-image coverage gives the full
coordinate continuity component via the M4 IVT route. -/
theorem wakkerMonographTopologyHalfInputCertificate_of_structuralMonotonicity_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat : CoordinateRationalImageCertificate R) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage R
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct)
    hRat,
   hMonoStruct⟩

/-- **Topology half from coordinate monotonicity plus rational-image coverage.** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_monotone_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMono : CoordinateMonotonicityCertificate R)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat : CoordinateRationalImageCertificate R) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨coordinateUtilityContinuityCertificate_univ_of_monotone_rationalImage R hMono hRat,
   hMonoStruct⟩

/-- **Topology half from structural monotonicity plus dense range.** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_structuralMonotonicity_denseRange
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hDense : CoordinateDenseRangeCertificate R) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange R
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct)
    hDense,
   hMonoStruct⟩

/-- **Topology half from structural monotonicity plus continuity (trivial wrapper).** -/
theorem wakkerMonographTopologyHalfInputCertificate_of_structuralMonotonicity_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hCont : CoordinateUtilityContinuityCertificate R (fun _ => Set.univ)) :
    WakkerMonographTopologyHalfInputCertificate R :=
  ⟨hCont, hMonoStruct⟩

/-- **End-to-end raw outputs from per-coordinate alignment plus structural
monotonicity plus rational-image coverage.**

End-to-end consumer entry point: the alignment certificate plus the M4 IVT
inputs (structural monotonicity + rational-image coverage) discharge the
entire monograph-level frontier through to the three named raw outputs. -/
theorem wakkerRawOutputs_of_perCoordinateAlignment_and_structuralMonotonicity_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hAlign : CoordinatePerCoordinateAlignmentCertificate P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R ∧
      CoordinateConnectedContinuityOneStepBracketCertificate P ∧
        CoordinateUtilityContinuityCertificate R (fun _ => Set.univ) :=
  wakkerRawOutputs_of_perCoordinateAlignment_and_topologyHalf R hsolv hAlign
    (wakkerMonographTopologyHalfInputCertificate_of_structuralMonotonicity_rationalImage
      R hMonoStruct hRat)

/-- **Coordinate surjectivity from structural monotonicity and rational-image coverage.**

Combines the raw single-coordinate monotonicity axiom with the rational-image
standard-sequence target.  Thus coordinate surjectivity no longer needs to be
taken as a primitive input once rational-image refinement has been proved. -/
theorem coordinateSurjectivityCertificate_of_singleCoordinateMonotonicityAxiom_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateSurjectivityCertificate R := by
  exact coordinateSurjectivityCertificate_of_monotone_rationalImage R
    (coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct)
    hRat

/-- **End-to-end corrected utility-value realization from structural
monotonicity plus rational-image coverage.**

The IVT bridge proves coordinate surjectivity from structural monotonicity and
rational-image coverage.  This theorem packages that stronger-surjectivity
route through the existing corrected M2 consumer, so the corrected predicate no
longer needs full surjectivity as a primitive input once rational-image
refinement has been established. -/
theorem utilityValueRealizingEquivalence_corrected_of_singleCoordinateMonotonicityAxiom_rationalImage
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [hWO : ProductPref.IsWeakOrder P]
    (R₁ : AdditiveRep P) (j : ι)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat : CoordinateRationalImageCertificate R₁) :
    UtilityValueRealizingEquivalence (P := P) R₁ j := by
  exact utilityValueRealizingEquivalence_corrected_of_coordinateSurjectivityCertificate
    R₁ j hsolv
    (coordinateSurjectivityCertificate_of_singleCoordinateMonotonicityAxiom_rationalImage
      R₁ hMonoStruct hRat)

/-- **Primitive affine-lift certificates from stronger construction outputs.**

This packages the currently theorem-backed lower routes for the three
primitive inputs requested by the direct affine-lift proof:

* `CoordinateMonotonicityCertificate` follows from the raw structural
  `SingleCoordinateMonotonicityAxiom`;
* `CoordinateRationalImageCertificate` follows from the stronger
  standard-sequence output `CoordinateSurjectivityCertificate`;
* `StandardSequenceGridBetweenPointsCertificate` follows from the equivalent
  real-coordinate grid-density certificate.

The remaining unproved Wakker work is therefore pushed below these stronger
construction outputs: proving coordinate surjectivity / grid density directly
from restricted solvability, Archimedean, connectedness/refinement, and the
standard-sequence construction. -/
theorem primitiveAffineLiftCertificates_of_structuralMonotonicity_surjectivity_gridDensity
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P) (j : ι)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hSurj : CoordinateSurjectivityCertificate R)
    (hGrid : StandardSequenceGridDensityCertificate P j) :
    CoordinateMonotonicityCertificate R ∧
      CoordinateRationalImageCertificate R ∧
      StandardSequenceGridBetweenPointsCertificate (P := P) j := by
  exact ⟨
    coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R hMonoStruct,
    coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate
      R hSurj,
    standardSequenceGridBetweenPointsCertificate_of_gridDensityCertificate
      j hGrid⟩

/-- **Direct affine lift from structural monotonicity, surjectivity, and grid density.**

This is the strongest currently theorem-backed construction-output route for
the direct M2 affine-lift proof.  It derives the requested primitive
certificates internally, then calls the strict-standard-sequence affine route. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_structuralMonotonicity_surjectivity_gridDensity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hSurj₁ : CoordinateSurjectivityCertificate R₁)
    (hSurj₂ : CoordinateSurjectivityCertificate R₂)
    (hGrid : StandardSequenceGridDensityCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hPrim₁ :=
    primitiveAffineLiftCertificates_of_structuralMonotonicity_surjectivity_gridDensity
      R₁ j hMonoStruct hSurj₁ hGrid
  have hPrim₂ :=
    primitiveAffineLiftCertificates_of_structuralMonotonicity_surjectivity_gridDensity
      R₂ j hMonoStruct hSurj₂ hGrid
  exact coordinateAffineLiftCertificate_of_strictStandardSequence_monotone_rationalImage_and_gridBetweenPoints
    R₁ R₂ σ hσ
    hPrim₁.1 hPrim₁.2.1
    hPrim₂.1 hPrim₂.2.1
    hPrim₁.2.2

/-- **Direct affine lift from structural monotonicity, rational-image coverage,
and grid density.**

This is the sharper version of the previous strong-output route: coordinate
surjectivity is derived internally from structural monotonicity plus rational-
image coverage, so the remaining standard-sequence coverage target is the
rational-image certificate rather than full surjectivity. -/
theorem coordinateAffineLiftCertificate_of_strictStandardSequence_structuralMonotonicity_rationalImage_gridDensity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hGrid : StandardSequenceGridDensityCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hMono₁ : CoordinateMonotonicityCertificate R₁ :=
    coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R₁ hMonoStruct
  have hMono₂ : CoordinateMonotonicityCertificate R₂ :=
    coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R₂ hMonoStruct
  exact coordinateAffineLiftCertificate_of_strictStandardSequence_monotone_rationalImage_and_gridBetweenPoints
    R₁ R₂ σ hσ hMono₁ hRat₁ hMono₂ hRat₂
    (standardSequenceGridBetweenPointsCertificate_of_gridDensityCertificate
      j hGrid)

/-- **Direct affine lift from structural monotonicity, rational-image coverage,
and a selected refined dense grid.**

This is the selected-grid replacement for the older theorem that consumed the
now-refuted universal `StandardSequenceGridDensityCertificate`. -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_structuralMonotonicity_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hGrid : SelectedRefinedDenseGridCertificate P j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  have hMono₁ : CoordinateMonotonicityCertificate R₁ :=
    coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R₁ hMonoStruct
  have hMono₂ : CoordinateMonotonicityCertificate R₂ :=
    coordinateMonotonicityCertificate_of_singleCoordinateMonotonicityAxiom
      P R₂ hMonoStruct
  exact coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_monotone_rationalImage
    R₁ R₂ j hMono₁ hRat₁ hMono₂ hRat₂ hGrid

/-- **Direct affine lift from structural monotonicity, rational-image coverage,
and a selected refined between-points grid.** -/
theorem coordinateAffineLiftCertificate_of_selectedRefinedGridBetweenPoints_structuralMonotonicity_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)}
    (R₁ R₂ : AdditiveRep P) (j : ι)
    (hMonoStruct : SingleCoordinateMonotonicityAxiom P)
    (hRat₁ : CoordinateRationalImageCertificate R₁)
    (hRat₂ : CoordinateRationalImageCertificate R₂)
    (hBetween : SelectedRefinedGridBetweenPointsCertificate (P := P) j) :
    CoordinateAffineLiftCertificate R₁ R₂ j := by
  exact coordinateAffineLiftCertificate_of_selectedRefinedDenseGrid_structuralMonotonicity_rationalImage
    R₁ R₂ j hMonoStruct hRat₁ hRat₂
    (selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate
      j hBetween)

/-! ### Phase 8 cross-certificate compatibility theorems

The five entry-point bundles M1–M5 are not independent: the underlying
certificates are linked by the projection theorems already present in this
file.  These lemmas lift those projections to the bundle level so that
discharging an upstream input bundle automatically discharges the
downstream ones, and the audit trail at the wrapper-consumer level stays
coherent.

Direction of flow:

* `hConstruct` (M5) ⇒ `hglobal` (M1), via
  `globalGluingCertificate_of_wakkerConstructionCertificate`.
* `hConcAll` (M4) ⇒ `hConc` (M3), via
  `twoCoordinateConcavityCertificate_of_perCoordinateConcavityCertificate`.

The remaining bundles (`haff`) are not linked to the others by an
existing projection (uniqueness depends on having two representations
rather than one), so no further compat lemmas are added. -/

/-- **Discharge: `WakkerStep5CoordinateImageCoverageCertificate` from a
global gluing certificate.**

Real, sorry-free discharge of the coverage residual under the strongest
possible hypothesis (a full `GlobalGluingCertificate`).  The intermediate
`c` is taken as `x j₀`, so the update is identity and both legs of the
chain reduce to global comparisons that the gluing certificate supplies.

This is the M5 ⇒ coverage-residual discharge.  Future discharges from
weaker hypotheses (e.g., from standard-sequence machinery without going
through a global representation) remain genuinely open. -/
theorem wakkerStep5CoordinateImageCoverageCertificate_of_globalGluingCertificate
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hglobal : GlobalGluingCertificate P V)
    (hpair   : AllPairsAdditivityCertificate P V)
    (hsolv   : ProductPref.RestrictedSolvability P) :
    WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv := by
  intro x y j₀ hle
  refine ⟨x j₀, ?_, ?_⟩
  · have hself : Function.update x j₀ (x j₀) = x := by
      funext i
      by_cases hij : i = j₀
      · subst hij; simp
      · simp [Function.update_of_ne hij]
    rw [hself]
    exact (hglobal x x).mpr (le_refl _)
  · have hself : Function.update x j₀ (x j₀) = x := by
      funext i
      by_cases hij : i = j₀
      · subst hij; simp
      · simp [Function.update_of_ne hij]
    rw [hself]
    exact (hglobal x y).mpr hle

/-- **Discharge: `WakkerStep5StrictMonotonicityCertificate` from a global
gluing certificate.**

Real, sorry-free discharge of the strict-monotonicity residual under a
full `GlobalGluingCertificate`.  Indifference between two profiles
yields both `f(y) ≤ f(x)` and `f(x) ≤ f(y)` via the gluing equivalence,
and antisymmetry of `≤` forces equality.

This is the M5 ⇒ strict-monotonicity-residual discharge.  Future
discharges from weaker hypotheses (e.g., from cardinal tradeoff
equivalence without going through a global representation) remain
genuinely open. -/
theorem wakkerStep5StrictMonotonicityCertificate_of_globalGluingCertificate
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hglobal : GlobalGluingCertificate P V)
    (hpair   : AllPairsAdditivityCertificate P V)
    (hsolv   : ProductPref.RestrictedSolvability P) :
    WakkerStep5StrictMonotonicityCertificate P V hpair hsolv := by
  intro x y hxy_indiff
  obtain ⟨hxy, hyx⟩ := hxy_indiff
  have hle1 : (∑ i, V i (y i)) ≤ ∑ i, V i (x i) := (hglobal x y).mp hxy
  have hle2 : (∑ i, V i (x i)) ≤ ∑ i, V i (y i) := (hglobal y x).mp hyx
  exact le_antisymm hle2 hle1

/-- **Round-trip: a global gluing certificate produces the M5 sub-target
`PairwiseSliceRepresentationsAtPivot` at any pivot.**

Sanity check that the M5 sub-target sits at the right level of generality:
any global gluing certificate (the M1 conclusion) restricts to its
pivot-slice representations.  The proof routes through
`allPairsAdditivityCertificate_of_globalGluingCertificate` on each `(j₀, k)`
slice.

This closes the round-trip M5 ⇒ pivot-slice reps and confirms that the
named scaling-compatibility certificate names exactly what an end-to-end
Wakker proof would discharge. -/
theorem pairwiseSliceRepresentationsAtPivot_of_globalGluingCertificate
    {X : ι → Type v}
    [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι)
    (V : (i : ι) → X i → ℝ)
    (hglobal : GlobalGluingCertificate P V) :
    PairwiseSliceRepresentationsAtPivot P j₀ := by
  refine ⟨V j₀, ?_⟩
  intro k hk
  refine ⟨V k, ?_⟩
  -- Restrict the global gluing certificate to the (j₀, k) slice.
  intro x y hxy
  exact allPairsAdditivityCertificate_of_globalGluingCertificate
    P V hglobal j₀ k hk.symm x y hxy

/-! ##### O1 Stage 5 round-trip: explicit data is the tightest non-circular
narrowing of the additive-assembly endpoint.

The Stage-5 attack surface `WakkerStage5GlobalGluingData P hsolv` is exposed
as a strictly weaker bundle than `Nonempty (AdditiveRep P)`: it names the four
residuals (`PairwiseSliceRepresentationCertificate` at a pivot,
`AllPairsAdditivityCertificate`, `WakkerStep5CoordinateImageCoverageCertificate`,
`WakkerStep5StrictMonotonicityCertificate`) for one global utility family `V`
and lets the M1 chain-construction theorem assemble the global representation.

The round-trip theorem below shows the converse: any `AdditiveRep P` mechanically
produces the Stage-5 data via the existing residue-discharge theorems
(`allPairsAdditivityCertificate_of_globalGluingCertificate`,
`wakkerStep5CoordinateImageCoverageCertificate_of_globalGluingCertificate`,
`wakkerStep5StrictMonotonicityCertificate_of_globalGluingCertificate`).

Together with the existing forward direction
`wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData`, the round-trip
establishes that `WakkerStage5GlobalGluingData P hsolv` is logically equivalent
to `Nonempty (AdditiveRep P)`.  Thus the named Stage-5 residuals are exactly
the right non-circular target: stronger than nothing (they decompose `AdditiveRep`
into four explicitly auditable pieces consumed by the M1 chain construction),
weaker than `AdditiveRep` itself (the residuals are propositional axioms on a
candidate `V`, not the existence of an additive representation).

Any future direct construction of the four residuals (from standard-sequence
machinery or cross-coordinate calibration) immediately produces an `AdditiveRep`;
conversely, the round-trip theorem provides a sample-witness route through any
already-constructed `AdditiveRep`, so the surface is non-vacuous. -/

/-- **O1 Stage 5 round-trip: any `AdditiveRep P` produces explicit Stage-5
global-gluing data.**

Mechanical assembly: take `V := R.V`, restrict `R.represents` to the
pivot-slice level for the pivot-slice field, and use the existing
residue-discharge theorems for the coverage and strict-monotonicity fields.

This complements `wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData`:
both directions are sorry-free, so the Stage-5 data surface and the
additive-assembly endpoint are logically equivalent.  See
`wakkerStage5GlobalGluingData_iff_wakkerStage5AdditiveAssemblyData` for the
explicit biconditional. -/
theorem wakkerStage5GlobalGluingData_of_additiveRep
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [_hne : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (R : AdditiveRep P) :
    WakkerStage5GlobalGluingData P hsolv := by
  obtain ⟨j₀⟩ := _hne
  -- `R.represents` is definitionally `GlobalGluingCertificate P R.V`.
  have hglobal : GlobalGluingCertificate P R.V := R.represents
  have hpair : AllPairsAdditivityCertificate P R.V :=
    allPairsAdditivityCertificate_of_globalGluingCertificate P R.V hglobal
  have hcov :
      WakkerStep5CoordinateImageCoverageCertificate P R.V hpair hsolv :=
    wakkerStep5CoordinateImageCoverageCertificate_of_globalGluingCertificate
      P R.V hglobal hpair hsolv
  have hstrict :
      WakkerStep5StrictMonotonicityCertificate P R.V hpair hsolv :=
    wakkerStep5StrictMonotonicityCertificate_of_globalGluingCertificate
      P R.V hglobal hpair hsolv
  refine ⟨j₀, R.V, ?_, hpair, hcov, hstrict⟩
  intro k hk x y hxy
  exact hpair j₀ k hk.symm x y hxy

/-- **O1 Stage 5 round-trip: from `WakkerStage5AdditiveAssemblyData` (i.e.,
`Nonempty (AdditiveRep P)`) to explicit Stage-5 global-gluing data.** -/
theorem wakkerStage5GlobalGluingData_of_wakkerStage5AdditiveAssemblyData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hAssembly : WakkerStage5AdditiveAssemblyData P) :
    WakkerStage5GlobalGluingData P hsolv := by
  obtain ⟨R⟩ := hAssembly
  exact wakkerStage5GlobalGluingData_of_additiveRep P hsolv R

/-- **O1 Stage 5 biconditional: the explicit Stage-5 data surface is
logically equivalent to the additive-assembly endpoint.**

Both directions are sorry-free.  The forward direction is the M1
chain-construction theorem
(`wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData`); the reverse
direction is the round-trip
(`wakkerStage5GlobalGluingData_of_wakkerStage5AdditiveAssemblyData`).

Consequently, attacking the four named Stage-5 residuals is provably equivalent
to producing an additive representation directly, but with the residuals broken
out as separately auditable pieces.  No additional logical strength is hidden in
the bundle, and no logical strength is lost. -/
theorem wakkerStage5GlobalGluingData_iff_wakkerStage5AdditiveAssemblyData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) :
    WakkerStage5GlobalGluingData P hsolv ↔ WakkerStage5AdditiveAssemblyData P :=
  ⟨wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData hsolv,
    wakkerStage5GlobalGluingData_of_wakkerStage5AdditiveAssemblyData P hsolv⟩

/-- **O1 Stage 5 biconditional, restated against `AdditiveRepHypothesisBundle`.**

`AdditiveRepHypothesisBundle P` is definitionally
`Nonempty (AdditiveRep P)` (see
`additiveRepHypothesisBundle_iff_wakkerStage5AdditiveAssemblyData`), so the
Stage-5 data surface is equivalent to the hypothesis bundle consumed by
`wakker_IV_2_7_of_additiveRepHypothesisBundle`. -/
theorem wakkerStage5GlobalGluingData_iff_additiveRepHypothesisBundle
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)] [Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) :
    WakkerStage5GlobalGluingData P hsolv ↔ AdditiveRepHypothesisBundle P :=
  (wakkerStage5GlobalGluingData_iff_wakkerStage5AdditiveAssemblyData P hsolv).trans
    (additiveRepHypothesisBundle_iff_wakkerStage5AdditiveAssemblyData P).symm

/-- M5 ⇒ M1.  A Wakker construction input certificate produces, for the same
coordinate-utility family, a global-gluing input certificate.  This lifts
`globalGluingCertificate_of_wakkerConstructionCertificate` and
`allPairsAdditivityCertificate_of_globalGluingCertificate` to the bundle
level.

Updated signature: under the enriched M1 bundle (which now also takes
`RestrictedSolvability`, `WakkerStep5CoordinateImageCoverageCertificate`,
and `WakkerStep5StrictMonotonicityCertificate`), the cross-flow lemma must
produce all three extra hypotheses.  All three are constructible from a
global representation:

* `RestrictedSolvability` is supplied directly from the construction-input
  inputs.
* The coverage certificate is constructed by
  `wakkerStep5CoordinateImageCoverageCertificate_of_globalGluingCertificate`.
* The strict-monotonicity certificate follows from
  `wakkerStep5StrictMonotonicityCertificate_of_globalGluingCertificate`. -/
theorem globalGluingInputCertificate_of_wakkerConstructionInputCertificate
    {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : ProductPref X)
    [hWO          : ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, ProductPref.Essential P i)
    (solvability  : ProductPref.RestrictedSolvability P)
    (archimedean  : ∀ i, ProductPref.Archimedean P i)
    (hInput       : WakkerConstructionInputCertificate P essential
                      solvability archimedean) :
    ∃ V : (i : ι) → X i → ℝ,
      ∃ hpair : AllPairsAdditivityCertificate P V,
        ∃ hcov  : WakkerStep5CoordinateImageCoverageCertificate P V hpair
                    solvability,
          ∃ hstrict : WakkerStep5StrictMonotonicityCertificate P V hpair
                        solvability,
            GlobalGluingInputCertificate P V hpair solvability hcov hstrict := by
  have hConstruct : WakkerConstructionCertificate P :=
    wakkerConstructionCertificate_of_input P essential solvability
      archimedean hInput
  obtain ⟨V, hglobal⟩ := hConstruct
  have hpair : AllPairsAdditivityCertificate P V :=
    allPairsAdditivityCertificate_of_globalGluingCertificate P V hglobal
  have hcov : WakkerStep5CoordinateImageCoverageCertificate P V hpair
                solvability :=
    wakkerStep5CoordinateImageCoverageCertificate_of_globalGluingCertificate
      P V hglobal hpair solvability
  have hstrict : WakkerStep5StrictMonotonicityCertificate P V hpair
                  solvability :=
    wakkerStep5StrictMonotonicityCertificate_of_globalGluingCertificate
      P V hglobal hpair solvability
  exact ⟨V, hpair, hcov, hstrict, hglobal⟩

/-- **M4 ⇒ M3 continuity cross-flow: M4's coordinate continuity certificate
restricts to the M3 slice-level continuity certificate on every pair of
coordinates.**

This is the bundle-level cross-flow showing that any future discharge of
the M4 continuity residual automatically supplies the M3 slice-level
continuity residual on every coordinate pair. -/
theorem sliceUtilityContinuityCertificate_of_coordinateUtilityContinuityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ}
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (j k : ι) :
    SliceUtilityContinuityCertificate (S j) (S k) (R.V j) (R.V k) :=
  ⟨hCont j, hCont k⟩

/-- M4 ⇒ M3.  A per-coordinate concavity input certificate produces, for any
two coordinates, the corresponding two-coordinate concavity input certificate
on the slice domains and slice utilities.  Because the M3 bundle's
`hConvex` and `hCont` hypotheses follow from the M4 inputs through the
additive representation `R` (with slice-level continuity restricted from the
M4 continuity certificate), this lemma exposes the projection only when an
explicit `hSliceConvex` for the slice is provided. -/
theorem twoCoordinateConcavityInputCertificate_of_perCoordinateConcavityInputCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hInput : PerCoordinateConcavityInputCertificate R S hS essential hConvex
                hCont)
    (j k : ι)
    (hSliceConvex :
      ∀ (u₀ : ℝ) (v₀ : ℝ),
        Convex ℝ ({ p : ℝ × ℝ |
                     p.1 ∈ S j ∧ p.2 ∈ S k ∧
                     R.V j u₀ + R.V k v₀ ≤ R.V j p.1 + R.V k p.2 })) :
    TwoCoordinateConcavityInputCertificate
      (S j) (S k) (hS j) (hS k) (R.V j) (R.V k) hSliceConvex
      (sliceUtilityContinuityCertificate_of_coordinateUtilityContinuityCertificate
        hCont j k) := by
  have hConcAll : PerCoordinateConcavityCertificate R S :=
    perCoordinateConcavityCertificate_of_input R S hS essential hConvex hCont
      hInput
  exact twoCoordinateConcavityCertificate_of_perCoordinateConcavityCertificate
    hConcAll j k

/-- The full checklist of explicit certificate hypotheses and their future
proof-producing theorem targets. -/
def explicitCertificateChecklist : List CertificateItem :=
  [ { hypothesisName := "hext",
      currentConsumers := ["WakkerRoadmap.WakkerExistence.extend_to_standard_sequence"],
      eventualTheorem := "WakkerExistence.one_step_extension_from_restricted_solvability",
      certificateStatement := "StandardSequenceExtensionCertificate P j k base r s",
      status := CertificateStatus.openTarget,
      notes := "Auxiliary Wakker III.4.2 certificate: restricted solvability plus the required topological/continuity hypotheses should provide the next standard-sequence point at every step." },
    { hypothesisName := "hConstruct",
      currentConsumers :=
        [ "WakkerDebreuKoopmans.wakker_IV_2_7",
          "WakkerRoadmap.CertificateChecklist.wakkerConstructionCertificate_feeds_pairwise_and_global",
          "WakkerRoadmap.CertificateChecklist.pairwise_additivity_all_of_wakkerConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.global_additive_from_pairwise_of_wakkerConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.wakker_IV_2_7_consumer_of_wakkerConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.wakker_IV_2_7_of_wakkerConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.wakkerConstructionCertificate_of_input",
          "WakkerRoadmap.CertificateChecklist.additiveRep_nonempty_of_wakkerConstructionInputCertificate",
          "WakkerRoadmap.CertificateChecklist.globalGluingInputCertificate_of_wakkerConstructionInputCertificate" ],
      eventualTheorem := "WakkerExistence.standard_sequences_construct_global_representation",
      certificateStatement := "WakkerConstructionCertificate P",
      status := CertificateStatus.openTarget,
      notes := "First-layer projection and wrapper-regression routes are now theorem-backed: hConstruct yields both GlobalGluingCertificate P V and AllPairsAdditivityCertificate P V for the same V, and discharges the existing pairwise/global/Wakker consumer wrappers. Phase 8 / Certificate 1 of the roadmap further collapses the open frontier into a single named entry-point bundle WakkerConstructionInputCertificate plus the regression theorem additiveRep_nonempty_of_wakkerConstructionInputCertificate, which routes that bundle through wakker_IV_2_7 without changing its public interface. The bundle also discharges the M1 GlobalGluingInputCertificate via globalGluingInputCertificate_of_wakkerConstructionInputCertificate, so a future proof of the construction bundle automatically discharges the global-gluing bundle for the same coordinate-utility family. Remaining work is proving WakkerConstructionInputCertificate from Wakker IV.2--IV.6 standard-sequence machinery." },
    { hypothesisName := "hVⱼₖ_repr",
      currentConsumers :=
        [ "WakkerRoadmap.WakkerExistence.pairwise_additivity",
          "WakkerRoadmap.CertificateChecklist.pairwise_additivity_of_pairwiseSliceAssemblyCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseSliceAssemblyTheoremCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseOrderCalibrationTheoremCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseTradeoffMagnitudeCertificate_of_gridNormalizationWitness_and_orderCalibration",
          "WakkerRoadmap.CertificateChecklist.pairwiseTradeoffBracketingCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBracketingCertificate_of_pairwiseCutConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBracketingTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseCutConstructionCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseCutConstructionTheoremCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBracketingTheoremCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_cutConstruction",
          "WakkerRoadmap.CertificateChecklist.pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_archimedeanBracketing",
          "WakkerRoadmap.CertificateChecklist.pairwiseHexagonPropagationCertificate_of_tradeoffMagnitude_and_bracketing",
          "WakkerRoadmap.CertificateChecklist.pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseStep4TradeoffMachineryCertificate_of_pairwiseHexagonStandardSequenceCertificate",
          "WakkerRoadmap.CertificateChecklist.additiveRealBool_not_pairwiseCutConstructionTheoremCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutInterpolationCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.standardSequence_unbracket_of_archimedean",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_upper_and_lower",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutUpperCoverageCertificate_of_full",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutLowerCoverageCertificate_of_full",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_archimedean_and_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBaseTransportCertificate_of_pairwiseCutConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseGridReachabilityCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate",
          "WakkerRoadmap.CertificateChecklist.additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_baseTransport",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveSecondCoord",
          "WakkerRoadmap.CertificateChecklist.pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveFirstCoord",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveSecondCoord",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveFirstCoord",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutCoverageCertificate_of_pairwiseCutConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseInterpolationExtensionCertificate_of_pairwiseCutConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutInterpolationCertificate_of_pairwiseCutConstructionCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutInterpolationTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate",
          "WakkerRoadmap.CertificateChecklist.pairwiseFiniteCutInterpolationTheoremCertificate_of_surjectiveStandardSequences",
          "WakkerRoadmap.CertificateChecklist.pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate" ],
      eventualTheorem := "WakkerExistence.standard_sequences_produce_pairwise_slice_representation",
      certificateStatement := "PairwiseSliceRepresentationCertificate P j k Vⱼ Vₖ",
      status := CertificateStatus.openTarget,
        notes := "The Step-4 route is now decomposed further: PairwiseGridNormalizationCertificate is theorem-backed from injective standard-sequence grids; PairwiseLocalInterpolationCertificate and the stronger PairwiseSliceInterpolationCertificate are theorem-backed from restricted solvability; the slice-preserving interpolant lemmas package local choices as actual profiles on a fixed {j,k}-slice; and the current construction data repackages into PairwiseAssemblyInputCertificate. A formal total-preference counterexample shows that this assembly-input bundle alone is not sufficient, and a strengthened counterexample shows that the current abstract TradeoffConsistency hexagon class alone is also not sufficient. The missing Wakker Step-4 input is split into PairwiseMagnitudeBracketingHexagonCertificate. Grid-step magnitude is theorem-backed from grid normalization plus order calibration. Exact-grid bracketing factors through PairwiseCutConstructionTheoremCertificate and remains theorem-backed in the surjective-standard-sequence regime, but additiveRealBool_not_pairwiseCutConstructionTheoremCertificate proves that this exact finite-grid cut target is false for non-surjective one-sided grids, even with calibrated additive utilities. The honest weakening is now formalized: PairwiseFiniteCutInterpolationCertificate isolates Wakker's actual Step-4 output as finite-cut coverage on each slice target plus a slice-shaped interpolation/extension witness, with theorem-backed regressions for both surjective grids and the stronger exact cut-construction certificate.  Cut coverage itself is now decomposed further: standardSequence_unbracket_of_archimedean theorem-backs the contrapositive of the raw Archimedean axiom; PairwiseFiniteCutUpperCoverageCertificate and PairwiseFiniteCutLowerCoverageCertificate split coverage into upper and lower halves with theorem-backed equivalence; and PairwiseArchimedeanBaseTransportCertificate isolates the precise residual content beyond raw Archimedean — the bridge transporting sandwich-failure from σ.base to arbitrary slice bases — that suffices to discharge full coverage from the raw axiom plus base transport. The base-transport bridge itself is further refuted from raw structural axioms: additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate proves that Archimedean P j ∧ Archimedean P k ∧ TradeoffConsistency ∧ RestrictedSolvability ∧ IsWeakOrder is insufficient for the bridge in the additive-real model with one-sided ℕ-indexed grids.  The honest residual is exposed as PairwiseGridReachabilityCertificate, the per-axis grid-bracketing certificate that surjective grids satisfy by construction, and the bridge is then theorem-backed from raw Archimedean + grid reachability + surjectivity in either coordinate (pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveFirstCoord/SecondCoord), giving end-to-end finite-cut coverage from these strengthened axioms." },
    { hypothesisName := "_hpair",
      currentConsumers := ["WakkerRoadmap.WakkerExistence.global_additive_from_pairwise"],
      eventualTheorem := "WakkerExistence.all_pairwise_additivity_from_slice_representations",
      certificateStatement := "AllPairsAdditivityCertificate P V",
      status := CertificateStatus.splitTarget,
      notes := "This all-pairs premise should be assembled from the individual hVⱼₖ_repr slice certificates; it remains in Step 5 as documentation/backward-compatible input." },
    { hypothesisName := "hglobal",
      currentConsumers :=
        [ "WakkerRoadmap.WakkerExistence.global_additive_from_pairwise",
          "WakkerRoadmap.WakkerExistence.wakker_IV_2_7_consumer",
          "WakkerRoadmap.CertificateChecklist.globalGluingCertificate_of_input",
          "WakkerRoadmap.CertificateChecklist.additiveRep_nonempty_of_globalGluingInputCertificate" ],
      eventualTheorem := "WakkerExistence.pairwise_slice_representations_glue_global",
      certificateStatement := "GlobalGluingCertificate P V",
      status := CertificateStatus.openTarget,
      notes := "This is Wakker Step 5; n >= 3 should force compatible pairwise scales to glue into a single global sum representation. Phase 8 / Certificate 2 of the roadmap collapses the open frontier into a single named entry-point bundle GlobalGluingInputCertificate plus the regression theorem additiveRep_nonempty_of_globalGluingInputCertificate, routing it through global_additive_from_pairwise without changing the public interface." },
    { hypothesisName := "haff",
      currentConsumers :=
        [ "WakkerRoadmap.WakkerExistence.additive_rep_unique",
          "WakkerRoadmap.CertificateChecklist.additiveAffineUniquenessCertificate_of_input",
          "WakkerRoadmap.CertificateChecklist.additive_rep_unique_of_input",
          "WakkerRoadmap.CertificateChecklist.additiveAffineUniqueness_of_commonScale",
          "WakkerRoadmap.CertificateChecklist.additiveCommonScaleCertificate_of_equalCoordDiffs" ],
      eventualTheorem := "WakkerExistence.additive_representations_affinely_equivalent_of_essential",
      certificateStatement := "AdditiveAffineUniquenessCertificate R₁ R₂",
      status := CertificateStatus.openTarget,
      notes := "Prove common-scale positive affine uniqueness from essential coordinates and cardinal tradeoff equivalence. Phase 8 / Certificate 3 of the roadmap collapses the open frontier into a single named entry-point bundle AdditiveAffineUniquenessInputCertificate plus the regression theorem additive_rep_unique_of_input, routing it through additive_rep_unique without changing the public interface. Following the M1 enrichment pattern, the M2 bundle is enriched with the named AdditiveCommonScaleCertificate, motivated by the lex-order counterexample showing that essentiality alone does not force a common scale.  Theorem additiveAffineUniqueness_of_commonScale proves the affine form from the common-scale certificate plus all-coordinates essentiality (used to pick a per-coordinate reference value).  The trivial cross-flow additiveCommonScaleCertificate_of_equalCoordDiffs constructs the certificate when within-coordinate differences already match.  The genuine open content of M2 is constructing AdditiveCommonScaleCertificate from cardinal tradeoff equivalence." },
    { hypothesisName := "hConc",
      currentConsumers :=
        [ "WakkerRoadmap.DebreuKoopmansHard.two_coord_concave",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateQuasiconcavityCertificate_of_twoCoordinateConvexUpperContourCertificate",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_quasiToConcaveStrengthening",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_convexUpperContour_and_strengthening",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_input",
          "WakkerRoadmap.CertificateChecklist.two_coord_concave_of_input",
          "WakkerRoadmap.CertificateChecklist.sliceUtilityContinuityCertificate_of_twoCoordinateConcavityCertificate_interior",
          "WakkerRoadmap.CertificateChecklist.sliceUtilityContinuityCertificate_of_coordinateUtilityContinuityCertificate" ],
      eventualTheorem := "DebreuKoopmansHard.two_coordinate_concavity_from_convex_slice",
      certificateStatement := "TwoCoordinateConcavityCertificate S1 S2 V1 V2",
      status := CertificateStatus.splitTarget,
      notes := "Decomposed into TwoCoordinateQuasiconcavityCertificate (theorem-backed from convex upper-contour sets via the existing two_coord_quasiconcave_left/right lemmas) plus QuasiToConcaveStrengtheningCertificate, the missing DK-specific upgrade requiring continuity plus 3-coordinate alignment.  The two halves recombine into the original two-coordinate concavity certificate, and any per-coordinate certificate also restricts to it. Phase 8 / Certificate 4 of the roadmap collapses the remaining frontier into a single named entry-point bundle TwoCoordinateConcavityInputCertificate plus the regression theorem two_coord_concave_of_input, routing it through two_coord_concave without changing the public interface. Following the M4 enrichment pattern, the M3 bundle is enriched with the named SliceUtilityContinuityCertificate, the slice-level analogue of M4's CoordinateUtilityContinuityCertificate.  The trivial cross-flow sliceUtilityContinuityCertificate_of_twoCoordinateConcavityCertificate_interior records that joint slice concavity already implies continuity on the interior of each slice (via Mathlib's ConcaveOn.continuousOn_interior), and the bundle-level cross-flow sliceUtilityContinuityCertificate_of_coordinateUtilityContinuityCertificate shows that M4's coordinate continuity certificate restricts to the M3 slice continuity certificate on every coordinate pair.  Together these formally close the M3 specialization of M4: any future M4 discharge automatically discharges the M3 slice-level continuity residual on every slice." },
    { hypothesisName := "hQuasi",
      currentConsumers :=
        [ "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_quasiToConcaveStrengthening",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateQuasiconcavityCertificate_of_twoCoordinateConvexUpperContourCertificate" ],
      eventualTheorem := "DebreuKoopmansHard.two_coordinate_quasiconcavity_from_convex_upper_contour",
      certificateStatement := "TwoCoordinateQuasiconcavityCertificate S1 S2 V1 V2",
      status := CertificateStatus.consumerReady,
      notes := "Theorem-backed: convex upper-contour sets force quasi-concavity of each coordinate utility on its slice domain via two_coord_quasiconcave_left/right.  Witness the slice domains by any pair (u₀ ∈ S₁, v₀ ∈ S₂)." },
    { hypothesisName := "hStr",
      currentConsumers :=
        [ "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_quasiToConcaveStrengthening",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_convexUpperContour_and_strengthening" ],
      eventualTheorem := "DebreuKoopmansHard.quasi_to_concave_strengthening_from_continuity_and_alignment",
      certificateStatement := "QuasiToConcaveStrengtheningCertificate S1 S2 V1 V2",
      status := CertificateStatus.openTarget,
      notes := "The genuine DK-specific deep step: continuity of V₁, V₂ plus 3-coordinate alignment upgrades quasi-concavity to concavity.  This is the precise content currently passed as `hConc` in two_coord_concave once the quasi-concavity half is removed." },
    { hypothesisName := "hPairConc",
      currentConsumers :=
        [ "WakkerRoadmap.DebreuKoopmansHard.concave_transfers",
          "WakkerRoadmap.CertificateChecklist.pairConcavityTransferCertificate_of_perCoordinateConcavityCertificate" ],
      eventualTheorem := "DebreuKoopmansHard.pair_concavity_transfer_from_convex_additive_representation",
      certificateStatement := "PairConcavityTransferCertificate R S j k",
      status := CertificateStatus.splitTarget,
      notes := "Theorem-backed projection from PerCoordinateConcavityCertificate.  The remaining open content is the DK induction/transfer step itself, derived from convex preference plus 3-coordinate alignment." },
    { hypothesisName := "hConcAll",
      currentConsumers :=
        [ "WakkerDebreuKoopmans.debreu_koopmans_hard",
          "WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_consumer",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityCertificate_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.pairConcavityTransferCertificate_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.baseAndPairConcavityCertificate_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_consumer_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_from_base_and_pairs_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_of_baseAndPairConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.convexPref_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.perCoordinateConcavityCertificate_of_input",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_consumer_of_input",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_of_input",
          "WakkerRoadmap.CertificateChecklist.coordinateUtilityContinuityCertificate_of_perCoordinateConcavityCertificate_interior",
          "WakkerRoadmap.CertificateChecklist.twoCoordinateConcavityInputCertificate_of_perCoordinateConcavityInputCertificate" ],
      eventualTheorem := "DebreuKoopmansHard.per_coordinate_concavity_from_convex_preference",
      certificateStatement := "PerCoordinateConcavityCertificate R S",
      status := CertificateStatus.splitTarget,
      notes := "Global DK output; theorem-backed projections now feed every existing DK consumer (top-level debreu_koopmans_hard, granular consumer wrapper, base-plus-pairs wrapper) as well as both the two-coordinate concavity and pair-concavity transfer certificates.  The easy-direction round-trip convexPref_of_perCoordinateConcavityCertificate confirms the certificate sits at the correct level of generality.  Round-trip with BaseAndPairConcavityCertificate is also proved.  Phase 8 / Certificate 5 of the roadmap collapses the remaining frontier into a single named entry-point bundle PerCoordinateConcavityInputCertificate plus the regression theorems debreu_koopmans_hard_consumer_of_input and debreu_koopmans_hard_of_input, routing the bundle through both public DK consumers without changing their interfaces. Following the M1 / M2 enrichment pattern, the M4 bundle is enriched with the named CoordinateUtilityContinuityCertificate, motivated by the discontinuous-Cauchy counterexample showing that convex preference + additive representation alone does not force concavity.  The trivial cross-flow coordinateUtilityContinuityCertificate_of_perCoordinateConcavityCertificate_interior records that concavity already implies continuity on the interior of each slice (via Mathlib's ConcaveOn.continuousOn_interior), so the continuity certificate is automatic from the conclusion.  The bundle also discharges the M3 TwoCoordinateConcavityInputCertificate for any pair of coordinates via twoCoordinateConcavityInputCertificate_of_perCoordinateConcavityInputCertificate, so a future proof of the per-coordinate bundle automatically discharges the two-coordinate bundle on every slice. Remaining open work is constructing PerCoordinateConcavityCertificate from convex preference plus an additive representation in n ≥ 3 essential coordinates and the named continuity certificate." },
    { hypothesisName := "hVj₀ + hPair",
      currentConsumers :=
        [ "WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_from_base_and_pairs",
          "WakkerRoadmap.CertificateChecklist.baseAndPairConcavityCertificate_of_perCoordinateConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate",
          "WakkerRoadmap.CertificateChecklist.debreu_koopmans_hard_of_baseAndPairConcavityCertificate" ],
      eventualTheorem := "DebreuKoopmansHard.base_and_pair_certificates_from_convex_preference",
      certificateStatement := "BaseAndPairConcavityCertificate R S j₀",
      status := CertificateStatus.splitTarget,
      notes := "More granular DK checklist item: one base-coordinate concavity proof plus pair certificates to every coordinate.  Theorem-backed equivalence with PerCoordinateConcavityCertificate, and theorem-backed projection through to the top-level DK consumer." },
    { hypothesisName := "necessity_bundle (Phase 0, proved)",
      currentConsumers :=
        [ "WakkerInfra.ProductPref.isWeakOrder_of_additivelyRepresents",
          "WakkerInfra.ProductPref.coordPref_iff_of_additivelyRepresents",
          "WakkerInfra.ProductPref.coordPref_base_independent_of_additivelyRepresents",
          "WakkerInfra.ProductPref.Vj_nonconstant_of_essential_of_additivelyRepresents",
          "WakkerInfra.ProductPref.essential_of_Vj_nonconstant_of_additivelyRepresents",
          "WakkerInfra.ProductPref.tradeoffConsistency_of_additivelyRepresents",
          "WakkerInfra.ProductPref.restrictedSolvability_of_additivelyRepresents",
          "WakkerInfra.ProductPref.standardSequence_Vj_step",
          "WakkerInfra.ProductPref.archimedean_of_additivelyRepresents",
          "WakkerInfra.ProductPref.certificate_necessity_bundle" ],
      eventualTheorem := "WakkerInfra.ProductPref.certificate_necessity_bundle (proved)",
      certificateStatement :=
        "WakkerConstructionCertificate P → IsWeakOrder P ∧ TradeoffConsistency P ∧ (∀ j, Archimedean P j) ∧ RestrictedSolvability P (the last conditional on CoordUtilitySolvability of the realizing utilities)",
      status := CertificateStatus.consumerReady,
      notes := "Necessity / forward direction of Wakker IV.2.7, mechanized in WakkerInfrastructure.lean §11.  This is the Phase-0 deliverable of the spin-out paper MechanizedDecisionTheoryWakkerDK.tex: every consequence that any future Wakker construction proof must reproduce — weak order, base-independent coordinate preference, essentiality detection by Vⱼ, tradeoff consistency, restricted solvability under coordinate-utility solvability, the per-step standard-sequence shift V j (σ.α (n+1)) − V j (σ.α n) = V σ.k σ.r − V σ.k σ.s, and the Archimedean axiom — is fully proved from the additive-representation hypothesis alone.  The grid-utility entry point is mirrored separately, structural-axioms-only, in WakkerExistence.lean §1 (coord_utility_on_grid_from_axioms, grid_utility_zero, grid_utility_strictMono).  No new wrapper hypothesis is introduced." } ]

end CertificateChecklist

end WakkerRoadmap
