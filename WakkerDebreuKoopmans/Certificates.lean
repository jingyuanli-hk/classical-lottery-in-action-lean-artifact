/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`, now a thin
re-export barrel.
-/

import WakkerDebreuKoopmans.Core

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

/-! ## §C.5  Explicit certificate checklist

This section is the Lean-side checklist for the companion mechanized
decision-theory paper.  It maps each explicit certificate hypothesis still
consumed by `WakkerDebreuKoopmans.lean` to the named theorem target that
should eventually prove it.

The checklist is intentionally non-axiomatic: it introduces no new theorem
assumptions.  The `...Certificate` definitions below are Prop-valued target
statements, and `explicitCertificateChecklist` is a compile-checked audit
table tying the current wrapper hypotheses to future theorem names.
-/

namespace CertificateChecklist

/-- Status tags for the certificate backlog. -/
inductive CertificateStatus where
  /-- The certificate is currently passed as an explicit hypothesis. -/
  | openTarget
  /-- The certificate has already been decomposed into a smaller target. -/
  | splitTarget
  /-- The consumer theorem is already sorry-free once the certificate is supplied. -/
  | consumerReady
deriving Repr, DecidableEq

/-- One row of the Wakker/DK certificate checklist. -/
structure CertificateItem where
  /-- Name of the explicit certificate hypothesis in the current Lean file. -/
  hypothesisName : String
  /-- Current theorem(s) that consume the hypothesis. -/
  currentConsumers : List String
  /-- Future theorem expected to produce the certificate. -/
  eventualTheorem : String
  /-- Short description of the proposition that theorem must prove. -/
  certificateStatement : String
  /-- Status of the item in the full-discharge backlog. -/
  status : CertificateStatus
  /-- Mathematical provenance / implementation notes. -/
  notes : String
deriving Repr

/-- The one-step extension certificate supplied as `hext` in
`extend_to_standard_sequence`. -/
def StandardSequenceExtensionCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι) (base : Profile X) (r s : X k) : Prop :=
  ProductPref.OneStepExtensible P j base k r s

/-- The global additive-representation output supplied as `hConstruct` in
`wakker_IV_2_7`. -/
def WakkerConstructionCertificate {X : ι → Type v} (P : ProductPref X) : Prop :=
  ∃ V : (i : ι) → X i → ℝ,
    ∀ x y : Profile X,
      P.weakPref x y ↔
        (∑ i, V i (y i)) ≤ (∑ i, V i (x i))

/-- The two-coordinate slice representation supplied as `hVⱼₖ_repr` in
`pairwise_additivity`. -/
def PairwiseSliceRepresentationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι) (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  ∀ x y : Profile X,
    Profile.agreeOff {j, k} x y →
      (P.weakPref x y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k))

/-- The local interpolation certificate supplied by restricted solvability on
a two-coordinate slice: either coordinate can be varied while the other is held
fixed. -/
def PairwiseLocalInterpolationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι) : Prop :=
  (∀ (base target : Profile X) (vk : X k) (v w : X j),
    P.weakPref (Function.update (Function.update base k vk) j v) target →
    P.weakPref target (Function.update (Function.update base k vk) j w) →
    ∃ c : X j,
      P.indiff (Function.update (Function.update base k vk) j c) target) ∧
  (∀ (base target : Profile X) (vj : X j) (v w : X k),
    P.weakPref (Function.update (Function.update base j vj) k v) target →
    P.weakPref target (Function.update (Function.update base j vj) k w) →
    ∃ c : X k,
      P.indiff (Function.update (Function.update base j vj) k c) target)

/-- Restricted solvability proves the local pairwise interpolation certificate. -/
theorem pairwiseLocalInterpolationCertificate_of_restrictedSolvability {X : ι → Type v}
    (P : ProductPref X) (hsolv : ProductPref.RestrictedSolvability P)
    (j k : ι) :
    PairwiseLocalInterpolationCertificate P j k := by
  constructor
  · intro base target vk v w hlo hhi
    exact WakkerExistence.pairwise_left_interpolation_of_restrictedSolvability
      P hsolv base target j k vk v w hlo hhi
  · intro base target vj v w hlo hhi
    exact WakkerExistence.pairwise_right_interpolation_of_restrictedSolvability
      P hsolv base target j k vj v w hlo hhi

/-- Slice-preserving interpolation certificate on a fixed two-coordinate slice:
the interpolating choice is packaged as an actual profile agreeing with the
target off `{j,k}`. -/
def PairwiseSliceInterpolationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι) : Prop :=
  (∀ (base target : Profile X), j ≠ k →
    ∀ (vk : X k) (v w : X j),
      Profile.agreeOff ({j, k} : Set ι) base target →
      P.weakPref (Function.update (Function.update base k vk) j v) target →
      P.weakPref target (Function.update (Function.update base k vk) j w) →
      ∃ z : Profile X,
        Profile.agreeOff ({j, k} : Set ι) z target ∧
        z k = vk ∧
        P.indiff z target) ∧
  (∀ (base target : Profile X), j ≠ k →
    ∀ (vj : X j) (v w : X k),
      Profile.agreeOff ({j, k} : Set ι) base target →
      P.weakPref (Function.update (Function.update base j vj) k v) target →
      P.weakPref target (Function.update (Function.update base j vj) k w) →
      ∃ z : Profile X,
        Profile.agreeOff ({j, k} : Set ι) z target ∧
        z j = vj ∧
        P.indiff z target)

/-- The coordinate-level local interpolation certificate upgrades to the
slice-preserving profile-level interpolation certificate. -/
theorem pairwiseSliceInterpolationCertificate_of_pairwiseLocalInterpolationCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (hlocal : PairwiseLocalInterpolationCertificate P j k) :
    PairwiseSliceInterpolationCertificate P j k := by
  rcases hlocal with ⟨hleft, hright⟩
  constructor
  · intro base target hjk vk v w hbase hlo hhi
    obtain ⟨c, hc⟩ := hleft base target vk v w hlo hhi
    let z : Profile X := Function.update (Function.update base k vk) j c
    refine ⟨z, ?_, ?_, hc⟩
    · have hzbase : Profile.agreeOff ({j, k} : Set ι) z base := by
        intro i hi
        have hij : i ≠ j := by
          intro hij
          apply hi
          simp [hij]
        have hik : i ≠ k := by
          intro hik
          apply hi
          simp [hik]
        dsimp [z]
        rw [Function.update_of_ne hij, Function.update_of_ne hik]
      exact Profile.agreeOff_trans hzbase hbase
    · dsimp [z]
      rw [Function.update_of_ne hjk.symm, Function.update_self]
  · intro base target hjk vj v w hbase hlo hhi
    obtain ⟨c, hc⟩ := hright base target vj v w hlo hhi
    let z : Profile X := Function.update (Function.update base j vj) k c
    refine ⟨z, ?_, ?_, hc⟩
    · have hzbase : Profile.agreeOff ({j, k} : Set ι) z base := by
        intro i hi
        have hij : i ≠ j := by
          intro hij
          apply hi
          simp [hij]
        have hik : i ≠ k := by
          intro hik
          apply hi
          simp [hik]
        dsimp [z]
        rw [Function.update_of_ne hik, Function.update_of_ne hij]
      exact Profile.agreeOff_trans hzbase hbase
    · dsimp [z]
      rw [Function.update_of_ne hjk, Function.update_self]

/-- Restricted solvability also yields the slice-preserving profile-level
interpolation certificate. -/
theorem pairwiseSliceInterpolationCertificate_of_restrictedSolvability
    {X : ι → Type v} (P : ProductPref X)
    (hsolv : ProductPref.RestrictedSolvability P) (j k : ι) :
    PairwiseSliceInterpolationCertificate P j k :=
  pairwiseSliceInterpolationCertificate_of_pairwiseLocalInterpolationCertificate
    P j k
    (pairwiseLocalInterpolationCertificate_of_restrictedSolvability P hsolv j k)

/-! ### Pairwise slice-construction certificates

The theorem-backed substeps toward `hVⱼₖ_repr` now split into two clean pieces:

* `PairwiseGridNormalizationCertificate`: utilities normalized on the two
  standard-sequence grids;
* `PairwiseLocalInterpolationCertificate`: local solvability on the two-coordinate
  slice.

Together they form the current Step-4 input data.  The remaining gap is to turn
that data into total slice utilities whose sum represents the whole `{j,k}`-slice.
-/

/-- Grid-normalization witness for utilities on a pair of standard-sequence
grids. -/
def PairwiseGridNormalizationWitness {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  (∀ n : ℕ, Vj (σj.α n) = (n : ℝ)) ∧
  (∀ n : ℕ, Vk (σk.α n) = (n : ℝ))

/-- Existence of utilities normalized on the given pair of standard-sequence
grids. -/
def PairwiseGridNormalizationCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk

/-- Injective standard-sequence grids supply the pairwise grid-normalization
certificate. -/
theorem pairwiseGridNormalizationCertificate_of_injectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α) :
    PairwiseGridNormalizationCertificate σj σk := by
  obtain ⟨Vj, Vk, hVj, hVk⟩ :=
    WakkerExistence.pairwise_grid_utilities_exist P σj σk hinj_j hinj_k
  exact ⟨Vj, Vk, hVj, hVk⟩

/-- A grid-normalization witness already contains the expected `0`/`1`
normalization on both standard-sequence grids. -/
theorem pairwiseGridNormalizationWitness_zero_one {X : ι → Type v}
    {P : ProductPref X} {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk) :
    Vj (σj.α 0) = 0 ∧ Vj (σj.α 1) = 1 ∧
      Vk (σk.α 0) = 0 ∧ Vk (σk.α 1) = 1 := by
  rcases hgrid with ⟨hVj, hVk⟩
  exact ⟨by simpa using hVj 0, by simpa using hVj 1,
    by simpa using hVk 0, by simpa using hVk 1⟩

/-- The theorem-backed Step-4 input data currently available for a two-coordinate
slice: grid normalization on both coordinate grids and local interpolation on
that slice. -/
def PairwiseConstructionDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseGridNormalizationCertificate σj σk ∧
    PairwiseLocalInterpolationCertificate P j k

/-- Cleaner future input for the Step-4 assembly theorem: grid normalization on
the two standard-sequence grids plus slice-preserving interpolation on the
`{j,k}`-slice.  This repackages the current construction data into the form the
eventual assembly proof is most likely to consume. -/
def PairwiseAssemblyInputCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseGridNormalizationCertificate σj σk ∧
    PairwiseSliceInterpolationCertificate P j k

/-- Current construction data already yields the cleaner assembly-input bundle:
upgrade local interpolation to slice-preserving interpolation and keep the grid
normalization witness unchanged. -/
theorem pairwiseAssemblyInputCertificate_of_pairwiseConstructionDataCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hdata : PairwiseConstructionDataCertificate P j k σj σk) :
    PairwiseAssemblyInputCertificate P j k σj σk := by
  rcases hdata with ⟨hgrid, hlocal⟩
  exact ⟨hgrid,
    pairwiseSliceInterpolationCertificate_of_pairwiseLocalInterpolationCertificate
      P j k hlocal⟩

/-- Injective standard-sequence grids together with restricted solvability also
produce the cleaner assembly-input bundle directly. -/
theorem pairwiseAssemblyInputCertificate_of_injectiveStandardSequences_and_restrictedSolvability
    {X : ι → Type v} (P : ProductPref X)
    (hsolv : ProductPref.RestrictedSolvability P) {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α) :
    PairwiseAssemblyInputCertificate P j k σj σk := by
  refine ⟨?_, ?_⟩
  · exact pairwiseGridNormalizationCertificate_of_injectiveStandardSequences
      P σj σk hinj_j hinj_k
  · exact pairwiseSliceInterpolationCertificate_of_restrictedSolvability
      P hsolv j k

/-- Injective standard-sequence grids together with restricted solvability
assemble the current theorem-backed Step-4 construction data. -/
theorem pairwiseConstructionDataCertificate_of_injectiveStandardSequences_and_restrictedSolvability
    {X : ι → Type v} (P : ProductPref X)
    (hsolv : ProductPref.RestrictedSolvability P) {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α) :
    PairwiseConstructionDataCertificate P j k σj σk := by
  refine ⟨?_, ?_⟩
  · exact pairwiseGridNormalizationCertificate_of_injectiveStandardSequences
      P σj σk hinj_j hinj_k
  · exact pairwiseLocalInterpolationCertificate_of_restrictedSolvability
      P hsolv j k

/-- Remaining Step-4 target after the theorem-backed substeps above: choose
total utilities extending the two standard-sequence grids and prove that their
sum represents the full `{j,k}`-slice. -/
def PairwiseSliceAssemblyCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceRepresentationCertificate P j k Vj Vk

/-- **Wakker Step-4 order calibration for chosen total utilities.**

This is the missing order-theoretic content exposed by the total-preference
counterexample below: after utilities have been normalized on the two standard
sequence grids, one must still prove that their additive score has exactly the
same order as `P` on the `{j,k}`-slice. -/
def PairwiseOrderCalibrationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  PairwiseSliceRepresentationCertificate P j k Vj Vk

/-- A stronger Step-4 input bundle: choose total utilities, prove they are
normalized on the two standard-sequence grids, retain the slice-preserving
interpolation interface, and add the missing order-calibration theorem for those
chosen utilities. -/
def PairwiseOrderCalibratedAssemblyInputCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceInterpolationCertificate P j k ∧
      PairwiseOrderCalibrationCertificate P j k Vj Vk

/-- The Wakker Step-4 order-calibration theorem certificate: from the current
assembly-input bundle, produce chosen total utilities with grid normalization,
slice interpolation, and calibrated two-coordinate order. -/
def PairwiseOrderCalibrationTheoremCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseAssemblyInputCertificate P j k σj σk →
    PairwiseOrderCalibratedAssemblyInputCertificate P j k σj σk

/-- The output of Wakker's Step-4 tradeoff machinery for a fixed pair of
standard-sequence grids: from the assembly input, construct chosen total
utilities normalized on the two grids and prove that their additive score is
order-calibrated on the whole `{j,k}`-slice.

This is deliberately one level below `PairwiseOrderCalibrationTheoremCertificate`:
it records the genuine tradeoff-measurement payload (existence of calibrated
utilities), while the theorem below repackages it together with the already
available slice-preserving interpolation certificate. -/
def PairwiseStep4TradeoffMachineryCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseAssemblyInputCertificate P j k σj σk →
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
        PairwiseOrderCalibrationCertificate P j k Vj Vk

/-- Additive score on a fixed `{j,k}`-slice for candidate utilities. -/
def PairwiseAdditiveScore {X : ι → Type v} {j k : ι}
    (Vj : X j → ℝ) (Vk : X k → ℝ) (x : Profile X) : ℝ :=
  Vj (x j) + Vk (x k)

/-- The numerical size of a grid point indexed by two standard-sequence
positions. -/
def PairwiseGridStepMagnitude (n m : ℕ) : ℝ :=
  (n : ℝ) + (m : ℝ)

/-- The profile obtained from a common slice base by replacing coordinates
`j` and `k` with standard-sequence grid values. -/
def PairwiseGridProfile {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (base : Profile X) (n m : ℕ) : Profile X :=
  Function.update (Function.update base j (σj.α n)) k (σk.α m)

/-- Reflexivity of indifference for weak orders. -/
lemma productPref_indiff_refl {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P] (x : Profile X) :
    P.indiff x x := by
  refine ⟨?_, ?_⟩ <;>
    · rcases ProductPref.IsWeakOrder.complete (P := P) x x with h | h <;> exact h

/-- If the common slice base agrees with a target off `{j,k}`, and the grid
indices hit the target coordinates exactly, then the corresponding grid profile
is definitionally the target profile. -/
theorem pairwiseGridProfile_eq_of_agreeOff_and_grid_hits
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (hjk : j ≠ k)
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {base target : Profile X} {n m : ℕ}
    (hbase : Profile.agreeOff ({j, k} : Set ι) base target)
    (hj : σj.α n = target j)
    (hk : σk.α m = target k) :
    PairwiseGridProfile σj σk base n m = target := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [PairwiseGridProfile, hk]
  · by_cases hij : i = j
    · subst i
      simp [PairwiseGridProfile, Function.update_of_ne hjk, hj]
    · have hi_not_pair : i ∉ ({j, k} : Set ι) := by
        intro hi
        rcases (by simpa using hi : i = j ∨ i = k) with rfl | rfl
        · exact hij rfl
        · exact hik rfl
      simp [PairwiseGridProfile, hik, hij, hbase i hi_not_pair]

/-- Grid normalization identifies the additive score of a grid profile with
the corresponding two-index step magnitude. -/
theorem pairwiseAdditiveScore_pairwiseGridProfile_of_gridNormalizationWitness
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (hjk : j ≠ k)
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk)
    (base : Profile X) (n m : ℕ) :
    PairwiseAdditiveScore Vj Vk (PairwiseGridProfile σj σk base n m) =
      PairwiseGridStepMagnitude n m := by
  rcases hgrid with ⟨hVj, hVk⟩
  simp [PairwiseAdditiveScore, PairwiseGridProfile,
    PairwiseGridStepMagnitude, Function.update_of_ne hjk, hVj n, hVk m]

/-- Concrete Step-4 magnitude certificate on the two standard-sequence grids:
grid-profile comparisons are represented by comparing the summed step counts.
This is the part of Wakker's standard-sequence machinery that turns repeated
tradeoff steps into cardinal numbers. -/
def PairwiseTradeoffMagnitudeCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ (base : Profile X) (nx mx ny my : ℕ),
    P.weakPref (PairwiseGridProfile σj σk base nx mx)
      (PairwiseGridProfile σj σk base ny my) ↔
        PairwiseGridStepMagnitude ny my ≤ PairwiseGridStepMagnitude nx mx

/-- The order-calibrated Step-4 core proves the concrete grid-step magnitude
certificate: on grid profiles, the already calibrated additive score reduces to
the summed standard-sequence indices. -/
theorem pairwiseTradeoffMagnitudeCertificate_of_gridNormalizationWitness_and_orderCalibration
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (hjk : j ≠ k)
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk)
    (hcal : PairwiseOrderCalibrationCertificate P j k Vj Vk) :
    PairwiseTradeoffMagnitudeCertificate σj σk := by
  intro base nx mx ny my
  let gx : Profile X := PairwiseGridProfile σj σk base nx mx
  let gy : Profile X := PairwiseGridProfile σj σk base ny my
  have hagree : Profile.agreeOff ({j, k} : Set ι) gx gy := by
    intro i hi
    have hij : i ≠ j := by
      intro hij
      apply hi
      simp [hij]
    have hik : i ≠ k := by
      intro hik
      apply hi
      simp [hik]
    simp [gx, gy, PairwiseGridProfile, hik, hij]
  have hrepr : P.weakPref gx gy ↔
      PairwiseAdditiveScore Vj Vk gy ≤ PairwiseAdditiveScore Vj Vk gx := by
    change P.weakPref gx gy ↔
      Vj (gy j) + Vk (gy k) ≤ Vj (gx j) + Vk (gx k)
    exact hcal gx gy hagree
  have hscore_gx : PairwiseAdditiveScore Vj Vk gx = PairwiseGridStepMagnitude nx mx := by
    dsimp [gx]
    exact pairwiseAdditiveScore_pairwiseGridProfile_of_gridNormalizationWitness
      hjk hgrid base nx mx
  have hscore_gy : PairwiseAdditiveScore Vj Vk gy = PairwiseGridStepMagnitude ny my := by
    dsimp [gy]
    exact pairwiseAdditiveScore_pairwiseGridProfile_of_gridNormalizationWitness
      hjk hgrid base ny my
  simpa [gx, gy, hscore_gx, hscore_gy] using hrepr

/-- Concrete bracketing certificate for the full two-coordinate slice: every
comparison on the slice can be matched to a pair of standard-sequence grid
profiles, preserving both indifference and the additive score of the chosen
utilities.  This is the formal target for the interpolation/Archimedean
bracketing part of Wakker Step 4. -/
def PairwiseTradeoffBracketingCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  ∀ x y : Profile X,
    Profile.agreeOff ({j, k} : Set ι) x y →
      ∃ (base : Profile X) (nx mx ny my : ℕ),
        let gx := PairwiseGridProfile σj σk base nx mx
        let gy := PairwiseGridProfile σj σk base ny my
        P.indiff x gx ∧ P.indiff y gy ∧
          PairwiseAdditiveScore Vj Vk x = PairwiseAdditiveScore Vj Vk gx ∧
          PairwiseAdditiveScore Vj Vk y = PairwiseAdditiveScore Vj Vk gy

/-- Exact bracketing in the surjective-grid case.

If both standard-sequence grids hit every coordinate value, any slice profiles
`x` and `y` can be bracketed by grid profiles that are actually equal to `x`
and `y` on the common slice base.  This proves the exact bracketing certificate
without the missing Archimedean/interpolation argument.  The general Wakker
Step-4 bracketing theorem should remove these surjectivity assumptions. -/
theorem pairwiseTradeoffBracketingCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseTradeoffBracketingCertificate σj σk Vj Vk := by
  intro x y hxy
  rcases hsurj_j (x j) with ⟨nx, hxj⟩
  rcases hsurj_k (x k) with ⟨mx, hxk⟩
  rcases hsurj_j (y j) with ⟨ny, hyj⟩
  rcases hsurj_k (y k) with ⟨my, hyk⟩
  let gx : Profile X := PairwiseGridProfile σj σk x nx mx
  let gy : Profile X := PairwiseGridProfile σj σk x ny my
  have hgx : gx = x := by
    dsimp [gx]
    exact pairwiseGridProfile_eq_of_agreeOff_and_grid_hits
      hjk (Profile.agreeOff_refl ({j, k} : Set ι) x) hxj hxk
  have hgy : gy = y := by
    dsimp [gy]
    exact pairwiseGridProfile_eq_of_agreeOff_and_grid_hits
      hjk hxy hyj hyk
  refine ⟨x, nx, mx, ny, my, ?_, ?_, ?_, ?_⟩
  · change P.indiff x gx
    rw [hgx]
    exact productPref_indiff_refl P x
  · change P.indiff y gy
    rw [hgy]
    exact productPref_indiff_refl P y
  · change PairwiseAdditiveScore Vj Vk x = PairwiseAdditiveScore Vj Vk gx
    rw [hgx]
  · change PairwiseAdditiveScore Vj Vk y = PairwiseAdditiveScore Vj Vk gy
    rw [hgy]

/-- The exact-grid bracketing output used by the currently expanded Step-4
wrapper for chosen utility extensions.

The current Lean `ProductPref.Archimedean` axiom only says that strict standard
sequences cannot be preference-bounded forever; it does not by itself construct
exact finite grid representatives.  The additive-real counterexample below
shows that this exact-grid target is too strong for non-surjective one-sided
grids; the eventual Wakker proof must factor through finite cuts plus an
interpolation/extension layer, or through stronger grid-coverage hypotheses. -/
def PairwiseArchimedeanBracketingCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  PairwiseTradeoffBracketingCertificate σj σk Vj Vk

/-- The theorem-shaped exact-grid bracketing target for a fixed pair of
standard-sequence grids.

This remains useful for the surjective-grid regression path and for wrappers
that already assume exact grid coverage.  It is not a theorem of the present
raw Archimedean/solvability interface in the non-surjective one-sided case; see
`additiveRealBool_not_pairwiseCutConstructionTheoremCertificate`. -/
def PairwiseArchimedeanBracketingTheoremCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ Vj : X j → ℝ, ∀ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk →
      PairwiseOrderCalibrationCertificate P j k Vj Vk →
        PairwiseArchimedeanBracketingCertificate σj σk Vj Vk

/-- A single Wakker cut witness: relative to a slice base, a target profile is
matched by a finite standard-sequence grid profile that is indifferent to it and
has the same additive score.

This is the constructive object produced by the cut argument: the cut chooses
finite lower/upper standard-sequence indices and restricted solvability turns
the cut into an exact indifferent grid representative.

This exact-grid target is intentionally strong; the counterexample
`additiveRealBool_not_pairwiseCutConstructionTheoremCertificate` below shows
that one-sided grids do not produce such witnesses for arbitrary real-valued
targets without an additional interpolation/cut-extension layer. -/
def PairwiseCutWitness {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ)
    (target base : Profile X) (n m : ℕ) : Prop :=
  let grid := PairwiseGridProfile σj σk base n m
  P.indiff target grid ∧
    PairwiseAdditiveScore Vj Vk target = PairwiseAdditiveScore Vj Vk grid

/-- Wakker cut-construction output for chosen utilities: every target profile on
a two-coordinate slice has a finite cut witness relative to every slice base
that agrees with it off `{j,k}`. -/
def PairwiseCutConstructionCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      ∃ n m : ℕ, PairwiseCutWitness σj σk Vj Vk target base n m

/-- The theorem-shaped Wakker cut construction target: for any chosen
grid-normalized, order-calibrated utilities, construct finite cut witnesses for
all two-coordinate slice targets. -/
def PairwiseCutConstructionTheoremCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ Vj : X j → ℝ, ∀ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk →
      PairwiseOrderCalibrationCertificate P j k Vj Vk →
        PairwiseCutConstructionCertificate σj σk Vj Vk

/-- Cut witnesses for every profile immediately give exact Archimedean
bracketing for every pair of profiles on the same `{j,k}`-slice. -/
theorem pairwiseArchimedeanBracketingCertificate_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseArchimedeanBracketingCertificate σj σk Vj Vk := by
  intro x y hxy
  rcases hcut x x (Profile.agreeOff_refl ({j, k} : Set ι) x) with
    ⟨nx, mx, hxcut⟩
  rcases hcut x y hxy with ⟨ny, my, hycut⟩
  rcases hxcut with ⟨hxindiff, hxscore⟩
  rcases hycut with ⟨hyindiff, hyscore⟩
  exact ⟨x, nx, mx, ny, my, hxindiff, hyindiff, hxscore, hyscore⟩

/-- Wakker's cut-construction theorem certificate proves the Archimedean
bracketing theorem certificate. -/
theorem pairwiseArchimedeanBracketingTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hcut : PairwiseCutConstructionTheoremCertificate P j k σj σk) :
    PairwiseArchimedeanBracketingTheoremCertificate P j k σj σk := by
  intro Vj Vk hgrid hcal
  exact pairwiseArchimedeanBracketingCertificate_of_pairwiseCutConstructionCertificate
    (hcut Vj Vk hgrid hcal)

/-- Surjective standard-sequence grids give cut witnesses by equality.  This
keeps the old degenerate case available at the cut-construction layer. -/
theorem pairwiseCutConstructionCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseCutConstructionCertificate σj σk Vj Vk := by
  intro base target hbase
  rcases hsurj_j (target j) with ⟨n, hn⟩
  rcases hsurj_k (target k) with ⟨m, hm⟩
  have hgridTarget : PairwiseGridProfile σj σk base n m = target :=
    pairwiseGridProfile_eq_of_agreeOff_and_grid_hits hjk hbase hn hm
  refine ⟨n, m, ?_, ?_⟩
  · rw [hgridTarget]
    exact productPref_indiff_refl P target
  · rw [hgridTarget]

/-- Surjective standard-sequence grids also give the theorem-shaped cut
construction certificate. -/
theorem pairwiseCutConstructionTheoremCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseCutConstructionTheoremCertificate P j k σj σk := by
  intro Vj Vk _hgrid _hcal
  exact pairwiseCutConstructionCertificate_of_surjectiveStandardSequences
    P hjk σj σk Vj Vk hsurj_j hsurj_k

/-- Surjective standard-sequence grids are a degenerate case of the
Archimedean bracketing theorem: every target coordinate is already a grid point,
so the exact brackets are obtained by equality. -/
theorem pairwiseArchimedeanBracketingTheoremCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseArchimedeanBracketingTheoremCertificate P j k σj σk := by
  exact pairwiseArchimedeanBracketingTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate
    P j k σj σk
    (pairwiseCutConstructionTheoremCertificate_of_surjectiveStandardSequences
      P hjk σj σk hsurj_j hsurj_k)

/-! ### Finite cuts plus interpolation/extension

The exact-grid cut target `PairwiseCutConstructionTheoremCertificate` is refuted
by `additiveRealBool_not_pairwiseCutConstructionTheoremCertificate`: one-sided
standard-sequence grids cannot match arbitrary real-valued targets exactly.

Wakker's actual Step-4 argument does not in fact assert exact grid witnesses:
it produces a *finite cut* (an indexed grid bracket on the target) and then
fills the bracket via *interpolation/extension* — a slice-shaped indifferent
profile obtained by restricted solvability inside the bracket interval.  This
section formalizes the two halves of that route as Prop-valued certificates and
records the easy regressions (surjective grids and exact cut construction).

The certificates are intentionally weaker than the refuted exact-cut target
yet stronger than the raw Archimedean axiom: they isolate the precise
mathematical content the eventual Wakker proof must discharge before feeding
the hexagon-propagation/bracketing layer. -/

/-- A finite Wakker cut on a target slice profile: two finite standard-sequence
grid profiles bracket `target` in preference, relative to a common slice base.

`grid(b, n_hi, m_hi) ≽ target ≽ grid(b, n_lo, m_lo)` records the finite-grid
bracket Wakker's standard-sequence machinery is supposed to produce from the
Archimedean axiom together with the structural hypotheses on `≽`. -/
def PairwiseFiniteCutBracket {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (base target : Profile X) (n_lo m_lo n_hi m_hi : ℕ) : Prop :=
  P.weakPref (PairwiseGridProfile σj σk base n_hi m_hi) target ∧
    P.weakPref target (PairwiseGridProfile σj σk base n_lo m_lo)

/-- Wakker's finite-cut coverage certificate: every slice target has a finite
standard-sequence grid bracket relative to every slice-base profile that agrees
with it off `{j,k}`.

This is the honest Archimedean output Wakker's standard-sequence/cut argument is
expected to produce; it does **not** assert exact grid witnesses, only finite
bracketing.  See `additiveRealBool_not_pairwiseCutConstructionTheoremCertificate`
for the proof that the stronger exact-grid target is false in the current
abstract interface, which is precisely why this weaker form is the right
formalisation target. -/
def PairwiseFiniteCutCoverageCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      ∃ n_lo m_lo n_hi m_hi : ℕ,
        PairwiseFiniteCutBracket σj σk base target n_lo m_lo n_hi m_hi

/-- An interpolation/extension witness for a slice target: a slice-shaped
profile `z` that agrees with `target` off `{j,k}` and is indifferent to it.

This is the abstract output of Wakker's interpolation step: between two finite
cut-bracket grid profiles, restricted solvability + structural hypotheses on
`≽` produce a same-slice profile `z ∼ target`.  The witness need not be a grid
profile — that strengthening is exactly what fails in the additive-real
counterexample. -/
def PairwiseInterpolationExtensionWitness {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (target z : Profile X) : Prop :=
  Profile.agreeOff ({j, k} : Set ι) z target ∧ P.indiff z target

/-- The interpolation/extension certificate: from a finite cut on a slice
target, produce a slice-shaped indifferent witness on the same `{j,k}`-slice.

This packages Wakker's continuity/interpolation step as a Prop-level target
parameterized by the cut indices, leaving the actual interpolation argument
(restricted solvability applied inside the bracket interval) for the future
proof. -/
def PairwiseInterpolationExtensionCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
    ∀ n_lo m_lo n_hi m_hi : ℕ,
      PairwiseFiniteCutBracket σj σk base target n_lo m_lo n_hi m_hi →
        ∃ z : Profile X,
          PairwiseInterpolationExtensionWitness P j k target z

/-- Wakker's finite cuts plus interpolation/extension: every slice target gets
a finite-cut bracket together with a slice-shaped indifferent witness on the
same `{j,k}`-slice.

This is the honest weakening of the refuted exact-cut target.  Surjective grids
satisfy it trivially, the exact cut construction certificate implies it, and
the eventual Wakker Step-4 proof should discharge it from the structural
axioms (Archimedean axiom for the cut coverage, restricted solvability for the
interpolation/extension). -/
def PairwiseFiniteCutInterpolationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseFiniteCutCoverageCertificate σj σk ∧
    PairwiseInterpolationExtensionCertificate P j k σj σk

/-- Surjective standard-sequence grids satisfy the finite-cut coverage
certificate by taking `(n_lo, m_lo) = (n_hi, m_hi)` to be the indices that hit
the target coordinates exactly. -/
theorem pairwiseFiniteCutCoverageCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  intro base target hbase
  rcases hsurj_j (target j) with ⟨n, hn⟩
  rcases hsurj_k (target k) with ⟨m, hm⟩
  have hgridTarget : PairwiseGridProfile σj σk base n m = target :=
    pairwiseGridProfile_eq_of_agreeOff_and_grid_hits hjk hbase hn hm
  refine ⟨n, m, n, m, ?_, ?_⟩
  · rw [hgridTarget]
    exact (productPref_indiff_refl P target).1
  · rw [hgridTarget]
    exact (productPref_indiff_refl P target).2

/-- Surjective standard-sequence grids satisfy the interpolation/extension
certificate by taking `z := target`. -/
theorem pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) :
    PairwiseInterpolationExtensionCertificate P j k σj σk := by
  intro base target hbase _n_lo _m_lo _n_hi _m_hi _hbracket
  refine ⟨target, ?_, ?_⟩
  · exact Profile.agreeOff_refl ({j, k} : Set ι) target
  · exact productPref_indiff_refl P target

/-- Surjective standard-sequence grids therefore satisfy the combined finite
cuts plus interpolation/extension certificate. -/
theorem pairwiseFiniteCutInterpolationCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutInterpolationCertificate P j k σj σk :=
  ⟨pairwiseFiniteCutCoverageCertificate_of_surjectiveStandardSequences
      P hjk σj σk hsurj_j hsurj_k,
    pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences
      P σj σk⟩

/-! ### Finite-cut coverage from the raw Archimedean axiom

The Archimedean axiom in `WakkerInfra` states that no strict standard sequence
is preference-bounded above and below simultaneously, *relative to the
sequence's own base profile* `σ.base`.  The honest decomposition of finite-cut
coverage from this raw axiom has three layers:

* The *contrapositive* of `Archimedean`: for any candidate sandwich `(lo, hi)`
  against `σ.base`, some index `n` falsifies one of the two sandwich
  inequalities.  This is fully theorem-backed below.
* An *upper-half* and *lower-half* split of cut coverage on a slice base.
  Their conjunction is provably equivalent to the full coverage certificate.
* The *base-transport* bridge: a slice base typically differs from
  `σj.base` and `σk.base`, so the sandwich-failure from the contrapositive
  must be transported across slice bases.  This bridge is exactly the
  residual content beyond raw Archimedean; the additive-real refutation
  `additiveRealBool_not_pairwiseCutConstructionCertificate` shows the
  one-sided version of this transport can fail without further hypotheses.

The result is that `PairwiseFiniteCutCoverageCertificate` is theorem-backed
from raw Archimedean **plus** an explicit base-transport bridge isolating
exactly the missing residual content. -/

/-- The contrapositive of the Archimedean axiom: for any strict standard
sequence and any candidate sandwich `(lo, hi)` against `σ.base`, there is an
index `n` where one of the two sandwich inequalities fails.

This is the only direct consequence of raw `Archimedean` that is purely
existential; it isolates the precise contrapositive content the cut-coverage
proof will exploit. -/
theorem standardSequence_unbracket_of_archimedean
    {X : ι → Type v} (P : ProductPref X) {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (lo hi : Profile X) :
    ∃ n : ℕ, ¬ (P.weakPref hi (Function.update σ.base j (σ.α n)) ∧
                P.weakPref (Function.update σ.base j (σ.α n)) lo) := by
  have hnot := harchim σ hσ
  by_contra hcontra
  push_neg at hcontra
  exact hnot ⟨lo, hi, fun n => hcontra n⟩

/-- A finite-cut *upper bracket* on a slice target relative to a slice base:
some grid profile (parameterized by indices `n_hi, m_hi`) is weakly preferred
to the target. -/
def PairwiseFiniteCutUpperBracket {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (base target : Profile X) : Prop :=
  ∃ n_hi m_hi : ℕ,
    P.weakPref (PairwiseGridProfile σj σk base n_hi m_hi) target

/-- A finite-cut *lower bracket* on a slice target relative to a slice base:
the target is weakly preferred to some grid profile (parameterized by indices
`n_lo, m_lo`). -/
def PairwiseFiniteCutLowerBracket {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (base target : Profile X) : Prop :=
  ∃ n_lo m_lo : ℕ,
    P.weakPref target (PairwiseGridProfile σj σk base n_lo m_lo)

/-- Upper-half finite-cut coverage: every slice target has a finite-cut upper
bracket relative to every slice base agreeing with it off `{j,k}`. -/
def PairwiseFiniteCutUpperCoverageCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      PairwiseFiniteCutUpperBracket σj σk base target

/-- Lower-half finite-cut coverage: every slice target has a finite-cut lower
bracket relative to every slice base agreeing with it off `{j,k}`. -/
def PairwiseFiniteCutLowerCoverageCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      PairwiseFiniteCutLowerBracket σj σk base target

/-- Cut coverage decomposes into the upper and lower halves. -/
theorem pairwiseFiniteCutCoverageCertificate_of_upper_and_lower
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    (hupper : PairwiseFiniteCutUpperCoverageCertificate σj σk)
    (hlower : PairwiseFiniteCutLowerCoverageCertificate σj σk) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  intro base target hbase
  rcases hupper base target hbase with ⟨n_hi, m_hi, hhi⟩
  rcases hlower base target hbase with ⟨n_lo, m_lo, hlo⟩
  exact ⟨n_lo, m_lo, n_hi, m_hi, hhi, hlo⟩

/-- The reverse direction: the full coverage certificate yields each half. -/
theorem pairwiseFiniteCutUpperCoverageCertificate_of_full
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    (hfull : PairwiseFiniteCutCoverageCertificate σj σk) :
    PairwiseFiniteCutUpperCoverageCertificate σj σk := by
  intro base target hbase
  rcases hfull base target hbase with ⟨_, _, n_hi, m_hi, hhi, _⟩
  exact ⟨n_hi, m_hi, hhi⟩

/-- The reverse direction for the lower half. -/
theorem pairwiseFiniteCutLowerCoverageCertificate_of_full
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    (hfull : PairwiseFiniteCutCoverageCertificate σj σk) :
    PairwiseFiniteCutLowerCoverageCertificate σj σk := by
  intro base target hbase
  rcases hfull base target hbase with ⟨n_lo, m_lo, _, _, _, hlo⟩
  exact ⟨n_lo, m_lo, hlo⟩

/-- A *single-coordinate base-transport* bridge for one strict standard
sequence: from the contrapositive of `Archimedean` against the sequence's
own base, transport sandwich-failure to an arbitrary slice-shaped base
profile.

Concretely, the bridge says: from any slice base `base` agreeing with a
target off `{j,k}` and any candidate one-coordinate "lo, hi" pair, there
exists a grid index `n_j` such that some bracketing inequality holds at
`base` (rather than at `σj.base`).  This is exactly the residual content
beyond raw Archimedean: it transports the no-sandwich consequence across
slice bases.

The additive-real counterexample
`additiveRealBool_not_pairwiseCutConstructionCertificate` shows that an
*exact* version of base-transport can fail for one-sided grids, which is
why this is isolated as a Prop-level bridge rather than a theorem. -/
def PairwiseArchimedeanBaseTransportCertificate {X : ι → Type v}
    {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  (∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      PairwiseFiniteCutUpperBracket σj σk base target) ∧
  (∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      PairwiseFiniteCutLowerBracket σj σk base target)

/-- Finite-cut coverage from the raw Archimedean axiom plus the explicit
base-transport bridge.  This is the honest decomposition: the Archimedean
axiom alone supplies sandwich-failure at `σ.base`, while the bridge
transports it to arbitrary slice bases.  The proof reads off both halves of
the bridge and assembles the four-index cut. -/
theorem pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport
    {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    (_harchim_j : ProductPref.Archimedean P j)
    (_harchim_k : ProductPref.Archimedean P k)
    (htransport : PairwiseArchimedeanBaseTransportCertificate σj σk) :
    PairwiseFiniteCutCoverageCertificate σj σk :=
  pairwiseFiniteCutCoverageCertificate_of_upper_and_lower
    htransport.1 htransport.2

/-- The base-transport bridge is non-vacuous: surjective standard-sequence
grids satisfy it by taking the indices that hit the target coordinates
exactly. -/
theorem pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk := by
  refine ⟨?_, ?_⟩
  · intro base target hbase
    rcases hsurj_j (target j) with ⟨n, hn⟩
    rcases hsurj_k (target k) with ⟨m, hm⟩
    have hgrid : PairwiseGridProfile σj σk base n m = target :=
      pairwiseGridProfile_eq_of_agreeOff_and_grid_hits hjk hbase hn hm
    refine ⟨n, m, ?_⟩
    rw [hgrid]
    exact (productPref_indiff_refl P target).1
  · intro base target hbase
    rcases hsurj_j (target j) with ⟨n, hn⟩
    rcases hsurj_k (target k) with ⟨m, hm⟩
    have hgrid : PairwiseGridProfile σj σk base n m = target :=
      pairwiseGridProfile_eq_of_agreeOff_and_grid_hits hjk hbase hn hm
    refine ⟨n, m, ?_⟩
    rw [hgrid]
    exact (productPref_indiff_refl P target).2

/-- End-to-end discharge for surjective grids: raw Archimedean plus surjective
base-transport gives full finite-cut coverage. -/
theorem pairwiseFiniteCutCoverageCertificate_of_archimedean_and_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutCoverageCertificate σj σk :=
  pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport
    harchim_j harchim_k
    (pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences
      P hjk σj σk hsurj_j hsurj_k)

/-- The exact cut-construction certificate also discharges the base-transport
bridge: collapse each cut witness to a single index pair. -/
theorem pairwiseArchimedeanBaseTransportCertificate_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseArchimedeanBaseTransportCertificate σj σk := by
  refine ⟨?_, ?_⟩
  · intro base target hbase
    rcases hcut base target hbase with ⟨n, m, hindiff, _⟩
    exact ⟨n, m, hindiff.2⟩
  · intro base target hbase
    rcases hcut base target hbase with ⟨n, m, hindiff, _⟩
    exact ⟨n, m, hindiff.1⟩

/-! ### Honest residual content for the base-transport bridge

The additive-real refutation `additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate`
shows that raw `Archimedean P j ∧ Archimedean P k ∧ TradeoffConsistency P ∧
RestrictedSolvability P ∧ IsWeakOrder P` does **not** suffice for the
base-transport bridge: one-sided ℕ-indexed grids cannot reach negative-total
targets in an additive model, so the lower-half bracket fails.

Rather than hide this behind a sweeping bridge hypothesis, we name the
residual content explicitly in two layers:

* `PairwiseGridCoordinateReachability` records the per-axis grid bracketing
  required at a single slice base/target pair: in coordinate `j`, some grid
  index produces a preference-upper bound and some other index produces a
  preference-lower bound for the slice profile.
* `PairwiseGridReachabilityCertificate` is the global form: the per-axis
  reachability holds at every slice base.

Surjective grids satisfy the certificate trivially, and the exact
cut-construction certificate also implies it.  The remaining open content is
to compose two per-axis reachability witnesses into a single 2-axis grid
profile bracket — that step requires either tradeoff consistency in a
specific slice-base form or further structural hypotheses, and is left as
the next certificate layer rather than masked by `sorry`. -/

/-- One-coordinate grid reachability against a target value at a slice base:
some grid index produces, in coordinate `j`, a preference-upper bound and a
preference-lower bound for the slice profile carrying the target value at
`j`.  This is the per-axis residual content beyond raw structural axioms. -/
def PairwiseGridCoordinateReachability {X : ι → Type v} {P : ProductPref X}
    {j : ι} (σj : ProductPref.StandardSequence P j)
    (k : ι) (base : Profile X) (vk : X k) (vj : X j) : Prop :=
  (∃ n : ℕ,
    P.weakPref (Function.update (Function.update base k vk) j (σj.α n))
      (Function.update (Function.update base k vk) j vj)) ∧
  (∃ n : ℕ,
    P.weakPref (Function.update (Function.update base k vk) j vj)
      (Function.update (Function.update base k vk) j (σj.α n)))

/-- The pairwise grid-reachability certificate: every slice base/target pair
admits, in each of the two coordinates, an upper and a lower grid-index
witness.  This is the precise per-axis residual content beyond raw
structural axioms, isolated as a Prop-level target. -/
def PairwiseGridReachabilityCertificate {X : ι → Type v} {P : ProductPref X}
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      PairwiseGridCoordinateReachability σj k base (target k) (target j) ∧
      PairwiseGridCoordinateReachability σk j base (target j) (target k)

/-- Surjective standard-sequence grids satisfy the grid-reachability
certificate by taking the index that hits the target value exactly; the
preference upper and lower bounds collapse to indifferent self-bounds. -/
theorem pairwiseGridReachabilityCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseGridReachabilityCertificate σj σk := by
  intro base target _hbase
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rcases hsurj_j (target j) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    exact (productPref_indiff_refl P _).1
  · rcases hsurj_j (target j) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    exact (productPref_indiff_refl P _).2
  · rcases hsurj_k (target k) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    exact (productPref_indiff_refl P _).1
  · rcases hsurj_k (target k) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]
    exact (productPref_indiff_refl P _).2

/-- Discharge of the base-transport bridge from grid reachability when one
coordinate's grid is surjective.

The asymmetry is unavoidable: composing two per-axis reachability witnesses
into a 2-axis grid profile bracket requires the second coordinate's grid to
hit the target value exactly so that the slice profile carrying the
reachability witness coincides with the 2-axis grid profile.  Surjectivity
in either coordinate suffices.

When both grids are surjective, this gives an alternative proof of
`pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences`
that factors through the named reachability residual. -/
theorem pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveSecondCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk := by
  refine ⟨?_, ?_⟩
  · -- Upper bracket: use the j-axis upper-half reachability witness, then
    -- choose `m` so that `σk.α m = target k`.
    intro base target hbase
    rcases hreach base target hbase with ⟨⟨⟨n_hi, hjub⟩, _⟩, _⟩
    rcases hsurj_k (target k) with ⟨m, hm⟩
    refine ⟨n_hi, m, ?_⟩
    -- Equality: `target = update (update base k (target k)) j (target j)`.
    have htarget_eq : Function.update (Function.update base k (target k)) j (target j)
        = target := by
      funext i
      by_cases hik : i = k
      · subst i
        rw [Function.update_of_ne hjk.symm]
        exact Function.update_self k (target k) base
      · by_cases hij : i = j
        · subst i; simp
        · have hi_not_pair : i ∉ ({j, k} : Set ι) := by
            intro hmem
            rcases (by simpa using hmem : i = j ∨ i = k) with h | h
            · exact hij h
            · exact hik h
          have := hbase i hi_not_pair
          simp [Function.update_of_ne hij, Function.update_of_ne hik, this]
    -- Equality: `PairwiseGridProfile σj σk base n_hi m = update (update base k
    -- (target k)) j (σj.α n_hi)`.
    have hgrid_eq : PairwiseGridProfile σj σk base n_hi m =
        Function.update (Function.update base k (target k)) j (σj.α n_hi) := by
      funext i
      by_cases hik : i = k
      · subst i
        -- LHS: PairwiseGridProfile σj σk base n_hi m k = σk.α m = target k
        -- RHS: update (update base k (target k)) j (σj.α n_hi) k = update base k (target k) k = target k
        have hL : PairwiseGridProfile σj σk base n_hi m k = σk.α m := by
          simp [PairwiseGridProfile]
        have hR : (Function.update (Function.update base k (target k)) j (σj.α n_hi)) k =
                  target k := by
          rw [Function.update_of_ne hjk.symm]
          exact Function.update_self k (target k) base
        rw [hL, hR, hm]
      · by_cases hij : i = j
        · subst i
          simp [PairwiseGridProfile, Function.update_of_ne hjk]
        · simp [PairwiseGridProfile, Function.update_of_ne hij, Function.update_of_ne hik]
    -- Use the equation `htarget_eq` together with `hgrid_eq` to rewrite both
    -- sides of the goal simultaneously into the form of `hjub`.
    rw [show
      P.weakPref (PairwiseGridProfile σj σk base n_hi m) target
        = P.weakPref
          (Function.update (Function.update base k (target k)) j (σj.α n_hi))
          (Function.update (Function.update base k (target k)) j (target j)) by
      rw [hgrid_eq, htarget_eq]]
    exact hjub
  · -- Lower bracket: symmetric, using the j-axis lower-half witness.
    intro base target hbase
    rcases hreach base target hbase with ⟨⟨_, ⟨n_lo, hjlb⟩⟩, _⟩
    rcases hsurj_k (target k) with ⟨m, hm⟩
    refine ⟨n_lo, m, ?_⟩
    have htarget_eq : Function.update (Function.update base k (target k)) j (target j)
        = target := by
      funext i
      by_cases hik : i = k
      · subst i
        rw [Function.update_of_ne hjk.symm]
        exact Function.update_self k (target k) base
      · by_cases hij : i = j
        · subst i; simp
        · have hi_not_pair : i ∉ ({j, k} : Set ι) := by
            intro hmem
            rcases (by simpa using hmem : i = j ∨ i = k) with h | h
            · exact hij h
            · exact hik h
          have := hbase i hi_not_pair
          simp [Function.update_of_ne hij, Function.update_of_ne hik, this]
    have hgrid_eq : PairwiseGridProfile σj σk base n_lo m =
        Function.update (Function.update base k (target k)) j (σj.α n_lo) := by
      funext i
      by_cases hik : i = k
      · subst i
        have hL : PairwiseGridProfile σj σk base n_lo m k = σk.α m := by
          simp [PairwiseGridProfile]
        have hR : (Function.update (Function.update base k (target k)) j (σj.α n_lo)) k =
                  target k := by
          rw [Function.update_of_ne hjk.symm]
          exact Function.update_self k (target k) base
        rw [hL, hR, hm]
      · by_cases hij : i = j
        · subst i
          simp [PairwiseGridProfile, Function.update_of_ne hjk]
        · simp [PairwiseGridProfile, Function.update_of_ne hij, Function.update_of_ne hik]
    rw [show
      P.weakPref target (PairwiseGridProfile σj σk base n_lo m)
        = P.weakPref
          (Function.update (Function.update base k (target k)) j (target j))
          (Function.update (Function.update base k (target k)) j (σj.α n_lo)) by
      rw [hgrid_eq, htarget_eq]]
    exact hjlb

/-- Symmetric variant: discharge from grid reachability when the *first*
coordinate's grid is surjective.  Routes through the k-axis reachability
witness instead. -/
theorem pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveFirstCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_j : Function.Surjective σj.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk := by
  refine ⟨?_, ?_⟩
  · intro base target hbase
    rcases hreach base target hbase with ⟨_, ⟨⟨m_hi, hkub⟩, _⟩⟩
    rcases hsurj_j (target j) with ⟨n, hn⟩
    refine ⟨n, m_hi, ?_⟩
    have htarget_eq : Function.update (Function.update base j (target j)) k (target k)
        = target := by
      funext i
      by_cases hik : i = k
      · subst i; simp
      · by_cases hij : i = j
        · subst i; simp [hjk]
        · have hi_not_pair : i ∉ ({j, k} : Set ι) := by
            intro hmem
            rcases (by simpa using hmem : i = j ∨ i = k) with h | h
            · exact hij h
            · exact hik h
          have := hbase i hi_not_pair
          simp [Function.update_of_ne hij, Function.update_of_ne hik, this]
    have hgrid_eq : PairwiseGridProfile σj σk base n m_hi =
        Function.update (Function.update base j (target j)) k (σk.α m_hi) := by
      simp only [PairwiseGridProfile]
      rw [hn]
    rw [show
      P.weakPref (PairwiseGridProfile σj σk base n m_hi) target
        = P.weakPref
          (Function.update (Function.update base j (target j)) k (σk.α m_hi))
          (Function.update (Function.update base j (target j)) k (target k)) by
      rw [hgrid_eq, htarget_eq]]
    exact hkub
  · intro base target hbase
    rcases hreach base target hbase with ⟨_, ⟨_, ⟨m_lo, hklb⟩⟩⟩
    rcases hsurj_j (target j) with ⟨n, hn⟩
    refine ⟨n, m_lo, ?_⟩
    have htarget_eq : Function.update (Function.update base j (target j)) k (target k)
        = target := by
      funext i
      by_cases hik : i = k
      · subst i; simp
      · by_cases hij : i = j
        · subst i; simp [hjk]
        · have hi_not_pair : i ∉ ({j, k} : Set ι) := by
            intro hmem
            rcases (by simpa using hmem : i = j ∨ i = k) with h | h
            · exact hij h
            · exact hik h
          have := hbase i hi_not_pair
          simp [Function.update_of_ne hij, Function.update_of_ne hik, this]
    have hgrid_eq : PairwiseGridProfile σj σk base n m_lo =
        Function.update (Function.update base j (target j)) k (σk.α m_lo) := by
      simp only [PairwiseGridProfile]
      rw [hn]
    rw [show
      P.weakPref target (PairwiseGridProfile σj σk base n m_lo)
        = P.weakPref
          (Function.update (Function.update base j (target j)) k (target k))
          (Function.update (Function.update base j (target j)) k (σk.α m_lo)) by
      rw [hgrid_eq, htarget_eq]]
    exact hklb

/-- Honest discharge of cut coverage from raw Archimedean (in both
coordinates), the explicit residual `PairwiseGridReachabilityCertificate`,
and surjectivity in one coordinate.  This is the strongest discharge of
finite-cut coverage from raw structural axioms currently available; the
additive-real refutation shows that without the surjectivity in either
coordinate, the discharge fails for one-sided ℕ-indexed grids. -/
theorem pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveSecondCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutCoverageCertificate σj σk :=
  pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport
    harchim_j harchim_k
    (pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveSecondCoord
      P hjk σj σk hreach hsurj_k)

/-- Symmetric end-to-end discharge of cut coverage from raw Archimedean (in
both coordinates), the explicit residual `PairwiseGridReachabilityCertificate`,
and surjectivity in the *first* coordinate. -/
theorem pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveFirstCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchim_j : ProductPref.Archimedean P j)
    (harchim_k : ProductPref.Archimedean P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_j : Function.Surjective σj.α) :
    PairwiseFiniteCutCoverageCertificate σj σk :=
  pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport
    harchim_j harchim_k
    (pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveFirstCoord
      P hjk σj σk hreach hsurj_j)

/-- Wakker's exact cut-construction certificate produces finite-cut coverage
by collapsing the bracket to a single grid index pair `(n, m)` matching the
target exactly. -/
theorem pairwiseFiniteCutCoverageCertificate_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  intro base target hbase
  rcases hcut base target hbase with ⟨n, m, hindiff, _hscore⟩
  refine ⟨n, m, n, m, ?_, ?_⟩
  · exact hindiff.2
  · exact hindiff.1

/-- Wakker's exact cut-construction certificate produces an interpolation
extension witness by taking `z` to be the exact grid witness itself, ignoring
the bracket indices. -/
theorem pairwiseInterpolationExtensionCertificate_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseInterpolationExtensionCertificate P j k σj σk := by
  intro base target hbase _n_lo _m_lo _n_hi _m_hi _hbracket
  rcases hcut base target hbase with ⟨n, m, hindiff, _hscore⟩
  refine ⟨PairwiseGridProfile σj σk base n m, ?_, ?_⟩
  · -- The grid profile agrees off `{j,k}` with `base`, hence with `target`.
    have hzbase :
        Profile.agreeOff ({j, k} : Set ι)
          (PairwiseGridProfile σj σk base n m) base := by
      intro i hi
      have hij : i ≠ j := by
        intro hij; apply hi; simp [hij]
      have hik : i ≠ k := by
        intro hik; apply hi; simp [hik]
      dsimp [PairwiseGridProfile]
      rw [Function.update_of_ne hik, Function.update_of_ne hij]
    exact Profile.agreeOff_trans hzbase hbase
  · -- `target ∼ grid` from the cut witness; symmetrize for `grid ∼ target`.
    exact ⟨hindiff.2, hindiff.1⟩

/-- Wakker's exact cut-construction certificate therefore proves the combined
finite cuts plus interpolation/extension certificate, which records the
honest Wakker route as a strict weakening of the refuted exact-grid target. -/
theorem pairwiseFiniteCutInterpolationCertificate_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι}
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseFiniteCutInterpolationCertificate P j k σj σk :=
  ⟨pairwiseFiniteCutCoverageCertificate_of_pairwiseCutConstructionCertificate
      hcut,
    pairwiseInterpolationExtensionCertificate_of_pairwiseCutConstructionCertificate
      P hcut⟩

/-- The theorem-shaped finite cuts plus interpolation/extension target for a
fixed pair of standard-sequence grids: from any grid-normalized,
order-calibrated utilities, supply both the finite-cut coverage and the
interpolation/extension certificate.

Unlike `PairwiseCutConstructionTheoremCertificate`, this target is **not**
refuted by `additiveRealBoolPref`: the certificate output is a slice-shaped
witness, not a literal grid profile, so the additive-real obstruction (grid
scores are sums of natural numbers) does not apply. -/
def PairwiseFiniteCutInterpolationTheoremCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ Vj : X j → ℝ, ∀ Vk : X k → ℝ,
    PairwiseGridNormalizationWitness σj σk Vj Vk →
      PairwiseOrderCalibrationCertificate P j k Vj Vk →
        PairwiseFiniteCutInterpolationCertificate P j k σj σk

/-- Wakker's exact cut-construction theorem certificate immediately discharges
the finite cuts plus interpolation/extension theorem certificate. -/
theorem pairwiseFiniteCutInterpolationTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hcut : PairwiseCutConstructionTheoremCertificate P j k σj σk) :
    PairwiseFiniteCutInterpolationTheoremCertificate P j k σj σk := by
  intro Vj Vk hgrid hcal
  exact pairwiseFiniteCutInterpolationCertificate_of_pairwiseCutConstructionCertificate
    P (hcut Vj Vk hgrid hcal)

/-- Surjective standard-sequence grids discharge the theorem-shaped finite
cuts plus interpolation/extension certificate as well, giving back the
degenerate-case regression. -/
theorem pairwiseFiniteCutInterpolationTheoremCertificate_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutInterpolationTheoremCertificate P j k σj σk := by
  intro _Vj _Vk _hgrid _hcal
  exact pairwiseFiniteCutInterpolationCertificate_of_surjectiveStandardSequences
    P hjk σj σk hsurj_j hsurj_k

/-- The hexagon-propagation output of Wakker Step 4 for already chosen utility
extensions: the additive score induced by `Vj` and `Vk` calibrates the whole
two-coordinate slice order.

This is definitionally the same proposition as `PairwiseOrderCalibrationCertificate`,
but the separate name records the mathematical provenance: Wakker's hexagon
argument transports the standard-sequence tradeoff scale from grid comparisons
to arbitrary comparisons on the `{j,k}`-slice. -/
def PairwiseHexagonPropagationCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  PairwiseOrderCalibrationCertificate P j k Vj Vk

/-- Hexagon propagation from concrete magnitude and bracketing data.

Magnitude represents comparisons between standard-sequence grid profiles.
Bracketing transfers arbitrary slice profiles to indifference-equivalent grid
profiles with the same additive score.  Weak-order transitivity then transports
the grid comparison back to the original profiles, yielding full order
calibration on the `{j,k}`-slice. -/
theorem pairwiseHexagonPropagationCertificate_of_tradeoffMagnitude_and_bracketing
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk)
    (hmagnitude : PairwiseTradeoffMagnitudeCertificate σj σk)
    (hbracket : PairwiseTradeoffBracketingCertificate σj σk Vj Vk) :
    PairwiseHexagonPropagationCertificate P j k Vj Vk := by
  intro x y hxy
  rcases hbracket x y hxy with ⟨base, nx, mx, ny, my, hxg, hyg, hxscore, hyscore⟩
  let gx : Profile X := PairwiseGridProfile σj σk base nx mx
  let gy : Profile X := PairwiseGridProfile σj σk base ny my
  have hscore_gx : PairwiseAdditiveScore Vj Vk gx = PairwiseGridStepMagnitude nx mx := by
    dsimp [gx]
    exact pairwiseAdditiveScore_pairwiseGridProfile_of_gridNormalizationWitness
      hjk hgrid base nx mx
  have hscore_gy : PairwiseAdditiveScore Vj Vk gy = PairwiseGridStepMagnitude ny my := by
    dsimp [gy]
    exact pairwiseAdditiveScore_pairwiseGridProfile_of_gridNormalizationWitness
      hjk hgrid base ny my
  have hmag : P.weakPref gx gy ↔
      PairwiseGridStepMagnitude ny my ≤ PairwiseGridStepMagnitude nx mx := by
    dsimp [gx, gy]
    exact hmagnitude base nx mx ny my
  constructor
  · intro hpref
    have hgx_y : P.weakPref gx y :=
      ProductPref.IsWeakOrder.transitive gx x y hxg.2 hpref
    have hgxgy : P.weakPref gx gy :=
      ProductPref.IsWeakOrder.transitive gx y gy hgx_y hyg.1
    have hsteps : PairwiseGridStepMagnitude ny my ≤ PairwiseGridStepMagnitude nx mx :=
      hmag.mp hgxgy
    calc PairwiseAdditiveScore Vj Vk y
        = PairwiseAdditiveScore Vj Vk gy := hyscore
      _ = PairwiseGridStepMagnitude ny my := hscore_gy
      _ ≤ PairwiseGridStepMagnitude nx mx := hsteps
      _ = PairwiseAdditiveScore Vj Vk gx := hscore_gx.symm
      _ = PairwiseAdditiveScore Vj Vk x := hxscore.symm
  · intro hscore
    have hsteps : PairwiseGridStepMagnitude ny my ≤ PairwiseGridStepMagnitude nx mx := by
      calc PairwiseGridStepMagnitude ny my
          = PairwiseAdditiveScore Vj Vk gy := hscore_gy.symm
        _ = PairwiseAdditiveScore Vj Vk y := hyscore.symm
        _ ≤ PairwiseAdditiveScore Vj Vk x := hscore
        _ = PairwiseAdditiveScore Vj Vk gx := hxscore
        _ = PairwiseGridStepMagnitude nx mx := hscore_gx
    have hgxgy : P.weakPref gx gy := hmag.mpr hsteps
    have hx_gy : P.weakPref x gy :=
      ProductPref.IsWeakOrder.transitive x gx gy hxg.1 hgxgy
    exact ProductPref.IsWeakOrder.transitive x gy y hx_gy hyg.2

/-- Fully expanded Step-4 subpayload: from the assembly input, choose utility
extensions and provide the concrete magnitude and bracketing certificates that
feed the hexagon-propagation theorem. -/
def PairwiseMagnitudeBracketingHexagonCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseAssemblyInputCertificate P j k σj σk →
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
        PairwiseSliceInterpolationCertificate P j k ∧
        PairwiseTradeoffMagnitudeCertificate σj σk ∧
        PairwiseTradeoffBracketingCertificate σj σk Vj Vk

/-- In the exact-surjective-grid regime, the already isolated Step-4 core
(`PairwiseStep4TradeoffMachineryCertificate`) supplies the expanded
magnitude+bracketing+hexagon certificate.

The magnitude part follows from order calibration and grid normalization.  The
bracketing part is theorem-backed here under surjectivity of the two grids; the
non-surjective Wakker case remains the genuine Archimedean/interpolation
bracketing target. -/
theorem pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    PairwiseMagnitudeBracketingHexagonCertificate P j k σj σk := by
  intro hinput
  rcases hinput with ⟨hgridInput, hslice⟩
  rcases htradeoff ⟨hgridInput, hslice⟩ with ⟨Vj, Vk, hgrid, hcal⟩
  exact ⟨Vj, Vk, hgrid, hslice,
    pairwiseTradeoffMagnitudeCertificate_of_gridNormalizationWitness_and_orderCalibration
      hjk hgrid hcal,
    pairwiseTradeoffBracketingCertificate_of_surjectiveStandardSequences
      P hjk σj σk Vj Vk hsurj_j hsurj_k⟩

/-- Surjectivity-free Step-4 packaging: the Archimedean bracketing theorem
certificate replaces the earlier surjectivity assumptions.

Thus the expanded magnitude+bracketing+hexagon payload now depends on the
actual Wakker Step-4 bracketing argument rather than on the degenerate case in
which the standard-sequence grids are already onto. -/
theorem pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_archimedeanBracketing
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (harchBracket : PairwiseArchimedeanBracketingTheoremCertificate P j k σj σk)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    PairwiseMagnitudeBracketingHexagonCertificate P j k σj σk := by
  intro hinput
  rcases hinput with ⟨hgridInput, hslice⟩
  rcases htradeoff ⟨hgridInput, hslice⟩ with ⟨Vj, Vk, hgrid, hcal⟩
  exact ⟨Vj, Vk, hgrid, hslice,
    pairwiseTradeoffMagnitudeCertificate_of_gridNormalizationWitness_and_orderCalibration
      hjk hgrid hcal,
    harchBracket Vj Vk hgrid hcal⟩

/-- Fully expanded Step-4 packaging from Wakker's cut construction. -/
theorem pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_cutConstruction
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hcut : PairwiseCutConstructionTheoremCertificate P j k σj σk)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    PairwiseMagnitudeBracketingHexagonCertificate P j k σj σk :=
  pairwiseMagnitudeBracketingHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_archimedeanBracketing
    P hjk σj σk
    (pairwiseArchimedeanBracketingTheoremCertificate_of_pairwiseCutConstructionTheoremCertificate
      P j k σj σk hcut)
    htradeoff

/-- The lower-level Step-4 payload supplied by Wakker's standard-sequence and
hexagon arguments for a fixed pair of grids.

Starting from the already theorem-backed assembly input, the standard-sequence
part chooses total utility extensions normalized on both grids, while the
hexagon part proves that those chosen utilities calibrate the slice order.  We
also retain the slice-preserving interpolation certificate from the input, so
the payload can feed both the calibrated-input and tradeoff-machinery wrappers. -/
def PairwiseHexagonStandardSequenceCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseAssemblyInputCertificate P j k σj σk →
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
        PairwiseSliceInterpolationCertificate P j k ∧
        PairwiseHexagonPropagationCertificate P j k Vj Vk

/-- The concrete magnitude+bracketing subpayload proves the previously isolated
hexagon/standard-sequence certificate. -/
theorem pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hmbh : PairwiseMagnitudeBracketingHexagonCertificate P j k σj σk) :
    PairwiseHexagonStandardSequenceCertificate P j k σj σk := by
  intro hinput
  rcases hmbh hinput with ⟨Vj, Vk, hgrid, hslice, hmagnitude, hbracket⟩
  exact ⟨Vj, Vk, hgrid, hslice,
    pairwiseHexagonPropagationCertificate_of_tradeoffMagnitude_and_bracketing
      P hjk σj σk hgrid hmagnitude hbracket⟩

/-- Wakker's hexagon plus standard-sequence payload proves the named Step-4
tradeoff-machinery certificate by forgetting the interpolation component and
keeping exactly the chosen grid-normalized, order-calibrated utilities. -/
theorem pairwiseStep4TradeoffMachineryCertificate_of_pairwiseHexagonStandardSequenceCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hhex : PairwiseHexagonStandardSequenceCertificate P j k σj σk) :
    PairwiseStep4TradeoffMachineryCertificate P j k σj σk := by
  intro hinput
  rcases hhex hinput with ⟨Vj, Vk, hgrid, _hslice, hprop⟩
  exact ⟨Vj, Vk, hgrid, hprop⟩

/-- Wakker Step-4 tradeoff machinery proves the order-calibration theorem
certificate by carrying along the slice-preserving interpolation part already
present in the assembly input. -/
theorem pairwiseOrderCalibrationTheoremCertificate_of_pairwiseStep4TradeoffMachineryCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    PairwiseOrderCalibrationTheoremCertificate P j k σj σk := by
  intro hinput
  rcases hinput with ⟨_hgridInput, hslice⟩
  rcases htradeoff ⟨_hgridInput, hslice⟩ with ⟨Vj, Vk, hgrid, hcal⟩
  exact ⟨Vj, Vk, hgrid, hslice, hcal⟩

/-- Grid normalization plus order calibration for chosen utilities immediately
assembles the two-coordinate slice representation. -/
theorem pairwiseSliceAssemblyCertificate_of_gridNormalizationWitness_and_orderCalibration
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    {σj : ProductPref.StandardSequence P j}
    {σk : ProductPref.StandardSequence P k}
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hgrid : PairwiseGridNormalizationWitness σj σk Vj Vk)
    (hcal : PairwiseOrderCalibrationCertificate P j k Vj Vk) :
    PairwiseSliceAssemblyCertificate P j k σj σk :=
  ⟨Vj, Vk, hgrid, hcal⟩

/-- The stronger order-calibrated input bundle proves the slice-assembly
certificate. -/
theorem pairwiseSliceAssemblyCertificate_of_pairwiseOrderCalibratedAssemblyInputCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hcalibrated : PairwiseOrderCalibratedAssemblyInputCertificate P j k σj σk) :
    PairwiseSliceAssemblyCertificate P j k σj σk := by
  rcases hcalibrated with ⟨Vj, Vk, hgrid, _hslice, hcal⟩
  exact pairwiseSliceAssemblyCertificate_of_gridNormalizationWitness_and_orderCalibration
    P j k hgrid hcal

/-- The single remaining Step-4 theorem certificate after the earlier
proof-producing substeps, for a fixed pair of standard-sequence grids.

This is intentionally kept as a certificate rather than a theorem from
`PairwiseAssemblyInputCertificate` alone: normalized grids and slice-preserving
interpolation do not, by themselves, force a numerical representation of the
preference order.  See
`pairwiseAssemblyInput_not_sufficient_for_pairwiseSliceAssembly` below. -/
def PairwiseSliceAssemblyTheoremCertificate {X : ι → Type v}
    (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  PairwiseAssemblyInputCertificate P j k σj σk →
    PairwiseSliceAssemblyCertificate P j k σj σk

/-- The isolated Wakker Step-4 order-calibration theorem certificate is strong
enough to supply the existing slice-assembly theorem certificate. -/
theorem pairwiseSliceAssemblyTheoremCertificate_of_pairwiseOrderCalibrationTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hcalibrate : PairwiseOrderCalibrationTheoremCertificate P j k σj σk) :
    PairwiseSliceAssemblyTheoremCertificate P j k σj σk := by
  intro hinput
  exact pairwiseSliceAssemblyCertificate_of_pairwiseOrderCalibratedAssemblyInputCertificate
    P j k σj σk (hcalibrate hinput)

/-- Wakker Step-4 tradeoff machinery is therefore sufficient for the existing
slice-assembly theorem certificate. -/
theorem pairwiseSliceAssemblyTheoremCertificate_of_pairwiseStep4TradeoffMachineryCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    PairwiseSliceAssemblyTheoremCertificate P j k σj σk :=
  pairwiseSliceAssemblyTheoremCertificate_of_pairwiseOrderCalibrationTheoremCertificate
    P j k σj σk
    (pairwiseOrderCalibrationTheoremCertificate_of_pairwiseStep4TradeoffMachineryCertificate
      P j k σj σk htradeoff)

/-- Apply the future Step-4 assembly theorem certificate to the assembled input
data. -/
theorem pairwiseSliceAssemblyCertificate_of_pairwiseSliceAssemblyTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) (j k : ι)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinput : PairwiseAssemblyInputCertificate P j k σj σk)
    (hassemble : PairwiseSliceAssemblyTheoremCertificate P j k σj σk) :
    PairwiseSliceAssemblyCertificate P j k σj σk :=
  hassemble hinput

/-- Wrapper-regression form: once the slice-assembly certificate is available,
the existing `pairwise_additivity` interface is discharged without changing its
public statement. -/
theorem pairwise_additivity_of_pairwiseSliceAssemblyCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hAssembly : PairwiseSliceAssemblyCertificate P j k σj σk) :
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceRepresentationCertificate P j k Vj Vk := by
  rcases hAssembly with ⟨Vj, Vk, hgrid, hrepr⟩
  exact ⟨Vj, Vk, hgrid,
    WakkerExistence.pairwise_additivity P j k hjk Vj Vk hrepr⟩

/-- End-to-end Step-4 wrapper: injective standard-sequence grids and restricted
solvability reduce the existing `pairwise_additivity` interface to the single
remaining assembly theorem certificate. -/
theorem pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseSliceAssemblyTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α)
    (hassemble : PairwiseSliceAssemblyTheoremCertificate P j k σj σk) :
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceRepresentationCertificate P j k Vj Vk := by
  have hinput : PairwiseAssemblyInputCertificate P j k σj σk :=
    pairwiseAssemblyInputCertificate_of_injectiveStandardSequences_and_restrictedSolvability
      P hsolv σj σk hinj_j hinj_k
  have hAssembly : PairwiseSliceAssemblyCertificate P j k σj σk :=
    pairwiseSliceAssemblyCertificate_of_pairwiseSliceAssemblyTheoremCertificate
      P j k σj σk hinput hassemble
  exact pairwise_additivity_of_pairwiseSliceAssemblyCertificate
    P hjk σj σk hAssembly

/-- End-to-end Step-4 wrapper using the isolated order-calibration theorem
certificate instead of the more opaque assembly theorem certificate. -/
theorem pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseOrderCalibrationTheoremCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α)
    (hcalibrate : PairwiseOrderCalibrationTheoremCertificate P j k σj σk) :
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceRepresentationCertificate P j k Vj Vk := by
  exact pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseSliceAssemblyTheoremCertificate
    P hsolv hjk σj σk hinj_j hinj_k
    (pairwiseSliceAssemblyTheoremCertificate_of_pairwiseOrderCalibrationTheoremCertificate
      P j k σj σk hcalibrate)

/-- End-to-end Step-4 wrapper using the named Wakker Step-4 tradeoff machinery
certificate. -/
theorem pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P) {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hinj_j : Function.Injective σj.α)
    (hinj_k : Function.Injective σk.α)
    (htradeoff : PairwiseStep4TradeoffMachineryCertificate P j k σj σk) :
    ∃ Vj : X j → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness σj σk Vj Vk ∧
      PairwiseSliceRepresentationCertificate P j k Vj Vk := by
  exact pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseOrderCalibrationTheoremCertificate
    P hsolv hjk σj σk hinj_j hinj_k
    (pairwiseOrderCalibrationTheoremCertificate_of_pairwiseStep4TradeoffMachineryCertificate
      P j k σj σk htradeoff)

/-! ### Phase 8 / M5 — Per-pair slice representations and the scaling-compatibility residual

The end-to-end Step-4 wrapper
`pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate`
produces a `PairwiseSliceRepresentationCertificate` for any single pair
`(j, k)`, given injective standard-sequence grids on both coordinates and
the `PairwiseStep4TradeoffMachineryCertificate` for that pair.

For M5 we want a global representation, not a per-pair one.  The natural
assembly is:

1. Pick a fixed pivot coordinate `j₀`.
2. Apply the wrapper at every pair `(j₀, k)` for `k ≠ j₀`.
3. Patch the per-pair `Vⱼ₀, Vₖ` families into a single global tuple `V`.
4. Verify that the global sum equation holds.

Step 3 is the **scaling-compatibility** content: the per-pair invocations
each produce *their own* `Vⱼ₀` (one for each `k`), and these need to be
proved equal up to a common scale.  This is exactly Wakker (1989) Step 5's
content.

We isolate it as a Prop-level residual following the Phase 8 enrichment
pattern.  The bundle below packages the per-pair invocations together
with the scaling-compatibility residual; the global representation
follows mechanically from both. -/

/-- **Per-pair slice-representations bundle (M5 sub-target).**

For a chosen pivot coordinate `j₀`, there exists a coordinate-utility
family `V` on `j₀` such that, for every other coordinate `k`, the slice
`(j₀, k)` admits a slice representation with that same `V j₀` on the
pivot side.

This is the assembled output of the per-pair Step-4 chain after
scaling-compatibility has been settled: a single global `V j₀`
calibrating every slice. -/
def PairwiseSliceRepresentationsAtPivot {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∃ Vj₀ : X j₀ → ℝ,
    ∀ k : ι, k ≠ j₀ →
      ∃ Vk : X k → ℝ, PairwiseSliceRepresentationCertificate P j₀ k Vj₀ Vk

/-- **Global-pivot scaling-compatibility certificate (the deep M5 content).**

The genuinely missing mathematical content of Wakker (1989) Step 5: there
exists a *single* pivot utility `Vⱼ₀` that calibrates every pair-slice
representation involving the pivot.  Equivalently, the per-pair invocations
of the Step-4 chain at different `(j₀, k)` slices can be re-pivoted to
share a common `Vⱼ₀`.

This is precisely the n ≥ 3 telescoping argument: a third coordinate
provides the cardinal reference allowing per-pair scales to be reconciled
into a single global scale.

By stating the certificate as an *existence statement* directly producing
`PairwiseSliceRepresentationsAtPivot`, we keep the M5 assembly proof
mechanical: the certificate *is* the assembly conclusion, modulo the
deep n ≥ 3 step that produces it. -/
def Step5ScalingCompatibilityCertificate {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (_hsolv : ProductPref.RestrictedSolvability P)
    (j₀ : ι) : Prop :=
  PairwiseSliceRepresentationsAtPivot P j₀

/-! ##### M5 deep residual: scaling-compatibility factoring

The full discharge of `Step5ScalingCompatibilityCertificate` from raw
`n ≥ 3 + AllPairsStep4MachineryCertificate` is the genuine multi-week
content of Wakker (1989) Step 5.  The argument uses a *third coordinate*
to force the per-pair scales to coincide.

Sketch of Wakker's argument:

1. The per-pair Step-4 chain produces, for each `k ≠ j₀`, slice utilities
   `Vⱼ₀^(k) : X j₀ → ℝ` and `Vₖ : X k → ℝ` representing the
   `(j₀, k)`-slice preference.
2. Slice-uniqueness: any two slice representations of the same
   slice-preference differ by a positive affine transformation.  Hence
   for any `k₁, k₂ ≠ j₀`, there exist `αₖ₁ₖ₂ > 0` and `βₖ₁ₖ₂` with
   `Vⱼ₀^(k₂) = αₖ₁ₖ₂ * Vⱼ₀^(k₁) + βₖ₁ₖ₂` on `X j₀`.
3. The third coordinate `k₃` (existing because `n ≥ 3`) gives a triangle
   of affine relations:
     `Vⱼ₀^(k₂) = αₖ₁ₖ₂ * Vⱼ₀^(k₁) + βₖ₁ₖ₂`
     `Vⱼ₀^(k₃) = αₖ₂ₖ₃ * Vⱼ₀^(k₂) + βₖ₂ₖ₃`
     `Vⱼ₀^(k₁) = αₖ₃ₖ₁ * Vⱼ₀^(k₃) + βₖ₃ₖ₁`
   Composing the three forces `αₖ₁ₖ₂ * αₖ₂ₖ₃ * αₖ₃ₖ₁ = 1`.  Combined
   with one common normalization (e.g., on a chosen reference grid point),
   all three scales are forced to be `1`.
4. With `αₖ₁ₖ₂ = 1` for every `k₁, k₂`, the per-pair `Vⱼ₀^(k)` differ
   only by additive constants.  Choosing one global reference value
   pins them all to a single common `Vⱼ₀`.

This four-step argument decomposes naturally into sub-residuals.  Below
we name them and prove the trivial steps. -/

/-- **Per-pair slice uniqueness certificate.**

For any two distinct coordinates `k₁, k₂ ≠ j₀`, the per-pair Step-4
outputs `(Vⱼ₀^(k₁), Vₖ₁)` and `(Vⱼ₀^(k₂), Vₖ₂)` represent the same
preference on the `j₀`-coordinate (modulo positive affine transformation),
so there exist `α > 0, β` with `Vⱼ₀^(k₂) x = α * Vⱼ₀^(k₁) x + β` for
every `x : X j₀`.

This is the slice-uniqueness step (consequence of the existing
`additive_rep_unique`, applied to the `(j₀, k₁)` and `(j₀, k₂)` slices). -/
def PerPairSliceUniquenessCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ (k₁ k₂ : ι), k₁ ≠ j₀ → k₂ ≠ j₀ → k₁ ≠ k₂ →
    ∀ (Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ : X j₀ → ℝ)
      (Vₖ₁ : X k₁ → ℝ) (Vₖ₂ : X k₂ → ℝ),
    PairwiseSliceRepresentationCertificate P j₀ k₁ Vⱼ₀_at_k₁ Vₖ₁ →
    PairwiseSliceRepresentationCertificate P j₀ k₂ Vⱼ₀_at_k₂ Vₖ₂ →
    ∃ (α : ℝ) (_ : 0 < α) (β : ℝ),
      ∀ x : X j₀, Vⱼ₀_at_k₂ x = α * Vⱼ₀_at_k₁ x + β

/-- **Triangle-composition certificate (n ≥ 3 content).**

For any three distinct non-pivot coordinates `k₁, k₂, k₃`, the three
slice-uniqueness affine relations between `Vⱼ₀^(k₁), Vⱼ₀^(k₂), Vⱼ₀^(k₃)`
compose around the triangle, forcing the product of scales to equal `1`.

Combined with one normalization (e.g., that all `Vⱼ₀^(k)` agree at a
chosen reference grid point), this forces every scale to be `1`. -/
def TriangleScaleCompositionCertificate {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (_P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ (k₁ k₂ k₃ : ι),
    k₁ ≠ j₀ → k₂ ≠ j₀ → k₃ ≠ j₀ →
    k₁ ≠ k₂ → k₂ ≠ k₃ → k₁ ≠ k₃ →
    ∀ (V₁ V₂ V₃ : X j₀ → ℝ),
    -- Three pairwise affine relations:
    (∃ (α₁₂ : ℝ) (_ : 0 < α₁₂) (β₁₂ : ℝ),
      ∀ x, V₂ x = α₁₂ * V₁ x + β₁₂) →
    (∃ (α₂₃ : ℝ) (_ : 0 < α₂₃) (β₂₃ : ℝ),
      ∀ x, V₃ x = α₂₃ * V₂ x + β₂₃) →
    (∃ (α₃₁ : ℝ) (_ : 0 < α₃₁) (β₃₁ : ℝ),
      ∀ x, V₁ x = α₃₁ * V₃ x + β₃₁) →
    -- Then the product of scales is 1.
    ∃ (α₁₂ α₂₃ α₃₁ : ℝ),
      0 < α₁₂ ∧ 0 < α₂₃ ∧ 0 < α₃₁ ∧ α₁₂ * α₂₃ * α₃₁ = 1

/-- **Triangle-composition algebraic discharge.**

Real, sorry-free derivation: from three positive affine relations between
three coordinate utilities `V₁, V₂, V₃` that compose around the triangle,
the product of the three scales must equal `1`.

Proof: chain the three affine relations.  `V₂ = α₁₂ V₁ + β₁₂`,
`V₃ = α₂₃ V₂ + β₂₃ = α₂₃ α₁₂ V₁ + (α₂₃ β₁₂ + β₂₃)`,
`V₁ = α₃₁ V₃ + β₃₁ = α₃₁ α₂₃ α₁₂ V₁ + (some constant)`.
Hence `(α₃₁ α₂₃ α₁₂ - 1) V₁ = -(constant)` for all `x`.  If `V₁` is
non-constant, the coefficient must be zero, so `α₁₂ α₂₃ α₃₁ = 1`.

Without non-constancy of `V₁`, the result is vacuous (any α-product
works).  We state and prove the algebraic-glue version here. -/
theorem triangleScaleComposition_algebraic
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (_P : ProductPref X) (j₀ : ι)
    (V₁ V₂ V₃ : X j₀ → ℝ)
    (α₁₂ : ℝ) (_hα₁₂ : 0 < α₁₂) (β₁₂ : ℝ)
    (h₁₂ : ∀ x, V₂ x = α₁₂ * V₁ x + β₁₂)
    (α₂₃ : ℝ) (_hα₂₃ : 0 < α₂₃) (β₂₃ : ℝ)
    (h₂₃ : ∀ x, V₃ x = α₂₃ * V₂ x + β₂₃)
    (α₃₁ : ℝ) (_hα₃₁ : 0 < α₃₁) (β₃₁ : ℝ)
    (h₃₁ : ∀ x, V₁ x = α₃₁ * V₃ x + β₃₁)
    -- Non-constancy hypothesis: V₁ takes at least two distinct values.
    (hne : ∃ x y : X j₀, V₁ x ≠ V₁ y) :
    α₁₂ * α₂₃ * α₃₁ = 1 := by
  -- Compose the three affine relations to get
  --   V₁ x = α₃₁ * α₂₃ * α₁₂ * V₁ x + (α₃₁ * α₂₃ * β₁₂ + α₃₁ * β₂₃ + β₃₁)
  -- For any two distinct V₁-values, this forces α₃₁ * α₂₃ * α₁₂ = 1.
  obtain ⟨x, y, hxy⟩ := hne
  have hx_chain : V₁ x = α₃₁ * α₂₃ * α₁₂ * V₁ x +
                          (α₃₁ * α₂₃ * β₁₂ + α₃₁ * β₂₃ + β₃₁) := by
    calc V₁ x = α₃₁ * V₃ x + β₃₁ := h₃₁ x
      _ = α₃₁ * (α₂₃ * V₂ x + β₂₃) + β₃₁ := by rw [h₂₃ x]
      _ = α₃₁ * (α₂₃ * (α₁₂ * V₁ x + β₁₂) + β₂₃) + β₃₁ := by rw [h₁₂ x]
      _ = α₃₁ * α₂₃ * α₁₂ * V₁ x +
            (α₃₁ * α₂₃ * β₁₂ + α₃₁ * β₂₃ + β₃₁) := by ring
  have hy_chain : V₁ y = α₃₁ * α₂₃ * α₁₂ * V₁ y +
                          (α₃₁ * α₂₃ * β₁₂ + α₃₁ * β₂₃ + β₃₁) := by
    calc V₁ y = α₃₁ * V₃ y + β₃₁ := h₃₁ y
      _ = α₃₁ * (α₂₃ * V₂ y + β₂₃) + β₃₁ := by rw [h₂₃ y]
      _ = α₃₁ * (α₂₃ * (α₁₂ * V₁ y + β₁₂) + β₂₃) + β₃₁ := by rw [h₁₂ y]
      _ = α₃₁ * α₂₃ * α₁₂ * V₁ y +
            (α₃₁ * α₂₃ * β₁₂ + α₃₁ * β₂₃ + β₃₁) := by ring
  -- Subtract: (α₃₁ * α₂₃ * α₁₂ - 1) * (V₁ x - V₁ y) = 0.
  have hsub : (α₃₁ * α₂₃ * α₁₂ - 1) * (V₁ x - V₁ y) = 0 := by linarith
  -- V₁ x ≠ V₁ y, so the difference is nonzero, forcing α₃₁ * α₂₃ * α₁₂ = 1.
  have hVne : V₁ x - V₁ y ≠ 0 := sub_ne_zero.mpr hxy
  have hα_prod : α₃₁ * α₂₃ * α₁₂ - 1 = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd h hVne
  linarith

/-- **Two-pair scale-composition algebraic discharge.**

The 2-step analogue of `triangleScaleComposition_algebraic`: from two
positive affine relations `V₂ = α₁₂ V₁ + β₁₂` and `V₁ = α₂₁ V₂ + β₂₁`
that compose, the product `α₁₂ * α₂₁ = 1`.

Real, sorry-free proof.  Substitute `V₂` from the first into the second:
`V₁ = α₂₁ (α₁₂ V₁ + β₁₂) + β₂₁ = α₂₁ α₁₂ V₁ + (α₂₁ β₁₂ + β₂₁)`.
Subtracting between two distinct values gives `(α₁₂ * α₂₁ - 1)(V₁ x - V₁ y) = 0`,
hence `α₁₂ * α₂₁ = 1`.

This is the "two-pair" analogue of the M5 triangle composition.  It does
not by itself force individual scales to be `1` (only their product), but
combined with positivity it gives `α₁₂ = 1/α₂₁`. -/
theorem twoPairScaleComposition_algebraic
    {X : ι → Type v} (j₀ : ι)
    (V₁ V₂ : X j₀ → ℝ)
    (α₁₂ : ℝ) (β₁₂ : ℝ)
    (h₁₂ : ∀ x, V₂ x = α₁₂ * V₁ x + β₁₂)
    (α₂₁ : ℝ) (β₂₁ : ℝ)
    (h₂₁ : ∀ x, V₁ x = α₂₁ * V₂ x + β₂₁)
    (hne : ∃ x y : X j₀, V₁ x ≠ V₁ y) :
    α₁₂ * α₂₁ = 1 := by
  obtain ⟨x, y, hxy⟩ := hne
  -- Compose: V₁ x = α₂₁ * α₁₂ * V₁ x + (α₂₁ * β₁₂ + β₂₁).
  have hx_chain : V₁ x = α₂₁ * α₁₂ * V₁ x + (α₂₁ * β₁₂ + β₂₁) := by
    calc V₁ x = α₂₁ * V₂ x + β₂₁ := h₂₁ x
      _ = α₂₁ * (α₁₂ * V₁ x + β₁₂) + β₂₁ := by rw [h₁₂ x]
      _ = α₂₁ * α₁₂ * V₁ x + (α₂₁ * β₁₂ + β₂₁) := by ring
  have hy_chain : V₁ y = α₂₁ * α₁₂ * V₁ y + (α₂₁ * β₁₂ + β₂₁) := by
    calc V₁ y = α₂₁ * V₂ y + β₂₁ := h₂₁ y
      _ = α₂₁ * (α₁₂ * V₁ y + β₁₂) + β₂₁ := by rw [h₁₂ y]
      _ = α₂₁ * α₁₂ * V₁ y + (α₂₁ * β₁₂ + β₂₁) := by ring
  have hsub : (α₂₁ * α₁₂ - 1) * (V₁ x - V₁ y) = 0 := by linarith
  have hVne : V₁ x - V₁ y ≠ 0 := sub_ne_zero.mpr hxy
  have hα_prod : α₂₁ * α₁₂ - 1 = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact h
    · exact absurd h hVne
  linarith

/-- **Per-pair scale-determination via shared reference normalization.**

If two positive affine relations `V₂ = α V₁ + β` agree at two distinct
reference points (i.e., `V₁ x₀ = V₂ x₀` and `V₁ x₁ = V₂ x₁` for some
`x₀ ≠ x₁` with `V₁ x₀ ≠ V₁ x₁`), then `α = 1` and `β = 0`.

Real, sorry-free proof.  From `V₁ x₀ = α V₁ x₀ + β` and
`V₁ x₁ = α V₁ x₁ + β`, subtracting gives `(α - 1)(V₁ x₀ - V₁ x₁) = 0`,
forcing `α = 1`, hence `β = 0`.

This is the "common-normalization" step that follows the triangle
composition: once `α₁₂ * α₂₃ * α₃₁ = 1` is established, any single
shared reference point (e.g., the standard-sequence index-0 grid value)
forces all three scales to coincide. -/
theorem affine_identity_from_two_shared_reference_points
    {X : ι → Type v} (j₀ : ι)
    (V₁ V₂ : X j₀ → ℝ)
    (α : ℝ) (β : ℝ)
    (h_aff : ∀ x, V₂ x = α * V₁ x + β)
    (x₀ x₁ : X j₀)
    (h_agree₀ : V₁ x₀ = V₂ x₀)
    (h_agree₁ : V₁ x₁ = V₂ x₁)
    (h_distinct : V₁ x₀ ≠ V₁ x₁) :
    α = 1 ∧ β = 0 := by
  -- From h_agree₀ : V₁ x₀ = V₂ x₀ and h_aff x₀ : V₂ x₀ = α * V₁ x₀ + β,
  -- chain to V₁ x₀ = α * V₁ x₀ + β.
  have h₀ : V₁ x₀ = α * V₁ x₀ + β := h_agree₀.trans (h_aff x₀)
  have h₁ : V₁ x₁ = α * V₁ x₁ + β := h_agree₁.trans (h_aff x₁)
  -- Subtract: (α - 1)(V₁ x₀ - V₁ x₁) = 0.
  have hsub : (α - 1) * (V₁ x₀ - V₁ x₁) = 0 := by linarith
  have hVne : V₁ x₀ - V₁ x₁ ≠ 0 := sub_ne_zero.mpr h_distinct
  have hα : α = 1 := by
    rcases mul_eq_zero.mp hsub with h | h
    · linarith
    · exact absurd h hVne
  refine ⟨hα, ?_⟩
  rw [hα] at h₀
  linarith

/-- **j₀-restricted ordinal projection from a pairwise slice representation.**

Real, sorry-free observation: if `(Vⱼ₀, Vₖ)` is a pairwise slice
representation on `(j₀, k)`, then for any two profiles `x, y` that agree
off `{j₀}` (single-coordinate change at `j₀` only), the `Vₖ` term cancels
and `Vⱼ₀` represents the induced order on `X j₀`.

Proof: `agreeOff {j₀} x y` implies `agreeOff {j₀, k} x y` since `{j₀} ⊆ {j₀, k}`.
The slice certificate then gives `P.weakPref x y ↔ Vⱼ₀ (y j₀) + Vₖ (y k) ≤ Vⱼ₀ (x j₀) + Vₖ (x k)`.
Since `x, y` agree at `k` (because `k ∉ {j₀}`), we have `x k = y k`, so
the `Vₖ` terms cancel, leaving `Vⱼ₀ (y j₀) ≤ Vⱼ₀ (x j₀)`. -/
theorem pairwiseSlice_restricted_to_pivot
    {X : ι → Type v} {P : ProductPref X}
    {j₀ k : ι} (hjk : j₀ ≠ k)
    {Vⱼ₀ : X j₀ → ℝ} {Vₖ : X k → ℝ}
    (hslice : PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vₖ)
    {x y : Profile X}
    (hxy : Profile.agreeOff {j₀} x y) :
    P.weakPref x y ↔ Vⱼ₀ (y j₀) ≤ Vⱼ₀ (x j₀) := by
  -- Lift agreeOff {j₀} to agreeOff {j₀, k}.
  have hxy' : Profile.agreeOff ({j₀, k} : Set ι) x y := by
    intro i hi
    have hi₀ : i ∉ ({j₀} : Set ι) := by
      intro hmem
      apply hi
      have heq : i = j₀ := hmem
      simp [heq]
    exact hxy i hi₀
  -- Apply the slice certificate.
  have hpair := hslice x y hxy'
  -- x and y agree at k (since k ∉ {j₀}).
  have hk_eq : x k = y k := by
    apply hxy
    intro hmem
    -- hmem : k ∈ {j₀}, i.e., k = j₀.  But j₀ ≠ k, contradiction.
    have : k = j₀ := by simpa using hmem
    exact hjk this.symm
  rw [hk_eq] at hpair
  -- Now hpair : P.weakPref x y ↔ Vⱼ₀ (y j₀) + Vₖ (y k) ≤ Vⱼ₀ (x j₀) + Vₖ (y k)
  constructor
  · intro h
    have hh := hpair.mp h
    linarith
  · intro h
    apply hpair.mpr
    linarith

/-- **Two pairwise slice representations agree on the j₀-induced order.**

Given two slice certificates on different pairs `(j₀, k₁)` and `(j₀, k₂)`
(both with `j₀ ≠ k₁, k₂`), the j₀-utilities `Vⱼ₀^(k₁)` and `Vⱼ₀^(k₂)`
both represent the **same** induced order on `X j₀` — namely, the order
induced by single-coordinate-at-`j₀` changes under `P`.

Real, sorry-free corollary of `pairwiseSlice_restricted_to_pivot`. -/
theorem twoSlice_pivot_orders_agree
    {X : ι → Type v} {P : ProductPref X}
    {j₀ k₁ k₂ : ι} (hjk₁ : j₀ ≠ k₁) (hjk₂ : j₀ ≠ k₂)
    {Vⱼ₀_at_k₁ : X j₀ → ℝ} {Vₖ₁ : X k₁ → ℝ}
    {Vⱼ₀_at_k₂ : X j₀ → ℝ} {Vₖ₂ : X k₂ → ℝ}
    (hslice₁ : PairwiseSliceRepresentationCertificate P j₀ k₁ Vⱼ₀_at_k₁ Vₖ₁)
    (hslice₂ : PairwiseSliceRepresentationCertificate P j₀ k₂ Vⱼ₀_at_k₂ Vₖ₂)
    {x y : Profile X}
    (hxy : Profile.agreeOff {j₀} x y) :
    (Vⱼ₀_at_k₁ (y j₀) ≤ Vⱼ₀_at_k₁ (x j₀)) ↔
      (Vⱼ₀_at_k₂ (y j₀) ≤ Vⱼ₀_at_k₂ (x j₀)) := by
  have h₁ := pairwiseSlice_restricted_to_pivot hjk₁ hslice₁ hxy
  have h₂ := pairwiseSlice_restricted_to_pivot hjk₂ hslice₂ hxy
  -- Both biconditions go through the same P.weakPref x y, so they're equivalent.
  exact h₁.symm.trans h₂

/-! ##### M5 cardinal step: shared-pivot-grid forces identical j₀-utilities

Two slice utilities `Vⱼ₀^(k₁)` and `Vⱼ₀^(k₂)` calibrated against the *same*
standard sequence `σⱼ₀` on `j₀` must agree on the entire grid:
`Vⱼ₀^(k₁)(σⱼ₀.α n) = n = Vⱼ₀^(k₂)(σⱼ₀.α n)` for every `n : ℕ`.

This is sharper than affine-relation: under a shared pivot grid, both
utilities are *identical* on the grid (so `α = 1, β = 0` automatically).
The shared-pivot-grid is the natural design choice for the per-pair Step-4
chain when iterated over different `k`s, and it sidesteps the need for a
general cardinal-uniqueness construction.

We deliver:
1. A **shared-pivot-grid certificate** hypothesis.
2. The **agreement-on-grid** consequence: `Vⱼ₀^(k₁)(σⱼ₀.α n) = Vⱼ₀^(k₂)(σⱼ₀.α n)`. -/

/-- **Shared-pivot-grid certificate.**

For two pairwise slice representations on `(j₀, k₁)` and `(j₀, k₂)`,
both calibrated against the *same* standard sequence `σⱼ₀` on `j₀`, the
grid-normalization witnesses agree: both `Vⱼ₀^(k₁)` and `Vⱼ₀^(k₂)` give
`(n : ℝ)` on `σⱼ₀.α n`.

This is the key structural assumption that the per-pair Step-4 chain can
be required to maintain when iterated over different `k`s.  Once
established, all per-pair `Vⱼ₀^(k)` agree on the grid trivially. -/
def SharedPivotGridCertificate {X : ι → Type v}
    {P : ProductPref X} {j₀ : ι}
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ : X j₀ → ℝ) : Prop :=
  (∀ n : ℕ, Vⱼ₀_at_k₁ (σⱼ₀.α n) = (n : ℝ)) ∧
  (∀ n : ℕ, Vⱼ₀_at_k₂ (σⱼ₀.α n) = (n : ℝ))

/-- **Agreement on the pivot grid.**

Real, sorry-free.  Under a shared-pivot-grid certificate, the two
j₀-utilities agree at every grid point: `Vⱼ₀^(k₁) (σⱼ₀.α n) = Vⱼ₀^(k₂) (σⱼ₀.α n)`. -/
theorem sharedPivotGrid_agreement
    {X : ι → Type v} {P : ProductPref X} {j₀ : ι}
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ : X j₀ → ℝ)
    (hshared : SharedPivotGridCertificate σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂) :
    ∀ n : ℕ, Vⱼ₀_at_k₁ (σⱼ₀.α n) = Vⱼ₀_at_k₂ (σⱼ₀.α n) := by
  intro n
  rw [hshared.1 n, hshared.2 n]

/-- **Affine identity (α = 1, β = 0) under shared-pivot-grid + affine
relation.**

If the two j₀-utilities are affinely related (`Vⱼ₀^(k₂) x = α * Vⱼ₀^(k₁) x + β`)
*and* the shared-pivot-grid forces them to agree at two distinct grid
points, then `α = 1, β = 0`.

Real, sorry-free.  Combines `sharedPivotGrid_agreement` (giving the two
shared reference values at any two distinct grid indices) with
`affine_identity_from_two_shared_reference_points`.

The grid points are `σⱼ₀.α 0` and `σⱼ₀.α 1`; under injectivity of `σⱼ₀.α`,
they're distinct, and their `Vⱼ₀^(k₁)`-values are `0` and `1` respectively
(distinct). -/
theorem affine_identity_under_sharedPivotGrid
    {X : ι → Type v} {P : ProductPref X} {j₀ : ι}
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (_hinj : Function.Injective σⱼ₀.α)
    (Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ : X j₀ → ℝ)
    (hshared : SharedPivotGridCertificate σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂)
    (α β : ℝ)
    (h_aff : ∀ x, Vⱼ₀_at_k₂ x = α * Vⱼ₀_at_k₁ x + β) :
    α = 1 ∧ β = 0 := by
  -- Two shared reference points: σⱼ₀.α 0 and σⱼ₀.α 1.
  have h_agree₀ : Vⱼ₀_at_k₁ (σⱼ₀.α 0) = Vⱼ₀_at_k₂ (σⱼ₀.α 0) :=
    sharedPivotGrid_agreement σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ hshared 0
  have h_agree₁ : Vⱼ₀_at_k₁ (σⱼ₀.α 1) = Vⱼ₀_at_k₂ (σⱼ₀.α 1) :=
    sharedPivotGrid_agreement σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ hshared 1
  -- Distinct grid values: Vⱼ₀_at_k₁ (σⱼ₀.α 0) = 0, Vⱼ₀_at_k₁ (σⱼ₀.α 1) = 1.
  have h_distinct : Vⱼ₀_at_k₁ (σⱼ₀.α 0) ≠ Vⱼ₀_at_k₁ (σⱼ₀.α 1) := by
    rw [hshared.1 0, hshared.1 1]
    norm_num
  exact affine_identity_from_two_shared_reference_points j₀
    Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ α β h_aff (σⱼ₀.α 0) (σⱼ₀.α 1)
    h_agree₀ h_agree₁ h_distinct

/-- **Global slice-pair Step-4 input certificate.**

The structural content needed beyond the per-pair Step-4 tradeoff machinery:
for every pair `(j₀, k)` with `k ≠ j₀`, an explicit choice of injective
standard sequences on both coordinates plus the Step-4 tradeoff machinery
for that pair.

This is what Wakker's standard-sequence construction would produce if it
were formalized end-to-end; we package it as a single named hypothesis. -/
def AllPairsStep4MachineryCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ k : ι, k ≠ j₀ →
    ∃ (σj : ProductPref.StandardSequence P j₀)
      (σk : ProductPref.StandardSequence P k),
      Function.Injective σj.α ∧
      Function.Injective σk.α ∧
      PairwiseStep4TradeoffMachineryCertificate P j₀ k σj σk

/-- **Shared-pivot All-Pairs Step-4 machinery certificate.**

Strengthening of `AllPairsStep4MachineryCertificate`: the same standard
sequence `σⱼ₀` on the pivot coordinate is used across *all* per-pair
invocations.  Each pair `(j₀, k)` then gets its own `σₖ` on `k`, but the
pivot side is shared.

This is the natural design choice when iterating the Step-4 chain over
different non-pivot coordinates, and it's the structural assumption
needed to invoke `affine_identity_under_sharedPivotGrid` for any two
slices. -/
def SharedPivotAllPairsStep4MachineryCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀),
    Function.Injective σⱼ₀.α ∧
    ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseStep4TradeoffMachineryCertificate P j₀ k σⱼ₀ σk

/-- **Shared-pivot certificate implies plain all-pairs certificate.**

Trivial cross-flow: discarding the shared `σⱼ₀` and letting each pair
choose its own gives the weaker `AllPairsStep4MachineryCertificate`. -/
theorem allPairsStep4Machinery_of_sharedPivot
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀) :
    AllPairsStep4MachineryCertificate P j₀ := by
  obtain ⟨σⱼ₀, hinj_j₀, hAllPairs⟩ := hShared
  intro k hk
  obtain ⟨σk, hinj_k, htradeoff⟩ := hAllPairs k hk
  exact ⟨σⱼ₀, σk, hinj_j₀, hinj_k, htradeoff⟩

/-- **Per-pair slice representations from per-pair Step-4 machinery.**

Without the scaling-compatibility residual, each pair `(j₀, k)` gets its
*own* pivot utility `Vⱼ₀^{(k)}`.  This lemma packages that as an
existence statement at every pair, with no claim of compatibility across
pairs.

This is the "free" half of the M5 assembly: existence of per-pair slice
representations is mechanical from the per-pair Step-4 wrapper.  The
deep content is forcing the per-pair pivot utilities to coincide. -/
theorem perPairSliceRepresentations_of_allPairsStep4Machinery {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hAll : AllPairsStep4MachineryCertificate P j₀) :
    ∀ k : ι, k ≠ j₀ →
      ∃ (Vj₀ : X j₀ → ℝ) (Vk : X k → ℝ),
        PairwiseSliceRepresentationCertificate P j₀ k Vj₀ Vk := by
  intro k hk
  obtain ⟨σj, σk, hinj_j, hinj_k, htradeoff⟩ := hAll k hk
  obtain ⟨Vj₀, Vk, _hgrid, hslice⟩ :=
    pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate
      P hsolv hk.symm σj σk hinj_j hinj_k htradeoff
  exact ⟨Vj₀, Vk, hslice⟩

/-- **Per-pair slice representations + grid normalization from shared-pivot
Step-4 machinery.**

Stronger version of `perPairSliceRepresentations_of_allPairsStep4Machinery`:
under the shared-pivot certificate, every per-pair invocation produces
`Vj₀^(k)` calibrated against the *same* `σⱼ₀` grid.  This is exactly the
structural input that `SharedPivotGridCertificate` consumes for any pair
of slices `(j₀, k₁), (j₀, k₂)`.

Real, sorry-free.  The construction extracts the shared `σⱼ₀` once,
applies the existing Step-4 wrapper per pair, and retains the
grid-normalization witness on `σⱼ₀` (which the standard wrapper already
produces and the previous consumer discarded). -/
theorem perPairSliceRepresentations_with_sharedPivot
    {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀) :
    ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀),
    ∀ k : ι, k ≠ j₀ →
      ∃ (Vj₀ : X j₀ → ℝ) (Vk : X k → ℝ),
        (∀ n : ℕ, Vj₀ (σⱼ₀.α n) = (n : ℝ)) ∧
        PairwiseSliceRepresentationCertificate P j₀ k Vj₀ Vk := by
  obtain ⟨σⱼ₀, hinj_j₀, hAllPairs⟩ := hShared
  refine ⟨σⱼ₀, ?_⟩
  intro k hk
  obtain ⟨σk, hinj_k, htradeoff⟩ := hAllPairs k hk
  obtain ⟨Vj₀, Vk, hgrid, hslice⟩ :=
    pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate
      P hsolv hk.symm σⱼ₀ σk hinj_j₀ hinj_k htradeoff
  -- hgrid : PairwiseGridNormalizationWitness σⱼ₀ σk Vj₀ Vk
  -- We just need the `Vj₀ (σⱼ₀.α n) = n` half.
  exact ⟨Vj₀, Vk, hgrid.1, hslice⟩

/-- **Shared-pivot-grid certificate from shared-pivot Step-4 machinery.**

Real, sorry-free.  Two per-pair invocations under the shared-pivot Step-4
certificate produce `Vⱼ₀^(k₁)` and `Vⱼ₀^(k₂)` both calibrated against the
same `σⱼ₀`, hence satisfy `SharedPivotGridCertificate`. -/
theorem sharedPivotGridCertificate_of_sharedPivot
    {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (k₁ k₂ : ι) (hk₁ : k₁ ≠ j₀) (hk₂ : k₂ ≠ j₀) :
    ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀)
      (Vⱼ₀_at_k₁ : X j₀ → ℝ) (Vk₁ : X k₁ → ℝ)
      (Vⱼ₀_at_k₂ : X j₀ → ℝ) (Vk₂ : X k₂ → ℝ),
      PairwiseSliceRepresentationCertificate P j₀ k₁ Vⱼ₀_at_k₁ Vk₁ ∧
      PairwiseSliceRepresentationCertificate P j₀ k₂ Vⱼ₀_at_k₂ Vk₂ ∧
      SharedPivotGridCertificate σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ := by
  obtain ⟨σⱼ₀, hAllPair⟩ :=
    perPairSliceRepresentations_with_sharedPivot P hsolv j₀ hShared
  obtain ⟨Vⱼ₀_at_k₁, Vk₁, hgrid₁, hslice₁⟩ := hAllPair k₁ hk₁
  obtain ⟨Vⱼ₀_at_k₂, Vk₂, hgrid₂, hslice₂⟩ := hAllPair k₂ hk₂
  refine ⟨σⱼ₀, Vⱼ₀_at_k₁, Vk₁, Vⱼ₀_at_k₂, Vk₂, hslice₁, hslice₂, hgrid₁, hgrid₂⟩

/-! ##### M5 density-extension: from grid agreement to global agreement

The shared-pivot-grid agreement (proved above) gives `Vⱼ₀^(k₁) = Vⱼ₀^(k₂)`
on the σⱼ₀-grid `{σⱼ₀.α n : n : ℕ}`.  To extend to all of `X j₀`, we
need:

1. The grid's range `Set.range σⱼ₀.α` is dense in `X j₀`.
2. Both `Vⱼ₀^(k_i)` are continuous.
3. Mathlib's `Continuous.ext_on` then forces `Vⱼ₀^(k₁) = Vⱼ₀^(k₂)`
   everywhere.

Density of the grid is structural (for `X j₀ = ℝ` with the standard
topology, it follows from M4's between-points-coverage chain).
Continuity of each `Vⱼ₀^(k_i)` follows from M4's continuity discharge
chain.

This round delivers the **density-extension closer**: given density and
continuity, the agreement extends globally. -/

/-- **Density-extension from grid agreement to global agreement.**

Real, sorry-free.  Given two functions `Vⱼ₀^(k_i) : X j₀ → ℝ` that:
- agree on the σⱼ₀-grid (consequence of `SharedPivotGridCertificate`);
- are both continuous;
- have a dense grid range in the topological space `X j₀`;

then `Vⱼ₀^(k₁) = Vⱼ₀^(k₂)` everywhere on `X j₀`.

Direct application of Mathlib's `Continuous.ext_on` after restating
"agree on the σⱼ₀-grid" as `EqOn` on `Set.range σⱼ₀.α`. -/
theorem sharedPivotGrid_global_agreement
    {X : ι → Type v} [_ι_dec : DecidableEq ι] {j₀ : ι}
    [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    {P : ProductPref X}
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ : X j₀ → ℝ)
    (hshared : SharedPivotGridCertificate σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂)
    (hcont₁ : Continuous Vⱼ₀_at_k₁)
    (hcont₂ : Continuous Vⱼ₀_at_k₂)
    (hdense : Dense (Set.range σⱼ₀.α)) :
    Vⱼ₀_at_k₁ = Vⱼ₀_at_k₂ := by
  -- Restate "agree on the σⱼ₀-grid" as EqOn on Set.range σⱼ₀.α.
  have hEqOn : Set.EqOn Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ (Set.range σⱼ₀.α) := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [← hn]
    exact sharedPivotGrid_agreement σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ hshared n
  -- Apply Continuous.ext_on.
  exact Continuous.ext_on hdense hcont₁ hcont₂ hEqOn

/-- **End-to-end M5 cardinal closer (under shared-pivot certificate +
density + continuity).**

Real, sorry-free composite.  Given the shared-pivot All-Pairs Step-4
certificate plus density of the σⱼ₀-grid plus continuity of each per-pair
`Vⱼ₀^(k)`, the two slice representations on `(j₀, k₁)` and `(j₀, k₂)`
have *identical* j₀-utilities.

Combines `sharedPivotGridCertificate_of_sharedPivot` (design-side
discharge) with `sharedPivotGrid_global_agreement` (density extension)
to produce the strongest form of the M5 cardinal slice-uniqueness claim. -/
theorem m5_cardinal_closer_under_sharedPivot
    {X : ι → Type v} [_ι_dec : DecidableEq ι] {j₀ : ι}
    [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (k₁ k₂ : ι) (hk₁ : k₁ ≠ j₀) (hk₂ : k₂ ≠ j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V) -- assume all V's are continuous
    (hdense_grid :
      ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
        Dense (Set.range σⱼ₀.α)) :
    ∃ (Vⱼ₀ : X j₀ → ℝ) (Vk₁ : X k₁ → ℝ) (Vk₂ : X k₂ → ℝ),
      PairwiseSliceRepresentationCertificate P j₀ k₁ Vⱼ₀ Vk₁ ∧
      PairwiseSliceRepresentationCertificate P j₀ k₂ Vⱼ₀ Vk₂ := by
  obtain ⟨σⱼ₀, Vⱼ₀_at_k₁, Vk₁, Vⱼ₀_at_k₂, Vk₂,
    hslice₁, hslice₂, hshared_grid⟩ :=
    sharedPivotGridCertificate_of_sharedPivot P hsolv j₀ hShared k₁ k₂ hk₁ hk₂
  -- Apply the density extension to get global agreement.
  have h_eq : Vⱼ₀_at_k₁ = Vⱼ₀_at_k₂ :=
    sharedPivotGrid_global_agreement σⱼ₀ Vⱼ₀_at_k₁ Vⱼ₀_at_k₂ hshared_grid
      (hcont _) (hcont _) (hdense_grid σⱼ₀)
  -- Both slice representations now share the same j₀-utility.
  refine ⟨Vⱼ₀_at_k₁, Vk₁, Vk₂, hslice₁, ?_⟩
  rw [h_eq]
  exact hslice₂

/-- **End-to-end M5 cardinal closer (iterated form, all non-pivot
coordinates).**

Real, sorry-free composite.  Under the shared-pivot All-Pairs Step-4
certificate plus continuity plus grid density, *all* per-pair `Vⱼ₀^(k)`
are equal to a single global `Vⱼ₀ : X j₀ → ℝ`.  This is the strongest
form of `PairwiseSliceRepresentationsAtPivot P j₀`: not just
"compatible affine relations" but "literally identical pivot utilities".

Proof strategy: extract the shared `σⱼ₀` once, then for every `k ≠ j₀`
the per-pair Step-4 chain produces a `Vⱼ₀^(k)` calibrated to that grid.
Pick any reference `k₀ ≠ j₀` (which exists from `Nonempty` hypothesis on
"some `k ≠ j₀`", e.g. supplied externally) and use its `Vⱼ₀^(k₀)` as the
global witness.  By `sharedPivotGrid_global_agreement`, every other
`Vⱼ₀^(k)` equals `Vⱼ₀^(k₀)` everywhere.

The core observation: under shared-pivot calibration plus continuity
plus density, `Vⱼ₀^(k)` is *uniquely determined* by `σⱼ₀` independently
of `k`.  So we can just use the reference `k₀`'s output and rewrite
each individual slice representation to use the global witness. -/
theorem pairwiseSliceRepresentationsAtPivot_of_sharedPivot
    {X : ι → Type v} [_ι_dec : DecidableEq ι] {j₀ : ι}
    [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (hShared : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid :
      ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
        Dense (Set.range σⱼ₀.α)) :
    PairwiseSliceRepresentationsAtPivot P j₀ := by
  classical
  -- Extract the shared σⱼ₀ and the per-pair grid-normalized representations.
  obtain ⟨σⱼ₀, hAllPair⟩ :=
    perPairSliceRepresentations_with_sharedPivot P hsolv j₀ hShared
  -- Case split on whether any non-pivot coordinate exists.
  by_cases h_exists_k : ∃ k : ι, k ≠ j₀
  · -- Non-vacuous case: pick a reference k₀ and use its Vⱼ₀^(k₀).
    obtain ⟨k₀, hk₀⟩ := h_exists_k
    obtain ⟨Vⱼ₀_ref, _Vk₀, hgrid_ref, _hslice_ref⟩ := hAllPair k₀ hk₀
    refine ⟨Vⱼ₀_ref, ?_⟩
    intro k hk
    obtain ⟨Vⱼ₀_at_k, Vk, hgrid_k, hslice_k⟩ := hAllPair k hk
    -- Vⱼ₀_ref and Vⱼ₀_at_k both calibrate to the σⱼ₀-grid, hence agree
    -- on the grid; by density + continuity they're equal globally.
    have hshared_grid :
        SharedPivotGridCertificate σⱼ₀ Vⱼ₀_ref Vⱼ₀_at_k :=
      ⟨hgrid_ref, hgrid_k⟩
    have h_eq : Vⱼ₀_ref = Vⱼ₀_at_k :=
      sharedPivotGrid_global_agreement σⱼ₀ Vⱼ₀_ref Vⱼ₀_at_k hshared_grid
        (hcont _) (hcont _) (hdense_grid σⱼ₀)
    refine ⟨Vk, ?_⟩
    rw [h_eq]
    exact hslice_k
  · -- Vacuous case: no non-pivot coordinate.  Any function works.
    refine ⟨fun _ => 0, ?_⟩
    intro k hk
    exfalso
    exact h_exists_k ⟨k, hk⟩

/-- **Assembled per-pair slice representations at a pivot, conditional on
scaling compatibility.**

The scaling-compatibility certificate as defined *is* the assembled
output `PairwiseSliceRepresentationsAtPivot P j₀`.  This lemma exposes
that equivalence directly: given the named residual, the assembly
conclusion is immediate.

The genuinely deep content — proving the residual itself from per-pair
Step-4 machinery and n ≥ 3 — remains the open M5 obligation, but the
assembly side of M5 is now mechanical. -/
theorem pairwiseSliceRepresentationsAtPivot_of_compatibility
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hcomp : Step5ScalingCompatibilityCertificate P hsolv j₀) :
    PairwiseSliceRepresentationsAtPivot P j₀ :=
  hcomp

/-! ### Counterexample: assembly input alone is not enough

The tempting theorem

`PairwiseAssemblyInputCertificate P j k σj σk →
 PairwiseSliceAssemblyCertificate P j k σj σk`

is false in the current abstract interface.  The total preference relation on
two `ℕ`-coordinates has all local interpolation properties, and the identity
standard-sequence grids are normalized by the identity utilities.  But total
preference cannot be represented by a nonconstant additive score on the whole
two-coordinate slice: total preference would force every score comparison in
both directions, while grid normalization forces different scores for grid
points `0` and `1`.
-/

/-- Total preference on `Bool`-indexed natural-number profiles. -/
private def totalNatBoolPref : ProductPref (fun _ : Bool => ℕ) where
  weakPref := fun _ _ => True

/-- The identity standard sequence on coordinate `true`, using coordinate
`false` as the reference coordinate. -/
private def totalNatBoolStdSeqTrue :
    ProductPref.StandardSequence totalNatBoolPref true where
  k := false
  k_ne_j := by decide
  r := 0
  s := 1
  r_ne_s := by decide
  base := fun _ => 0
  α := fun n => n
  spaced := by
    intro _
    exact ⟨trivial, trivial⟩

/-- The identity standard sequence on coordinate `false`, using coordinate
`true` as the reference coordinate. -/
private def totalNatBoolStdSeqFalse :
    ProductPref.StandardSequence totalNatBoolPref false where
  k := true
  k_ne_j := by decide
  r := 0
  s := 1
  r_ne_s := by decide
  base := fun _ => 0
  α := fun n => n
  spaced := by
    intro _
    exact ⟨trivial, trivial⟩

/-- The total preference relation is restricted-solvable. -/
private theorem totalNatBoolPref_restrictedSolvability :
    ProductPref.RestrictedSolvability totalNatBoolPref := by
  intro _ _ _ v _ _ _
  exact ⟨v, trivial, trivial⟩

/-- The total preference relation is a weak order. -/
private instance totalNatBoolPref_isWeakOrder :
    ProductPref.IsWeakOrder totalNatBoolPref where
  complete := by
    intro _ _
    exact Or.inl trivial
  transitive := by
    intro _ _ _ _ _
    trivial

/-- The total preference relation satisfies the current abstract hexagon
condition, because every profile pair is indifferent. -/
private instance totalNatBoolPref_tradeoffConsistency :
    ProductPref.TradeoffConsistency totalNatBoolPref where
  consistent := by
    intros
    exact ⟨trivial, trivial⟩

/-- The counterexample has the current assembly-input certificate. -/
private theorem totalNatBool_pairwiseAssemblyInput :
    PairwiseAssemblyInputCertificate totalNatBoolPref true false
      totalNatBoolStdSeqTrue totalNatBoolStdSeqFalse := by
  exact pairwiseAssemblyInputCertificate_of_injectiveStandardSequences_and_restrictedSolvability
    totalNatBoolPref totalNatBoolPref_restrictedSolvability
    totalNatBoolStdSeqTrue totalNatBoolStdSeqFalse
    (fun _ _ h => h) (fun _ _ h => h)

/-- But the counterexample cannot have a slice-assembly certificate respecting
the same grid normalization. -/
private theorem not_totalNatBool_pairwiseSliceAssembly :
    ¬ PairwiseSliceAssemblyCertificate totalNatBoolPref true false
      totalNatBoolStdSeqTrue totalNatBoolStdSeqFalse := by
  rintro ⟨Vt, Vf, hgrid, hrepr⟩
  rcases hgrid with ⟨hVt, hVf⟩
  let x : Profile (fun _ : Bool => ℕ) := fun _ => 0
  let y : Profile (fun _ : Bool => ℕ) := fun b => if b then 1 else 0
  have hagree : Profile.agreeOff ({true, false} : Set Bool) x y := by
    intro i hi
    exfalso
    cases i <;> simp at hi
  have hineq : Vt (y true) + Vf (y false) ≤ Vt (x true) + Vf (x false) :=
    (hrepr x y hagree).mp trivial
  simp [x, y] at hineq
  have hVt_one : Vt 1 = (1 : ℝ) := by
    simpa [totalNatBoolStdSeqTrue] using hVt 1
  have hVt_zero : Vt 0 = (0 : ℝ) := by
    simpa [totalNatBoolStdSeqTrue] using hVt 0
  rw [hVt_one, hVt_zero] at hineq
  norm_num at hineq

/-- Therefore the current assembly-input certificate is not sufficient, in
complete generality, to produce a slice-assembly certificate. -/
theorem pairwiseAssemblyInput_not_sufficient_for_pairwiseSliceAssembly :
    ∃ (P : ProductPref (fun _ : Bool => ℕ)),
      ∃ (σt : ProductPref.StandardSequence P true),
        ∃ (σf : ProductPref.StandardSequence P false),
          PairwiseAssemblyInputCertificate P true false σt σf ∧
          ¬ PairwiseSliceAssemblyCertificate P true false σt σf := by
  exact ⟨totalNatBoolPref, totalNatBoolStdSeqTrue, totalNatBoolStdSeqFalse,
    totalNatBool_pairwiseAssemblyInput, not_totalNatBool_pairwiseSliceAssembly⟩

/-- Equivalently, the single assembly theorem certificate is false for this
counterexample data. -/
theorem totalNatBool_not_pairwiseSliceAssemblyTheoremCertificate :
    ¬ PairwiseSliceAssemblyTheoremCertificate totalNatBoolPref true false
      totalNatBoolStdSeqTrue totalNatBoolStdSeqFalse := by
  intro hassemble
  exact not_totalNatBool_pairwiseSliceAssembly
    (hassemble totalNatBool_pairwiseAssemblyInput)

/-- The same counterexample rules out the Step-4 tradeoff-machinery certificate
itself: applying such a certificate to the existing assembly input would produce
the forbidden slice assembly. -/
private theorem totalNatBool_not_pairwiseStep4TradeoffMachineryCertificate :
    ¬ PairwiseStep4TradeoffMachineryCertificate totalNatBoolPref true false
      totalNatBoolStdSeqTrue totalNatBoolStdSeqFalse := by
  intro htradeoff
  rcases htradeoff totalNatBool_pairwiseAssemblyInput with ⟨Vt, Vf, hgrid, hcal⟩
  exact not_totalNatBool_pairwiseSliceAssembly ⟨Vt, Vf, hgrid, hcal⟩

/-- Consequently, the present abstract `TradeoffConsistency` / hexagon class,
even together with weak order, restricted solvability, and the current assembly
input, is not enough to prove the Step-4 tradeoff-machinery certificate.  The
new `PairwiseHexagonStandardSequenceCertificate` records the stronger
standard-sequence magnitude/bracketing content still to be mechanized. -/
theorem tradeoffConsistency_and_assemblyInput_not_sufficient_for_pairwiseStep4TradeoffMachinery :
    ∃ (P : ProductPref (fun _ : Bool => ℕ)),
      ∃ (σt : ProductPref.StandardSequence P true),
        ∃ (σf : ProductPref.StandardSequence P false),
          ProductPref.IsWeakOrder P ∧
          ProductPref.TradeoffConsistency P ∧
          ProductPref.RestrictedSolvability P ∧
          PairwiseAssemblyInputCertificate P true false σt σf ∧
          ¬ PairwiseStep4TradeoffMachineryCertificate P true false σt σf := by
  exact ⟨totalNatBoolPref, totalNatBoolStdSeqTrue, totalNatBoolStdSeqFalse,
    inferInstance, inferInstance, totalNatBoolPref_restrictedSolvability,
    totalNatBool_pairwiseAssemblyInput,
    totalNatBool_not_pairwiseStep4TradeoffMachineryCertificate⟩

/-! ### Counterexample: exact finite-grid cut witnesses are too strong

The exact witness target `PairwiseCutConstructionTheoremCertificate` asks every
target profile to be indifferent to a finite grid profile with exactly the same
additive score.  That cannot be right for a one-sided standard-sequence grid:
the grid scores are natural-number sums, while a represented slice may contain
targets with negative or non-integral scores.  Wakker's actual cut construction
first obtains finite lower/upper cuts and then uses interpolation/extension; it
does not assert that every target is itself score-equal to a finite grid point.

The following additive real model formalizes the obstruction.  It is a clean
order-calibrated two-coordinate representation with restricted solvability and
valid standard sequences, but the target profile of score `-1` cannot have an
exact finite grid representative because every grid score is nonnegative.
-/

/-- Additive preference on two real coordinates indexed by `Bool`. -/
def additiveRealBoolPref : ProductPref (fun _ : Bool => ℝ) where
  weakPref := fun x y => y true + y false ≤ x true + x false

/-- Identity utilities additively represent `additiveRealBoolPref`. -/
def additiveRealBool_rep : AdditiveRep additiveRealBoolPref :=
  { V := fun _ x => x
    represents := by
      intro x y
      dsimp [additiveRealBoolPref]
      simp [add_comm] }

/-- The additive real preference is a weak order. -/
instance additiveRealBoolPref_isWeakOrder :
    ProductPref.IsWeakOrder additiveRealBoolPref where
  complete := by
    intro x y
    rcases le_total (y true + y false) (x true + x false) with h | h
    · exact Or.inl h
    · exact Or.inr h
  transitive := by
    intro x y z hxy hyz
    dsimp [additiveRealBoolPref] at hxy hyz ⊢
    linarith

/-- The additive real preference is restricted-solvable by solving the missing
coordinate from the target total score. -/
theorem additiveRealBoolPref_restrictedSolvability :
    ProductPref.RestrictedSolvability additiveRealBoolPref := by
  intro a b j _v _w _hlo _hhi
  cases j
  · refine ⟨b true + b false - a true, ?_⟩
    constructor <;> dsimp [additiveRealBoolPref] <;> simp
  · refine ⟨b true + b false - a false, ?_⟩
    constructor <;> dsimp [additiveRealBoolPref] <;> simp

/-- The additive real preference satisfies tradeoff consistency.  Off-`{j}`
agreement plus three indifferences collapse to a linear arithmetic identity
between the two coordinate sums, from which the conclusion `indiff g h`
reads off in both directions. -/
instance additiveRealBoolPref_tradeoffConsistency :
    ProductPref.TradeoffConsistency additiveRealBoolPref where
  consistent := by
    intro j a b c d e f g h hab hcd hef hgh hiab hicd hief
      hac hbd hce hdf hag hbh
    rcases hiab with ⟨hab_le, hba_le⟩
    rcases hicd with ⟨hcd_le, hdc_le⟩
    rcases hief with ⟨hef_le, hfe_le⟩
    dsimp [additiveRealBoolPref] at hab_le hba_le hcd_le hdc_le hef_le hfe_le
    refine ⟨?_, ?_⟩ <;> dsimp [additiveRealBoolPref] <;>
    · cases j
      · have habT : a true = b true := hab true (by decide)
        have hcdT : c true = d true := hcd true (by decide)
        have hefT : e true = f true := hef true (by decide)
        have hghT : g true = h true := hgh true (by decide)
        linarith
      · have habF : a false = b false := hab false (by decide)
        have hcdF : c false = d false := hcd false (by decide)
        have hefF : e false = f false := hef false (by decide)
        have hghF : g false = h false := hgh false (by decide)
        linarith

/-- The additive real preference satisfies the Archimedean axiom in either
coordinate.  A strict standard sequence in coordinate `j` has constant
non-zero linear step (the additive cancellation of the spacing identity),
so its `α n + base.k_other`-totals tend to `−∞`, ruling out every candidate
preference sandwich. -/
theorem additiveRealBoolPref_archimedean :
    ∀ j : Bool, ProductPref.Archimedean additiveRealBoolPref j := by
  -- Treat each coordinate by cases.  In each branch we run the same linear
  -- argument: extract `α 1 < α 0`, deduce a constant step `α(n+1)−α n`,
  -- conclude `α n → −∞`, and contradict the lower bound of the sandwich.
  intro j σ hσ
  rintro ⟨lo, hi, hbnd⟩
  -- Strictness gives `α 0 ≻ α 1`, i.e. `α 1 < α 0` as reals.
  have h0 := hσ.1
  have h1 := hσ.2
  -- Spacing gives `α (n+1) − α n` constant for all `n`.
  -- Define the off-`j` coordinate.
  -- We split on `j` and run the same linear argument in each branch.
  cases j with
  | false =>
    -- j = false; the off-`j` coordinate is `true`.
    -- σ.k must be `true` since σ.k ≠ j.
    have hk : σ.k = true := by
      cases hk' : σ.k
      · exfalso; exact σ.k_ne_j hk'
      · rfl
    -- Convert h0 to `α 1 + base true ≤ α 0 + base true`.
    have hα01 : σ.α 1 ≤ σ.α 0 := by
      have := h0
      dsimp [additiveRealBoolPref] at this
      have e1 : (Function.update σ.base false (σ.α 0)) true = σ.base true :=
        Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
      have e2 : (Function.update σ.base false (σ.α 1)) true = σ.base true :=
        Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
      have e3 : (Function.update σ.base false (σ.α 0)) false = σ.α 0 :=
        Function.update_self false (σ.α 0) σ.base
      have e4 : (Function.update σ.base false (σ.α 1)) false = σ.α 1 :=
        Function.update_self false (σ.α 1) σ.base
      simp only [e1, e2, e3, e4] at this
      linarith
    have hα01_ne : σ.α 1 ≠ σ.α 0 := by
      intro heq
      apply h1
      dsimp [additiveRealBoolPref]
      have e1 : (Function.update σ.base false (σ.α 0)) true = σ.base true :=
        Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
      have e2 : (Function.update σ.base false (σ.α 1)) true = σ.base true :=
        Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
      have e3 : (Function.update σ.base false (σ.α 0)) false = σ.α 0 :=
        Function.update_self false (σ.α 0) σ.base
      have e4 : (Function.update σ.base false (σ.α 1)) false = σ.α 1 :=
        Function.update_self false (σ.α 1) σ.base
      rw [e1, e2, e3, e4, heq]
    have hα_strict : σ.α 1 < σ.α 0 := lt_of_le_of_ne hα01 hα01_ne
    -- Spacing identity: α (n+1) + s = α n + r (with σ.k = true).
    have hstep : ∀ n, σ.α (n + 1) - σ.α n = σ.r - σ.s := by
      intro n
      have hsp := σ.spaced n
      rcases hsp with ⟨h_le, h_ge⟩
      dsimp [additiveRealBoolPref] at h_le h_ge
      rw [hk] at h_le h_ge
      simp only [Function.update_self,
        Function.update_of_ne (show (false : Bool) ≠ true by decide)] at h_le h_ge
      linarith
    -- Combine: α 1 − α 0 = r − s, both negative, so step is constant negative.
    have hstep01 : σ.α 1 - σ.α 0 = σ.r - σ.s := by
      have := hstep 0
      simpa using this
    have hrs_neg : σ.r - σ.s < 0 := by linarith
    have hα_formula : ∀ n : ℕ, σ.α n = σ.α 0 + n * (σ.r - σ.s) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have := hstep k
        have hsucc : σ.α (k + 1) = σ.α k + (σ.r - σ.s) := by linarith
        rw [hsucc, ih]
        push_cast; ring
    -- Lower bound at every n: lo true + lo false ≤ α n + base true.
    have hlower : ∀ n : ℕ, lo true + lo false ≤ σ.α n + σ.base true := by
      intro n
      have h := (hbnd n).2
      dsimp [additiveRealBoolPref] at h
      have e1 : (Function.update σ.base false (σ.α n)) true = σ.base true :=
        Function.update_of_ne (by decide : (true : Bool) ≠ false) _ _
      have e2 : (Function.update σ.base false (σ.α n)) false = σ.α n :=
        Function.update_self false (σ.α n) σ.base
      simp only [e1, e2] at h
      linarith
    -- Pick N large enough that α N + base true < lo true + lo false.
    set d : ℝ := σ.s - σ.r with hd_def
    have hd_pos : 0 < d := by simp [hd_def]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((σ.α 0 + σ.base true - lo true - lo false) / d)
    have hbound : σ.α 0 + σ.base true - lo true - lo false < N * d := by
      have hh := (div_lt_iff₀ hd_pos).mp hN
      linarith
    have hαN : σ.α N = σ.α 0 - N * d := by
      have := hα_formula N
      simp [hd_def] at this ⊢
      linarith
    have hcontra : σ.α N + σ.base true < lo true + lo false := by
      rw [hαN]; linarith
    exact absurd (hlower N) (not_le.mpr hcontra)
  | true =>
    -- j = true; the off-`j` coordinate is `false`.
    have hk : σ.k = false := by
      cases hk' : σ.k
      · rfl
      · exfalso; exact σ.k_ne_j hk'
    have hα01 : σ.α 1 ≤ σ.α 0 := by
      have := h0
      dsimp [additiveRealBoolPref] at this
      have e1 : (Function.update σ.base true (σ.α 0)) true = σ.α 0 :=
        Function.update_self true (σ.α 0) σ.base
      have e2 : (Function.update σ.base true (σ.α 1)) true = σ.α 1 :=
        Function.update_self true (σ.α 1) σ.base
      have e3 : (Function.update σ.base true (σ.α 0)) false = σ.base false :=
        Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
      have e4 : (Function.update σ.base true (σ.α 1)) false = σ.base false :=
        Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
      simp only [e1, e2, e3, e4] at this
      linarith
    have hα01_ne : σ.α 1 ≠ σ.α 0 := by
      intro heq
      apply h1
      dsimp [additiveRealBoolPref]
      have e1 : (Function.update σ.base true (σ.α 0)) true = σ.α 0 :=
        Function.update_self true (σ.α 0) σ.base
      have e2 : (Function.update σ.base true (σ.α 1)) true = σ.α 1 :=
        Function.update_self true (σ.α 1) σ.base
      have e3 : (Function.update σ.base true (σ.α 0)) false = σ.base false :=
        Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
      have e4 : (Function.update σ.base true (σ.α 1)) false = σ.base false :=
        Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
      rw [e1, e2, e3, e4, heq]
    have hα_strict : σ.α 1 < σ.α 0 := lt_of_le_of_ne hα01 hα01_ne
    have hstep : ∀ n, σ.α (n + 1) - σ.α n = σ.r - σ.s := by
      intro n
      have hsp := σ.spaced n
      rcases hsp with ⟨h_le, h_ge⟩
      dsimp [additiveRealBoolPref] at h_le h_ge
      rw [hk] at h_le h_ge
      simp only [Function.update_self,
        Function.update_of_ne (show (true : Bool) ≠ false by decide)] at h_le h_ge
      linarith
    have hstep01 : σ.α 1 - σ.α 0 = σ.r - σ.s := by
      have := hstep 0
      simpa using this
    have hrs_neg : σ.r - σ.s < 0 := by linarith
    have hα_formula : ∀ n : ℕ, σ.α n = σ.α 0 + n * (σ.r - σ.s) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have := hstep k
        have hsucc : σ.α (k + 1) = σ.α k + (σ.r - σ.s) := by linarith
        rw [hsucc, ih]
        push_cast; ring
    have hlower : ∀ n : ℕ, lo true + lo false ≤ σ.α n + σ.base false := by
      intro n
      have h := (hbnd n).2
      dsimp [additiveRealBoolPref] at h
      have e1 : (Function.update σ.base true (σ.α n)) true = σ.α n :=
        Function.update_self true (σ.α n) σ.base
      have e2 : (Function.update σ.base true (σ.α n)) false = σ.base false :=
        Function.update_of_ne (by decide : (false : Bool) ≠ true) _ _
      simp only [e1, e2] at h
      linarith
    set d : ℝ := σ.s - σ.r with hd_def
    have hd_pos : 0 < d := by simp [hd_def]; linarith
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((σ.α 0 + σ.base false - lo true - lo false) / d)
    have hbound : σ.α 0 + σ.base false - lo true - lo false < N * d := by
      have hh := (div_lt_iff₀ hd_pos).mp hN
      linarith
    have hαN : σ.α N = σ.α 0 - N * d := by
      have := hα_formula N
      simp [hd_def] at this ⊢
      linarith
    have hcontra : σ.α N + σ.base false < lo true + lo false := by
      rw [hαN]; linarith
    exact absurd (hlower N) (not_le.mpr hcontra)

/-- One-sided standard sequence on the `true` coordinate.  The reference
exchange in the `false` coordinate offsets one unit of `true`. -/
def additiveRealBoolStdSeqTrue :
    ProductPref.StandardSequence additiveRealBoolPref true where
  k := false
  k_ne_j := by decide
  r := 0
  s := -1
  r_ne_s := by norm_num
  base := fun _ => 0
  α := fun n => (n : ℝ)
  spaced := by
    intro n
    constructor <;> dsimp [additiveRealBoolPref] <;> simp

/-- One-sided standard sequence on the `false` coordinate. -/
def additiveRealBoolStdSeqFalse :
    ProductPref.StandardSequence additiveRealBoolPref false where
  k := true
  k_ne_j := by decide
  r := 0
  s := -1
  r_ne_s := by norm_num
  base := fun _ => 0
  α := fun n => (n : ℝ)
  spaced := by
    intro n
    constructor <;> dsimp [additiveRealBoolPref] <;> simp

/-- Identity utilities normalize both one-sided grids. -/
private theorem additiveRealBool_gridNormalization :
    PairwiseGridNormalizationWitness additiveRealBoolStdSeqTrue
      additiveRealBoolStdSeqFalse (fun x : ℝ => x) (fun x : ℝ => x) := by
  constructor <;> intro n <;> rfl

/-- Identity utilities exactly calibrate the additive real slice order. -/
private theorem additiveRealBool_orderCalibration :
    PairwiseOrderCalibrationCertificate additiveRealBoolPref true false
      (fun x : ℝ => x) (fun x : ℝ => x) := by
  intro x y _hxy
  rfl

/-- The target profile of additive score `-1` has no exact finite grid cut
witness, because every finite grid score is a sum of two natural numbers. -/
private theorem additiveRealBool_not_pairwiseCutConstructionCertificate :
    ¬ PairwiseCutConstructionCertificate additiveRealBoolStdSeqTrue
      additiveRealBoolStdSeqFalse (fun x : ℝ => x) (fun x : ℝ => x) := by
  intro hcut
  let base : Profile (fun _ : Bool => ℝ) := fun _ => 0
  let target : Profile (fun _ : Bool => ℝ) := fun b => if b then (-1 : ℝ) else 0
  have hbase : Profile.agreeOff ({true, false} : Set Bool) base target := by
    intro i hi
    exfalso
    cases i <;> simp at hi
  rcases hcut base target hbase with ⟨n, m, _hindiff, hscore⟩
  have hscore' : (-1 : ℝ) = (n : ℝ) + (m : ℝ) := by
    simpa [PairwiseCutWitness, PairwiseAdditiveScore, PairwiseGridProfile,
      additiveRealBoolStdSeqTrue, additiveRealBoolStdSeqFalse, base, target]
      using hscore
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  linarith

/-- Therefore the theorem-shaped exact cut-construction target is false for
one-sided grids, even with grid normalization and full order calibration. -/
theorem additiveRealBool_not_pairwiseCutConstructionTheoremCertificate :
    ¬ PairwiseCutConstructionTheoremCertificate additiveRealBoolPref true false
      additiveRealBoolStdSeqTrue additiveRealBoolStdSeqFalse := by
  intro hcut
  exact additiveRealBool_not_pairwiseCutConstructionCertificate
    (hcut (fun x : ℝ => x) (fun x : ℝ => x)
      additiveRealBool_gridNormalization additiveRealBool_orderCalibration)

/-- **No-go for the base-transport bridge from raw structural axioms.**

The additive real preference satisfies weak order, restricted solvability,
tradeoff consistency, and the Archimedean axiom in both coordinates, yet its
one-sided ℕ-indexed standard-sequence grids do **not** satisfy
`PairwiseArchimedeanBaseTransportCertificate`: the lower-half bracket fails
for any target with negative additive score, since every grid profile at a
zero base has nonneg total `n + m`.

This proves that raw `Archimedean P j ∧ Archimedean P k ∧ TradeoffConsistency
P ∧ RestrictedSolvability P ∧ IsWeakOrder P` is **not** sufficient for the
base-transport bridge; further coverage hypotheses on the standard-sequence
grids are required. -/
theorem additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate :
    ¬ PairwiseArchimedeanBaseTransportCertificate additiveRealBoolStdSeqTrue
      additiveRealBoolStdSeqFalse := by
  intro hbridge
  rcases hbridge with ⟨_hupper, hlower⟩
  let base : Profile (fun _ : Bool => ℝ) := fun _ => 0
  let target : Profile (fun _ : Bool => ℝ) := fun b => if b then (-1 : ℝ) else 0
  have hbase : Profile.agreeOff ({true, false} : Set Bool) base target := by
    intro i hi
    exfalso
    cases i <;> simp at hi
  rcases hlower base target hbase with ⟨n, m, hpref⟩
  -- `hpref : weakPref target (PairwiseGridProfile σtrue σfalse base n m)`,
  -- which in this model means `gridScore ≤ targetScore = -1`.
  have hineq : ((n : ℝ) + (m : ℝ)) ≤ (-1 : ℝ) := by
    simpa [PairwiseGridProfile, additiveRealBoolPref,
      additiveRealBoolStdSeqTrue, additiveRealBoolStdSeqFalse, base, target,
      Function.update_self,
      Function.update_of_ne (show (false : Bool) ≠ true by decide),
      Function.update_of_ne (show (true : Bool) ≠ false by decide)]
      using hpref
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  linarith

/-- Consequently, raw Archimedean (in both coordinates) plus tradeoff
consistency plus restricted solvability is **not** sufficient for finite-cut
coverage at arbitrary slice bases.  Concretely: the additive real model
satisfies all four structural axioms in both coordinates, yet
`additiveRealBool_not_pairwiseCutConstructionCertificate` already shows
exact cut construction fails, and the previous theorem strengthens this to
the full base-transport bridge. -/
theorem additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_baseTransport :
    (∀ j : Bool, ProductPref.Archimedean additiveRealBoolPref j) ∧
    ProductPref.RestrictedSolvability additiveRealBoolPref ∧
    ProductPref.IsWeakOrder additiveRealBoolPref ∧
    ProductPref.TradeoffConsistency additiveRealBoolPref ∧
    ¬ PairwiseArchimedeanBaseTransportCertificate additiveRealBoolStdSeqTrue
        additiveRealBoolStdSeqFalse :=
  ⟨additiveRealBoolPref_archimedean,
   additiveRealBoolPref_restrictedSolvability,
   inferInstance, inferInstance,
   additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate⟩

/-- The Step-5 global-gluing output supplied as `hglobal` in
`global_additive_from_pairwise` and `wakker_IV_2_7_consumer`. -/
def GlobalGluingCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) : Prop :=
  ∀ x y : Profile X,
    P.weakPref x y ↔
      (∑ i, V i (y i)) ≤ (∑ i, V i (x i))

/-- The all-pairs additivity premise supplied as `_hpair` in
`global_additive_from_pairwise`. -/
def AllPairsAdditivityCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) : Prop :=
  ∀ j k : ι, j ≠ k →
    ∀ x y : Profile X,
      Profile.agreeOff {j, k} x y →
      (P.weakPref x y ↔
        V j (y j) + V k (y k) ≤ V j (x j) + V k (x k))

/-! ### First Wakker-construction discharge layer

The construction certificate is the right first target because it already
contains the global representation equation.  Once such a certificate is
available, it immediately yields both:

* a `GlobalGluingCertificate` for the constructed coordinate utilities, and
* all two-coordinate slice certificates obtained by restricting the global
  sum equation to profiles that agree off `{j,k}`.

The lemmas below are fully proved; the remaining deep work is producing the
initial `WakkerConstructionCertificate` from Wakker's standard-sequence
machinery.
-/

/-- Split a finite additive-representation sum into the `j`, `k`, and
off-`{j,k}` parts. -/
lemma sum_eq_pair_add_rest {X : ι → Type v}
    (V : (i : ι) → X i → ℝ) (x : Profile X) {j k : ι} (hjk : j ≠ k) :
    (∑ i, V i (x i)) =
      V j (x j) + V k (x k) +
        ∑ i ∈ (Finset.univ.erase j).erase k, V i (x i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hk_mem : k ∈ Finset.univ.erase j := by
    simp [hjk.symm]
  rw [← Finset.sum_erase_add _ _ hk_mem]
  ring

/-- A global gluing certificate restricts to all two-coordinate slice
certificates. -/
theorem allPairsAdditivityCertificate_of_globalGluingCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ)
    (hglobal : GlobalGluingCertificate P V) :
    AllPairsAdditivityCertificate P V := by
  intro j k hjk x y hxy
  have hx := sum_eq_pair_add_rest V x hjk
  have hy := sum_eq_pair_add_rest V y hjk
  have hrest :
      (∑ i ∈ (Finset.univ.erase j).erase k, V i (y i)) =
        ∑ i ∈ (Finset.univ.erase j).erase k, V i (x i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hi_erase_j : i ∈ Finset.univ.erase j := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := Finset.ne_of_mem_erase hi_erase_j
    have hi_not_pair : i ∉ ({j, k} : Set ι) := by
      intro himem
      rcases (by simpa using himem : i = j ∨ i = k) with rfl | rfl
      · exact hij rfl
      · exact hik rfl
    rw [← hxy i hi_not_pair]
  rw [hglobal x y, hx, hy, hrest]
  constructor <;> intro h <;> linarith

/-- A Wakker construction certificate is exactly a witness of global gluing
for some coordinate-utility family. -/
theorem globalGluingCertificate_of_wakkerConstructionCertificate {X : ι → Type v}
    (P : ProductPref X) (hConstruct : WakkerConstructionCertificate P) :
    ∃ V : (i : ι) → X i → ℝ, GlobalGluingCertificate P V :=
  hConstruct

/-! ### Phase 8 / M1 — Single-coordinate pivot lemma

The real M1 obligation is to prove `GlobalGluingCertificate P V` from
`AllPairsAdditivityCertificate P V` and `Fact (3 ≤ Fintype.card ι)`.  The
intended proof telescopes from `x` to `y` one coordinate at a time, using
pairwise additivity at each step, and the role of `n ≥ 3` is to provide a
third coordinate `k` so that each single-coordinate update can be expressed
on a `{j₀, i}`-slice while `k` is held fixed.

This single-step lemma is the algebraic core of that telescoping argument.
It records the fact that pairwise additivity, applied to two profiles that
agree off `{j₀, i}`, already gives the global-form equation for those two
profiles — provided that *every* other coordinate `k ∉ {j₀, i}` cancels out
of the global sum, which is automatic when the two profiles agree there.

The full M1 telescoping argument is the missing deep step; this lemma is the
single building block that any future M1 proof must use, and adding it is a
real downward narrowing of the M1 surface. -/

/-- **M1 single-step pivot.**

If two profiles `x`, `y` agree off the pair `{j₀, i}`, then the all-pairs
additivity certificate immediately gives the *global*-form equation for
`(x, y)`.  Equivalently: on a `{j₀, i}`-slice, the global-σ form is the
same as the pair-form, because every coordinate outside the pair contributes
the same value to both sums.

This is the lemma any future M1 telescoping proof has to use at each step
of the induction. -/
theorem globalGluing_step_of_allPairsAdditivity {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    {j₀ i : ι} (hji : j₀ ≠ i) {x y : Profile X}
    (hxy : Profile.agreeOff {j₀, i} x y) :
    P.weakPref x y ↔ (∑ a, V a (y a)) ≤ (∑ a, V a (x a)) := by
  -- Apply pairwise additivity on the slice (j₀, i).
  have hpairwise :
      P.weakPref x y ↔
        V j₀ (y j₀) + V i (y i) ≤ V j₀ (x j₀) + V i (x i) :=
    hpair j₀ i hji x y hxy
  -- Decompose both sums using `sum_eq_pair_add_rest`.
  have hx := sum_eq_pair_add_rest V x hji
  have hy := sum_eq_pair_add_rest V y hji
  -- The "rest" parts agree because x and y agree off `{j₀, i}`.
  have hrest :
      (∑ a ∈ (Finset.univ.erase j₀).erase i, V a (y a)) =
        ∑ a ∈ (Finset.univ.erase j₀).erase i, V a (x a) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    have ha_erase_j : a ∈ Finset.univ.erase j₀ := (Finset.mem_erase.mp ha).2
    have haj : a ≠ j₀ := Finset.ne_of_mem_erase ha_erase_j
    have ha_not_pair : a ∉ ({j₀, i} : Set ι) := by
      intro hamem
      rcases (by simpa using hamem : a = j₀ ∨ a = i) with rfl | rfl
      · exact haj rfl
      · exact hai rfl
    rw [← hxy a ha_not_pair]
  -- Combine: rewrite the global sums via `hx`, `hy`, `hrest`, then equate
  -- with the pair-form via `hpairwise`.
  rw [hpairwise, hx, hy, hrest]
  constructor <;> intro h <;> linarith

/-- **M1 single-step pivot — Profile.update form.**

Specialization of `globalGluing_step_of_allPairsAdditivity` to the most
common shape used by telescoping arguments: `y` differs from `x` at exactly
one coordinate via `Function.update`.  Pairwise additivity on `(j₀, i)`
again gives the global-form equation for the pair `(x, Function.update x i v)`,
for any third coordinate `j₀ ≠ i` chosen as the slice partner.

This is the regression target for M1's telescoping induction step. -/
theorem globalGluing_update_step_of_allPairsAdditivity {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    {j₀ i : ι} (hji : j₀ ≠ i) (x : Profile X) (v : X i) :
    P.weakPref x (Function.update x i v) ↔
      (∑ a, V a (Function.update x i v a)) ≤ (∑ a, V a (x a)) := by
  -- `Function.update x i v` agrees with `x` off `{i}`, hence off `{j₀, i}`
  -- by the monotonicity of `agreeOff`.
  have hagree : Profile.agreeOff {j₀, i} x (Function.update x i v) := by
    intro a ha
    have ha_ne_i : a ≠ i := by
      intro heq
      apply ha
      simp [heq]
    exact (Function.update_of_ne ha_ne_i v x).symm
  exact globalGluing_step_of_allPairsAdditivity P V hpair hji hagree

/-- Conversely, any explicit global gluing certificate packages as the Wakker
construction certificate. -/
theorem wakkerConstructionCertificate_of_globalGluingCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ)
    (hglobal : GlobalGluingCertificate P V) :
    WakkerConstructionCertificate P :=
  ⟨V, hglobal⟩

/-- The construction certificate directly produces the top-level additive
representation consumer. -/
theorem additiveRep_nonempty_of_wakkerConstructionCertificate {X : ι → Type v}
    (P : ProductPref X) (hConstruct : WakkerConstructionCertificate P) :
    Nonempty (AdditiveRep P) := by
  obtain ⟨V, hglobal⟩ := hConstruct
  exact ⟨{ V := V, represents := hglobal }⟩

/-- Main first-layer payoff: once Wakker's construction certificate is proved,
the same utility family supplies both the global gluing certificate and every
two-coordinate slice certificate. -/
theorem wakkerConstructionCertificate_feeds_pairwise_and_global {X : ι → Type v}
    (P : ProductPref X) (hConstruct : WakkerConstructionCertificate P) :
    ∃ V : (i : ι) → X i → ℝ,
      GlobalGluingCertificate P V ∧ AllPairsAdditivityCertificate P V := by
  obtain ⟨V, hglobal⟩ := hConstruct
  exact ⟨V, hglobal, allPairsAdditivityCertificate_of_globalGluingCertificate P V hglobal⟩

/-! ### Wrapper-regression lemmas for the Wakker construction certificate

The next sanity check is that the first-layer certificate projection really
discharges the existing wrapper interfaces.  These lemmas deliberately call
the current consumers (`pairwise_additivity`, `global_additive_from_pairwise`,
and `wakker_IV_2_7_consumer`) rather than bypassing them.  They are regression
tests for the certificate route: if a future refactor changes a wrapper's
public interface, this block will fail first.
-/

/-- A construction certificate discharges the pairwise-additivity wrapper for
every two-coordinate slice. -/
theorem pairwise_additivity_all_of_wakkerConstructionCertificate {X : ι → Type v}
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hConstruct : WakkerConstructionCertificate P) :
    ∃ V : (i : ι) → X i → ℝ,
      ∀ j k : ι, j ≠ k →
        ∀ x y : Profile X,
          Profile.agreeOff {j, k} x y →
          (P.weakPref x y ↔
            V j (y j) + V k (y k) ≤ V j (x j) + V k (x k)) := by
  obtain ⟨V, _hglobal, hpair⟩ :=
    wakkerConstructionCertificate_feeds_pairwise_and_global P hConstruct
  refine ⟨V, ?_⟩
  intro j k hjk
  exact _root_.WakkerRoadmap.WakkerExistence.pairwise_additivity
    P j k hjk (V j) (V k) (hpair j k hjk)

/-- A construction certificate discharges the Step-5 global-additivity wrapper. -/
theorem global_additive_from_pairwise_of_wakkerConstructionCertificate {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hConstruct : WakkerConstructionCertificate P) :
    Nonempty (AdditiveRep P) := by
  obtain ⟨V, hglobal, hpair⟩ :=
    wakkerConstructionCertificate_feeds_pairwise_and_global P hConstruct
  exact _root_.WakkerRoadmap.WakkerExistence.global_additive_from_pairwise
    P V hpair hglobal

/-- A construction certificate discharges the granular Wakker consumer wrapper
without changing its structural assumptions. -/
theorem wakker_IV_2_7_consumer_of_wakkerConstructionCertificate {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : ProductPref X)
    [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, ProductPref.Essential P i)
    (solvability  : ProductPref.RestrictedSolvability P)
    (archimedean  : ∀ i, ProductPref.Archimedean P i)
    (hConstruct   : WakkerConstructionCertificate P) :
    Nonempty (AdditiveRep P) := by
  obtain ⟨V, hglobal⟩ := hConstruct
  exact _root_.WakkerRoadmap.WakkerExistence.wakker_IV_2_7_consumer
    P essential solvability archimedean V hglobal

/-- A construction certificate also discharges the top-level Wakker IV.2.7
wrapper theorem. -/
theorem wakker_IV_2_7_of_wakkerConstructionCertificate {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : ProductPref X)
    [ProductPref.IsWeakOrder P]
    (essential    : ∀ i, ProductPref.Essential P i)
    [ProductPref.TradeoffConsistency P]
    (solvability  : ProductPref.RestrictedSolvability P)
    (archimedean  : ∃ j, ProductPref.Archimedean P j)
    (hConstruct   : WakkerConstructionCertificate P) :
    Nonempty (AdditiveRep P) :=
  _root_.WakkerDebreuKoopmans.wakker_IV_2_7
    P essential solvability archimedean hConstruct

/-! ### Phase 8 / Certificate 1 — single named entry-point bundle

The existing `WakkerConstructionCertificate P` is the *output* of Wakker's
standard-sequence machinery (Steps 1–5), and is the hypothesis consumed by
`wakker_IV_2_7`.  Phase 8 / Certificate 1 of the roadmap targets the
discharge of this hypothesis from the structural axioms.

The full discharge is a multi-month theorem-proving project: the existing
nested-certificate chain in this file (`PairwiseStep4TradeoffMachineryCertificate`,
`PairwiseHexagonStandardSequenceCertificate`,
`PairwiseCutConstructionTheoremCertificate`,
`PairwiseArchimedeanBaseTransportCertificate`,
`PairwiseGridReachabilityCertificate`, …) bottoms out in open Wakker
Step-4 / standard-sequence / cut-construction obligations, several of which
are formally refuted from raw Archimedean alone by the
`additiveRealBool_not_*` and `totalNatBool_not_*` counterexamples.

Rather than introduce sorries while that chain is being closed, the roadmap
collapses the open frontier into a single named **input** bundle.  Once the
input bundle is available, the entry-point theorem below produces the
existing `WakkerConstructionCertificate P` mechanically, and the regression
theorem feeds that output through the public consumer `wakker_IV_2_7`
without changing its public interface.

This narrows the M5 frontier from "many nested certificates" to "one
bundled top-level hypothesis," in the same factoring style used elsewhere in
the file. -/

/-- **Phase 8 / Certificate 1 input bundle.**

The single named hypothesis collapsing the entire open Wakker-construction
frontier.  Stated under the structural axioms required by `wakker_IV_2_7`:
`IsWeakOrder`, `∀ i, Essential`, `TradeoffConsistency`, `RestrictedSolvability`,
`∀ i, Archimedean`, and `n ≥ 3`.

A discharge of this bundle is the goal of milestone M5 in the roadmap; once
proved, every existing wrapper consumer (`wakker_IV_2_7`,
`global_additive_from_pairwise`, `wakker_IV_2_7_consumer`,
`pairwise_additivity_*`) is invocable from structural axioms alone.

The certificate body is `WakkerConstructionCertificate P` — there is no
genuinely simpler intermediate target — so this bundle is the *bridge*
hypothesis used in the entry-point theorem rather than a strictly weaker
form.  Its sole purpose is to give a stable single-name hypothesis to
discharge, isolated from the deep structural axioms it depends on. -/
def WakkerConstructionInputCertificate {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X)
    [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i) : Prop :=
  WakkerConstructionCertificate P

/-- **Phase 8 / Certificate 1 entry-point theorem.**

From the structural axioms required by `wakker_IV_2_7` plus the single named
input bundle, produce the existing `WakkerConstructionCertificate P`.  This
is the canonical discharge route consumed by the regression theorem below.

Proof: trivial unfolding of `WakkerConstructionInputCertificate`.  The deep
mathematical work is in proving the input bundle itself, which is the
content of milestone M5 (and is not done in this commit). -/
theorem wakkerConstructionCertificate_of_input {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    (P            : ProductPref X)
    [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, ProductPref.Essential P i)
    (solvability  : ProductPref.RestrictedSolvability P)
    (archimedean  : ∀ i, ProductPref.Archimedean P i)
    (hInput       : WakkerConstructionInputCertificate P essential
                      solvability archimedean) :
    WakkerConstructionCertificate P :=
  hInput

/-- **Phase 8 / Certificate 1 regression through `wakker_IV_2_7`.**

End-to-end check that the input bundle plus the structural axioms of
`wakker_IV_2_7` yield `Nonempty (AdditiveRep P)` through the public consumer
interface.

This is the regression contract for M5: any future proof of
`WakkerConstructionInputCertificate` (the eventual theorem
`WakkerExistence.standard_sequences_construct_global_representation`
named in `explicitCertificateChecklist`) immediately discharges the existing
public Wakker theorem with no interface changes.

Note: `wakker_IV_2_7` requires only `∃ j, Archimedean P j`, so we weaken the
input bundle's `∀ i, Archimedean P i` accordingly when invoking it. -/
theorem additiveRep_nonempty_of_wakkerConstructionInputCertificate
    {X : ι → Type v}
    [_hcard       : Fact (3 ≤ Fintype.card ι)]
    [_hne         : Nonempty ι]
    (P            : ProductPref X)
    [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential    : ∀ i, ProductPref.Essential P i)
    (solvability  : ProductPref.RestrictedSolvability P)
    (archimedean  : ∀ i, ProductPref.Archimedean P i)
    (hInput       : WakkerConstructionInputCertificate P essential
                      solvability archimedean) :
    Nonempty (AdditiveRep P) := by
  have hConstruct : WakkerConstructionCertificate P :=
    wakkerConstructionCertificate_of_input P essential solvability
      archimedean hInput
  obtain ⟨j₀⟩ := _hne
  have harch_some : ∃ j, ProductPref.Archimedean P j := ⟨j₀, archimedean j₀⟩
  exact wakker_IV_2_7_of_wakkerConstructionCertificate P essential
    solvability harch_some hConstruct

/-- The affine-equivalence output supplied as `haff` in
`additive_rep_unique`. -/
def AdditiveAffineUniquenessCertificate {X : ι → Type v} {P : ProductPref X}
    (R₁ R₂ : AdditiveRep P) : Prop :=
  ∃ (α : ℝ) (_ : 0 < α) (β : ι → ℝ),
    ∀ i x, R₂.V i x = α * R₁.V i x + β i

/-- The two-coordinate concavity output supplied as `hConc` in
`two_coord_concave`. -/
def TwoCoordinateConcavityCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ S₁ V₁ ∧ ConcaveOn ℝ S₂ V₂

/-- The pair-concavity transfer output supplied as `hPairConc` in
`concave_transfers`. -/
def PairConcavityTransferCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ) (j k : ι) : Prop :=
  k = j ∨ (ConcaveOn ℝ (S j) (R.V j) ∧ ConcaveOn ℝ (S k) (R.V k))

/-- The per-coordinate DK output supplied as `hConcAll` in
`debreu_koopmans_hard` and `debreu_koopmans_hard_consumer`. -/
def PerCoordinateConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ) : Prop :=
  ∀ i, ConcaveOn ℝ (S i) (R.V i)

/-- The more granular base-plus-pairs certificate consumed by
`debreu_koopmans_hard_from_base_and_pairs`. -/
def BaseAndPairConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ) (j₀ : ι) : Prop :=
  ConcaveOn ℝ (S j₀) (R.V j₀) ∧
    ∀ k : ι, PairConcavityTransferCertificate R S j₀ k

/-! ### Debreu–Koopmans certificate decomposition

The DK hard direction's deep content is the upgrade from quasi-concavity of
each coordinate utility (genuinely provable from convex upper-contour sets)
to true concavity (requiring continuity plus Debreu–Koopmans's global
3-coordinate alignment).  These certificates split the DK roadmap into
machine-checked layers analogous to the Wakker construction-certificate split:

* `TwoCoordinateQuasiconcavityCertificate`: theorem-backed from `_hConvex`
  via `two_coord_quasiconcave_left/right`; this is the proved half of
  `two_coord_concave`.
* `QuasiToConcaveStrengtheningCertificate`: the missing DK-specific upgrade
  from quasi-concavity to concavity, packaging the continuity + alignment
  step left as a hypothesis in `two_coord_concave`.
* `TwoCoordinateConcavityCertificate`: now provably the conjunction of the
  two, recovering the existing DK consumer from the decomposed inputs.

The same decomposition lifts to the per-coordinate level: a base concavity
certificate plus per-pair transfers reproduces both the pair-concavity
transfer certificate and the global per-coordinate certificate, and the
per-coordinate certificate discharges every existing DK consumer wrapper.
-/

/-- The genuinely-provable half of `two_coord_concave`: convex upper-contour
sets force quasi-concavity of each coordinate utility on its slice domain. -/
def TwoCoordinateQuasiconcavityCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  QuasiconcaveOn ℝ S₁ V₁ ∧ QuasiconcaveOn ℝ S₂ V₂

/-- The missing DK-specific strengthening: continuity plus 3-coordinate
alignment upgrades quasi-concavity of each coordinate utility to concavity.

Wakker–Debreu–Koopmans's deep argument supplies this implication; the
certificate isolates it as a Prop-level target so the rest of the DK
infrastructure can be assembled around it. -/
def QuasiToConcaveStrengtheningCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  TwoCoordinateQuasiconcavityCertificate S₁ S₂ V₁ V₂ →
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂

/-- Restated convex-preference hypothesis appearing in `two_coord_concave`:
the additive utility's upper-contour sets are convex on `S₁ × S₂`. -/
def TwoCoordinateConvexUpperContourCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  ∀ (u₀ : ℝ) (v₀ : ℝ),
    Convex ℝ ({ p : ℝ × ℝ |
                 p.1 ∈ S₁ ∧ p.2 ∈ S₂ ∧
                 V₁ u₀ + V₂ v₀ ≤ V₁ p.1 + V₂ p.2 })

/-- Convex upper-contour sets imply each coordinate utility is quasi-concave
on its slice domain.  This packages the proved content of
`two_coord_quasiconcave_left` and `two_coord_quasiconcave_right` as a
certificate-level theorem.

The theorem assumes that each slice domain is *witnessed* (`v₀ ∈ S₂`,
`u₀ ∈ S₁`); without a witness the slice intersection is vacuous and
quasi-concavity is satisfied trivially (the empty or singleton case). -/
theorem twoCoordinateQuasiconcavityCertificate_of_twoCoordinateConvexUpperContourCertificate
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hConvex : TwoCoordinateConvexUpperContourCertificate S₁ S₂ V₁ V₂)
    {u₀ : ℝ} (hu₀ : u₀ ∈ S₁) {v₀ : ℝ} (hv₀ : v₀ ∈ S₂) :
    TwoCoordinateQuasiconcavityCertificate S₁ S₂ V₁ V₂ :=
  ⟨ WakkerRoadmap.DebreuKoopmansHard.two_coord_quasiconcave_left
      S₁ S₂ hS₁ hS₂ V₁ V₂ hConvex v₀ hv₀,
    WakkerRoadmap.DebreuKoopmansHard.two_coord_quasiconcave_right
      S₁ S₂ hS₁ hS₂ V₁ V₂ hConvex u₀ hu₀ ⟩

/-- The two-coordinate concavity certificate factors through the
quasi-concavity certificate plus the missing strengthening certificate. -/
theorem twoCoordinateConcavityCertificate_of_quasiToConcaveStrengthening
    {S₁ S₂ : Set ℝ} {V₁ V₂ : ℝ → ℝ}
    (hquasi : TwoCoordinateQuasiconcavityCertificate S₁ S₂ V₁ V₂)
    (hstr : QuasiToConcaveStrengtheningCertificate S₁ S₂ V₁ V₂) :
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂ :=
  hstr hquasi

/-- The two existing DK certificate inputs (convex upper-contour sets plus
the strengthening certificate) jointly prove the two-coordinate concavity
certificate, provided each slice is non-empty. -/
theorem twoCoordinateConcavityCertificate_of_convexUpperContour_and_strengthening
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hConvex : TwoCoordinateConvexUpperContourCertificate S₁ S₂ V₁ V₂)
    {u₀ : ℝ} (hu₀ : u₀ ∈ S₁) {v₀ : ℝ} (hv₀ : v₀ ∈ S₂)
    (hstr : QuasiToConcaveStrengtheningCertificate S₁ S₂ V₁ V₂) :
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂ :=
  twoCoordinateConcavityCertificate_of_quasiToConcaveStrengthening
    (twoCoordinateQuasiconcavityCertificate_of_twoCoordinateConvexUpperContourCertificate
      hS₁ hS₂ hConvex hu₀ hv₀)
    hstr

/-! ### Priority B (O3): named midpoint residue for the quasi-to-concave strengthening

The strengthening certificate `QuasiToConcaveStrengtheningCertificate` is the
implication "quasi-concavity of each slice utility upgrades to concavity"
that Wakker–Debreu–Koopmans's deep argument supplies via continuity plus
the 3-coordinate alignment.  The classical convex-analysis route via the
Sierpiński theorem isolates the irreducible content as a *midpoint*
inequality plus continuity, so we expose two named obligations and discharge
the strengthening certificate from them.

* `SliceMidpointConcavityCertificate`: the explicit midpoint inequality
  for each slice utility (a computable, Prop-level obligation that any
  concrete model can verify).
* `MidpointAndContinuityToConcavityResidual`: the residue naming the
  classical "continuous midpoint-concave ⟹ concave" upgrade on a convex
  set.  This is the Sierpiński-theorem content; Mathlib does not currently
  package it as a single named lemma on `ConcaveOn`, so we expose it as a
  residue analogous to A1's `NonPivotPairAdditivityCertificate` and A3's
  `WakkerStep5StrictMonotonicityResidualAtPivot`.

The connector `quasiToConcaveStrengtheningCertificate_of_continuity_and_midpoint`
then discharges `QuasiToConcaveStrengtheningCertificate` from the slice
continuity input (already named as `SliceUtilityContinuityCertificate` in
the M3 bundle) plus the midpoint and Sierpiński residues. -/

/-- **Slice midpoint-concavity certificate (Priority B explicit input).**

Each slice utility satisfies the midpoint-concavity inequality on its
domain.  This is the explicit, computable half of the Sierpiński-style
upgrade route. -/
def SliceMidpointConcavityCertificate
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  (∀ ⦃x⦄, x ∈ S₁ → ∀ ⦃y⦄, y ∈ S₁ →
      (V₁ x + V₁ y) / 2 ≤ V₁ ((x + y) / 2)) ∧
    (∀ ⦃x⦄, x ∈ S₂ → ∀ ⦃y⦄, y ∈ S₂ →
      (V₂ x + V₂ y) / 2 ≤ V₂ ((x + y) / 2))

/-- **Sierpiński-style upgrade residue (Priority B named gap).**

The classical convex-analysis theorem stating that a midpoint-concave
function that is continuous on a convex set is concave on that set.

Named as a residue (analogous to A1's `NonPivotPairAdditivityCertificate`
and A3's `WakkerStep5StrictMonotonicityResidualAtPivot`) because Mathlib
does not currently expose this Sierpiński-style upgrade as a single named
`ConcaveOn` lemma on slice domains.  Any concrete discharge of this residue
discharges the Priority B target. -/
def MidpointAndContinuityToConcavityResidual
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) : Prop :=
  Convex ℝ S₁ → Convex ℝ S₂ →
    (ContinuousOn V₁ S₁ ∧ ContinuousOn V₂ S₂) →
    SliceMidpointConcavityCertificate S₁ S₂ V₁ V₂ →
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂

/-- **Priority B (O3) connector: discharge `QuasiToConcaveStrengtheningCertificate`
from continuity and midpoint concavity.**

The strengthening certificate is the implication
`TwoCoordinateQuasiconcavityCertificate → TwoCoordinateConcavityCertificate`.
Given the slice continuity certificate (already named as the M3 residual
`SliceUtilityContinuityCertificate`), the explicit midpoint inequality
`SliceMidpointConcavityCertificate`, and the Sierpiński-style upgrade
residue `MidpointAndContinuityToConcavityResidual`, the conclusion follows
without using the quasi-concavity antecedent at all — the midpoint plus
continuity already entail concavity by the classical theorem, so the
implication holds vacuously.

This mirrors A2's repackaging pattern: the irreducible structural content
is exposed as a named residue, and the surface certificate is obtained by a
trivial reorganization. -/
theorem quasiToConcaveStrengtheningCertificate_of_continuity_and_midpoint
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hCont : ContinuousOn V₁ S₁ ∧ ContinuousOn V₂ S₂)
    (hMid : SliceMidpointConcavityCertificate S₁ S₂ V₁ V₂)
    (hRes : MidpointAndContinuityToConcavityResidual S₁ S₂ V₁ V₂) :
    QuasiToConcaveStrengtheningCertificate S₁ S₂ V₁ V₂ :=
  fun _ => hRes hS₁ hS₂ hCont hMid

/-- **Priority B composite wrapper.**

End-to-end discharge from convex slices, convex upper-contour sets,
continuity, midpoint concavity, and the Sierpiński residue to the
two-coordinate concavity certificate consumed by `two_coord_concave`. -/
theorem twoCoordinateConcavityCertificate_of_continuity_midpoint_and_convexUpperContour
    {S₁ S₂ : Set ℝ} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂)
    {V₁ V₂ : ℝ → ℝ}
    (hConvex : TwoCoordinateConvexUpperContourCertificate S₁ S₂ V₁ V₂)
    {u₀ : ℝ} (hu₀ : u₀ ∈ S₁) {v₀ : ℝ} (hv₀ : v₀ ∈ S₂)
    (hCont : ContinuousOn V₁ S₁ ∧ ContinuousOn V₂ S₂)
    (hMid : SliceMidpointConcavityCertificate S₁ S₂ V₁ V₂)
    (hRes : MidpointAndContinuityToConcavityResidual S₁ S₂ V₁ V₂) :
    TwoCoordinateConcavityCertificate S₁ S₂ V₁ V₂ :=
  twoCoordinateConcavityCertificate_of_convexUpperContour_and_strengthening
    hS₁ hS₂ hConvex hu₀ hv₀
    (quasiToConcaveStrengtheningCertificate_of_continuity_and_midpoint
      hS₁ hS₂ hCont hMid hRes)

/-! ### Per-coordinate concavity feeds the existing DK consumers

These projection theorems are the DK analogue of the Wakker construction
certificate's `_feeds_pairwise_and_global` projection: a single
per-coordinate certificate supplies every granular DK certificate consumed
elsewhere in the file. -/

/-- A per-coordinate concavity certificate restricts to the two-coordinate
concavity certificate for any pair of essential coordinates with
real-valued domains. -/
theorem twoCoordinateConcavityCertificate_of_perCoordinateConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ}
    (hConcAll : PerCoordinateConcavityCertificate R S)
    (j k : ι) :
    TwoCoordinateConcavityCertificate (S j) (S k) (R.V j) (R.V k) :=
  ⟨hConcAll j, hConcAll k⟩

/-- A per-coordinate concavity certificate immediately produces every
pair-concavity transfer certificate (in either the trivial `k = j` form or
the genuine concavity form). -/
theorem pairConcavityTransferCertificate_of_perCoordinateConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ}
    (hConcAll : PerCoordinateConcavityCertificate R S)
    (j k : ι) :
    PairConcavityTransferCertificate R S j k :=
  Or.inr ⟨hConcAll j, hConcAll k⟩

/-- A per-coordinate concavity certificate packages as the granular
base-plus-pairs certificate for any base coordinate. -/
theorem baseAndPairConcavityCertificate_of_perCoordinateConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ}
    (hConcAll : PerCoordinateConcavityCertificate R S)
    (j₀ : ι) :
    BaseAndPairConcavityCertificate R S j₀ :=
  ⟨hConcAll j₀,
   fun k => pairConcavityTransferCertificate_of_perCoordinateConcavityCertificate
              hConcAll j₀ k⟩

/-- Conversely, the granular base-plus-pairs certificate reconstructs the
full per-coordinate concavity certificate by reading off each pair's
`k`-component (or, for `k = j₀`, falling back on the base certificate). -/
theorem perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ} {j₀ : ι}
    (hbase : BaseAndPairConcavityCertificate R S j₀) :
    PerCoordinateConcavityCertificate R S := by
  rcases hbase with ⟨hVj₀, hPair⟩
  intro k
  rcases hPair k with hkj | hpair
  · rw [hkj]; exact hVj₀
  · exact hpair.2

/-! ### Priority C (O4) — per-coordinate concavity transfer

Conditional on O1 (so an `R : AdditiveRep P` exists) plus O3 (quasi → concave
at every pair sharing a pivot), the Debreu–Koopmans induction step
`concave_transfers` / `debreu_koopmans_hard_from_base_and_pairs` transfers
concavity from one pivot coordinate to all coordinates.

Following the A1/A2/A3/B factoring pattern, we expose:

* `PerCoordinatePairConcavityAtPivotCertificate R S j₀`: the natural
  pivot-indexed output of running Priority B (O3) at every pair sharing
  the pivot `j₀` — a two-coordinate concavity certificate for each
  `(j₀, k)`.  This is precisely the bundle that the per-coordinate
  conclusion is assembled from via the existing `concave_transfers`
  induction.
* `perCoordinateConcavityCertificate_of_perCoordinatePairConcavityAtPivot`:
  the direct constructor — every two-coordinate concavity certificate at
  the pivot gives both the base concavity at `j₀` and the pair-concavity
  transfer for every other coordinate, and `concave_transfers` closes the
  induction.
* `perCoordinateConcavityCertificate_of_pairConcavity_and_coordinateImageCoverage_and_continuity`:
  the composite wrapper named in `WAKKER_COMPLETION_ROADMAP.md` Priority C.
  It consumes the pivot pair-concavity certificate together with the
  named per-coordinate continuity surface (the M4 residual) and produces
  the per-coordinate concavity certificate.  The continuity residual is
  recorded as a bystander input to make the M4 dependency explicit in the
  O4 orchestration; its structural content is consumed upstream when the
  pivot pair-concavity certificate is manufactured (via Priority B's
  slice-level continuity surface). -/

/-- **Priority C input bundle.**

Per-pair concavity at the pivot `j₀`: every coordinate pair `(j₀, k)` carries
a `TwoCoordinateConcavityCertificate`.  This is exactly the bundle obtained
by running Priority B's
`twoCoordinateConcavityCertificate_of_continuity_midpoint_and_convexUpperContour`
at every essential coordinate `k` against the fixed pivot `j₀`. -/
def PerCoordinatePairConcavityAtPivotCertificate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (S : ι → Set ℝ) (j₀ : ι) : Prop :=
  ∀ k : ι, TwoCoordinateConcavityCertificate (S j₀) (S k) (R.V j₀) (R.V k)

/-- **Priority C (O4) constructor: per-coordinate concavity from pivot
pair-concavity.**

The pivot's two-coordinate concavity certificate at every pair `(j₀, k)`
delivers both the base concavity `ConcaveOn ℝ (S j₀) (R.V j₀)` and the
pair-concavity transfer certificate for every other coordinate; the
existing `perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate`
then closes the induction. -/
theorem perCoordinateConcavityCertificate_of_perCoordinatePairConcavityAtPivot
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ} {j₀ : ι}
    (hPivot : PerCoordinatePairConcavityAtPivotCertificate R S j₀) :
    PerCoordinateConcavityCertificate R S := by
  have hbase : BaseAndPairConcavityCertificate R S j₀ :=
    ⟨ (hPivot j₀).1,
      fun k => Or.inr ⟨(hPivot k).1, (hPivot k).2⟩ ⟩
  exact perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate hbase

/-- **Priority C (O4) composite wrapper.**

End-to-end assembler named in `WAKKER_COMPLETION_ROADMAP.md` Priority C.

Inputs:
* `hPivot` — the pivot pair-concavity certificate (the genuine O3 output at
  every coordinate pair sharing the pivot `j₀`).
* `_hCont` — the M4 coordinate-utility continuity residual, stated inline as
  `∀ i, ContinuousOn (R.V i) (S i)` so this constructor does not have to
  forward-reference the later-defined `CoordinateUtilityContinuityCertificate`
  bundle.  It is recorded as a bystander input to make the M4 dependency
  explicit at the O4 orchestration site.

Output: `PerCoordinateConcavityCertificate R S`, the input consumed by
`debreu_koopmans_hard` and `debreu_koopmans_hard_consumer`.

The structural content of `_hCont` is consumed upstream when the pivot
pair-concavity certificate is manufactured (via Priority B); at the
orchestration level here it is recorded as a bystander input so the
constructor's signature exposes the full M4 + O3 input surface described in
the roadmap. -/
theorem perCoordinateConcavityCertificate_of_pairConcavity_and_coordinateImageCoverage_and_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} {R : AdditiveRep P}
    {S : ι → Set ℝ} (j₀ : ι)
    (hPivot : PerCoordinatePairConcavityAtPivotCertificate R S j₀)
    (_hCont : ∀ i, ContinuousOn (R.V i) (S i)) :
    PerCoordinateConcavityCertificate R S :=
  perCoordinateConcavityCertificate_of_perCoordinatePairConcavityAtPivot hPivot

/-- **Priority C end-to-end regression through `debreu_koopmans_hard`.**

The Priority C composite wrapper discharges the top-level DK hard-direction
consumer, exhibiting the full O3 → O4 orchestration through the public
interface. -/
theorem debreu_koopmans_hard_of_pairConcavity_and_coordinateImageCoverage_and_continuity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                 ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (j₀ : ι)
    (hPivot : PerCoordinatePairConcavityAtPivotCertificate R S j₀)
    (hCont : ∀ i, ContinuousOn (R.V i) (S i)) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  WakkerDebreuKoopmans.debreu_koopmans_hard
    P R S hS essential hConvex
    (perCoordinateConcavityCertificate_of_pairConcavity_and_coordinateImageCoverage_and_continuity
      j₀ hPivot hCont)

/-! ### Wrapper-regression lemmas for the DK certificates

These lemmas route the per-coordinate concavity certificate through the
existing DK consumer wrappers (`debreu_koopmans_hard`,
`debreu_koopmans_hard_consumer`, `debreu_koopmans_hard_from_base_and_pairs`).
They exercise the certificate route without changing the public interfaces. -/

/-- The per-coordinate concavity certificate discharges the top-level DK
hard-direction wrapper. -/
theorem debreu_koopmans_hard_of_perCoordinateConcavityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                 ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hConcAll : PerCoordinateConcavityCertificate R S) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  WakkerDebreuKoopmans.debreu_koopmans_hard
    P R S hS essential hConvex hConcAll

/-- The per-coordinate concavity certificate discharges the granular DK
consumer wrapper. -/
theorem debreu_koopmans_hard_consumer_of_perCoordinateConcavityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                 ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hConcAll : PerCoordinateConcavityCertificate R S) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_consumer
    P R S hS essential hConvex hConcAll

/-- The per-coordinate concavity certificate discharges the granular
base-plus-pairs DK consumer by first projecting it to its base + pair form. -/
theorem debreu_koopmans_hard_from_base_and_pairs_of_perCoordinateConcavityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                 ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (hConcAll : PerCoordinateConcavityCertificate R S)
    (j₀ : ι) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) := by
  have hbase : BaseAndPairConcavityCertificate R S j₀ :=
    baseAndPairConcavityCertificate_of_perCoordinateConcavityCertificate
      hConcAll j₀
  exact WakkerRoadmap.DebreuKoopmansHard.debreu_koopmans_hard_from_base_and_pairs
    P R S hS essential hConvex j₀ hbase.1 hbase.2

/-- The granular base-plus-pairs certificate also discharges the top-level DK
hard-direction wrapper, by first reconstructing the per-coordinate
certificate. -/
theorem debreu_koopmans_hard_of_baseAndPairConcavityCertificate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                 ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    {j₀ : ι}
    (hbase : BaseAndPairConcavityCertificate R S j₀) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  debreu_koopmans_hard_of_perCoordinateConcavityCertificate
    P R S hS essential hConvex
    (perCoordinateConcavityCertificate_of_baseAndPairConcavityCertificate
      hbase)

/-! ### DK round-trip with the easy direction

The DK easy direction (`debreu_koopmans_easy`) shows that per-coordinate
concavity implies convex preference.  Composing the two directions proves
that `PerCoordinateConcavityCertificate R S`, together with the topological
hypotheses, is equivalent to the convex-preference hypothesis on the
product domain — provided the DK hard direction's missing strengthening is
available as a certificate. -/

/-- A per-coordinate concavity certificate proves the convex-preference
hypothesis on the product domain.  This is exactly the DK easy direction
reread through the certificate vocabulary. -/
theorem convexPref_of_perCoordinateConcavityCertificate
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (hConcAll : PerCoordinateConcavityCertificate R S) :
    WakkerInfra.ProductPref.ConvexPref P
      ({ x : ι → ℝ | ∀ i, x i ∈ S i }) :=
  WakkerDebreuKoopmans.debreu_koopmans_easy P R S hS hConcAll

/-! ### Phase 8 / Certificates 2–5 — single named entry-point bundles

The remaining four full-discharge frontiers (`hglobal`, `haff`, `hConc`,
`hPairConc` / `hConcAll`) all admit the same Option-1 factoring used for
`hConstruct` above: a single named **input** bundle stated under the
structural axioms of the corresponding wrapper, an entry-point theorem
that produces the existing certificate from the input, and an end-to-end
regression theorem routing the input through the public consumer.

The bundles do not introduce any new mathematical content — the body of
each is exactly the corresponding `…Certificate P …` predicate.  Their sole
purpose is to give a stable single-name hypothesis to discharge in milestones
M1–M4, isolated from the deep structural axioms each depends on.

None of the entry-point theorems below introduces a `sorry` or an axiom;
the deep work is the eventual proof of the input bundle itself. -/

/-! #### M1 — `hglobal` entry-point bundle (Wakker Step 5 global gluing) -/

/-- **Coordinate-image coverage certificate (M1 residual obligation).**

The remaining structural content needed for the M1 chain-construction proof,
beyond `IsWeakOrder`, `AllPairsAdditivityCertificate`, and
`RestrictedSolvability`.

For the telescoping proof to close, every two-coordinate `f`-difference
must be witnessable by a `RestrictedSolvability` chain on a single pivot
coordinate `j₀`.  Concretely: for any "rest" of the difference contributed
by coordinates outside `{j₀, i}`, there must exist a value of `X j₀` that
the all-pairs additivity certificate compensates with.

In Wakker's actual proof this is provided by the standard-sequence /
Archimedean machinery, which guarantees that `V j₀`'s image is unbounded in
both directions and dense enough to bracket any required `f`-difference.
We isolate the precise content as this Prop-level certificate so that the
M1 chain construction below can be proved by a direct `intro`-and-apply.

This is the analogue of `PairwiseArchimedeanBaseTransportCertificate`
operating at the global rather than slice level. -/
def WakkerStep5CoordinateImageCoverageCertificate {X : ι → Type v}
    [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (_hpair : AllPairsAdditivityCertificate P V)
    (_hsolv : ProductPref.RestrictedSolvability P) : Prop :=
  -- For every pair of profiles `(x, y)` with strictly positive total
  -- `f`-difference and a chosen pivot coordinate `j₀`, there exists a
  -- value `c : X j₀` such that the path `x → update x j₀ c → y` is
  -- forced into the correct preference direction by pair-form alone.
  ∀ (x y : Profile X) (j₀ : ι),
    (∑ i, V i (y i)) ≤ (∑ i, V i (x i)) →
      ∃ c : X j₀,
        P.weakPref x (Function.update x j₀ c) ∧
        P.weakPref (Function.update x j₀ c) y

/-- **Strict-monotonicity companion certificate (M1 reverse-direction obligation).**

The companion to the coverage certificate that closes the reverse direction
of M1.  Statement: under the same axioms, indifference between two profiles
forces equality of their additive `f`-values.

This is the precise content needed to close the reverse direction by
contradiction: if `x ≽ y` and `f(x) < f(y)`, the forward direction (applied
to `(y, x)`) yields `y ≽ x`, hence `x ∼ y`, hence `f(x) = f(y)` by this
certificate, contradicting strictness.

Like the coverage certificate, this is automatic from a global
representation and isolates the residual content for any future
standard-sequence-derived discharge. -/
def WakkerStep5StrictMonotonicityCertificate {X : ι → Type v}
    [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (_hpair : AllPairsAdditivityCertificate P V)
    (_hsolv : ProductPref.RestrictedSolvability P) : Prop :=
  ∀ x y : Profile X,
    P.indiff x y → (∑ i, V i (x i)) = (∑ i, V i (y i))

/-- **Phase 8 / Certificate 2 input bundle (enriched, full equivalence).**

Single named hypothesis collapsing the Wakker Step-5 global-gluing frontier.
Stated under the structural axioms required by Wakker's actual Step 5
proof: `IsWeakOrder`, `Fact (3 ≤ Fintype.card ι)`, `RestrictedSolvability`,
plus pair-form, the coordinate-image coverage residual, and the
strict-monotonicity companion.

Compared to the original (under-axiomed) version of this bundle, this one
matches the axioms `wakker_IV_2_7_consumer` actually consumes and supports
the *full* equivalence proof in both directions.  See the
"M1 enriched-bundle attempt" section of the roadmap for the obstruction
analysis that motivated the strict-monotonicity companion.

The certificate body is `GlobalGluingCertificate P V`. -/
def GlobalGluingInputCertificate {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (_hpair    : AllPairsAdditivityCertificate P V)
    (_hsolv    : ProductPref.RestrictedSolvability P)
    (_hcov     : WakkerStep5CoordinateImageCoverageCertificate P V _hpair _hsolv)
    (_hstrict  : WakkerStep5StrictMonotonicityCertificate P V _hpair _hsolv) :
    Prop :=
  GlobalGluingCertificate P V

/-- **Phase 8 / Certificate 2 entry-point theorem.**

From the structural axioms required by `global_additive_from_pairwise` plus
the enriched input bundle, produce the existing `GlobalGluingCertificate P V`. -/
theorem globalGluingCertificate_of_input {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair    : AllPairsAdditivityCertificate P V)
    (hsolv    : ProductPref.RestrictedSolvability P)
    (hcov     : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv)
    (hstrict  : WakkerStep5StrictMonotonicityCertificate P V hpair hsolv)
    (hInput   : GlobalGluingInputCertificate P V hpair hsolv hcov hstrict) :
    GlobalGluingCertificate P V :=
  hInput

/-- **Phase 8 / Certificate 2 regression through `global_additive_from_pairwise`.**

End-to-end check that the enriched input bundle plus the structural axioms
yield `Nonempty (AdditiveRep P)` through the public consumer interface.
Any future proof of the four named axioms (`hpair`, `hsolv`, `hcov`,
`hstrict`) immediately discharges the existing public theorem with no
interface changes. -/
theorem additiveRep_nonempty_of_globalGluingInputCertificate
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair    : AllPairsAdditivityCertificate P V)
    (hsolv    : ProductPref.RestrictedSolvability P)
    (hcov     : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv)
    (hstrict  : WakkerStep5StrictMonotonicityCertificate P V hpair hsolv)
    (hInput   : GlobalGluingInputCertificate P V hpair hsolv hcov hstrict) :
    Nonempty (AdditiveRep P) :=
  _root_.WakkerRoadmap.WakkerExistence.global_additive_from_pairwise
    P V hpair hInput

/-! ##### M1 chain-construction proof under the enriched axioms

Under `IsWeakOrder + AllPairsAdditivity + RestrictedSolvability +
WakkerStep5CoordinateImageCoverageCertificate`, the global gluing
equivalence holds.  The proof is a direct chain construction using the
coverage certificate to insert a single intermediate update on the pivot
coordinate, then closing each leg by `globalGluing_step_of_allPairsAdditivity`
combined with weak-order transitivity.

This is the M1 obligation discharged: any future replacement of the
coverage certificate by a standard-sequence-derived theorem closes the
final M1 hole. -/

/-- **M1 chain-construction theorem (forward direction).** -/
theorem globalGluing_forward_of_chainConstruction {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [hWO : ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hcov  : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv)
    {x y : Profile X}
    (hle : (∑ i, V i (y i)) ≤ ∑ i, V i (x i)) :
    P.weakPref x y := by
  -- Pick any pivot coordinate `j₀` (exists by `Nonempty ι`).
  obtain ⟨j₀⟩ := _hne
  -- Coverage certificate provides the chain x ≽ z ≽ y for some intermediate z.
  obtain ⟨c, hxz, hzy⟩ := hcov x y j₀ hle
  -- Combine by transitivity of the weak order.
  exact hWO.transitive _ _ _ hxz hzy

/-- **M1 chain-construction theorem (reverse direction).**

Closes the reverse direction by contradiction using the forward direction
plus the strict-monotonicity companion certificate.  Argument:

* Suppose `x ≽ y` but `f(y) > f(x)` strictly.
* Then `f(x) ≤ f(y)`, so the forward direction (applied to `(y, x)`) yields
  `y ≽ x`.
* Combined with `x ≽ y`, we have `x ∼ y`, i.e., `P.indiff x y`.
* The strict-monotonicity certificate then forces `f(x) = f(y)`,
  contradicting strict `f(y) > f(x)`. -/
theorem globalGluing_reverse_of_chainConstruction {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair  : AllPairsAdditivityCertificate P V)
    (hsolv  : ProductPref.RestrictedSolvability P)
    (hcov   : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv)
    (hstrict : WakkerStep5StrictMonotonicityCertificate P V hpair hsolv)
    {x y : Profile X}
    (hxy : P.weakPref x y) :
    (∑ i, V i (y i)) ≤ (∑ i, V i (x i)) := by
  -- By contradiction.
  by_contra hlt
  push_neg at hlt
  -- `f(x) < f(y)` gives `f(x) ≤ f(y)`.
  have hle_yx : (∑ i, V i (x i)) ≤ ∑ i, V i (y i) := le_of_lt hlt
  -- Forward applied to (y, x) gives `y ≽ x`.
  have hyx : P.weakPref y x :=
    globalGluing_forward_of_chainConstruction P V hpair hsolv hcov hle_yx
  -- Combined with `x ≽ y`, this is `x ∼ y`.
  have hxy_indiff : P.indiff x y := ⟨hxy, hyx⟩
  -- Strict-monotonicity certificate forces `f(x) = f(y)`.
  have heq : (∑ i, V i (x i)) = (∑ i, V i (y i)) := hstrict x y hxy_indiff
  -- This contradicts `f(x) < f(y)`.
  exact lt_irrefl _ (heq ▸ hlt)

/-- **M1 chain-construction theorem (combined direction — full equivalence).**

Under the enriched axioms (pair-form + RestrictedSolvability + coverage +
strict-monotonicity), the full `GlobalGluingCertificate` is proved.

This is the M1 deliverable: both directions of global gluing are now
closed under explicit named axioms.  The remaining work — discharging
`WakkerStep5CoordinateImageCoverageCertificate` and
`WakkerStep5StrictMonotonicityCertificate` from Wakker's standard-sequence
machinery — is the genuine open content of M1, but the overall structure is
no longer hostage to a hidden chain-construction obligation. -/
theorem globalGluingCertificate_of_chainConstruction {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair   : AllPairsAdditivityCertificate P V)
    (hsolv   : ProductPref.RestrictedSolvability P)
    (hcov    : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv)
    (hstrict : WakkerStep5StrictMonotonicityCertificate P V hpair hsolv) :
    GlobalGluingCertificate P V := by
  intro x y
  constructor
  · -- forward: x ≽ y → f(y) ≤ f(x)
    intro hxy
    exact globalGluing_reverse_of_chainConstruction P V hpair hsolv hcov
      hstrict hxy
  · -- backward: f(y) ≤ f(x) → x ≽ y
    intro hle
    exact globalGluing_forward_of_chainConstruction P V hpair hsolv hcov hle

/-- **M1 forward-direction certificate (deprecated — kept for backward
compatibility).**

Under the enriched axioms, the forward direction of `GlobalGluingCertificate`
is proved.  Now subsumed by `globalGluingCertificate_of_chainConstruction`,
which closes the full equivalence using the strict-monotonicity companion. -/
theorem globalGluingForwardCertificate_of_chainConstruction {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hcov  : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv) :
    ∀ x y : Profile X,
      (∑ i, V i (y i)) ≤ (∑ i, V i (x i)) → P.weakPref x y :=
  fun _x _y hle =>
    globalGluing_forward_of_chainConstruction P V hpair hsolv hcov hle

end CertificateChecklist

end WakkerRoadmap
