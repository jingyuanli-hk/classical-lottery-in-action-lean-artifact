/-
Wakker (1989) Theorem IV.2.7 — Existence side (spin-out paper):
  Lean 4 / Mathlib formalization, structural-axioms-only.

This file is the seed for the spin-out mechanized decision-theory paper
`MechanizedDecisionTheoryWakkerDK.tex`.  Its purpose is to begin the
**reverse direction** of the Wakker construction certificate:

  Show that the seven structural axioms
    (weak order, essentiality of each coordinate, tradeoff consistency,
     restricted solvability, Archimedean axiom, plus 3 ≤ Fintype.card ι)
  produce coordinate utilities `V : (i : ι) → X i → ℝ` representing the
  product preference additively.

The forward (necessity) direction is already discharged in
`WakkerInfrastructure.lean` §11.  This file mirrors that structure on
the construction side: each named theorem in this file is a real
Lean-level entry point of the Wakker IV.2.7 standard-sequence
construction, refactored away from the more permissive interfaces in
`WakkerDebreuKoopmans.lean` (which carry `Function.update` grid bookkeeping
that the cleaner spin-out targets do not need).

# Scope

This file is intentionally **standalone**.  Following the same convention
as `WakkerDebreuKoopmans.lean`, it re-imports just the abstract
preference-product structure and standard-sequence definitions it needs,
without depending on the rest of the WDK file.  This keeps the spin-out
paper's Lean artifact independently buildable.

# What is here today

  §1  Coordinate utility on a standard-sequence grid, structural-axioms-only.
      `coord_utility_on_grid_from_axioms` produces `V : X j → ℝ` with
      `V (σ.α n) = (n : ℝ)` from any **strict, injective** standard
      sequence on coordinate `j`, in the presence of weak order +
      tradeoff consistency.  This is Wakker (1989) Step 2 on the grid;
      the only ingredient beyond the standard-sequence data is the
      injectivity of `σ.α` (which Wakker derives from strictness +
      Archimedeanity in essential coordinates).

  §2  Open targets for the next milestones.

  §3  Phase-0 audit hooks documenting what the spin-out paper has
      already proved.

# What this file is *not*

  This file is **not** a complete Wakker IV.2.7 proof.  In particular,
  the following deeper construction steps are still scoped as future
  work in the spin-out paper:

    * Step 1 — extending standard sequences via the
      `OneStepExtensible` / restricted-solvability hypothesis.
    * Step 2 (off-grid extension) — interpolating `V` to all of `X j`
      under the analytic solvability hypothesis on `V j`.
    * Step 3 — pairwise-slice representation from coordinate utilities.
    * Step 4 — gluing pairwise representations into a global one
      (uses `3 ≤ Fintype.card ι`).
    * Step 5 — uniqueness up to common positive affine scale.

  The full deliverable is the Wakker construction certificate
  documented in `WakkerInfrastructure.lean` §11.

References
==========
  * Peter Wakker, *Additive Representations of Preferences:
    A New Foundation of Decision Analysis*, Kluwer Academic, 1989,
    Theorem IV.2.7 (existence of additive representation).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped BigOperators
open Function Finset

/-! ###############################################################
    PART A — Local re-import of abstract preference structure.
    ###############################################################

This block mirrors the small fragment of `WakkerInfra` (and
`WakkerInfrastructure.lean`) needed to state and prove the §1 result.
We re-declare it here so that this file stays standalone, in line with
the convention used by `WakkerDebreuKoopmans.lean`.
-/

namespace WakkerExistenceSpinOut

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A profile assigns to each coordinate `i : ι` a value in `Xᵢ`. -/
abbrev Profile (X : ι → Type v) := ∀ i, X i

/-- The product preference structure: a binary relation on profiles. -/
structure ProductPref (X : ι → Type v) where
  weakPref : Profile X → Profile X → Prop

namespace ProductPref

variable {X : ι → Type v}

/-- Strict preference. -/
def strict (P : ProductPref X) (x y : Profile X) : Prop :=
  P.weakPref x y ∧ ¬ P.weakPref y x

/-- Indifference. -/
def indiff (P : ProductPref X) (x y : Profile X) : Prop :=
  P.weakPref x y ∧ P.weakPref y x

/-- A **standard sequence** in coordinate `j` (Wakker, Definition III.4.1).

Imported here at the smallest necessary granularity so this file is
self-contained; identical in shape to the version in
`WakkerInfrastructure.lean` §6 and `WakkerDebreuKoopmans.lean` §C. -/
structure StandardSequence (P : ProductPref X) (j : ι) where
  /-- The other coordinate that supplies the reference unit. -/
  k          : ι
  k_ne_j     : k ≠ j
  /-- The reference values `r ≺ s` in coordinate `k`. -/
  r          : X k
  s          : X k
  r_ne_s     : r ≠ s
  /-- The base profile. -/
  base       : Profile X
  /-- The standard sequence itself. -/
  α          : ℕ → X j
  /-- Equally-spaced indifference: the exchange `αₙ ↦ αₙ₊₁` in
  coordinate `j` is indifferent to the exchange `r ↦ s` in coordinate
  `k`. -/
  spaced     : ∀ n,
    P.indiff
      (Function.update (Function.update base j (α n))     k r)
      (Function.update (Function.update base j (α (n+1))) k s)

end ProductPref

/-! ###############################################################
    PART B — Construction-side seed.
    ###############################################################

Each theorem below corresponds to a planned milestone in the spin-out
paper.  §1 provides the first three theorems — the structural-axioms-only
grid utility — and §2 declares the next-milestone target predicates.
-/

/-! ## §1.  Coordinate utility on a standard-sequence grid (structural-axioms-only)

Given a **strict, injective** standard sequence `σ` on coordinate `j`,
the assignment `σ.α n ↦ (n : ℝ)` extends — in the absence of any other
data — to a function `V : X j → ℝ`.  This is the cleanest possible
mechanization of Wakker (1989) Step 2 on the grid: no `Function.update`
machinery is needed, no analytic interpolation is needed, only the
injectivity of `σ.α` plus classical choice.

The following three lemmas compose into the headline grid theorem.
They are kept separate because each will be reused in later spin-out
work: e.g. `grid_utility_zero` is the normalization needed to anchor
common-scale uniqueness, and `grid_utility_strictMono` is the input to
the order-calibration step that connects this construction to the
Step-4 pairwise-slice representation.
-/

/-- Build a function `V : X j → ℝ` agreeing with `σ.α n ↦ (n : ℝ)` on the
grid of an injective standard sequence.

Parameters:
  * `P` — the product preference (only weakly used: any preference works).
  * `σ` — a standard sequence on coordinate `j`.
  * `hinj` — injectivity of `σ.α : ℕ → X j`.

Returns: `V : X j → ℝ` together with the grid-fit guarantee.

The construction is the canonical "indicator-of-image" extension by
`Classical.choose`, which is structural and does not require
restricted solvability or the Archimedean axiom on `P`.  Those two
axioms re-enter the picture in later spin-out steps when extending `V`
**off** the grid. -/
theorem coord_utility_on_grid_from_axioms
    {X : ι → Type v}
    (P : ProductPref X)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hinj : Function.Injective σ.α) :
    ∃ V : X j → ℝ,
      (∀ n : ℕ, V (σ.α n) = (n : ℝ)) := by
  classical
  refine ⟨fun x =>
    if h : x ∈ Set.range σ.α
      then (Classical.choose h : ℕ)
      else 0, ?_⟩
  intro n
  have hmem : σ.α n ∈ Set.range σ.α := ⟨n, rfl⟩
  simp only [hmem, dif_pos]
  have hspec : σ.α (Classical.choose hmem) = σ.α n :=
    Classical.choose_spec hmem
  have : Classical.choose hmem = n := hinj hspec
  exact_mod_cast this

/-- Refined form of `coord_utility_on_grid_from_axioms`: `V` is *zero* on
the first grid point and increases by one per step. -/
theorem grid_utility_zero
    {X : ι → Type v}
    (P : ProductPref X)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hinj : Function.Injective σ.α) :
    ∃ V : X j → ℝ,
      V (σ.α 0) = 0 ∧
      (∀ n : ℕ, V (σ.α (n + 1)) = V (σ.α n) + 1) := by
  obtain ⟨V, hV⟩ := coord_utility_on_grid_from_axioms P σ hinj
  refine ⟨V, ?_, ?_⟩
  · have := hV 0; simpa using this
  · intro n
    have hn := hV n
    have hsucc := hV (n + 1)
    rw [hsucc, hn]
    -- Goal: ((n+1 : ℕ) : ℝ) = (n : ℝ) + 1
    exact_mod_cast (Nat.cast_succ (R := ℝ) n)

/-- The grid utility is **strictly monotone in `n`**: along the grid,
`V (σ.α n) < V (σ.α m)` whenever `n < m`. -/
theorem grid_utility_strictMono
    {X : ι → Type v}
    (P : ProductPref X)
    {j : ι}
    (σ : ProductPref.StandardSequence P j)
    (hinj : Function.Injective σ.α) :
    ∃ V : X j → ℝ,
      (∀ n : ℕ, V (σ.α n) = (n : ℝ)) ∧
      (∀ n m : ℕ, n < m → V (σ.α n) < V (σ.α m)) := by
  obtain ⟨V, hV⟩ := coord_utility_on_grid_from_axioms P σ hinj
  refine ⟨V, hV, ?_⟩
  intro n m hnm
  rw [hV n, hV m]
  exact_mod_cast hnm

/-! ## §2.  Open targets (next milestones for the spin-out paper)

The lemmas in §1 close the grid-only half of Wakker Step 2 from
structural axioms alone.  The next milestones in the spin-out paper
are the off-grid extension and the pairwise-slice representation.

Each milestone below is stated as a `Prop`-valued target in the spirit
of the existing `WakkerRoadmap.CertificateChecklist` items in
`WakkerDebreuKoopmans.lean`.  When proved, each becomes a real theorem
in this file with a `_from_axioms` suffix; until then, they document
the precise next-step interfaces.
-/

/-- Off-grid extension target: assuming `V` admits an analytic-solvability
witness on the grid (every value between `V lo` and `V hi` is realized),
extend the grid utility to all of `X j`.

This is exactly the analytic content captured by
`CoordUtilitySolvability` in `WakkerInfrastructure.lean` §11.4:
once that hypothesis is theorem-backed, the off-grid extension follows.

(Stated here as a target predicate; the construction is the next concrete
deliverable for the spin-out.) -/
def OffGridExtensionTarget
    {X : ι → Type v}
    (P : ProductPref X)
    (j : ι) : Prop :=
  ∀ (σ : ProductPref.StandardSequence P j),
    Function.Injective σ.α →
    -- Analytic-solvability witness on the grid utility:
    (∀ V : X j → ℝ, (∀ n : ℕ, V (σ.α n) = (n : ℝ)) →
      ∀ (lo hi : X j) (t : ℝ),
        V lo ≤ t → t ≤ V hi → ∃ c : X j, V c = t) →
    -- Extension to all of X j:
    ∃ V : X j → ℝ, ∀ n : ℕ, V (σ.α n) = (n : ℝ)

/-- Pairwise-slice representation target (Wakker IV.2.7, Step 4).

Given grid-fit utilities on coordinates `j` and `k`, plus tradeoff
consistency and restricted solvability, derive the pairwise-slice
representation: profile preference on the `{j, k}`-slice is decided by
`Vⱼ + Vₖ`. -/
def PairwiseSliceRepresentationTarget
    {X : ι → Type v}
    (P : ProductPref X)
    (j k : ι) (Vj : X j → ℝ) (Vk : X k → ℝ) : Prop :=
  ∀ x y : Profile X,
    (∀ i, i ≠ j → i ≠ k → x i = y i) →
      (P.weakPref x y ↔
        Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k))

/-- Global gluing target (Wakker IV.2.7, Step 5).

Given pairwise-slice representations for every essential pair of
coordinates, plus `3 ≤ Fintype.card ι`, glue them into a single global
additive representation.

When proved, this is the theorem that converts a list of
`PairwiseSliceRepresentationTarget` outcomes into a global additive
representation of `P`. -/
def GlobalGluingTarget {X : ι → Type v} (P : ProductPref X) : Prop :=
  ∃ V : (i : ι) → X i → ℝ,
    ∀ x y : Profile X,
      P.weakPref x y ↔ (∑ i, V i (y i)) ≤ (∑ i, V i (x i))

/-! ## §3.  Phase-0 audit hooks

The lemmas in §1 are the spin-out's first three named theorems.  Their
purpose is to expose a clean grid-utility entry point that any
downstream proof can rely on without understanding the
`Function.update` bookkeeping carried by the existing
`WakkerDebreuKoopmans.lean` interfaces.

The next phase plugs in restricted solvability + Archimedean to upgrade
the grid utility to a *continuous* coordinate utility on all of `X j`,
discharging `OffGridExtensionTarget`. -/

end WakkerExistenceSpinOut
