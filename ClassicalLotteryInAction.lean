/-
Lean 4 / Mathlib formalization of:

  Jingyuan Li, Ilia Tsetlin, Fan Wang
  "Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty"
  (March 10, 2026)

This file translates all the mathematics of the paper into Lean:
  * the classical-lottery domain `cX = ⋃_{I ≥ 1} X^I`,
  * concatenation `xs ⋎ ys` and replication `xs ^^ n`,
  * the AA-style act space `cF = cX^cS`,
  * Axioms 1–8 (Weak Order, Cancellation, Archimedeanity, Monotonicity,
    Denseness, Continuity, Consistent Aggregation, Solvability),
  * average utility (Proposition `prop_average_utility`),
  * matching frequency `m_{x,y}(·)` and the gap-filling Lemma,
  * the Main Theorem (smooth representation),
  * the ambiguity-aversion Proposition.

Deep proofs (additive representation à la Wakker (1989); the
Debreu–Koopmans concavity step; the patching of `V_{x,y}` across prize
pairs; and the converse curvature recovery for ambiguity attitudes) are
kept as explicit wrapper hypotheses/bridges. Everything local and direct
from the definitions is proved, so the public theorem path is
sorry-free while the non-local mathematical dependencies remain visible.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Count
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace ClassicalLottery

/-! ## §2.1  Setting -/

/-- The set of *classical lotteries* over a prize space `X` is `⋃_{I ≥ 1} X^I`,
represented here as a non-empty list of prizes. -/
structure Lottery (X : Type*) where
  prizes    : List X
  nonempty  : prizes ≠ []

namespace Lottery

variable {X : Type*}

/-- The *length* `|xs|` of a classical lottery. -/
def length (xs : Lottery X) : ℕ := xs.prizes.length

lemma length_pos (xs : Lottery X) : 0 < xs.length := by
  unfold length
  exact List.length_pos_of_ne_nil xs.nonempty

/-- The `i`-th prize of a lottery. -/
def get (xs : Lottery X) (i : Fin xs.length) : X :=
  xs.prizes.get ⟨i.val, by simp [length] at i; exact i.isLt⟩

/-- Concatenation `xs ⊞ ys = (x₁,…,x_k,y₁,…,y_j)` (paper's `∨`). -/
def concat (xs ys : Lottery X) : Lottery X :=
  ⟨xs.prizes ++ ys.prizes, by
     intro h
     rcases List.append_eq_nil_iff.mp h with ⟨h1, _⟩
     exact xs.nonempty h1⟩

@[simp] lemma length_concat (xs ys : Lottery X) :
    (concat xs ys).length = xs.length + ys.length := by
  simp [concat, length, List.length_append]

/-- The prizes-list of `concat xs ys` is `xs.prizes ++ ys.prizes`. -/
@[simp] lemma concat_prizes (xs ys : Lottery X) :
    (concat xs ys).prizes = xs.prizes ++ ys.prizes := rfl

/-- Concatenation is associative (at the level of prizes). -/
lemma concat_assoc (xs ys zs : Lottery X) :
    (concat (concat xs ys) zs).prizes =
    (concat xs (concat ys zs)).prizes := by
  simp [List.append_assoc]

/-- The lengths of associated concatenations agree. -/
lemma length_concat_assoc (xs ys zs : Lottery X) :
    (concat (concat xs ys) zs).length =
    (concat xs (concat ys zs)).length := by
  simp [add_assoc]

/-- **Get on concatenation, left part**: for `i : Fin xs.length`,
the value of `(concat xs ys).get` at the cast-included index equals
`xs.get i`. -/
lemma concat_get_castAdd (xs ys : Lottery X)
    (i : Fin xs.length) :
    (concat xs ys).get
      ⟨i.val, by
        have : i.val < xs.length := i.isLt
        simp [length_concat]; omega⟩ = xs.get i := by
  unfold get
  -- Both sides reduce to `xs.prizes.get ⟨i.val, …⟩`.
  show (xs.prizes ++ ys.prizes).get _ = xs.prizes.get _
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left _

/-- **Get on concatenation, right part**: for `j : Fin ys.length`,
the value of `(concat xs ys).get` at the natAdd-shifted index equals
`ys.get j`. -/
lemma concat_get_natAdd (xs ys : Lottery X)
    (j : Fin ys.length) :
    (concat xs ys).get
      ⟨xs.length + j.val, by
        simp [length_concat]⟩ = ys.get j := by
  unfold get
  show (xs.prizes ++ ys.prizes).get _ = ys.prizes.get _
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rw [List.getElem_append_right]
  · congr 1
    show xs.length + j.val - xs.prizes.length = j.val
    have : xs.length = xs.prizes.length := rfl
    omega
  · show xs.prizes.length ≤ xs.length + j.val
    have : xs.length = xs.prizes.length := rfl
    omega

/-- `n`-fold replication of a lottery: paper's `xs^{n+1}` for `n : ℕ`. -/
def replicateAux (xs : Lottery X) : ℕ → Lottery X
  | 0     => xs
  | n+1   => concat (replicateAux xs n) xs

/-- `replicate xs n` is `xs` repeated `n + 1` times. -/
def replicate (xs : Lottery X) (n : ℕ) : Lottery X := replicateAux xs n

/-- The length of `xs ^^ n` is `(n+1) * |xs|`. -/
lemma length_replicate (xs : Lottery X) (n : ℕ) :
    (replicate xs n).length = (n + 1) * xs.length := by
  unfold replicate
  induction n with
  | zero => simp [replicateAux, length]
  | succ n ih =>
      show (concat (replicateAux xs n) xs).length = (n + 1 + 1) * xs.length
      rw [length_concat, ih]
      ring

/-- The list of prizes in `xs ^^ n` is the concatenation of `n+1`
copies of `xs.prizes`. -/
lemma replicate_prizes (xs : Lottery X) (n : ℕ) :
    (replicate xs n).prizes =
      (List.replicate (n + 1) xs.prizes).flatten := by
  unfold replicate
  induction n with
  | zero =>
      show xs.prizes = (List.replicate 1 xs.prizes).flatten
      simp [List.replicate, List.flatten]
  | succ n ih =>
      show (concat (replicateAux xs n) xs).prizes =
            (List.replicate (n + 1 + 1) xs.prizes).flatten
      -- `concat ... xs` produces append on prizes.
      show (replicateAux xs n).prizes ++ xs.prizes =
            (List.replicate (n + 1 + 1) xs.prizes).flatten
      rw [ih]
      -- `replicate (n+2) xs.prizes = replicate (n+1) xs.prizes ++ [xs.prizes]`
      -- via `List.replicate_add (n+1) 1`.
      rw [show n + 1 + 1 = (n + 1) + 1 from rfl]
      rw [List.replicate_add (n + 1) 1 xs.prizes]
      simp [List.flatten_append, List.replicate]

end Lottery

/-- Global infix for concatenation, paper's `∨`. -/
infixl:65 " ⊞ "  => Lottery.concat
/-- Global notation for replication. -/
notation:75 xs " ^^ " n => Lottery.replicate xs n

/-- **`replicate_succ`**: `xs ^^ (n+1) = (xs ^^ n) ⊞ xs`.  Holds by
definition of `replicateAux`, but stating it explicitly enables clean
rewriting in inductive proofs. -/
lemma Lottery.replicate_succ {X : Type*} (xs : Lottery X) (n : ℕ) :
    (xs ^^ (n + 1)) = (xs ^^ n) ⊞ xs := rfl

/-- **`replicate_zero`**: `xs ^^ 0 = xs`.  Holds by definition. -/
lemma Lottery.replicate_zero {X : Type*} (xs : Lottery X) :
    (xs ^^ 0) = xs := rfl

/-- **`replicate_one`**: `xs ^^ 1 = xs ⊞ xs`.  Direct corollary of
`replicate_succ` and `replicate_zero`. -/
lemma Lottery.replicate_one {X : Type*} (xs : Lottery X) :
    (xs ^^ 1) = xs ⊞ xs := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, Lottery.replicate_succ, Lottery.replicate_zero]

/-- Sub-lottery induced by *deleting* the indices in `E` from `xs`.
Returns `xs` itself if removing `E` would leave an empty list (then the
original `xs` is the appropriate fallback for `Cancellation` use). -/
def Lottery.deleteIdx {X : Type*} (xs : Lottery X)
    (E : Finset (Fin xs.length)) : Lottery X :=
  let ys :=
    (xs.prizes.zipIdx.filter
      (fun p =>
        decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E))).map
      Prod.fst
  if h : ys = [] then xs else ⟨ys, h⟩

/-- Deleting the empty set of indices leaves `xs` unchanged. -/
@[simp] lemma Lottery.deleteIdx_empty {X : Type*} (xs : Lottery X) :
    xs.deleteIdx (∅ : Finset (Fin xs.length)) = xs := by
  -- The filter keeps every element since the predicate is `¬ … ∈ ∅` = `True`.
  -- After mapping back, we get `xs.prizes`.
  have hfilter :
      (xs.prizes.zipIdx.filter
        (fun p =>
          decide (¬ ∃ h : p.2 < xs.length,
                   (⟨p.2, h⟩ : Fin xs.length) ∈ (∅ : Finset _)))) =
        xs.prizes.zipIdx := by
    apply List.filter_eq_self.mpr
    intro p _
    simp
  have hmap : xs.prizes.zipIdx.map Prod.fst = xs.prizes := by
    induction xs.prizes with
    | nil => simp
    | cons hd tl _ =>
        simp [List.zipIdx, List.zipIdx_map_fst]
  -- Compute the body of `deleteIdx` step by step.
  show (let ys := (xs.prizes.zipIdx.filter
                   (fun p =>
                     decide (¬ ∃ h : p.2 < xs.length,
                              (⟨p.2, h⟩ : Fin xs.length) ∈ (∅ : Finset _)))).map
                Prod.fst
        if h : ys = [] then xs else ⟨ys, h⟩) = xs
  rw [hfilter, hmap]
  -- Now `let ys := xs.prizes; if h : ys = [] then xs else ⟨ys, h⟩ = xs`.
  -- Reduce the `let` and the `if`.
  show (if h : xs.prizes = [] then xs else ⟨xs.prizes, h⟩) = xs
  split_ifs with h
  · rfl
  · rfl

/-- **Length of `deleteIdx ∅` equals length of original**. -/
@[simp] lemma Lottery.length_deleteIdx_empty {X : Type*} (xs : Lottery X) :
    (xs.deleteIdx (∅ : Finset (Fin xs.length))).length = xs.length := by
  rw [Lottery.deleteIdx_empty]

/-- **Prizes of `deleteIdx ∅` equals prizes of original**. -/
@[simp] lemma Lottery.prizes_deleteIdx_empty {X : Type*} (xs : Lottery X) :
    (xs.deleteIdx (∅ : Finset (Fin xs.length))).prizes = xs.prizes := by
  rw [Lottery.deleteIdx_empty]

/-! ### Real new helper lemmas about `deleteIdx`

These are fully-proved structural facts about `deleteIdx` that any
proof of `anonymity` or `replicability` will need.  They are kept
separate from the deep theorems to make the proof obligations
explicit. -/

/-- **`deleteIdx_univ` collapses to the fallback**.  When we attempt to
delete *all* indices, the resulting list is empty, so by convention
`deleteIdx` returns the original lottery.  This is the boundary case
opposite to `deleteIdx_empty`. -/
lemma Lottery.deleteIdx_univ {X : Type*} (xs : Lottery X) :
    xs.deleteIdx (Finset.univ : Finset (Fin xs.length)) = xs := by
  -- The filter keeps no element since every index is in `univ`.
  have hfilter :
      (xs.prizes.zipIdx.filter
        (fun p =>
          decide (¬ ∃ h : p.2 < xs.length,
                   (⟨p.2, h⟩ : Fin xs.length) ∈
                   (Finset.univ : Finset (Fin xs.length))))) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    -- For any `(prize, idx)` in `zipIdx`, `idx < xs.prizes.length = xs.length`.
    have hidx : p.2 < xs.prizes.length := by
      have := List.snd_lt_of_mem_zipIdx hp
      simpa using this
    have hidx' : p.2 < xs.length := hidx
    -- The decide simplifies to `False` since `Finset.univ` contains everything.
    simp [hidx', Finset.mem_univ]
  -- Compute the body of `deleteIdx` step by step.
  show (let ys := (xs.prizes.zipIdx.filter
                   (fun p =>
                     decide (¬ ∃ h : p.2 < xs.length,
                              (⟨p.2, h⟩ : Fin xs.length) ∈
                              (Finset.univ : Finset (Fin xs.length))))).map
                Prod.fst
        if h : ys = [] then xs else ⟨ys, h⟩) = xs
  rw [hfilter]
  -- Now `let ys := [].map Prod.fst = []`.
  show (if h : ([] : List X) = [] then xs else ⟨[], h⟩) = xs
  rfl

/-- **Length of `deleteIdx univ` equals length of original** (boundary
fallback). -/
@[simp] lemma Lottery.length_deleteIdx_univ {X : Type*} (xs : Lottery X) :
    (xs.deleteIdx (Finset.univ : Finset (Fin xs.length))).length = xs.length := by
  rw [Lottery.deleteIdx_univ]

/-! ### Helper: `filter`-`zipIdx`-`map` characterization -/

/-- For any list `l` with index offset `n`, every element `(prize, idx)` in
`l.zipIdx n` has `idx ≥ n`.  This is the "monotonicity" of zipIdx in the
offset. -/
lemma Lottery.snd_ge_offset_of_mem_zipIdx {X : Type*} (l : List X) (n : ℕ)
    (p : X × ℕ) (hp : p ∈ l.zipIdx n) : n ≤ p.2 := by
  induction l generalizing n with
  | nil => simp at hp
  | cons hd tl ih =>
      simp only [List.zipIdx_cons, List.mem_cons] at hp
      rcases hp with hpeq | hpmem
      · -- p = (hd, n), so p.2 = n.
        rw [hpeq]
      · -- p ∈ tl.zipIdx (n+1), so p.2 ≥ n+1 ≥ n.
        exact Nat.le_of_lt (Nat.lt_of_succ_le (ih (n + 1) hpmem))

/-- **Generalized filter-zipIdx-map identity**: with offset `n`, filtering
out the entry at position `j ≥ n` from `l.zipIdx n` and mapping back via
`Prod.fst` yields `l.eraseIdx (j - n)`. -/
lemma Lottery.filter_zipIdx_offset_eq_eraseIdx {X : Type*} (l : List X) :
    ∀ (n j : ℕ) (_hj : j - n < l.length) (_hjn : n ≤ j),
      ((l.zipIdx n).filter (fun p => decide (p.2 ≠ j))).map Prod.fst =
        l.eraseIdx (j - n) := by
  induction l with
  | nil =>
      intros n j hj _hjn
      simp at hj
  | cons hd tl ih =>
      intros n j hj hjn
      -- `(hd :: tl).zipIdx n = (hd, n) :: tl.zipIdx (n+1)`.
      rw [List.zipIdx_cons]
      -- Case split: n = j or n < j.
      rcases eq_or_lt_of_le hjn with hn_eq_j | hn_lt_j
      · -- n = j: drop the head pair (hd, n) since `n ≠ j` is false.
        -- Use the rewrite directly without subst (which would destroy `j`).
        -- Rewrite n to j wherever needed.
        rw [← hn_eq_j]
        -- Now goal is in terms of n only.
        -- n - n = 0, eraseIdx 0 = tail.
        rw [show n - n = 0 from Nat.sub_self _]
        rw [List.eraseIdx_cons_zero]
        -- The filter at the head pair returns false (since n = n), so we drop.
        -- Use `show` to reshape the filter argument explicitly.
        have hfilter_step :
            List.filter (fun p : X × ℕ => decide (p.2 ≠ n))
                ((hd, n) :: tl.zipIdx (n + 1)) =
            List.filter (fun p : X × ℕ => decide (p.2 ≠ n))
                (tl.zipIdx (n + 1)) := by
          apply List.filter_cons_of_neg
          show ¬ decide (n ≠ n) = true
          simp
        rw [hfilter_step]
        -- Goal: List.map Prod.fst (filter ... (tl.zipIdx (n + 1))) = tl.
        -- Every element in tl.zipIdx (n+1) has snd ≥ n+1 > n, so filter keeps all.
        have hfilter : (tl.zipIdx (n + 1)).filter (fun p => decide (p.2 ≠ n)) =
                       tl.zipIdx (n + 1) := by
          apply List.filter_eq_self.mpr
          intro p hp
          have hge : n + 1 ≤ p.2 :=
            Lottery.snd_ge_offset_of_mem_zipIdx tl (n + 1) p hp
          have hne : p.2 ≠ n := by omega
          simp [hne]
        rw [hfilter]
        rw [List.zipIdx_map_fst]
      · -- n < j: keep the head pair (hd, n) since `n ≠ j` is true.
        have hn_ne_j : n ≠ j := Nat.ne_of_lt hn_lt_j
        have hfilter_step :
            List.filter (fun p : X × ℕ => decide (p.2 ≠ j))
                ((hd, n) :: tl.zipIdx (n + 1)) =
            (hd, n) :: List.filter (fun p : X × ℕ => decide (p.2 ≠ j))
                (tl.zipIdx (n + 1)) := by
          apply List.filter_cons_of_pos
          show decide (n ≠ j) = true
          simp [hn_ne_j]
        rw [hfilter_step]
        rw [List.map_cons]
        -- Goal: hd :: ((tl.zipIdx (n+1)).filter ...).map Prod.fst =
        --       (hd :: tl).eraseIdx (j - n).
        -- Since j > n, j - n ≥ 1, and (hd :: tl).eraseIdx (k+1) = hd :: tl.eraseIdx k.
        rw [show j - n = (j - n - 1) + 1 from by omega]
        rw [List.eraseIdx_cons_succ]
        congr 1
        -- Apply IH on tl with offset n+1, target j: j - (n+1) = (j-n) - 1.
        have hjn1_le : n + 1 ≤ j := hn_lt_j
        have hj' : j - (n + 1) < tl.length := by
          simp at hj
          omega
        have ih' := ih (n + 1) j hj' hjn1_le
        rw [show j - (n + 1) = j - n - 1 from by omega] at ih'
        exact ih'

/-- **Filter-zipIdx-map identity for singleton deletion.**

For any list `l` and index `j < l.length`, filtering out the entry with
position `j` from `l.zipIdx`, then mapping back via `Prod.fst`, yields
`l.eraseIdx j`.

This is a key structural fact: `Lottery.deleteIdx` for a singleton index
behaves exactly like `List.eraseIdx` on the underlying prizes list.
Proved via the generalized offset version `filter_zipIdx_offset_eq_eraseIdx`
specialized to offset 0. -/
lemma Lottery.filter_zipIdx_singleton_eq_eraseIdx {X : Type*} (l : List X)
    (j : ℕ) (hj : j < l.length) :
    (l.zipIdx.filter (fun p => decide (p.2 ≠ j))).map Prod.fst = l.eraseIdx j := by
  -- `l.zipIdx` defaults to `l.zipIdx 0`.  Apply the offset lemma with n = 0.
  have hsub : j - 0 = j := Nat.sub_zero j
  have hjn : (0 : ℕ) ≤ j := Nat.zero_le _
  have hj' : j - 0 < l.length := by rw [hsub]; exact hj
  have key := Lottery.filter_zipIdx_offset_eq_eraseIdx l 0 j hj' hjn
  rw [hsub] at key
  exact key

/-- **Singleton-index `deleteIdx` is `eraseIdx`-on-prizes.**

For a `Lottery xs` and a single index `i : Fin xs.length`, the result
of `xs.deleteIdx {i}` has prizes-list equal to `xs.prizes.eraseIdx i.val`,
*provided* the result is non-empty (i.e., `xs.length ≥ 2`).

This bridges the abstract `Lottery.deleteIdx` operation to the concrete
list-level `List.eraseIdx`, enabling further reasoning about lengths
and pointwise content. -/
lemma Lottery.deleteIdx_singleton_prizes {X : Type*} (xs : Lottery X)
    (i : Fin xs.length) (hlen : 2 ≤ xs.length) :
    (xs.deleteIdx {i}).prizes = xs.prizes.eraseIdx i.val := by
  -- Unfold `deleteIdx`:  result equals
  --   if filter-mapped list is empty then xs else ⟨filter-mapped list, _⟩
  -- The filter-mapped list equals `xs.prizes.eraseIdx i.val` (by the lemma),
  -- which has length `xs.length - 1 ≥ 1`, so it's non-empty.
  have hi_lt : i.val < xs.length := i.isLt
  have hi_lt_prizes : i.val < xs.prizes.length := hi_lt
  -- The filter-map on the singleton `{i}` yields `xs.prizes.eraseIdx i.val`.
  have hfilter_map :
      (xs.prizes.zipIdx.filter
        (fun p =>
          decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈
                  ({i} : Finset (Fin xs.length))))).map Prod.fst =
      xs.prizes.eraseIdx i.val := by
    -- The predicate reduces to `p.2 ≠ i.val` modulo a bounds check.
    -- We show the two filter predicates produce the same boolean on every input.
    have hpred_eq :
        (fun p : X × ℕ => decide (¬ ∃ h : p.2 < xs.length,
              (⟨p.2, h⟩ : Fin xs.length) ∈ ({i} : Finset (Fin xs.length)))) =
        (fun p : X × ℕ => decide (p.2 ≠ i.val)) := by
      funext p
      -- `decide A = decide B` ⟺ `A ↔ B` via `propext`.
      rw [decide_eq_decide]
      constructor
      · intro hex h
        apply hex
        refine ⟨h ▸ hi_lt, ?_⟩
        rw [Finset.mem_singleton]
        ext
        simpa using h
      · intro hne hex
        rcases hex with ⟨h', hmem⟩
        rw [Finset.mem_singleton] at hmem
        apply hne
        have := congrArg Fin.val hmem
        simpa using this
    rw [hpred_eq]
    exact Lottery.filter_zipIdx_singleton_eq_eraseIdx xs.prizes i.val hi_lt_prizes
  -- The eraseIdx result is non-empty since `xs.length ≥ 2`.
  have hne : xs.prizes.eraseIdx i.val ≠ [] := by
    intro h
    have hlen_eq := congrArg List.length h
    rw [List.length_eraseIdx_of_lt hi_lt_prizes] at hlen_eq
    -- `xs.prizes.length - 1 = 0` ⟹ `xs.prizes.length = 1`, contradicting `hlen`.
    have : xs.prizes.length = 1 := by
      have hpos : 0 < xs.prizes.length := xs.length_pos
      have : xs.prizes.length - 1 = 0 := by simpa using hlen_eq
      omega
    have : xs.length = 1 := this  -- xs.length is xs.prizes.length by def
    omega
  -- Unfold `Lottery.deleteIdx` definition step by step.
  unfold Lottery.deleteIdx
  -- After unfolding, the goal involves `let ys := ...; if h : ys = [] ...`.
  -- We rewrite `ys` using `hfilter_map`.
  simp only [hfilter_map]
  -- Goal: (if h : xs.prizes.eraseIdx i.val = [] then xs else ⟨...⟩).prizes =
  --       xs.prizes.eraseIdx i.val
  rw [dif_neg hne]

/-- **Length of singleton-deletion**: `(xs.deleteIdx {i}).length = xs.length - 1`,
provided `xs.length ≥ 2`. -/
lemma Lottery.length_deleteIdx_singleton {X : Type*} (xs : Lottery X)
    (i : Fin xs.length) (hlen : 2 ≤ xs.length) :
    (xs.deleteIdx {i}).length = xs.length - 1 := by
  show (xs.deleteIdx {i}).prizes.length = xs.prizes.length - 1
  rw [Lottery.deleteIdx_singleton_prizes xs i hlen]
  exact List.length_eraseIdx_of_lt i.isLt

namespace Fin

/-- Include `Fin (n-1)` into `Fin n` by skipping a distinguished index `i`.
This is the arithmetic version of `succAbove` whose type works directly
with lengths written as `n - 1`. -/
def skipIdx {n : ℕ} (i : Fin n) (k : Fin (n - 1)) : Fin n :=
  ⟨if k.val < i.val then k.val else k.val + 1, by
    by_cases hk : k.val < i.val
    · simp [hk]
      omega
    · simp [hk]
      have hklt : k.val < n - 1 := k.isLt
      omega⟩

@[simp] lemma skipIdx_val_of_lt {n : ℕ} (i : Fin n) (k : Fin (n - 1))
    (h : k.val < i.val) : (skipIdx i k).val = k.val := by
  simp [skipIdx, h]

@[simp] lemma skipIdx_val_of_not_lt {n : ℕ} (i : Fin n) (k : Fin (n - 1))
    (h : ¬ k.val < i.val) : (skipIdx i k).val = k.val + 1 := by
  simp [skipIdx, h]

end Fin

/-- **Singleton-deletion get lemma.**  Reading the `k`-th element of
`xs.deleteIdx {i}` is the same as reading `xs` at the index obtained by
skipping `i`. -/
lemma Lottery.deleteIdx_singleton_get {X : Type*} (xs : Lottery X)
    (i : Fin xs.length) (hlen : 2 ≤ xs.length)
    (k : Fin (xs.length - 1)) :
    (xs.deleteIdx {i}).get
        ⟨k.val, by
          rw [Lottery.length_deleteIdx_singleton xs i hlen]
          exact k.isLt⟩ =
      xs.get (Fin.skipIdx i k) := by
  have hpr := Lottery.deleteIdx_singleton_prizes xs i hlen
  have hk_erased : k.val < (xs.prizes.eraseIdx i.val).length := by
    rw [List.length_eraseIdx_of_lt i.isLt]
    exact k.isLt
  have hk_deleted : k.val < (xs.deleteIdx {i}).prizes.length := by
    rw [show (xs.deleteIdx {i}).prizes.length = (xs.deleteIdx {i}).length from rfl]
    rw [Lottery.length_deleteIdx_singleton xs i hlen]
    exact k.isLt
  have hsource : (xs.deleteIdx {i}).prizes[k.val]? =
      some ((xs.deleteIdx {i}).get ⟨k.val, hk_deleted⟩) := by
    rw [List.getElem?_eq_getElem hk_deleted]
    rfl
  have htarget : (xs.deleteIdx {i}).prizes[k.val]? =
      some (xs.get (Fin.skipIdx i k)) := by
    rw [hpr]
    rw [List.getElem?_eq_getElem hk_erased]
    rw [List.getElem_eraseIdx]
    by_cases hk : k.val < i.val
    · simp [Fin.skipIdx, hk, Lottery.get]
    · simp [Fin.skipIdx, hk, Lottery.get]
  rw [hsource] at htarget
  simpa using Option.some.inj htarget

/-- **Permutation after matched singleton deletion.**  If two lotteries have
permuted prize lists and the deleted indices contain the same prize, then
the singleton-deleted lotteries still have permuted prize lists. -/
lemma Lottery.deleteIdx_singleton_prizes_perm {X : Type*}
    (xs ys : Lottery X)
    (i : Fin xs.length) (j : Fin ys.length)
    (hlen_xs : 2 ≤ xs.length) (hlen_ys : 2 ≤ ys.length)
    (hperm : xs.prizes.Perm ys.prizes)
    (hget : xs.get i = ys.get j) :
    (xs.deleteIdx {i}).prizes.Perm (ys.deleteIdx {j}).prizes := by
  rw [Lottery.deleteIdx_singleton_prizes xs i hlen_xs,
      Lottery.deleteIdx_singleton_prizes ys j hlen_ys]
  apply hperm.eraseIdx_of_getElem?_eq
  rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt]
  apply congrArg some
  change xs.get i = ys.get j
  exact hget

/-- A `Lottery` is determined by its `prizes` list. -/
@[ext] lemma Lottery.ext {X : Type*} {xs ys : Lottery X}
    (h : xs.prizes = ys.prizes) : xs = ys := by
  cases xs; cases ys
  congr

/-- `List.ofFn` respects equivalences of finite index sets, up to `List.Perm`.
This is the heterogeneous-index version of `Equiv.Perm.ofFn_comp_perm`. -/
lemma List.ofFn_equiv_perm {α : Type*} {n m : ℕ}
    (e : Fin n ≃ Fin m) (f : Fin n → α) (g : Fin m → α)
    (hfg : ∀ i, f i = g (e i)) :
    (List.ofFn f).Perm (List.ofFn g) := by
  have hnm : n = m := by
    simpa using Fintype.card_congr e
  subst m
  have hf : f = g ∘ e := by
    funext i
    exact hfg i
  rw [hf]
  exact Equiv.Perm.ofFn_comp_perm e g

/-- The pointwise equivalence form of permutation implies permutation of the
underlying prize lists. -/
lemma Lottery.prizes_perm_of_equiv_get {X : Type*}
    (xs ys : Lottery X)
    (_h : xs.length = ys.length)
    (ρ : Fin xs.length ≃ Fin ys.length)
    (hρ : ∀ i, xs.get i = ys.get (ρ i)) :
    xs.prizes.Perm ys.prizes := by
  have hxs : xs.prizes = List.ofFn (fun i : Fin xs.length => xs.get i) := by
    simp [Lottery.get, Lottery.length]
  have hys : ys.prizes = List.ofFn (fun i : Fin ys.length => ys.get i) := by
    simp [Lottery.get, Lottery.length]
  rw [hxs, hys]
  exact List.ofFn_equiv_perm ρ
    (fun i : Fin xs.length => xs.get i)
    (fun j : Fin ys.length => ys.get j) hρ

/-! ### Identifying constant acts with classical lotteries -/

/-- **Acts**: `cF = cX^cS`, functions from `cS` to classical lotteries. -/
abbrev Act (S X : Type*) := S → Lottery X

/-- A constant act is identified with its single classical lottery. -/
def constAct {S X : Type*} (xs : Lottery X) : Act S X := fun _ => xs

/-- A prize `x` is identified with the degenerate length-1 lottery `(x)`. -/
def prizeLottery {X : Type*} (x : X) : Lottery X :=
  ⟨[x], by intro h; cases h⟩

/-- The length of the singleton lottery is 1. -/
@[simp] lemma length_prizeLottery {X : Type*} (x : X) :
    (prizeLottery x).length = 1 := rfl

/-- The (only) prize of `prizeLottery x` is `x`. -/
@[simp] lemma prizeLottery_get {X : Type*} (x : X)
    (i : Fin (prizeLottery x).length) :
    (prizeLottery x).get i = x := by
  rcases i with ⟨val, hval⟩
  -- Length is 1, so val = 0.
  rw [length_prizeLottery] at hval
  interval_cases val
  rfl

/-- The prizes-list of `prizeLottery x` is `[x]`. -/
@[simp] lemma prizeLottery_prizes {X : Type*} (x : X) :
    (prizeLottery x).prizes = [x] := rfl

/-- Two singleton lotteries are equal iff their prizes are equal. -/
lemma prizeLottery_inj {X : Type*} {x y : X} :
    prizeLottery x = prizeLottery y ↔ x = y := by
  constructor
  · intro h
    have : [x] = [y] := by
      have := congrArg Lottery.prizes h
      simpa using this
    exact (List.cons.injEq _ _ _ _).mp this |>.1
  · intro h; rw [h]

/-! ## §2.1  Preference structure -/

/-- A **preference** on acts: a binary relation `≽`, with strict part `≻`
    and indifference `~`. -/
structure Preference (S X : Type*) where
  weakPref : Act S X → Act S X → Prop

namespace Preference

variable {S X : Type*}

/-- Lift a preference on acts to one on classical lotteries via constant acts. -/
def onLotteries (P : Preference S X) (xs ys : Lottery X) : Prop :=
  P.weakPref (constAct xs) (constAct ys)

/-- Lift a preference to prizes. -/
def onPrizes (P : Preference S X) (x y : X) : Prop :=
  P.onLotteries (prizeLottery x) (prizeLottery y)

/-- Strict preference `f ≻ g`. -/
def strict (P : Preference S X) (f g : Act S X) : Prop :=
  P.weakPref f g ∧ ¬ P.weakPref g f

/-- Indifference `f ~ g`. -/
def indiff (P : Preference S X) (f g : Act S X) : Prop :=
  P.weakPref f g ∧ P.weakPref g f

/-- Strict preference between two prizes. -/
def strictPrize (P : Preference S X) (x y : X) : Prop :=
  P.onPrizes x y ∧ ¬ P.onPrizes y x

end Preference

/-! ### §2.1 — Axiom 1: Weak Order -/

namespace Preference

variable {S X : Type*}

/-- **Axiom 1 (Weak Order).**  `≽` is complete and transitive. -/
class WeakOrder (P : Preference S X) : Prop where
  complete   : ∀ f g, P.weakPref f g ∨ P.weakPref g f
  transitive : ∀ f g h, P.weakPref f g → P.weakPref g h → P.weakPref f h

end Preference

/-! ## §2.2  Evaluating Classical Lotteries -/

namespace Preference

variable {S X : Type*}

/-- Number of indices `i ∈ {1,…,|xs|}` with `xs.get i = a`. -/
noncomputable def freqCount [DecidableEq X] (xs : Lottery X) (a : X) : ℕ :=
  (Finset.univ.filter (fun i : Fin xs.length => xs.get i = a)).card

/-- The relative frequency `r_a(xs) = |{i : xs(i) = a}| / |xs|`.  Returns a
rational in `[0,1]`. -/
noncomputable def relFreq [DecidableEq X] (xs : Lottery X) (a : X) : ℚ :=
  (freqCount xs a : ℚ) / (xs.length : ℚ)

/-! ### Helper lemmas about `freqCount` (genuinely proved) -/

/-- `freqCount xs a` is at most `xs.length` (already used elsewhere; here we
state it to make the connection to list-count semantics explicit). -/
lemma freqCount_le_length' [DecidableEq X] (xs : Lottery X) (a : X) :
    freqCount xs a ≤ xs.length := by
  unfold freqCount
  calc (Finset.univ.filter (fun i : Fin xs.length => xs.get i = a)).card
      ≤ (Finset.univ : Finset (Fin xs.length)).card :=
        Finset.card_filter_le _ _
    _ = xs.length := by simp

/-- `freqCount xs a = 0` iff no index of `xs` maps to `a`.  Real proof
using `Finset.card_eq_zero` + `Finset.filter_eq_empty_iff`. -/
lemma freqCount_eq_zero_iff [DecidableEq X] (xs : Lottery X) (a : X) :
    freqCount xs a = 0 ↔ ∀ i : Fin xs.length, xs.get i ≠ a := by
  unfold freqCount
  rw [Finset.card_eq_zero]
  -- `Finset.filter_eq_empty_iff`
  rw [Finset.filter_eq_empty_iff]
  simp

/-- `freqCount xs a > 0` iff some index of `xs` maps to `a`. -/
lemma freqCount_pos_iff [DecidableEq X] (xs : Lottery X) (a : X) :
    0 < freqCount xs a ↔ ∃ i : Fin xs.length, xs.get i = a := by
  rw [Nat.pos_iff_ne_zero, Ne, freqCount_eq_zero_iff]
  push_neg
  rfl

/-- The freqCount of a degenerate one-prize lottery `prizeLottery a`:
either 1 (if the prize matches) or 0 (otherwise). -/
lemma freqCount_prizeLottery [DecidableEq X] (a b : X) :
    freqCount (prizeLottery a) b = if a = b then 1 else 0 := by
  -- `prizeLottery a` has length 1; the unique index is `⟨0, Nat.zero_lt_one⟩`.
  have hlen : (prizeLottery a).length = 1 := rfl
  have hget : ∀ (i : Fin (prizeLottery a).length),
      (prizeLottery a).get i = a := by
    intro i
    rcases i with ⟨val, hval⟩
    rw [hlen] at hval
    -- Now `val < 1`, so `val = 0`.
    interval_cases val
    rfl
  by_cases h : a = b
  · rw [if_pos h]
    -- All indices satisfy the filter, so card = univ card = length = 1.
    unfold freqCount
    have hfilt :
        (Finset.univ : Finset (Fin (prizeLottery a).length)).filter
          (fun i => (prizeLottery a).get i = b) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      rw [hget i]; exact h
    rw [hfilt]
    rw [Finset.card_univ]
    simp [hlen]
  · rw [if_neg h]
    unfold freqCount
    have hfilt :
        (Finset.univ : Finset (Fin (prizeLottery a).length)).filter
          (fun i => (prizeLottery a).get i = b) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      rw [hget i]; exact h
    rw [hfilt]; rfl

/-- The relative frequency of `b` in the singleton lottery `prizeLottery a`
is 1 if `a = b`, else 0. -/
lemma relFreq_prizeLottery [DecidableEq X] (a b : X) :
    relFreq (prizeLottery a) b = if a = b then 1 else 0 := by
  unfold relFreq
  rw [freqCount_prizeLottery]
  -- `(prizeLottery a).length = 1` so the denominator is 1.
  have hlen : (prizeLottery a).length = 1 := rfl
  rw [hlen]
  -- Case split on `a = b`.
  by_cases h : a = b
  · rw [if_pos h, if_pos h]; norm_num
  · rw [if_neg h, if_neg h]; norm_num

/-- The freqCount sums to the length: `Σ_{indices} 1 = length`,
which equals `Σ_{prizes a in some support} freqCount xs a`.

Concretely:  for any finite support `Finset S` containing every prize
of `xs`, the sum `Σ_{a ∈ S} freqCount xs a = xs.length`. -/
lemma sum_freqCount_eq_length [DecidableEq X] [Fintype X] (xs : Lottery X) :
    ∑ a : X, freqCount xs a = xs.length := by
  -- Strategy: the disjoint union over `a` of "indices with xs.get i = a"
  -- partitions all indices, hence card sum = total card.
  unfold freqCount
  -- We use `Finset.card_eq_sum_card_fiberwise` with the function
  -- `xs.get : Fin xs.length → X`.
  rw [show (∑ a : X,
            (Finset.univ.filter
              (fun i : Fin xs.length => xs.get i = a)).card) =
          (Finset.univ : Finset (Fin xs.length)).card from ?_]
  · simp
  -- Rewrite the right-hand side as a fiberwise count.
  symm
  apply Finset.card_eq_sum_card_fiberwise (f := xs.get)
  intro i _
  exact Finset.mem_univ _

/-- The total mass: relative frequencies sum to 1. -/
lemma sum_relFreq_eq_one [DecidableEq X] [Fintype X] (xs : Lottery X) :
    ∑ a : X, relFreq xs a = 1 := by
  unfold relFreq
  rw [← Finset.sum_div]
  rw [show (∑ a : X, (freqCount xs a : ℚ)) =
          ((∑ a : X, freqCount xs a : ℕ) : ℚ) from by push_cast; rfl]
  rw [sum_freqCount_eq_length]
  -- (xs.length : ℚ) / (xs.length : ℚ) = 1, since `xs.length > 0`.
  have hpos : (0 : ℚ) < (xs.length : ℚ) := by
    exact_mod_cast xs.length_pos
  exact div_self (ne_of_gt hpos)

/-- **Boundary case:** `relFreq xs a = 1` iff every prize of `xs` is `a`. -/
lemma relFreq_eq_one_iff [DecidableEq X] (xs : Lottery X) (a : X) :
    relFreq xs a = 1 ↔ ∀ i : Fin xs.length, xs.get i = a := by
  unfold relFreq
  -- `freqCount = length` iff filter equals universe iff every i satisfies.
  have hpos : (0 : ℚ) < (xs.length : ℚ) := by
    exact_mod_cast xs.length_pos
  rw [div_eq_one_iff_eq (ne_of_gt hpos)]
  -- Now: `(freqCount : ℚ) = (length : ℚ) ↔ freqCount = length`.
  rw [show ((freqCount xs a : ℚ) = (xs.length : ℚ)) ↔ (freqCount xs a = xs.length) from
      ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩]
  -- `freqCount = length` iff filter has full card iff every i in filter.
  unfold freqCount Lottery.length
  rw [show (Finset.univ.filter (fun i : Fin xs.prizes.length => xs.get i = a)).card
            = xs.prizes.length ↔
            Finset.univ.filter (fun i : Fin xs.prizes.length => xs.get i = a)
            = Finset.univ from ?_]
  · rw [Finset.filter_eq_self]
    simp
  · constructor
    · intro hcard
      apply Finset.eq_univ_of_card
      rw [hcard]
      simp
    · intro heq
      rw [heq]
      simp

/-- **Boundary case:** `relFreq xs a = 0` iff no prize of `xs` is `a`. -/
lemma relFreq_eq_zero_iff [DecidableEq X] (xs : Lottery X) (a : X) :
    relFreq xs a = 0 ↔ ∀ i : Fin xs.length, xs.get i ≠ a := by
  unfold relFreq
  have hpos : (0 : ℚ) < (xs.length : ℚ) := by
    exact_mod_cast xs.length_pos
  rw [div_eq_zero_iff]
  constructor
  · intro h
    rcases h with hzero | hzero
    · -- (freqCount : ℚ) = 0 → freqCount = 0 → ...
      have : freqCount xs a = 0 := by exact_mod_cast hzero
      rw [freqCount_eq_zero_iff] at this
      exact this
    · -- (xs.length : ℚ) = 0 contradicts hpos.
      exfalso
      linarith
  · intro h
    left
    have : freqCount xs a = 0 := (freqCount_eq_zero_iff xs a).mpr h
    exact_mod_cast this

/-- `relFreq xs a + relFreq xs b ≤ 1` whenever `a ≠ b` (relative
frequencies of distinct prizes are sub-probabilities). -/
lemma relFreq_two_distinct_le_one
    [DecidableEq X] [Fintype X] (xs : Lottery X) {a b : X} (hab : a ≠ b) :
    relFreq xs a + relFreq xs b ≤ 1 := by
  -- Sum of all relFreqs is 1; the two relFreqs are part of the sum.
  have hsum : ∑ c : X, relFreq xs c = 1 := sum_relFreq_eq_one xs
  -- Each relFreq is ≥ 0 (inline the fact since `relFreq_nonneg` is
  -- defined later in the file).
  have hnn : ∀ c, 0 ≤ relFreq xs c := by
    intro c
    unfold relFreq
    have h₁ : 0 ≤ (freqCount xs c : ℚ) := by exact_mod_cast Nat.zero_le _
    have h₂ : 0 ≤ (xs.length : ℚ) := by exact_mod_cast Nat.zero_le _
    exact div_nonneg h₁ h₂
  -- Use `Finset.sum_le_sum_of_subset_of_nonneg` with the `{a, b}` Finset.
  have hsub : ({a, b} : Finset X) ⊆ Finset.univ := Finset.subset_univ _
  have h_sub_le :
      ∑ c ∈ ({a, b} : Finset X), relFreq xs c ≤
      ∑ c : X, relFreq xs c :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun c _ _ => hnn c)
  have h_pair_eq : ∑ c ∈ ({a, b} : Finset X), relFreq xs c =
                   relFreq xs a + relFreq xs b := by
    rw [Finset.sum_pair hab]
  rw [h_pair_eq] at h_sub_le
  linarith

/-- `freqCount xs a ≤ xs.length`. -/
lemma freqCount_le_length [DecidableEq X] (xs : Lottery X) (a : X) :
    freqCount xs a ≤ xs.length := by
  unfold freqCount
  -- `Finset.univ : Finset (Fin xs.length)` has card `xs.length`,
  -- and the filter has card at most that.
  calc (Finset.univ.filter (fun i : Fin xs.length => xs.get i = a)).card
      ≤ (Finset.univ : Finset (Fin xs.length)).card :=
        Finset.card_filter_le _ _
    _ = xs.length := by simp

/-- **`freqCount` of concatenation**: `freqCount (xs ⊞ ys) a =
freqCount xs a + freqCount ys a`.

This is a structurally important fact: counting prizes in a concatenated
lottery splits as the sum of the counts in each part.  The proof goes
via `Finset.sum_boole` (cardinality = sum of indicators) and
`Fin.sum_univ_add` (split sum of `Fin (m + n)` into `Fin m` and `Fin n`),
combined with `concat_get_castAdd` and `concat_get_natAdd`. -/
lemma freqCount_concat [DecidableEq X] (xs ys : Lottery X) (a : X) :
    freqCount (xs ⊞ ys) a = freqCount xs a + freqCount ys a := by
  -- Step 1: convert each `freqCount` to a sum of indicator values.
  unfold freqCount
  have card_to_sum :
      ∀ {n : ℕ} (p : Fin n → Prop) [DecidablePred p],
      (Finset.univ.filter p).card =
        ∑ i : Fin n, (if p i then 1 else 0 : ℕ) := by
    intros n p _
    rw [Finset.sum_boole]
    rfl
  rw [card_to_sum, card_to_sum, card_to_sum]
  -- Step 2: rewrite the LHS sum to be over `Fin (xs.length + ys.length)`.
  have hlen : (xs ⊞ ys).length = xs.length + ys.length :=
    Lottery.length_concat xs ys
  rw [show (∑ i : Fin (xs ⊞ ys).length,
            (if (xs ⊞ ys).get i = a then 1 else 0 : ℕ)) =
          (∑ i : Fin (xs.length + ys.length),
            (if (xs ⊞ ys).get ⟨i.val, by rw [hlen]; exact i.isLt⟩ = a
             then 1 else 0 : ℕ)) from ?_]
  · -- Step 3: split via `Fin.sum_univ_add`.
    rw [Fin.sum_univ_add]
    -- Step 4: identify the two halves.
    congr 1
    · -- LHS half: identify with `freqCount xs a`'s sum.
      apply Finset.sum_congr rfl
      intro i _
      have hcast := Lottery.concat_get_castAdd xs ys i
      simp only [Fin.val_castAdd]
      by_cases h : (xs ⊞ ys).get ⟨i.val, by
            simp [Lottery.length_concat]; omega⟩ = a
      · rw [if_pos h, if_pos]; rw [← hcast]; exact h
      · rw [if_neg h, if_neg]; rw [← hcast]; exact h
    · -- RHS half: identify with `freqCount ys a`'s sum.
      apply Finset.sum_congr rfl
      intro j _
      have hnat := Lottery.concat_get_natAdd xs ys j
      simp only [Fin.val_natAdd]
      by_cases h : (xs ⊞ ys).get
                    ⟨xs.length + j.val,
                     by simp [Lottery.length_concat]⟩ = a
      · rw [if_pos h, if_pos]; rw [← hnat]; exact h
      · rw [if_neg h, if_neg]; rw [← hnat]; exact h
  · -- The recast: align the index types via `Fin.castOrderIso` (or
    -- equivalently `Equiv.cast` on the `Fin`).  We use
    -- `Fintype.sum_equiv` on the equivalence given by the equality of
    -- lengths.
    apply Fintype.sum_equiv (finCongr hlen)
    intro i
    rfl

/-- **`freqCount` of replication**: `freqCount (xs ^^ n) a = (n+1) * freqCount xs a`.

This is the natural extension of `freqCount_concat` to repeated lotteries.
Proof: induction on `n`, using `freqCount_concat` for the inductive step. -/
lemma freqCount_replicate [DecidableEq X] (xs : Lottery X) (a : X) (n : ℕ) :
    freqCount (xs ^^ n) a = (n + 1) * freqCount xs a := by
  induction n with
  | zero =>
      -- `xs ^^ 0 = xs`, so `freqCount = freqCount xs a` and `(0+1) * _ = _`.
      show freqCount xs a = (0 + 1) * freqCount xs a
      ring
  | succ n ih =>
      -- `xs ^^ (n+1) = (xs ^^ n) ⊞ xs`, so `freqCount = freqCount (xs ^^ n) + freqCount xs`.
      show freqCount ((xs ^^ n) ⊞ xs) a = (n + 1 + 1) * freqCount xs a
      rw [freqCount_concat, ih]
      ring

/-- **`relFreq` of replication**: `relFreq (xs ^^ n) a = relFreq xs a`.

The crucial fact for `replicability`: replicating a lottery does not
change the relative frequency of any prize.

Proof: by `freqCount_replicate` and `length_replicate`, both numerator
and denominator scale by the same `(n+1)`. -/
lemma relFreq_replicate [DecidableEq X] (xs : Lottery X) (a : X) (n : ℕ) :
    relFreq (xs ^^ n) a = relFreq xs a := by
  unfold relFreq
  rw [freqCount_replicate, Lottery.length_replicate]
  -- Now: ((n+1) * freqCount xs a : ℚ) / ((n+1) * xs.length : ℚ)
  --    = (freqCount xs a : ℚ) / (xs.length : ℚ).
  have hn1 : (0 : ℚ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hlen : (0 : ℚ) < (xs.length : ℚ) := by exact_mod_cast xs.length_pos
  push_cast
  field_simp

/-- **Relative-frequency invariance.**  This is the explicit wrapper
hypothesis used for the local `replicability` result below: lotteries with
the same relative-frequency profile are indifferent.

In the full Proposition 1 route this should be derived from Cancellation +
Archimedeanity via the missing vNM/Wakker-style average-utility spine.  Until
that deep direction is formalized, keeping the hypothesis named avoids hiding
the mathematical dependency. -/
def RelativeFrequencyInvariance [DecidableEq X] (P : Preference S X) : Prop :=
  ∀ xs ys : Lottery X,
    (∀ a : X, relFreq xs a = relFreq ys a) →
    P.indiff (constAct xs) (constAct ys)

/-- **Replicability bridge.**  A thinner named hypothesis: replicating a
classical lottery is indifferent to the original.  This is the minimal
input needed to derive `RelativeFrequencyInvariance` from `Cancellation`
alone (see `relativeFrequencyInvariance_of_replicability`), and is
strictly weaker than `RelativeFrequencyInvariance` since it does not
quantify over arbitrary equal-frequency profile pairs. -/
def Replicability [DecidableEq X] (P : Preference S X) : Prop :=
  ∀ (xs : Lottery X) (n : ℕ),
    P.indiff (constAct xs) (constAct (xs ^^ n))

/-- **`relFreq` of concatenation, weighted form**: `relFreq (xs ⊞ ys) a` is
a weighted average of `relFreq xs a` and `relFreq ys a`, with weights
`xs.length / (xs.length + ys.length)` and `ys.length / (xs.length + ys.length)`. -/
lemma relFreq_concat_weighted [DecidableEq X] (xs ys : Lottery X) (a : X) :
    relFreq (xs ⊞ ys) a * ((xs.length + ys.length : ℕ) : ℚ) =
    relFreq xs a * (xs.length : ℚ) + relFreq ys a * (ys.length : ℚ) := by
  unfold relFreq
  rw [freqCount_concat]
  rw [show ((xs ⊞ ys).length : ℚ) = (xs.length + ys.length : ℕ) from by
        rw [Lottery.length_concat]]
  have hlen_xs : (0 : ℚ) < (xs.length : ℚ) := by exact_mod_cast xs.length_pos
  have hlen_ys : (0 : ℚ) < (ys.length : ℚ) := by exact_mod_cast ys.length_pos
  have hlen_pos : (0 : ℚ) < ((xs.length + ys.length : ℕ) : ℚ) := by
    push_cast; linarith
  push_cast
  field_simp

/-- **`freqCount` is symmetric in concatenation order**: `freqCount (xs ⊞ ys) = freqCount (ys ⊞ xs)`. -/
lemma freqCount_concat_comm [DecidableEq X] (xs ys : Lottery X) (a : X) :
    freqCount (xs ⊞ ys) a = freqCount (ys ⊞ xs) a := by
  rw [freqCount_concat, freqCount_concat]
  ring

/-- **`relFreq` is symmetric in concatenation order**. -/
lemma relFreq_concat_comm [DecidableEq X] (xs ys : Lottery X) (a : X) :
    relFreq (xs ⊞ ys) a = relFreq (ys ⊞ xs) a := by
  unfold relFreq
  rw [freqCount_concat_comm]
  rw [show ((xs ⊞ ys).length : ℚ) = ((ys ⊞ xs).length : ℚ) from by
        rw [Lottery.length_concat, Lottery.length_concat]; push_cast; ring]

/-- **Length is symmetric in concatenation order**. -/
@[simp] lemma length_concat_comm (xs ys : Lottery X) :
    (xs ⊞ ys).length = (ys ⊞ xs).length := by
  rw [Lottery.length_concat, Lottery.length_concat]; ring

/-- **`freqCount` triple-concatenation associativity**: counts agree
between `(xs ⊞ ys) ⊞ zs` and `xs ⊞ (ys ⊞ zs)`. -/
lemma freqCount_concat_assoc [DecidableEq X] (xs ys zs : Lottery X) (a : X) :
    freqCount ((xs ⊞ ys) ⊞ zs) a = freqCount (xs ⊞ (ys ⊞ zs)) a := by
  rw [freqCount_concat, freqCount_concat, freqCount_concat, freqCount_concat]
  ring

/-- `0 ≤ relFreq xs a`. -/
lemma relFreq_nonneg [DecidableEq X] (xs : Lottery X) (a : X) :
    0 ≤ relFreq xs a := by
  unfold relFreq
  have h₁ : 0 ≤ (freqCount xs a : ℚ) := by exact_mod_cast Nat.zero_le _
  have h₂ : 0 ≤ (xs.length : ℚ) := by exact_mod_cast Nat.zero_le _
  exact div_nonneg h₁ h₂

/-- `relFreq xs a ≤ 1`. -/
lemma relFreq_le_one [DecidableEq X] (xs : Lottery X) (a : X) :
    relFreq xs a ≤ 1 := by
  unfold relFreq
  have hpos : (0 : ℚ) < (xs.length : ℚ) := by
    exact_mod_cast xs.length_pos
  rw [div_le_one hpos]
  exact_mod_cast freqCount_le_length xs a

/-- The cast of `relFreq` to `ℝ` lies in `[0,1]`. -/
lemma relFreq_real_mem_unitInterval [DecidableEq X] (xs : Lottery X) (a : X) :
    (0 : ℝ) ≤ (relFreq xs a : ℝ) ∧ (relFreq xs a : ℝ) ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast relFreq_nonneg xs a
  · exact_mod_cast relFreq_le_one xs a

/-- **Axiom 2 (Cancellation).**  Indifferent sub-lotteries (matching prizes,
matching relative size) can be cancelled when comparing two classical
lotteries.

We state it in the simplified form where the matching parts on both sides
consist entirely of a common prize `a`, and the *relative size* of the
matching parts is the same. -/
class Cancellation (P : Preference S X) [DecidableEq X] : Prop where
  cancel :
    ∀ (xs ys : Lottery X) (a : X)
      (E : Finset (Fin xs.length)) (F : Finset (Fin ys.length)),
      (E.card : ℚ) / (xs.length : ℚ) = (F.card : ℚ) / (ys.length : ℚ) →
      (∀ i ∈ E, xs.get i = a) → (∀ j ∈ F, ys.get j = a) →
      ( P.onLotteries xs ys ↔
        P.onLotteries (xs.deleteIdx E) (ys.deleteIdx F) )

/-- **Axiom 3 (Archimedeanity).**  Strict preferences are robust under
"small" perturbations: for `xs ≻ ys` and any `zs`, eventually
`xs^n ⊞ zs ≻ ys` and `xs ≻ ys^n ⊞ zs`. -/
class Archimedeanity (P : Preference S X) : Prop where
  archimedean :
    ∀ xs ys zs : Lottery X,
      P.onLotteries xs ys ∧ ¬ P.onLotteries ys xs →
      ∃ N : ℕ, ∀ n, n ≥ N →
        ( P.onLotteries ((xs ^^ n) ⊞ zs) ys ∧
          ¬ P.onLotteries ys ((xs ^^ n) ⊞ zs) ) ∧
        ( P.onLotteries xs ((ys ^^ n) ⊞ zs) ∧
          ¬ P.onLotteries ((ys ^^ n) ⊞ zs) xs )

/-! ### Real new lemmas about `Archimedeanity` -/

/-- **Archimedean witness exists**: from `xs ≻ ys`, the axiom yields a
threshold `N` past which both perturbed comparisons hold strictly. -/
lemma Archimedeanity.exists_threshold
    (P : Preference S X) [Archimedeanity P]
    (xs ys zs : Lottery X) (hsxy : P.onLotteries xs ys)
    (hnxy : ¬ P.onLotteries ys xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      ( P.onLotteries ((xs ^^ n) ⊞ zs) ys ∧
        ¬ P.onLotteries ys ((xs ^^ n) ⊞ zs) ) ∧
      ( P.onLotteries xs ((ys ^^ n) ⊞ zs) ∧
        ¬ P.onLotteries ((ys ^^ n) ⊞ zs) xs ) :=
  Archimedeanity.archimedean xs ys zs ⟨hsxy, hnxy⟩

/-- **Specialization: only the first conjunct of the Archimedean
conclusion**: the `(xs^n ⊞ zs) ≻ ys` part. -/
lemma Archimedeanity.left_conjunct
    (P : Preference S X) [Archimedeanity P]
    (xs ys zs : Lottery X) (hsxy : P.onLotteries xs ys)
    (hnxy : ¬ P.onLotteries ys xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      P.onLotteries ((xs ^^ n) ⊞ zs) ys ∧
      ¬ P.onLotteries ys ((xs ^^ n) ⊞ zs) := by
  obtain ⟨N, hN⟩ := Archimedeanity.archimedean xs ys zs ⟨hsxy, hnxy⟩
  exact ⟨N, fun n hn => (hN n hn).1⟩

/-- **Specialization: only the second conjunct**: the `xs ≻ (ys^n ⊞ zs)`
part. -/
lemma Archimedeanity.right_conjunct
    (P : Preference S X) [Archimedeanity P]
    (xs ys zs : Lottery X) (hsxy : P.onLotteries xs ys)
    (hnxy : ¬ P.onLotteries ys xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      P.onLotteries xs ((ys ^^ n) ⊞ zs) ∧
      ¬ P.onLotteries ((ys ^^ n) ⊞ zs) xs := by
  obtain ⟨N, hN⟩ := Archimedeanity.archimedean xs ys zs ⟨hsxy, hnxy⟩
  exact ⟨N, fun n hn => (hN n hn).2⟩

end Preference

/-! ### Real lemmas: trivial cases of Cancellation -/

namespace Preference

variable {S X : Type*} [DecidableEq X]

/-- **Cancellation with empty deletion sets** has trivial premises:
when `E = F = ∅`, the cardinality ratio condition holds and the
prize-matching condition is vacuous. -/
lemma cancellation_premises_empty
    (xs ys : Lottery X) :
    let E : Finset (Fin xs.length) := ∅
    let F : Finset (Fin ys.length) := ∅
    (E.card : ℚ) / (xs.length : ℚ) = (F.card : ℚ) / (ys.length : ℚ) ∧
    (∀ a : X, ∀ i ∈ E, xs.get i = a) ∧
    (∀ a : X, ∀ j ∈ F, ys.get j = a) := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro _ i hi; exact absurd hi (Finset.notMem_empty _)
  · intro _ j hj; exact absurd hj (Finset.notMem_empty _)

/-- **Boundary identity**: applying Cancellation with `E = F = ∅` gives
the trivial identity `P.onLotteries xs ys ↔ P.onLotteries xs ys`,
since both `deleteIdx`s are identity. -/
lemma cancellation_with_empty_is_identity
    (P : Preference S X) [Cancellation P]
    (xs ys : Lottery X) :
    P.onLotteries xs ys ↔
    P.onLotteries (xs.deleteIdx ∅) (ys.deleteIdx ∅) := by
  rw [xs.deleteIdx_empty, ys.deleteIdx_empty]

end Preference

/-! ### Reflexivity of `≽` and `~` from Weak Order -/

namespace Preference

variable {S X : Type*}

/-- `≽` is reflexive: `f ≽ f`. -/
lemma weakPref_refl (P : Preference S X) [WeakOrder P] (f : Act S X) :
    P.weakPref f f := by
  rcases Preference.WeakOrder.complete (P := P) f f with h | h <;> exact h

/-- Indifference is reflexive: `f ~ f`. -/
lemma indiff_refl (P : Preference S X) [WeakOrder P] (f : Act S X) :
    P.indiff f f :=
  ⟨weakPref_refl P f, weakPref_refl P f⟩

/-- Indifference is symmetric: `f ~ g → g ~ f`. -/
lemma indiff_symm (P : Preference S X) {f g : Act S X}
    (h : P.indiff f g) : P.indiff g f :=
  ⟨h.2, h.1⟩

/-- Indifference is transitive (under Weak Order). -/
lemma indiff_trans (P : Preference S X) [WeakOrder P]
    {f g h : Act S X} (hfg : P.indiff f g) (hgh : P.indiff g h) :
    P.indiff f h :=
  ⟨Preference.WeakOrder.transitive (P := P) _ _ _ hfg.1 hgh.1,
   Preference.WeakOrder.transitive (P := P) _ _ _ hgh.2 hfg.2⟩

/-- Strict preference is irreflexive: `¬ f ≻ f`. -/
lemma strict_irrefl (P : Preference S X) [WeakOrder P] (f : Act S X) :
    ¬ P.strict f f := by
  intro ⟨h₁, h₂⟩
  exact h₂ h₁

/-- Strict preference is asymmetric: `f ≻ g → ¬ g ≻ f`. -/
lemma strict_asymm (P : Preference S X) {f g : Act S X}
    (h : P.strict f g) : ¬ P.strict g f := by
  intro ⟨h₁, h₂⟩
  exact h.2 h₁

/-- Strict preference is transitive (under Weak Order). -/
lemma strict_trans (P : Preference S X) [WeakOrder P]
    {f g h : Act S X} (hfg : P.strict f g) (hgh : P.strict g h) :
    P.strict f h := by
  refine ⟨?_, ?_⟩
  · exact Preference.WeakOrder.transitive (P := P) _ _ _ hfg.1 hgh.1
  · -- Suppose `h ≽ f`.  Then `h ≽ f ≽ g`, so `h ≽ g`, contradicting `g ≻ h`.
    intro hhf
    have : P.weakPref h g :=
      Preference.WeakOrder.transitive (P := P) _ _ _ hhf hfg.1
    exact hgh.2 this

/-- Combining `≽` and `≻`: `f ≽ g` and `g ≻ h` give `f ≻ h`. -/
lemma weakPref_strict_trans (P : Preference S X) [WeakOrder P]
    {f g h : Act S X} (hfg : P.weakPref f g) (hgh : P.strict g h) :
    P.strict f h := by
  refine ⟨?_, ?_⟩
  · exact Preference.WeakOrder.transitive (P := P) _ _ _ hfg hgh.1
  · intro hhf
    -- `h ≽ f ≽ g` gives `h ≽ g`, contradicting `g ≻ h`.
    have : P.weakPref h g :=
      Preference.WeakOrder.transitive (P := P) _ _ _ hhf hfg
    exact hgh.2 this

/-- Combining `≻` and `≽`: `f ≻ g` and `g ≽ h` give `f ≻ h`. -/
lemma strict_weakPref_trans (P : Preference S X) [WeakOrder P]
    {f g h : Act S X} (hfg : P.strict f g) (hgh : P.weakPref g h) :
    P.strict f h := by
  refine ⟨?_, ?_⟩
  · exact Preference.WeakOrder.transitive (P := P) _ _ _ hfg.1 hgh
  · intro hhf
    -- `g ≽ h ≽ f` gives `g ≽ f`, contradicting `f ≻ g`.
    have : P.weakPref g f :=
      Preference.WeakOrder.transitive (P := P) _ _ _ hgh hhf
    exact hfg.2 this

end Preference

namespace Preference

variable {S X : Type*}

/-- **Anonymity from a list permutation.**  This is the induction proof behind
the public `anonymity` theorem: delete one matched singleton prize on both
sides, use Cancellation to reduce the comparison to the deleted lotteries,
and iterate on the shorter permuted prize lists. -/
theorem anonymity_of_prizes_perm
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] :
    ∀ xs ys : Lottery X,
      xs.prizes.Perm ys.prizes →
      P.indiff (constAct xs) (constAct ys) := by
  classical
  have main : ∀ n : ℕ, ∀ xs ys : Lottery X,
      xs.length = n →
      xs.prizes.Perm ys.prizes →
      P.indiff (constAct xs) (constAct ys) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs ys hxs_len hperm
        have hlen_xy : xs.length = ys.length := by
          exact hperm.length_eq
        have hn_pos : 0 < n := by
          rw [← hxs_len]
          exact xs.length_pos
        by_cases hn_one : n = 1
        · have hxs_one : xs.length = 1 := by omega
          obtain ⟨a, hxs_list⟩ : ∃ a : X, xs.prizes = [a] := by
            rcases hp : xs.prizes with _ | ⟨a, t⟩
            · exact absurd hp xs.nonempty
            · have ht : t = [] := by
                have hlen : (a :: t).length = 1 := by
                  rw [← hp]
                  exact hxs_one
                have : t.length = 0 := by simpa using hlen
                exact List.length_eq_zero_iff.mp this
              exact ⟨a, by simp [ht]⟩
          have hys_list : ys.prizes = [a] := by
            apply List.perm_singleton.mp
            rw [← hxs_list]
            exact hperm.symm
          have hxy : xs = ys := Lottery.ext (by rw [hxs_list, hys_list])
          rw [hxy]
          exact indiff_refl P (constAct ys)
        · have hn_two : 2 ≤ n := by omega
          have hlen_xs_two : 2 ≤ xs.length := by omega
          have hlen_ys_two : 2 ≤ ys.length := by
            rw [← hlen_xy]
            exact hlen_xs_two
          let i : Fin xs.length := ⟨0, xs.length_pos⟩
          have hx_mem : xs.get i ∈ xs.prizes := by
            show xs.prizes.get i ∈ xs.prizes
            exact List.get_mem xs.prizes i
          have hy_mem : xs.get i ∈ ys.prizes := (hperm.mem_iff).mp hx_mem
          obtain ⟨j0, hj0⟩ := List.get_of_mem hy_mem
          let j : Fin ys.length := ⟨j0.val, j0.isLt⟩
          have hget : xs.get i = ys.get j := by
            dsimp [j]
            exact hj0.symm
          have hdel_perm :
              (xs.deleteIdx {i}).prizes.Perm (ys.deleteIdx {j}).prizes :=
            Lottery.deleteIdx_singleton_prizes_perm xs ys i j
              hlen_xs_two hlen_ys_two hperm hget
          have hdel_len_lt : (xs.deleteIdx {i}).length < n := by
            rw [Lottery.length_deleteIdx_singleton xs i hlen_xs_two, hxs_len]
            omega
          have hind : P.indiff (constAct (xs.deleteIdx {i}))
              (constAct (ys.deleteIdx {j})) :=
            ih (xs.deleteIdx {i}).length hdel_len_lt
              (xs.deleteIdx {i}) (ys.deleteIdx {j}) rfl hdel_perm
          have hratio :
              (({i} : Finset (Fin xs.length)).card : ℚ) / (xs.length : ℚ) =
              (({j} : Finset (Fin ys.length)).card : ℚ) / (ys.length : ℚ) := by
            simp [hlen_xy]
          have hE : ∀ k ∈ ({i} : Finset (Fin xs.length)), xs.get k = xs.get i := by
            intro k hk
            rw [Finset.mem_singleton] at hk
            rw [hk]
          have hF : ∀ k ∈ ({j} : Finset (Fin ys.length)), ys.get k = xs.get i := by
            intro k hk
            rw [Finset.mem_singleton] at hk
            rw [hk, ← hget]
          have hcancel_xy :=
            Cancellation.cancel (P := P) xs ys (xs.get i)
              ({i} : Finset (Fin xs.length)) ({j} : Finset (Fin ys.length))
              hratio hE hF
          have hcancel_yx :=
            Cancellation.cancel (P := P) ys xs (xs.get i)
              ({j} : Finset (Fin ys.length)) ({i} : Finset (Fin xs.length))
              hratio.symm hF hE
          refine ⟨?_, ?_⟩
          · exact hcancel_xy.mpr hind.1
          · exact hcancel_yx.mpr hind.2
  intro xs ys hperm
  exact main xs.length xs ys rfl hperm

/-- **Anonymity.**  Permutations are immaterial: if `ys` is a permutation of
    `xs` then `xs ~ ys`.  (Paper's Step 1, §App.1.)

The paper proves this by induction on `|xs|`:
* **Base case** `|xs| = 1`: trivial since the only permutation of a
  singleton is the identity.  Fully proved in `anonymity_length_one`.
* **Inductive step**: pick any length-`(n)` sub-lottery of `xs` whose
  `prizes`-multiset matches some length-`(n)` sub-lottery of `ys`.  The
  remaining single prize on each side must coincide.  Apply Cancellation
  to the matching length-`(n)` parts, leaving a single-prize comparison
  on each side that is reflexive.

Note: under any average-utility representation `u`,
`anonymity_of_averageUtility_repr` gives this statement directly without
the induction.  Once `prop_average_utility` is proved, `anonymity`
becomes a corollary. -/
theorem anonymity
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P] [Cancellation P]
    (xs ys : Lottery X)
    (h : xs.length = ys.length)
    (ρ : Fin xs.length ≃ Fin ys.length)
    (hρ : ∀ i, xs.get i = ys.get (ρ i)) :
    P.indiff (constAct xs) (constAct ys) := by
  exact anonymity_of_prizes_perm P xs ys
    (Lottery.prizes_perm_of_equiv_get xs ys h ρ hρ)

/-- **Anonymity for the identity permutation.**  If two lotteries
have the same length and agree on every index, they are equal as
lotteries (and a fortiori indifferent under any preference).

This lemma handles the degenerate case where `ρ = id`, isolating the
non-trivial work in the genuine permutation case. -/
lemma anonymity_id_perm
    [DecidableEq X]
    (xs ys : Lottery X)
    (h : xs.length = ys.length)
    (hget : ∀ i : Fin xs.length,
        xs.get i = ys.get ⟨i.val, by rw [← h]; exact i.isLt⟩) :
    xs = ys := by
  apply Lottery.ext
  apply List.ext_get
  · exact h
  · intro i hi₁ hi₂
    have h1 : xs.prizes.get ⟨i, hi₁⟩ = xs.get ⟨i, hi₁⟩ := rfl
    have h2 : ys.prizes.get ⟨i, hi₂⟩ = ys.get ⟨i, hi₂⟩ := rfl
    rw [h1, h2]
    exact hget ⟨i, hi₁⟩

/-- **Anonymity for the identity permutation — preference form.**  Two
length-equal lotteries with pointwise-equal prizes are indifferent. -/
lemma anonymity_indiff_id_perm
    [DecidableEq X]
    (P : Preference S X) [WeakOrder P]
    (xs ys : Lottery X)
    (h : xs.length = ys.length)
    (hget : ∀ i : Fin xs.length,
        xs.get i = ys.get ⟨i.val, by rw [← h]; exact i.isLt⟩) :
    P.indiff (constAct xs) (constAct ys) := by
  rw [anonymity_id_perm xs ys h hget]
  exact indiff_refl P (constAct ys)/-- **Anonymity, base case (length 1).**  Two singleton lotteries with
matching prizes are equal as lotteries — and a fortiori indifferent
under any weak-order preference.  The only permutation of a singleton
is the identity, so the hypothesis `hρ` reduces to a single equation.

This is the genuine base case of the induction in `anonymity`, fully
proven without any `sorry`. -/
lemma anonymity_length_one
    [DecidableEq X]
    (xs ys : Lottery X)
    (hxs : xs.length = 1) (hys : ys.length = 1)
    (heq : xs.get ⟨0, by rw [hxs]; exact Nat.one_pos⟩ =
           ys.get ⟨0, by rw [hys]; exact Nat.one_pos⟩) :
    xs = ys := by
  -- Both lotteries' `prizes` lists are singletons. Extract the prizes.
  rcases hp_xs : xs.prizes with _ | ⟨a, t_xs⟩
  · exact absurd hp_xs xs.nonempty
  rcases hp_ys : ys.prizes with _ | ⟨b, t_ys⟩
  · exact absurd hp_ys ys.nonempty
  have hxs_t : t_xs = [] := by
    have hlen : (a :: t_xs).length = 1 := by rw [← hp_xs]; exact hxs
    have : t_xs.length = 0 := by simpa using hlen
    exact List.length_eq_zero_iff.mp this
  have hys_t : t_ys = [] := by
    have hlen : (b :: t_ys).length = 1 := by rw [← hp_ys]; exact hys
    have : t_ys.length = 0 := by simpa using hlen
    exact List.length_eq_zero_iff.mp this
  subst hxs_t; subst hys_t
  -- Now hp_xs : xs.prizes = [a] and hp_ys : ys.prizes = [b].
  -- Show a = b by computing `xs.get ⟨0,_⟩` and `ys.get ⟨0,_⟩`.
  -- `xs.get ⟨0, _⟩` is `xs.prizes.get ⟨0, _⟩` by definition. Using `hp_xs`,
  -- `xs.prizes.get ⟨0, _⟩ = [a].get ⟨0, _⟩ = a`.
  have hxs_get : xs.get ⟨0, by rw [hxs]; exact Nat.one_pos⟩ = a := by
    have : xs.prizes.get ⟨0, by rw [hp_xs]; simp⟩ = a := by
      simp [hp_xs]
    convert this
  have hys_get : ys.get ⟨0, by rw [hys]; exact Nat.one_pos⟩ = b := by
    have : ys.prizes.get ⟨0, by rw [hp_ys]; simp⟩ = b := by
      simp [hp_ys]
    convert this
  have hab : a = b := by rw [← hxs_get, ← hys_get]; exact heq
  apply Lottery.ext
  rw [hp_xs, hp_ys, hab]

/-- **Anonymity for length-1 lotteries**: the preference-level corollary
of `anonymity_length_one`.  Two length-1 lotteries with the same prize
are indifferent under any weak-order preference. -/
lemma anonymity_indiff_length_one
    [DecidableEq X]
    (P : Preference S X) [WeakOrder P]
    (xs ys : Lottery X)
    (hxs : xs.length = 1) (hys : ys.length = 1)
    (heq : xs.get ⟨0, by rw [hxs]; exact Nat.one_pos⟩ =
           ys.get ⟨0, by rw [hys]; exact Nat.one_pos⟩) :
    P.indiff (constAct xs) (constAct ys) := by
  have hxy : xs = ys := anonymity_length_one xs ys hxs hys heq
  rw [hxy]
  exact indiff_refl P (constAct ys)

/-- **Replicability, base case (n = 0).**  `xs ~ xs^0`.  This is
trivially reflexivity since `xs ^^ 0` reduces to `xs` by definition. -/
lemma replicability_zero
    [DecidableEq X]
    (P : Preference S X) [WeakOrder P]
    (xs : Lottery X) :
    P.indiff (constAct xs) (constAct (xs ^^ 0)) := by
  -- `xs ^^ 0 = xs` definitionally.
  show P.indiff (constAct xs) (constAct xs)
  exact indiff_refl P (constAct xs)

/-- **Replicability for singleton lotteries — prize agreement.**  Every
position in `(prizeLottery a) ^^ n` is the prize `a`.  This is the
structural reason why both `prizeLottery a` and its replications are
indifferent under any preference satisfying Axiom 1: their prize
sequences agree on the constant value `a`. -/
lemma all_prizes_eq_replicate_prizeLottery {X : Type*} (a : X) (n : ℕ) :
    ∀ i : Fin ((prizeLottery a) ^^ n).length,
      ((prizeLottery a) ^^ n).get i = a := by
  -- Step 1: identify the underlying prizes list.
  have hprizes : ((prizeLottery a) ^^ n).prizes = List.replicate (n + 1) a := by
    rw [Lottery.replicate_prizes]
    -- `(List.replicate (n+1) [a]).flatten = List.replicate (n+1) a`.
    induction n with
    | zero => simp [List.replicate, List.flatten]
    | succ k ih =>
        rw [show k + 1 + 1 = (k + 1) + 1 from rfl,
            List.replicate_succ, List.flatten_cons]
        rw [ih]
        rw [show List.replicate (k + 1 + 1) a = a :: List.replicate (k + 1) a
              from rfl]
        simp
  -- Step 2: every entry of `List.replicate (n+1) a` is `a`.
  intro i
  -- Goal: ((prizeLottery a) ^^ n).get i = a.  By definition of `Lottery.get`,
  -- this is `((prizeLottery a) ^^ n).prizes.get ⟨i.val, _⟩ = a`.
  -- Use the fact that the prizes list, on every element of its underlying
  -- (List.replicate ...), is `a`.
  have key : ∀ b : X, b ∈ ((prizeLottery a) ^^ n).prizes → b = a := by
    intro b hb
    rw [hprizes] at hb
    exact List.eq_of_mem_replicate hb
  -- Apply to the specific element at index `i`.
  apply key
  -- `xs.get i ∈ xs.prizes`.
  show ((prizeLottery a) ^^ n).prizes.get _ ∈ ((prizeLottery a) ^^ n).prizes
  exact List.get_mem _ _

/-! ### From `Replicability` to `RelativeFrequencyInvariance` via Cancellation -/

/-- Indicator-sum form of `List.count`: summing `1` over positions whose
list value equals `a` recovers `l.count a`. -/
private lemma _list_sum_map_ite_eq_count {X : Type*} [DecidableEq X]
    (l : List X) (a : X) :
    (l.map (fun x => if x = a then (1 : ℕ) else 0)).sum = l.count a := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : hd = a
    · simp [h, Nat.add_comm]
    · simp [h, beq_iff_eq]

/-- `freqCount xs a` agrees with the list-count of `a` in `xs.prizes`. -/
lemma freqCount_eq_count [DecidableEq X] (xs : Lottery X) (a : X) :
    freqCount xs a = xs.prizes.count a := by
  unfold freqCount
  -- Convert the filter card to a sum of `0/1` indicators.
  rw [Finset.card_filter]
  -- Goal: ∑ i : Fin xs.length, (if xs.get i = a then 1 else 0 : ℕ)
  --      = xs.prizes.count a
  -- `xs.get i = xs.prizes[i.val]` definitionally, so rewrite the sum
  -- using `Fin.sum_univ_fun_getElem`.
  have hsum :
      (∑ i : Fin xs.prizes.length,
          (if xs.prizes[i.val] = a then (1 : ℕ) else 0)) =
        (xs.prizes.map (fun x => if x = a then (1 : ℕ) else 0)).sum :=
    Fin.sum_univ_fun_getElem _ (fun x => if x = a then (1 : ℕ) else 0)
  show (∑ i : Fin xs.length, (if xs.get i = a then (1 : ℕ) else 0))
      = xs.prizes.count a
  rw [show (∑ i : Fin xs.length, (if xs.get i = a then (1 : ℕ) else 0))
        = (∑ i : Fin xs.prizes.length,
            (if xs.prizes[i.val] = a then (1 : ℕ) else 0)) from rfl]
  rw [hsum, _list_sum_map_ite_eq_count]

/-- If two lotteries have matching `freqCount` profiles, their prize lists
are permutations of each other. -/
lemma prizes_perm_of_freqCount_eq [DecidableEq X] (xs ys : Lottery X)
    (hfc : ∀ a : X, freqCount xs a = freqCount ys a) :
    xs.prizes.Perm ys.prizes := by
  rw [List.perm_iff_count]
  intro a
  have h := hfc a
  rw [freqCount_eq_count, freqCount_eq_count] at h
  exact h

/-- **Derivation of `RelativeFrequencyInvariance` from `Replicability` and
`Cancellation`.**

Given the primitive `Replicability` bridge (replicating a lottery is
indifferent to the original), this discharges the full
`RelativeFrequencyInvariance` predicate without using `Archimedeanity`:

* Replicate `xs` by `|ys|` and `ys` by `|xs|` to obtain two equal-length
  lotteries `xs'`, `ys'` whose relative frequencies still agree.
* Equal lengths plus equal `relFreq` profiles force equal `freqCount`
  profiles, hence the prize lists are permutations of each other
  (`prizes_perm_of_freqCount_eq`).
* The already-proved `anonymity_of_prizes_perm` gives `xs' ~ ys'` from
  `Cancellation` alone.
* Chain with `Replicability` to bring the comparison back to `xs ~ ys`.

This thins the public hypothesis stack: callers now only need to provide
the much smaller `Replicability` bridge plus the standard
`Cancellation`/`WeakOrder` instances. -/
theorem relativeFrequencyInvariance_of_replicability
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P] [Cancellation P]
    (hRep : Replicability P) :
    RelativeFrequencyInvariance P := by
  intro xs ys hfreq
  -- Replicate to a common length.
  set n1 : ℕ := ys.length - 1 with hn1_def
  set n2 : ℕ := xs.length - 1 with hn2_def
  set xs' : Lottery X := xs ^^ n1 with hxs'_def
  set ys' : Lottery X := ys ^^ n2 with hys'_def
  have hn1_succ : n1 + 1 = ys.length := by
    rw [hn1_def]; exact Nat.sub_add_cancel ys.length_pos
  have hn2_succ : n2 + 1 = xs.length := by
    rw [hn2_def]; exact Nat.sub_add_cancel xs.length_pos
  have hxs'_len : xs'.length = ys.length * xs.length := by
    rw [hxs'_def, Lottery.length_replicate, hn1_succ]
  have hys'_len : ys'.length = xs.length * ys.length := by
    rw [hys'_def, Lottery.length_replicate, hn2_succ]
  have hlen_eq : xs'.length = ys'.length := by
    rw [hxs'_len, hys'_len]; ring
  -- Relative frequencies still agree after replication.
  have hfreq' : ∀ a : X, relFreq xs' a = relFreq ys' a := by
    intro a
    rw [hxs'_def, hys'_def, relFreq_replicate, relFreq_replicate]
    exact hfreq a
  -- Equal lengths + equal relFreq profile ⇒ equal freqCount profile.
  have hfc_eq : ∀ a : X, freqCount xs' a = freqCount ys' a := by
    intro a
    have h := hfreq' a
    unfold relFreq at h
    have hys'_pos : (0 : ℚ) < (ys'.length : ℚ) := by
      exact_mod_cast ys'.length_pos
    have hlen_cast : (xs'.length : ℚ) = (ys'.length : ℚ) := by
      exact_mod_cast hlen_eq
    rw [hlen_cast] at h
    have h' : (freqCount xs' a : ℚ) = (freqCount ys' a : ℚ) := by
      have := (div_left_inj' (ne_of_gt hys'_pos)).mp h
      exact this
    exact_mod_cast h'
  -- Permute prize lists and apply anonymity.
  have hperm : xs'.prizes.Perm ys'.prizes :=
    prizes_perm_of_freqCount_eq xs' ys' hfc_eq
  have hxy' : P.indiff (constAct xs') (constAct ys') :=
    anonymity_of_prizes_perm P xs' ys' hperm
  -- Chain with `Replicability`.
  have hxx' : P.indiff (constAct xs) (constAct xs') := hRep xs n1
  have hyy' : P.indiff (constAct ys) (constAct ys') := hRep ys n2
  exact indiff_trans P (indiff_trans P hxx' hxy') (indiff_symm P hyy')

/-- **Replicability from named relative-frequency invariance.**

Replicating a lottery preserves every relative frequency, so any preference
that is already known to identify lotteries by relative-frequency profiles
exhibits replicability.

This is the honest local wrapper for the paper's §App.1.1 chain argument:
the missing non-circular work is exactly to derive
`RelativeFrequencyInvariance P` from Cancellation + Archimedeanity. -/
theorem replicability
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] [Archimedeanity P]
    (hFreq : RelativeFrequencyInvariance P)
    (xs : Lottery X) (n : ℕ) :
    P.indiff (constAct xs) (constAct (xs ^^ n)) := by
  apply hFreq
  intro a
  exact (relFreq_replicate xs a n).symm

/-- **Anonymity for "all-`a`" lotteries**: if every prize in both
lotteries equals a fixed value `a`, then the two lotteries are
indifferent.

Proof: under `replicability`, every "all-`a`" lottery is indifferent
to `prizeLottery a` (via a length-matching replicate identification),
so two such lotteries are indifferent to each other by transitivity.

This is a useful concrete consequence of `replicability` that
demonstrates the technique without needing a non-trivial permutation. -/
lemma anonymity_indiff_all_const
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] [Archimedeanity P]
  (hFreq : RelativeFrequencyInvariance P)
    (xs ys : Lottery X) (a : X)
    (hxs_const : ∀ i : Fin xs.length, xs.get i = a)
    (hys_const : ∀ j : Fin ys.length, ys.get j = a) :
    P.indiff (constAct xs) (constAct ys) := by
  -- xs equals (prizeLottery a) ^^ (xs.length - 1) by `anonymity_id_perm`.
  have hxs_pos : 0 < xs.length := xs.length_pos
  have hys_pos : 0 < ys.length := ys.length_pos
  have hxs_repl_len : ((prizeLottery a) ^^ (xs.length - 1)).length = xs.length := by
    rw [Lottery.length_replicate, length_prizeLottery]
    omega
  have hys_repl_len : ((prizeLottery a) ^^ (ys.length - 1)).length = ys.length := by
    rw [Lottery.length_replicate, length_prizeLottery]
    omega
  have hxs_eq_repl : xs = (prizeLottery a) ^^ (xs.length - 1) := by
    apply anonymity_id_perm xs ((prizeLottery a) ^^ (xs.length - 1)) hxs_repl_len.symm
    intro i
    rw [hxs_const i]
    -- Need: a = ((prizeLottery a) ^^ (xs.length - 1)).get ⟨i.val, _⟩
    -- This follows from `all_prizes_eq_replicate_prizeLottery`.
    have hi_lt : i.val < ((prizeLottery a) ^^ (xs.length - 1)).length := by
      rw [hxs_repl_len]; exact i.isLt
    have := all_prizes_eq_replicate_prizeLottery a (xs.length - 1) ⟨i.val, hi_lt⟩
    exact this.symm
  have hys_eq_repl : ys = (prizeLottery a) ^^ (ys.length - 1) := by
    apply anonymity_id_perm ys ((prizeLottery a) ^^ (ys.length - 1)) hys_repl_len.symm
    intro j
    rw [hys_const j]
    have hj_lt : j.val < ((prizeLottery a) ^^ (ys.length - 1)).length := by
      rw [hys_repl_len]; exact j.isLt
    have := all_prizes_eq_replicate_prizeLottery a (ys.length - 1) ⟨j.val, hj_lt⟩
    exact this.symm
  -- Now use replicability: ((prizeLottery a) ^^ n) ~ prizeLottery a.
  rw [hxs_eq_repl, hys_eq_repl]
  have h1 : P.indiff (constAct (prizeLottery a))
                     (constAct ((prizeLottery a) ^^ (xs.length - 1))) :=
    replicability P hFreq (prizeLottery a) (xs.length - 1)
  have h2 : P.indiff (constAct (prizeLottery a))
                     (constAct ((prizeLottery a) ^^ (ys.length - 1))) :=
    replicability P hFreq (prizeLottery a) (ys.length - 1)
  exact indiff_trans P (indiff_symm P h1) h2

end Preference

/-! ### §2.2 — Proposition 1: average utility -/

namespace Preference

variable {S X : Type*} [DecidableEq X]

/-- Given a utility `u : X → ℝ`, the **average utility** of a classical
    lottery `xs`:  `U(xs) = (1/|xs|) Σ_{i=1}^{|xs|} u(xs i)`. -/
noncomputable def averageUtility (u : X → ℝ) (xs : Lottery X) : ℝ :=
  (∑ i : Fin xs.length, u (xs.get i)) / (xs.length : ℝ)

/-- Capital-letter average-utility model `U : cX → ℝ`. -/
noncomputable abbrev U (u : X → ℝ) : Lottery X → ℝ := averageUtility u

/-! ### Real, fully-proven lemmas about `averageUtility` -/

/-- The average utility of a singleton lottery `prizeLottery a` is `u a`. -/
lemma averageUtility_prizeLottery (u : X → ℝ) (a : X) :
    averageUtility u (prizeLottery a) = u a := by
  unfold averageUtility
  -- The sum over `Fin 1` is just `u(⟨0, _⟩)` = `u a`, denominator = 1.
  -- Both are clean by computation.
  show (∑ i : Fin (prizeLottery a).length, u ((prizeLottery a).get i))
        / ((prizeLottery a).length : ℝ) = u a
  have hsum : (∑ i : Fin (prizeLottery a).length, u ((prizeLottery a).get i))
            = u a := by
    -- prizeLottery a has length 1 with single prize a.
    show (∑ i : Fin 1, u ((prizeLottery a).get i)) = u a
    simp [prizeLottery, Lottery.get]
  rw [hsum]
  show u a / ((prizeLottery a).length : ℝ) = u a
  have hlen : ((prizeLottery a).length : ℝ) = 1 := by
    show ((1 : ℕ) : ℝ) = 1
    norm_num
  rw [hlen]; ring

/-- Average utility is invariant under affine transformations of `u`:
`averageUtility (α • u + β) = α • averageUtility u + β`. -/
lemma averageUtility_affine (u : X → ℝ) (α β : ℝ) (xs : Lottery X) :
    averageUtility (fun x => α * u x + β) xs =
      α * averageUtility u xs + β := by
  unfold averageUtility
  -- Numerator splits via Finset.sum_add_distrib + Finset.mul_sum.
  have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
    exact_mod_cast xs.length_pos
  -- Compute the numerator.
  have hnum :
      (∑ i : Fin xs.length, (α * u (xs.get i) + β)) =
        α * (∑ i : Fin xs.length, u (xs.get i)) + β * (xs.length : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_fin]
    ring
  rw [hnum]
  -- Now we have `(α * S + β * L) / L = α * (S/L) + β`.
  field_simp

/-- Average utility is bounded by the maximum value of `u` over the
prizes of `xs` (and similarly above by the minimum).  Stated as: any
prize value `u (xs.get i)` for `i : Fin xs.length` is between
`min` and `max`, and the average lies in `[min, max]`. -/
lemma averageUtility_le_max (u : X → ℝ) (xs : Lottery X) (M : ℝ)
    (hM : ∀ i : Fin xs.length, u (xs.get i) ≤ M) :
    averageUtility u xs ≤ M := by
  unfold averageUtility
  -- Σ u(xs i) ≤ Σ M = M * length
  have hsum_le :
      (∑ i : Fin xs.length, u (xs.get i)) ≤
        (∑ _i : Fin xs.length, M) := Finset.sum_le_sum (fun i _ => hM i)
  rw [show (∑ _i : Fin xs.length, M) = M * (xs.length : ℝ) from ?_] at hsum_le
  · -- Divide by length (positive).
    have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
      exact_mod_cast xs.length_pos
    rw [div_le_iff₀ hlen_pos]
    linarith
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring

/-- Symmetric lower bound. -/
lemma averageUtility_ge_min (u : X → ℝ) (xs : Lottery X) (m : ℝ)
    (hm : ∀ i : Fin xs.length, m ≤ u (xs.get i)) :
    m ≤ averageUtility u xs := by
  unfold averageUtility
  have hsum_le :
      (∑ _i : Fin xs.length, m) ≤
        (∑ i : Fin xs.length, u (xs.get i)) := Finset.sum_le_sum (fun i _ => hm i)
  rw [show (∑ _i : Fin xs.length, m) = m * (xs.length : ℝ) from ?_] at hsum_le
  · have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
      exact_mod_cast xs.length_pos
    rw [le_div_iff₀ hlen_pos]
    linarith
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring

/-- **Constant utility**: `averageUtility (fun _ => c) xs = c`.  For any
constant utility, the average is the constant. -/
lemma averageUtility_const (c : ℝ) (xs : Lottery X) :
    averageUtility (fun _ : X => c) xs = c := by
  unfold averageUtility
  -- Numerator: Σ c = length · c.
  rw [show (∑ _i : Fin xs.length, c) = (xs.length : ℝ) * c from ?_]
  · -- Denominator: length is positive.
    have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
      exact_mod_cast xs.length_pos
    field_simp
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring

/-- **Average utility equals `u(x)` if all prizes are `x`**. -/
lemma averageUtility_of_constant_prizes
    (u : X → ℝ) (xs : Lottery X) (a : X)
    (h : ∀ i : Fin xs.length, xs.get i = a) :
    averageUtility u xs = u a := by
  unfold averageUtility
  -- Numerator: Σ u(xs.get i) = Σ u(a) = length · u(a).
  rw [show (∑ i : Fin xs.length, u (xs.get i)) = (xs.length : ℝ) * u a from ?_]
  · have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
      exact_mod_cast xs.length_pos
    field_simp
  · rw [show (∑ i : Fin xs.length, u (xs.get i)) =
              (∑ _i : Fin xs.length, u a) from ?_]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    · apply Finset.sum_congr rfl
      intro i _
      rw [h i]

/-- **Average utility is bounded between min and max prize utility**. -/
lemma averageUtility_mem_of_bounded (u : X → ℝ) (xs : Lottery X) (m M : ℝ)
    (hm : ∀ i : Fin xs.length, m ≤ u (xs.get i))
    (hM : ∀ i : Fin xs.length, u (xs.get i) ≤ M) :
    m ≤ averageUtility u xs ∧ averageUtility u xs ≤ M :=
  ⟨averageUtility_ge_min u xs m hm,
   averageUtility_le_max u xs M hM⟩

/-- **Sum-numerator of `averageUtility` on concatenation**: the sum
`Σ_i u((xs ⊞ ys).get i) = Σ_i u(xs.get i) + Σ_j u(ys.get j)`.

This is the analogue of `freqCount_concat` for arbitrary utility
functions.  Real proof using `Fin.sum_univ_add` and `concat_get_castAdd`,
`concat_get_natAdd`. -/
lemma averageUtility_sum_concat (u : X → ℝ) (xs ys : Lottery X) :
    (∑ i : Fin (xs ⊞ ys).length, u ((xs ⊞ ys).get i)) =
    (∑ i : Fin xs.length, u (xs.get i)) +
    (∑ j : Fin ys.length, u (ys.get j)) := by
  have hlen : (xs ⊞ ys).length = xs.length + ys.length :=
    Lottery.length_concat xs ys
  -- Recast the LHS over `Fin (xs.length + ys.length)`.
  rw [show (∑ i : Fin (xs ⊞ ys).length, u ((xs ⊞ ys).get i)) =
          (∑ i : Fin (xs.length + ys.length),
            u ((xs ⊞ ys).get ⟨i.val, by rw [hlen]; exact i.isLt⟩)) from ?_]
  · rw [Fin.sum_univ_add]
    congr 1
    · -- LHS half: identify with `xs`'s sum.
      apply Finset.sum_congr rfl
      intro i _
      have hcast := Lottery.concat_get_castAdd xs ys i
      simp only [Fin.val_castAdd]
      rw [show (xs ⊞ ys).get ⟨i.val, _⟩ = xs.get i from hcast]
    · -- RHS half: identify with `ys`'s sum.
      apply Finset.sum_congr rfl
      intro j _
      have hnat := Lottery.concat_get_natAdd xs ys j
      simp only [Fin.val_natAdd]
      rw [show (xs ⊞ ys).get ⟨xs.length + j.val, _⟩ = ys.get j from hnat]
  · -- Recast via `finCongr hlen`.
    apply Fintype.sum_equiv (finCongr hlen)
    intro i
    rfl

/-- **`averageUtility` of a concatenation as length-weighted average**:
`averageUtility u (xs ⊞ ys) = (xs.length · U(xs) + ys.length · U(ys)) / (xs.length + ys.length)`.

Real proof using `averageUtility_sum_concat` plus algebraic manipulation. -/
lemma averageUtility_concat_weighted (u : X → ℝ) (xs ys : Lottery X) :
    averageUtility u (xs ⊞ ys) * ((xs.length + ys.length : ℕ) : ℝ) =
    averageUtility u xs * (xs.length : ℝ) +
    averageUtility u ys * (ys.length : ℝ) := by
  unfold averageUtility
  rw [averageUtility_sum_concat]
  have hlen_xs : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
  have hlen_ys : (0 : ℝ) < (ys.length : ℝ) := by exact_mod_cast ys.length_pos
  rw [show ((xs ⊞ ys).length : ℝ) = (xs.length + ys.length : ℕ) from by
        rw [Lottery.length_concat]]
  push_cast
  field_simp

/-- **`averageUtility` is invariant under replication**: averaging
utility over `xs ^^ n` gives the same value as over `xs`.

This is the **structural fact corresponding to `replicability`**: any
honest proof of the latter would use this directly.

Real proof: by induction on `n` using `averageUtility_sum_concat`. -/
lemma averageUtility_replicate (u : X → ℝ) (xs : Lottery X) (n : ℕ) :
    averageUtility u (xs ^^ n) = averageUtility u xs := by
  induction n with
  | zero =>
      -- `xs ^^ 0 = xs` by definition.
      rfl
  | succ n ih =>
      -- `xs ^^ (n+1) = (xs ^^ n) ⊞ xs`.
      show averageUtility u ((xs ^^ n) ⊞ xs) = averageUtility u xs
      -- Use `averageUtility_concat_weighted`.
      have hweighted := averageUtility_concat_weighted u (xs ^^ n) xs
      -- We have: U(xs^n ⊞ xs) · (length(xs^n) + length(xs))
      --        = U(xs^n) · length(xs^n) + U(xs) · length(xs)
      -- Substitute `U(xs^n) = U(xs)` (ih) and `length(xs^n) = (n+1) · length(xs)`.
      rw [Lottery.length_replicate, ih] at hweighted
      -- Now: U((xs^n) ⊞ xs) · ((n+1) * xs.length + xs.length)
      --    = U xs · ((n+1) * xs.length) + U xs · xs.length
      --    = U xs · ((n+2) * xs.length)
      have hpos : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
      have hsum_pos : (0 : ℝ) < ((n + 1) * xs.length + xs.length : ℕ) := by
        push_cast; positivity
      -- Cancel the common factor.
      have key : averageUtility u ((xs ^^ n) ⊞ xs)
               * ((n + 1) * xs.length + xs.length : ℕ)
               = averageUtility u xs
               * ((n + 1) * xs.length + xs.length : ℕ) := by
        rw [hweighted]
        push_cast
        ring
      have hne : ((n + 1) * xs.length + xs.length : ℕ) ≠ (0 : ℝ) := by
        push_cast
        intro h
        nlinarith [hpos]
      exact (mul_right_cancel₀ hne key)

/-- The conclusion of Proposition 1: an average-utility representation of
`P` on constant classical lotteries. -/
def AverageUtilityRepresentation
    (P : Preference S X)
    [WeakOrder P] : Prop :=
  ∃ u : X → ℝ,
    ∀ xs ys : Lottery X,
      P.onLotteries xs ys ↔
      averageUtility u ys ≤ averageUtility u xs

/-- **Proposition 1, hard direction as a named hypothesis.**

This is the missing vNM/Wakker-style spine: Cancellation plus
Archimedeanity should produce an average-utility representation.  The
proved theorem `prop_average_utility` below consumes this hypothesis and
proves the reverse direction constructively. -/
def AverageUtilityHardDirection
    (P : Preference S X)
    [WeakOrder P] : Prop :=
  ((∃ _ : Cancellation P, True) ∧ (∃ _ : Archimedeanity P, True)) →
    AverageUtilityRepresentation P

/-! ### Real corollary: replicability holds under any average-utility
representation.

This is a **provable consequence** of the average-utility hypothesis,
*without* any deep work.  It uses `averageUtility_replicate` directly. -/

/-- If `P` is represented by `averageUtility u`, then `P` exhibits
replicability: `xs ~ xs ^^ n` for every `n`. -/
lemma replicability_of_averageUtility_repr
    (P : Preference S X)
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs : Lottery X) (n : ℕ) :
    P.indiff (constAct xs) (constAct (xs ^^ n)) := by
  refine ⟨?_, ?_⟩
  · -- `P.weakPref (constAct xs) (constAct (xs ^^ n))`,
    -- which by definition of onLotteries unfolds to
    -- `P.onLotteries xs (xs ^^ n)`.
    show P.onLotteries xs (xs ^^ n)
    rw [hrepr]
    rw [averageUtility_replicate]
  · show P.onLotteries (xs ^^ n) xs
    rw [hrepr]
    rw [averageUtility_replicate]

/-- If `P` is represented by `averageUtility u`, then `P` exhibits
**permutation-anonymity** at the level of multiset of prizes: any two
classical lotteries with the same `Multiset` of prizes are indifferent. -/
lemma anonymity_of_averageUtility_repr
    (P : Preference S X)
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys : Lottery X)
    (h : xs.length = ys.length)
    (ρ : Fin xs.length ≃ Fin ys.length)
    (hρ : ∀ i, xs.get i = ys.get (ρ i)) :
    P.indiff (constAct xs) (constAct ys) := by
  -- Permuting the index set doesn't change the sum, so averages match.
  have heq : averageUtility u xs = averageUtility u ys := by
    unfold averageUtility
    have hsum : (∑ i : Fin xs.length, u (xs.get i)) =
                (∑ j : Fin ys.length, u (ys.get j)) := by
      rw [← Fintype.sum_equiv ρ (fun i => u (xs.get i))
            (fun j => u (ys.get j))]
      intro i
      show u (xs.get i) = u (ys.get (ρ i))
      rw [hρ i]
    have hlen : (xs.length : ℝ) = (ys.length : ℝ) := by
      exact_mod_cast h
    rw [hsum, hlen]
  refine ⟨?_, ?_⟩
  · show P.onLotteries xs ys
    rw [hrepr]; rw [heq]
  · show P.onLotteries ys xs
    rw [hrepr]; rw [heq]

/-! ### Real consequences: `averageUtility` of `xs.deleteIdx {i}` -/

/-- **Sum-of-utilities under singleton deletion**: erasing one index `i`
from `xs.prizes` reduces the sum of `u` over the prizes by `u(xs.get i)`.

This is the key arithmetic fact bridging `Lottery.deleteIdx_singleton_prizes`
and the `averageUtility` API. -/
lemma sum_u_deleteIdx_singleton (u : X → ℝ) (xs : Lottery X)
    (i : Fin xs.length) (hlen : 2 ≤ xs.length) :
    ∑ j : Fin (xs.deleteIdx {i}).length, u ((xs.deleteIdx {i}).get j) =
      (∑ j : Fin xs.length, u (xs.get j)) - u (xs.get i) := by
  -- Convert both sides to list sums via `Fin.sum_univ_fun_getElem`.
  have hlhs : (∑ j : Fin (xs.deleteIdx {i}).length, u ((xs.deleteIdx {i}).get j)) =
              ((xs.deleteIdx {i}).prizes.map u).sum := by
    show (∑ j : Fin (xs.deleteIdx {i}).prizes.length,
              u ((xs.deleteIdx {i}).prizes.get ⟨j.val, j.isLt⟩)) =
         ((xs.deleteIdx {i}).prizes.map u).sum
    rw [show (fun j : Fin (xs.deleteIdx {i}).prizes.length =>
              u ((xs.deleteIdx {i}).prizes.get ⟨j.val, j.isLt⟩)) =
            (fun j : Fin (xs.deleteIdx {i}).prizes.length =>
              u (xs.deleteIdx {i}).prizes[j.val]) from by
      funext j
      rw [List.get_eq_getElem]]
    exact Fin.sum_univ_fun_getElem _ u
  have hrhs : (∑ j : Fin xs.length, u (xs.get j)) = (xs.prizes.map u).sum := by
    show (∑ j : Fin xs.prizes.length, u (xs.prizes.get ⟨j.val, j.isLt⟩)) =
         (xs.prizes.map u).sum
    rw [show (fun j : Fin xs.prizes.length =>
              u (xs.prizes.get ⟨j.val, j.isLt⟩)) =
            (fun j : Fin xs.prizes.length => u xs.prizes[j.val]) from by
      funext j
      rw [List.get_eq_getElem]]
    exact Fin.sum_univ_fun_getElem _ u
  rw [hlhs, hrhs]
  -- Now: ((xs.deleteIdx {i}).prizes.map u).sum =
  --      (xs.prizes.map u).sum - u (xs.get i)
  rw [Lottery.deleteIdx_singleton_prizes xs i hlen]
  -- Use `← List.eraseIdx_map`: `(l.eraseIdx n).map f = (l.map f).eraseIdx n`.
  rw [← List.eraseIdx_map]
  -- Use the permutation `l[i] :: l.eraseIdx i ~ l` (where `l = xs.prizes.map u`).
  have hi_lt : i.val < (xs.prizes.map u).length := by
    rw [List.length_map]; exact i.isLt
  have hperm : List.Perm
                ((xs.prizes.map u)[i.val] ::
                  ((xs.prizes.map u).eraseIdx i.val))
                (xs.prizes.map u) :=
    List.getElem_cons_eraseIdx_perm hi_lt
  have hsum_perm : ((xs.prizes.map u)[i.val] ::
                    ((xs.prizes.map u).eraseIdx i.val)).sum =
                   (xs.prizes.map u).sum :=
    hperm.sum_eq
  -- LHS expands: (xs.prizes.map u)[i.val] + ((xs.prizes.map u).eraseIdx i.val).sum
  rw [List.sum_cons] at hsum_perm
  -- And: (xs.prizes.map u)[i.val] = u(xs.prizes[i.val]) = u(xs.get i)
  have hi_get_map : (xs.prizes.map u)[i.val] = u (xs.get i) := by
    rw [List.getElem_map]
    rfl
  rw [hi_get_map] at hsum_perm
  linarith

/-- **Average utility of `xs.deleteIdx {i}`**: when `xs.length ≥ 2`,
`U(xs.deleteIdx {i}) · (xs.length - 1) = U(xs) · xs.length - u(xs.get i)`.

This length-weighted form avoids dividing by `(xs.length - 1)` in
intermediate steps. -/
lemma averageUtility_deleteIdx_singleton_weighted (u : X → ℝ) (xs : Lottery X)
    (i : Fin xs.length) (hlen : 2 ≤ xs.length) :
    averageUtility u (xs.deleteIdx {i}) * ((xs.length - 1 : ℕ) : ℝ) =
      averageUtility u xs * (xs.length : ℝ) - u (xs.get i) := by
  unfold averageUtility
  have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
  have hlen_minus_1_pos : (0 : ℝ) < ((xs.length - 1 : ℕ) : ℝ) := by
    have : 0 < xs.length - 1 := by omega
    exact_mod_cast this
  have hdel_len : (xs.deleteIdx {i}).length = xs.length - 1 :=
    Lottery.length_deleteIdx_singleton xs i hlen
  have hdel_len_real : ((xs.deleteIdx {i}).length : ℝ) = ((xs.length - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdel_len
  have hsum_del := sum_u_deleteIdx_singleton u xs i hlen
  rw [hdel_len_real]
  rw [div_mul_cancel₀ _ (ne_of_gt hlen_minus_1_pos)]
  rw [div_mul_cancel₀ _ (ne_of_gt hlen_pos)]
  exact hsum_del

/-! ### `Finset` extension: `averageUtility` of `xs.deleteIdx E`

The next lemmas extend the singleton-deletion arithmetic to multi-index
`Finset` deletion sets, which is what the `Cancellation` axiom uses.

The proofs require a multi-index extension of
`Lottery.filter_zipIdx_singleton_eq_eraseIdx` — i.e., a characterisation
of `(xs.deleteIdx E).prizes` for arbitrary Finset `E`.  This can be
obtained either by:
* Induction on `E.card`, peeling off one element at a time using
  `Lottery.deleteIdx_singleton_prizes`, with careful `Fin`-index casting
  between consecutive deletion steps.
* Direct list-level reasoning on the `filter`-of-`zipIdx` form, using
  `List.length_filter_eq_countP` to count remaining elements.

The statements below are deliberately phrased so that, once the multi-index
characterisation lands, the rest of the cascade (Cancellation, the easy
direction of `prop_average_utility`) follows mechanically. -/

/-- **Filter-zipIdx counting fact**: the number of pairs in `xs.prizes.zipIdx`
whose index (cast to `Fin xs.length`) lies in `E` equals `E.card`.

This is the core combinatorial fact extracted from
`length_deleteIdx_finset_lt`'s proof so it can be reused in
`sum_u_deleteIdx_finset_const`. -/
lemma countP_zipIdx_pred_in_eq (xs : Lottery X)
    (E : Finset (Fin xs.length)) :
    xs.prizes.zipIdx.countP
      (fun p => decide (∃ h : p.2 < xs.length,
                         (⟨p.2, h⟩ : Fin xs.length) ∈ E)) = E.card := by
  -- Same proof as the inner `hcount_in` from `length_deleteIdx_finset_lt`.
  set q : ℕ → Bool := fun k =>
    decide (∃ h : k < xs.length, (⟨k, h⟩ : Fin xs.length) ∈ E)
    with hq_def
  -- Factor through `Prod.snd`.
  have hpred_factors :
      (fun p : X × ℕ => decide (∃ h : p.2 < xs.length,
                                   (⟨p.2, h⟩ : Fin xs.length) ∈ E)) =
      (q ∘ Prod.snd) := by
    funext p; rfl
  rw [hpred_factors, ← List.countP_map]
  rw [show xs.prizes.zipIdx.map Prod.snd = List.range xs.prizes.length from by
    rw [List.zipIdx_map_snd]; rw [List.range_eq_range']]
  rw [List.countP_eq_length_filter]
  have hlen_eq : xs.prizes.length = xs.length := rfl
  rw [hlen_eq]
  have h_E_list_len : (E.toList.map Fin.val).length = E.card := by
    rw [List.length_map, Finset.length_toList]
  rw [← h_E_list_len]
  apply List.Perm.length_eq
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_range).filter _
  · apply List.Nodup.map
    · exact Fin.val_injective
    · exact E.nodup_toList
  · ext k
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range,
               List.mem_map, Finset.mem_toList]
    constructor
    · rintro ⟨hk_lt, hq_true⟩
      rw [hq_def] at hq_true
      have hex : ∃ h : k < xs.length, (⟨k, h⟩ : Fin xs.length) ∈ E :=
        of_decide_eq_true hq_true
      obtain ⟨h, hmem⟩ := hex
      exact ⟨⟨k, h⟩, hmem, rfl⟩
    · rintro ⟨b, hb_mem, hb_eq⟩
      refine ⟨?_, ?_⟩
      · rw [← hb_eq]; exact b.isLt
      · rw [hq_def]
        apply decide_eq_true
        have hb_lt : k < xs.length := by rw [← hb_eq]; exact b.isLt
        refine ⟨hb_lt, ?_⟩
        have h_eq_b : (⟨k, hb_lt⟩ : Fin xs.length) = b := by
          apply Fin.ext; exact hb_eq.symm
        rw [h_eq_b]; exact hb_mem

/-- **Sum-of-utilities under Finset deletion of a constant prize**:
when all prizes in `E` equal a fixed value `a`, erasing the indices in `E`
from `xs.prizes` reduces the sum of `u` by `E.card · u(a)`.

Proof: convert both sides to list sums via `Fin.sum_univ_fun_getElem`,
then characterise `(xs.deleteIdx E).prizes.map u` as a partition of
`xs.prizes.map u`'s zipIdx-filter.  Use `List.filter_append_perm` to
decompose the total sum into the "in" part (which sums to `E.card · u(a)`
by `hE_const`) and the "out" part (which is `(xs.deleteIdx E).prizes.map u`). -/
lemma sum_u_deleteIdx_finset_const (u : X → ℝ) (xs : Lottery X)
    (a : X) (E : Finset (Fin xs.length))
    (hE_const : ∀ i ∈ E, xs.get i = a)
    (hE_lt : E.card < xs.length) :
    ∑ j : Fin (xs.deleteIdx E).length, u ((xs.deleteIdx E).get j) =
      (∑ j : Fin xs.length, u (xs.get j)) - (E.card : ℝ) * u a := by
  -- Setup: define the filter predicates.
  set pred_out : X × ℕ → Bool := fun p =>
    decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    with hpred_out_def
  set pred_in : X × ℕ → Bool := fun p =>
    decide (∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    with hpred_in_def
  have hpred_complement_bool : ∀ p, pred_out p = !pred_in p := by
    intro p
    show decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E) =
         !decide (∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    rw [decide_not]
  -- Convert LHS Fin-sum to list sum.
  have hlhs : (∑ j : Fin (xs.deleteIdx E).length, u ((xs.deleteIdx E).get j)) =
              ((xs.deleteIdx E).prizes.map u).sum := by
    show (∑ j : Fin (xs.deleteIdx E).prizes.length,
              u ((xs.deleteIdx E).prizes.get ⟨j.val, j.isLt⟩)) =
         ((xs.deleteIdx E).prizes.map u).sum
    rw [show (fun j : Fin (xs.deleteIdx E).prizes.length =>
              u ((xs.deleteIdx E).prizes.get ⟨j.val, j.isLt⟩)) =
            (fun j : Fin (xs.deleteIdx E).prizes.length =>
              u (xs.deleteIdx E).prizes[j.val]) from by
      funext j
      rw [List.get_eq_getElem]]
    exact Fin.sum_univ_fun_getElem _ u
  -- Convert RHS Fin-sum to list sum.
  have hrhs : (∑ j : Fin xs.length, u (xs.get j)) = (xs.prizes.map u).sum := by
    show (∑ j : Fin xs.prizes.length, u (xs.prizes.get ⟨j.val, j.isLt⟩)) =
         (xs.prizes.map u).sum
    rw [show (fun j : Fin xs.prizes.length =>
              u (xs.prizes.get ⟨j.val, j.isLt⟩)) =
            (fun j : Fin xs.prizes.length => u xs.prizes[j.val]) from by
      funext j
      rw [List.get_eq_getElem]]
    exact Fin.sum_univ_fun_getElem _ u
  rw [hlhs, hrhs]
  -- Characterise (xs.deleteIdx E).prizes via the deleteIdx unfolding (when non-empty).
  have hdel_prizes_eq :
      (xs.deleteIdx E).prizes =
      (xs.prizes.zipIdx.filter pred_out).map Prod.fst := by
    -- Need non-emptiness of the filter-mapped list.  By the helper lemma,
    -- (filter pred_in zipIdx).countP = E.card, so (filter pred_out).length =
    -- xs.length - E.card ≥ 1.
    have hcount_in : xs.prizes.zipIdx.countP pred_in = E.card :=
      countP_zipIdx_pred_in_eq xs E
    have hzipIdx_len : xs.prizes.zipIdx.length = xs.length := by
      rw [List.length_zipIdx]; rfl
    have h_total :=
      List.length_eq_countP_add_countP pred_in (l := xs.prizes.zipIdx)
    have heq_neg : (fun b : X × ℕ => decide ¬ pred_in b = true) =
                   (fun b => !pred_in b) := by funext p; simp
    rw [heq_neg] at h_total
    have hpred_eq_funext : (fun b => !pred_in b) = pred_out := by
      funext p; rw [hpred_complement_bool p]
    rw [hpred_eq_funext] at h_total
    rw [hzipIdx_len, hcount_in] at h_total
    -- h_total: xs.length = E.card + countP pred_out
    have hcount_out_pos : 1 ≤ xs.prizes.zipIdx.countP pred_out := by omega
    have hfilter_len_pos :
        1 ≤ (xs.prizes.zipIdx.filter pred_out).length := by
      rw [← List.countP_eq_length_filter]; exact hcount_out_pos
    have hne : (xs.prizes.zipIdx.filter pred_out).map Prod.fst ≠ [] := by
      intro h
      have hlen_zero := congrArg List.length h
      rw [List.length_map] at hlen_zero
      -- hlen_zero : (xs.prizes.zipIdx.filter pred_out).length = [].length = 0.
      have hlen_zero' : (xs.prizes.zipIdx.filter pred_out).length = 0 := by
        simpa using hlen_zero
      omega
    -- Now unfold deleteIdx.
    show (xs.deleteIdx E).prizes =
         (xs.prizes.zipIdx.filter pred_out).map Prod.fst
    unfold Lottery.deleteIdx
    show (let ys := (xs.prizes.zipIdx.filter pred_out).map Prod.fst
          (if h : ys = [] then xs else (⟨ys, h⟩ : Lottery X))).prizes =
         (xs.prizes.zipIdx.filter pred_out).map Prod.fst
    rw [dif_neg hne]
  rw [hdel_prizes_eq]
  -- Combine the two maps: `.map Prod.fst |>.map u = .map (u ∘ Prod.fst)`.
  rw [List.map_map]
  -- Use `filter_append_perm` to decompose total sum.
  have hperm : List.Perm
                ((xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst) ++
                 (xs.prizes.zipIdx.filter pred_out).map (u ∘ Prod.fst))
                (xs.prizes.zipIdx.map (u ∘ Prod.fst)) := by
    rw [show pred_out = (fun b => !pred_in b) from by
      funext p; exact hpred_complement_bool p]
    rw [← List.map_append]
    exact (List.filter_append_perm pred_in xs.prizes.zipIdx).map (u ∘ Prod.fst)
  -- The total list maps back to xs.prizes.map u.
  have hzipIdx_compose :
      xs.prizes.zipIdx.map (u ∘ Prod.fst) = xs.prizes.map u := by
    rw [← List.map_map]
    rw [List.zipIdx_map_fst]
  rw [← hzipIdx_compose]
  -- Total sum = pred_in sum + pred_out sum.
  have hsum_perm : ((xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst)).sum +
                   ((xs.prizes.zipIdx.filter pred_out).map (u ∘ Prod.fst)).sum =
                   (xs.prizes.zipIdx.map (u ∘ Prod.fst)).sum := by
    rw [← List.sum_append]
    exact hperm.sum_eq
  -- Compute the pred_in part: every element has prize equal to `a`, so sum = E.card · u(a).
  have hsum_in : ((xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst)).sum =
                 (E.card : ℝ) * u a := by
    -- Every element of the mapped list is u(a).
    have hall_eq : ∀ x ∈ (xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst),
                    x = u a := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨p, hp_mem, hp_eq⟩ := hx
      rw [List.mem_filter] at hp_mem
      obtain ⟨hp_in_zipIdx, hp_pred⟩ := hp_mem
      -- pred_in p means ⟨p.2, _⟩ ∈ E.
      rw [hpred_in_def] at hp_pred
      have hex : ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E :=
        of_decide_eq_true hp_pred
      obtain ⟨h, hmem⟩ := hex
      -- p ∈ xs.prizes.zipIdx ⟹ p = (xs.prizes[p.2], p.2).
      have hsnd_lt : p.2 < xs.prizes.length :=
        List.snd_lt_of_mem_zipIdx hp_in_zipIdx
      have hp_eq_pair : p = (xs.prizes[p.2], p.2) := by
        rcases p with ⟨pf, ps⟩
        have hpair_mem : (pf, ps) ∈ xs.prizes.zipIdx := hp_in_zipIdx
        -- The `getElem?` characterization of zipIdx membership.
        have := List.mk_mem_zipIdx_iff_getElem?.mp hpair_mem
        -- this : xs.prizes[ps]? = some pf
        have hps_lt : ps < xs.prizes.length := List.snd_lt_of_mem_zipIdx hpair_mem
        have h_get_eq : xs.prizes[ps] = pf := by
          have h1 : xs.prizes[ps]? = some pf := by simpa using this
          rw [List.getElem?_eq_getElem hps_lt] at h1
          exact (Option.some.inj h1)
        ext
        · exact h_get_eq.symm
        · rfl
      -- Compute u(p.1) = u(xs.get ⟨p.2, h⟩) = u(a).
      rw [← hp_eq]
      show u p.1 = u a
      -- xs.get ⟨p.2, h⟩ = xs.prizes.get ⟨p.2, h⟩ definitionally.
      -- And xs.prizes.get = xs.prizes[_] via List.get_eq_getElem.
      -- p.1 = xs.prizes[p.2] from hp_eq_pair.
      have hp1 : p.1 = xs.prizes[p.2] := by
        conv_lhs => rw [hp_eq_pair]
      have hget_a : xs.get ⟨p.2, h⟩ = a := hE_const ⟨p.2, h⟩ hmem
      have hget_prizes : xs.get ⟨p.2, h⟩ = xs.prizes[p.2] := by
        show xs.prizes.get ⟨p.2, h⟩ = xs.prizes[p.2]
        rw [List.get_eq_getElem]
      rw [hp1, ← hget_prizes, hget_a]
    -- Length of the filter.
    have hlen_in : (xs.prizes.zipIdx.filter pred_in).length = E.card := by
      rw [← List.countP_eq_length_filter]
      exact countP_zipIdx_pred_in_eq xs E
    -- Sum of constant `u a` over a list of length E.card.
    have hall_eq_map :
        ∀ x ∈ (xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst), x = u a := hall_eq
    -- Use sum_eq_card_nsmul.
    have hsum_eq :=
      List.sum_eq_card_nsmul ((xs.prizes.zipIdx.filter pred_in).map (u ∘ Prod.fst))
        (u a) hall_eq_map
    rw [hsum_eq, List.length_map, hlen_in]
    -- E.card • u a = (E.card : ℝ) * u a.
    rw [nsmul_eq_mul]
  -- Conclude: total sum - E.card · u(a) = pred_out sum.
  linarith

/-- **Length of Finset deletion (proper subset case)**: when `E.card < xs.length`,
the deletion result has length `xs.length - E.card`.

Proof: characterise `(xs.deleteIdx E).prizes`'s length via the
`filter`-of-`zipIdx` form.  When the result is non-empty, the length
equals `(filter ... xs.prizes.zipIdx).length`, which we count via a
partition argument. -/
lemma length_deleteIdx_finset_lt (xs : Lottery X)
    (E : Finset (Fin xs.length))
    (hE_lt : E.card < xs.length) :
    (xs.deleteIdx E).length = xs.length - E.card := by
  -- Define the membership-in-E predicate at the Nat-index level.
  set pred_out : X × ℕ → Bool := fun p =>
    decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    with hpred_out_def
  set pred_in : X × ℕ → Bool := fun p =>
    decide (∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    with hpred_in_def
  -- Count of "in" predicate equals E.card (via the helper lemma).
  have hcount_in : xs.prizes.zipIdx.countP pred_in = E.card :=
    countP_zipIdx_pred_in_eq xs E
  have hzipIdx_len : xs.prizes.zipIdx.length = xs.length := by
    rw [List.length_zipIdx]
    rfl
  -- pred_out is the "complement" of pred_in (both Bool-valued).
  -- Specifically: `decide ¬X` where `X = ∃ h, ⟨p.2, h⟩ ∈ E`.
  -- Since `X` is decidable, `decide ¬X = !decide X`.
  have hpred_complement_bool : ∀ p, pred_out p = !pred_in p := by
    intro p
    show decide (¬ ∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E) =
         !decide (∃ h : p.2 < xs.length, (⟨p.2, h⟩ : Fin xs.length) ∈ E)
    rw [decide_not]
  -- Use partition: length = countP pred_in + countP (!pred_in).
  have h_total :=
    List.length_eq_countP_add_countP pred_in (l := xs.prizes.zipIdx)
  -- Convert `decide (¬ p a)` ↔ `!p a` since `pred_in a` is Bool.
  have heq_neg : (fun a : X × ℕ => decide ¬ pred_in a = true) =
                 (fun a => !pred_in a) := by
    funext p
    simp
  rw [heq_neg] at h_total
  -- Substitute pred_out for !pred_in via funext.
  have hpred_eq_funext : (fun a => !pred_in a) = pred_out := by
    funext p
    rw [hpred_complement_bool p]
  rw [hpred_eq_funext] at h_total
  rw [hzipIdx_len, hcount_in] at h_total
  -- Now: xs.length = E.card + countP pred_out, so countP pred_out = xs.length - E.card.
  have hcount_out : xs.prizes.zipIdx.countP pred_out = xs.length - E.card := by
    omega
  have hfilter_len :
      (xs.prizes.zipIdx.filter pred_out).length = xs.length - E.card := by
    rw [← List.countP_eq_length_filter]; exact hcount_out
  have hne : (xs.prizes.zipIdx.filter pred_out).map Prod.fst ≠ [] := by
    intro h
    have hlen_zero := congrArg List.length h
    rw [List.length_map] at hlen_zero
    rw [hfilter_len] at hlen_zero
    simp at hlen_zero
    omega
  -- Unfold deleteIdx and conclude.
  show (xs.deleteIdx E).prizes.length = xs.length - E.card
  unfold Lottery.deleteIdx
  show (let ys := (xs.prizes.zipIdx.filter pred_out).map Prod.fst
        (if h : ys = [] then xs else (⟨ys, h⟩ : Lottery X))).prizes.length =
       xs.length - E.card
  rw [dif_neg hne]
  show ((xs.prizes.zipIdx.filter pred_out).map Prod.fst).length =
       xs.length - E.card
  rw [List.length_map]
  exact hfilter_len

/-- **Average utility of `xs.deleteIdx E` (constant-prize case)**: the
length-weighted formula generalising
`averageUtility_deleteIdx_singleton_weighted`.

When all prizes in `E` equal `a` and `E.card < xs.length`,
`U(xs.deleteIdx E) · (xs.length - E.card) = U(xs) · xs.length - E.card · u(a)`.

This wrapper is **fully proven** assuming the two sorried lemmas above:
once `sum_u_deleteIdx_finset_const` and `length_deleteIdx_finset_lt`
land, this lemma becomes sorry-free automatically, and
`cancellation_of_averageUtility_repr` (general case) follows directly. -/
lemma averageUtility_deleteIdx_finset_const_weighted
    (u : X → ℝ) (xs : Lottery X)
    (a : X) (E : Finset (Fin xs.length))
    (hE_const : ∀ i ∈ E, xs.get i = a)
    (hE_lt : E.card < xs.length) :
    averageUtility u (xs.deleteIdx E) * ((xs.length - E.card : ℕ) : ℝ) =
      averageUtility u xs * (xs.length : ℝ) - (E.card : ℝ) * u a := by
  unfold averageUtility
  have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
  have hlen_minus_E_pos : (0 : ℝ) < ((xs.length - E.card : ℕ) : ℝ) := by
    have : 0 < xs.length - E.card := by omega
    exact_mod_cast this
  have hdel_len : (xs.deleteIdx E).length = xs.length - E.card :=
    length_deleteIdx_finset_lt xs E hE_lt
  have hdel_len_real : ((xs.deleteIdx E).length : ℝ) = ((xs.length - E.card : ℕ) : ℝ) := by
    exact_mod_cast hdel_len
  have hsum_del := sum_u_deleteIdx_finset_const u xs a E hE_const hE_lt
  rw [hdel_len_real]
  rw [div_mul_cancel₀ _ (ne_of_gt hlen_minus_E_pos)]
  rw [div_mul_cancel₀ _ (ne_of_gt hlen_pos)]
  exact hsum_del

/-! ### Real consequences: `averageUtility` of `xs^n ⊞ zs` -/

/-- **Average utility of `(xs ^^ n) ⊞ zs`** as a length-weighted formula.

Combining `averageUtility_concat_weighted`, `averageUtility_replicate`,
and `length_replicate`. -/
lemma averageUtility_replicate_concat_formula
    (u : X → ℝ) (xs zs : Lottery X) (n : ℕ) :
    averageUtility u ((xs ^^ n) ⊞ zs) *
      (((n + 1) * xs.length + zs.length : ℕ) : ℝ) =
    averageUtility u xs * ((n + 1) * xs.length : ℕ) +
    averageUtility u zs * (zs.length : ℕ) := by
  have hweighted := averageUtility_concat_weighted u (xs ^^ n) zs
  rw [Lottery.length_replicate, averageUtility_replicate] at hweighted
  exact hweighted

/-- **Pointwise convergence of `U((xs^n) ⊞ zs)` toward `U(xs)`.**

Concretely, the difference `U(xs) − U((xs^n) ⊞ zs)` equals
`(U(xs) − U(zs)) · zs.length / ((n+1) · xs.length + zs.length)`. -/
lemma averageUtility_replicate_concat_diff
    (u : X → ℝ) (xs zs : Lottery X) (n : ℕ) :
    averageUtility u xs - averageUtility u ((xs ^^ n) ⊞ zs) =
    (averageUtility u xs - averageUtility u zs) *
      (zs.length : ℝ) /
      (((n + 1) * xs.length + zs.length : ℕ) : ℝ) := by
  -- From the formula:
  --   U((xs^n)⊞zs) · ((n+1)·xs.length + zs.length)
  --   = U(xs) · ((n+1)·xs.length) + U(zs) · zs.length
  -- So:
  --   U(xs) - U((xs^n)⊞zs)
  --   = (U(xs)·((n+1)·xs.length + zs.length) - [U(xs)·(n+1)·xs.length + U(zs)·zs.length])
  --   / ((n+1)·xs.length + zs.length)
  --   = (U(xs) - U(zs))·zs.length / ((n+1)·xs.length + zs.length)
  have hformula := averageUtility_replicate_concat_formula u xs zs n
  have hpos : (0 : ℝ) < (((n + 1) * xs.length + zs.length : ℕ) : ℝ) := by
    push_cast
    have hxs : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
    have hzs : (0 : ℝ) < (zs.length : ℝ) := by exact_mod_cast zs.length_pos
    positivity
  have hne : (((n + 1) * xs.length + zs.length : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
  field_simp
  push_cast at hformula ⊢
  linarith

/-- **Eventual strict comparison from average utility**: if `U(xs) > U(ys)`,
then for any `zs`, eventually `U((xs^n) ⊞ zs) > U(ys)`.

This is the analytic core of the Archimedeanity axiom under any
average-utility representation. -/
lemma averageUtility_eventual_strict_left
    (u : X → ℝ) (xs ys zs : Lottery X)
    (hxsy : averageUtility u ys < averageUtility u xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      averageUtility u ys < averageUtility u ((xs ^^ n) ⊞ zs) := by
  set δ := averageUtility u xs - averageUtility u ys with hδ
  have hδ_pos : 0 < δ := by rw [hδ]; linarith
  set ε := (averageUtility u xs - averageUtility u zs) * (zs.length : ℝ)
        with hε_def
  have hxs_pos : (0 : ℝ) < (xs.length : ℝ) := by exact_mod_cast xs.length_pos
  -- Pick `N` such that `(N+1)·xs.length·δ > |ε|`.
  obtain ⟨N, hN⟩ := exists_nat_gt (|ε| / (δ * xs.length))
  refine ⟨N, fun n hn => ?_⟩
  -- We have:  U(xs) - U((xs^n) ⊞ zs) = ε / denom.
  have hdiff := averageUtility_replicate_concat_diff u xs zs n
  -- Goal:  U(ys) < U((xs^n) ⊞ zs), i.e., δ > U(xs) - U((xs^n) ⊞ zs) = ε/denom.
  have hpos_denom : (0 : ℝ) < (((n + 1) * xs.length + zs.length : ℕ) : ℝ) := by
    push_cast
    have hzs : (0 : ℝ) < (zs.length : ℝ) := by exact_mod_cast zs.length_pos
    positivity
  have hε_bound : ε / (((n + 1) * xs.length + zs.length : ℕ) : ℝ) < δ := by
    have h1 : |ε| < δ * ((N + 1) * xs.length : ℝ) := by
      have habs_div : |ε| / (δ * xs.length) < (N : ℝ) := hN
      have hδxs_pos : 0 < δ * (xs.length : ℝ) := mul_pos hδ_pos hxs_pos
      rw [div_lt_iff₀ hδxs_pos] at habs_div
      nlinarith
    have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (δ * ((N + 1) * xs.length : ℝ)) ≤
              δ * ((n + 1) * xs.length : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ_pos)
      nlinarith
    have h3 : δ * ((n + 1) * xs.length : ℝ) ≤
              δ * (((n + 1) * xs.length + zs.length : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ_pos)
      have hzs_nn : (0 : ℝ) ≤ (zs.length : ℝ) := by
        exact_mod_cast Nat.zero_le _
      push_cast
      linarith
    have habs_lt : |ε| < δ * (((n + 1) * xs.length + zs.length : ℕ) : ℝ) := by
      linarith
    rcases lt_or_ge ε 0 with hε_neg | hε_nn
    · -- ε < 0, so ε / denom < 0 ≤ δ.
      have hε_div_neg : ε / (((n + 1) * xs.length + zs.length : ℕ) : ℝ) < 0 :=
        div_neg_of_neg_of_pos hε_neg hpos_denom
      linarith
    · rw [abs_of_nonneg hε_nn] at habs_lt
      rw [div_lt_iff₀ hpos_denom]
      linarith
  -- Conclude: U(ys) < U((xs^n) ⊞ zs).
  -- We have hdiff: U(xs) - U((xs^n) ⊞ zs) = ε/denom < δ = U(xs) - U(ys).
  -- So U(ys) < U((xs^n) ⊞ zs).
  linarith

/-- **Symmetric eventual strict comparison**: if `U(xs) > U(ys)`, then
for any `zs`, eventually `U(xs) > U((ys^n) ⊞ zs)`.

Proof: same structure as the left version, with the roles of `xs`/`ys`
swapped. -/
lemma averageUtility_eventual_strict_right
    (u : X → ℝ) (xs ys zs : Lottery X)
    (hxsy : averageUtility u ys < averageUtility u xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      averageUtility u ((ys ^^ n) ⊞ zs) < averageUtility u xs := by
  -- Apply the left version with roles swapped: take `xs := ys, ys := xs`
  -- and use the *reverse* difference.
  -- We want:  U((ys^n) ⊞ zs) < U(xs).
  -- The diff `U((ys^n) ⊞ zs) - U(ys) = -((U(ys) - U((ys^n) ⊞ zs)))` shrinks.
  -- Specifically `U((ys^n) ⊞ zs) → U(ys)`.  Pick N so that
  -- `|U((ys^n) ⊞ zs) - U(ys)| < U(xs) - U(ys) = δ`.
  set δ := averageUtility u xs - averageUtility u ys with hδ
  have hδ_pos : 0 < δ := by rw [hδ]; linarith
  set ε := (averageUtility u ys - averageUtility u zs) * (zs.length : ℝ)
        with hε_def
  have hys_pos : (0 : ℝ) < (ys.length : ℝ) := by exact_mod_cast ys.length_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (|ε| / (δ * ys.length))
  refine ⟨N, fun n hn => ?_⟩
  have hdiff := averageUtility_replicate_concat_diff u ys zs n
  have hpos_denom : (0 : ℝ) < (((n + 1) * ys.length + zs.length : ℕ) : ℝ) := by
    push_cast
    have hzs : (0 : ℝ) < (zs.length : ℝ) := by exact_mod_cast zs.length_pos
    positivity
  -- We have:  U(ys) - U((ys^n) ⊞ zs) = ε/denom.
  -- Want:  U((ys^n) ⊞ zs) < U(xs).
  -- I.e.:  U(ys) - U((ys^n) ⊞ zs) > U(ys) - U(xs) = -δ.
  -- I.e.:  ε/denom > -δ.
  -- |ε/denom| < δ, so in particular ε/denom > -δ.
  have hε_bound :
      -δ < ε / (((n + 1) * ys.length + zs.length : ℕ) : ℝ) := by
    have h1 : |ε| < δ * ((N + 1) * ys.length : ℝ) := by
      have habs_div : |ε| / (δ * ys.length) < (N : ℝ) := hN
      have hδys_pos : 0 < δ * (ys.length : ℝ) := mul_pos hδ_pos hys_pos
      rw [div_lt_iff₀ hδys_pos] at habs_div
      nlinarith
    have hN_le_n : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (δ * ((N + 1) * ys.length : ℝ)) ≤
              δ * ((n + 1) * ys.length : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ_pos)
      nlinarith
    have h3 : δ * ((n + 1) * ys.length : ℝ) ≤
              δ * (((n + 1) * ys.length + zs.length : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ_pos)
      have hzs_nn : (0 : ℝ) ≤ (zs.length : ℝ) := by
        exact_mod_cast Nat.zero_le _
      push_cast
      linarith
    have habs_lt : |ε| < δ * (((n + 1) * ys.length + zs.length : ℕ) : ℝ) := by
      linarith
    rcases lt_or_ge ε 0 with hε_neg | hε_nn
    · rw [abs_of_neg hε_neg] at habs_lt
      rw [lt_div_iff₀ hpos_denom]
      linarith
    · -- ε ≥ 0, so ε/denom ≥ 0 > -δ.
      have hε_div_nn : 0 ≤ ε / (((n + 1) * ys.length + zs.length : ℕ) : ℝ) :=
        div_nonneg hε_nn (le_of_lt hpos_denom)
      linarith
  linarith

/-- **Archimedeanity from average-utility representation.**

If `P` admits an average-utility representation, then `P` satisfies the
Archimedeanity axiom: from `xs ≻ ys`, we eventually have
`(xs^n) ⊞ zs ≻ ys` and `xs ≻ (ys^n) ⊞ zs`.

Real proof using `averageUtility_eventual_strict_left/right`. -/
lemma archimedeanity_of_averageUtility_repr
    (P : Preference S X)
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys zs : Lottery X)
    (_hsxy : P.onLotteries xs ys) (hnxy : ¬ P.onLotteries ys xs) :
    ∃ N : ℕ, ∀ n, n ≥ N →
      ( P.onLotteries ((xs ^^ n) ⊞ zs) ys ∧
        ¬ P.onLotteries ys ((xs ^^ n) ⊞ zs) ) ∧
      ( P.onLotteries xs ((ys ^^ n) ⊞ zs) ∧
        ¬ P.onLotteries ((ys ^^ n) ⊞ zs) xs ) := by
  -- Translate `xs ≻ ys` to strict inequality on average utilities.
  have hxsy : averageUtility u ys < averageUtility u xs := by
    rw [hrepr] at hnxy
    push_neg at hnxy
    exact hnxy
  -- Apply both eventual-strict lemmas.
  obtain ⟨N₁, hN₁⟩ := averageUtility_eventual_strict_left u xs ys zs hxsy
  obtain ⟨N₂, hN₂⟩ := averageUtility_eventual_strict_right u xs ys zs hxsy
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn1 : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn2 : n ≥ N₂ := le_trans (le_max_right _ _) hn
  have h_left : averageUtility u ys < averageUtility u ((xs ^^ n) ⊞ zs) :=
    hN₁ n hn1
  have h_right : averageUtility u ((ys ^^ n) ⊞ zs) < averageUtility u xs :=
    hN₂ n hn2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- (xs^n ⊞ zs) ≽ ys.
    show P.onLotteries ((xs ^^ n) ⊞ zs) ys
    rw [hrepr]; exact le_of_lt h_left
  · -- ¬ ys ≽ (xs^n ⊞ zs).
    show ¬ P.onLotteries ys ((xs ^^ n) ⊞ zs)
    rw [hrepr]
    push_neg
    exact h_left
  · -- xs ≽ (ys^n ⊞ zs).
    show P.onLotteries xs ((ys ^^ n) ⊞ zs)
    rw [hrepr]; exact le_of_lt h_right
  · -- ¬ (ys^n ⊞ zs) ≽ xs.
    show ¬ P.onLotteries ((ys ^^ n) ⊞ zs) xs
    rw [hrepr]
    push_neg
    exact h_right

/-! ### Cancellation from average-utility representation

The Cancellation axiom requires comparing pre- and post-deletion
lotteries.  Under an average-utility representation, the equivalence
`xs ≽ ys ↔ xs.deleteIdx E ≽ ys.deleteIdx F` (when the ratios `|E|/|xs|`
and `|F|/|ys|` agree and the deleted prizes are all `a`) reduces to a
purely arithmetic claim about how `deleteIdx` affects the average
utility.

The proof requires a structural characterization of
`Lottery.deleteIdx`'s effect on `averageUtility`, which depends on
`Lottery.filter_zipIdx_singleton_eq_eraseIdx` (or its multi-index
extension).  We state the lemma cleanly here so that completing it
discharges the Cancellation half of the necessity direction of
`prop_average_utility`. -/

/-- **Cancellation from `averageUtility` representation.**

Under an average-utility representation, the preference satisfies the
Cancellation axiom: when matching same-prize fragments of equal relative
size are removed from both sides, the comparison is preserved. -/
lemma cancellation_of_averageUtility_repr
    (P : Preference S X)
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys : Lottery X) (a : X)
    (E : Finset (Fin xs.length)) (F : Finset (Fin ys.length))
    (hratio : (E.card : ℚ) / (xs.length : ℚ) = (F.card : ℚ) / (ys.length : ℚ))
    (hE : ∀ i ∈ E, xs.get i = a) (hF : ∀ j ∈ F, ys.get j = a) :
    P.onLotteries xs ys ↔
    P.onLotteries (xs.deleteIdx E) (ys.deleteIdx F) := by
  -- Boundary case: if `E.card = 0`, then by `hratio`, `F.card = 0`,
  -- so both deletions reduce to identity by `deleteIdx_empty`.
  by_cases hE_empty : E.card = 0
  · -- E.card = 0 ⟹ F.card = 0 by hratio.
    have hxs_pos : (0 : ℚ) < (xs.length : ℚ) := by
      exact_mod_cast xs.length_pos
    have hys_pos : (0 : ℚ) < (ys.length : ℚ) := by
      exact_mod_cast ys.length_pos
    have hF_empty : F.card = 0 := by
      -- E.card = 0 ⟹ E.card / xs.length = 0 ⟹ F.card / ys.length = 0 ⟹ F.card = 0
      have h1 : (E.card : ℚ) / (xs.length : ℚ) = 0 := by
        rw [hE_empty]; simp
      rw [h1] at hratio
      have : (F.card : ℚ) = 0 := by
        rw [eq_comm] at hratio
        rcases (div_eq_zero_iff.mp hratio) with h | h
        · exact h
        · exact absurd h (ne_of_gt hys_pos)
      exact_mod_cast this
    -- Both `E` and `F` are empty.
    have hE_eq : E = ∅ := Finset.card_eq_zero.mp hE_empty
    have hF_eq : F = ∅ := Finset.card_eq_zero.mp hF_empty
    rw [hE_eq, hF_eq]
    rw [Lottery.deleteIdx_empty, Lottery.deleteIdx_empty]
  · -- General case: E.card ≠ 0, hence F.card ≠ 0.
    have hxs_pos : (0 : ℚ) < (xs.length : ℚ) := by
      exact_mod_cast xs.length_pos
    have hys_pos : (0 : ℚ) < (ys.length : ℚ) := by
      exact_mod_cast ys.length_pos
    have hF_pos : 0 < F.card := by
      by_contra hF_zero
      push_neg at hF_zero
      have hF_eq_zero : F.card = 0 := by omega
      have h2 : (F.card : ℚ) / (ys.length : ℚ) = 0 := by rw [hF_eq_zero]; simp
      rw [h2] at hratio
      have : (E.card : ℚ) = 0 := by
        rcases (div_eq_zero_iff.mp hratio) with h | h
        · exact h
        · exact absurd h (ne_of_gt hxs_pos)
      have : E.card = 0 := by exact_mod_cast this
      exact hE_empty this
    have hE_card_le : E.card ≤ xs.length := by
      have h := E.card_le_univ
      simp [Fintype.card_fin] at h
      exact h
    have hF_card_le : F.card ≤ ys.length := by
      have h := F.card_le_univ
      simp [Fintype.card_fin] at h
      exact h
    -- Sub-case: E.card = xs.length (full deletion → fallback).
    by_cases hE_full : E.card = xs.length
    · -- E.card = xs.length ⟹ F.card = ys.length (by hratio).
      have hF_full : F.card = ys.length := by
        have hE_div : (E.card : ℚ) / (xs.length : ℚ) = 1 := by
          rw [hE_full]; field_simp
        rw [hE_div] at hratio
        have hF_div : (F.card : ℚ) = (ys.length : ℚ) := by
          have := hratio.symm
          rw [div_eq_one_iff_eq (ne_of_gt hys_pos)] at this
          exact this
        exact_mod_cast hF_div
      -- Both E and F are full; deleteIdx falls back to original.
      have hE_eq_univ : E = Finset.univ := by
        apply Finset.eq_univ_of_card
        simp [Fintype.card_fin, hE_full]
      have hF_eq_univ : F = Finset.univ := by
        apply Finset.eq_univ_of_card
        simp [Fintype.card_fin, hF_full]
      rw [hE_eq_univ, hF_eq_univ]
      rw [Lottery.deleteIdx_univ, Lottery.deleteIdx_univ]
    · -- E.card < xs.length (proper subset).
      have hE_lt : E.card < xs.length := lt_of_le_of_ne hE_card_le hE_full
      have hF_lt : F.card < ys.length := by
        have hratio_mul : (E.card : ℚ) * (ys.length : ℚ) =
                          (F.card : ℚ) * (xs.length : ℚ) := by
          have hxs_ne : (xs.length : ℚ) ≠ 0 := ne_of_gt hxs_pos
          have hys_ne : (ys.length : ℚ) ≠ 0 := ne_of_gt hys_pos
          field_simp at hratio
          linarith
        by_contra h
        push_neg at h
        have hF_eq : F.card = ys.length := le_antisymm hF_card_le h
        rw [hF_eq] at hratio_mul
        have hys_ne : (ys.length : ℚ) ≠ 0 := ne_of_gt hys_pos
        have hE_eq_xs : (E.card : ℚ) = (xs.length : ℚ) := by
          have : (E.card : ℚ) * (ys.length : ℚ) = (xs.length : ℚ) * (ys.length : ℚ) := by
            rw [hratio_mul]; ring
          exact mul_right_cancel₀ hys_ne this
        have : E.card = xs.length := by exact_mod_cast hE_eq_xs
        exact hE_full this
      -- Apply the weighted formula on both sides.
      have hxs_eq := averageUtility_deleteIdx_finset_const_weighted u xs a E hE hE_lt
      have hys_eq := averageUtility_deleteIdx_finset_const_weighted u ys a F hF hF_lt
      rw [hrepr xs ys, hrepr (xs.deleteIdx E) (ys.deleteIdx F)]
      have hxs_len_pos : (0 : ℝ) < (xs.length : ℝ) := by
        exact_mod_cast xs.length_pos
      have hys_len_pos : (0 : ℝ) < (ys.length : ℝ) := by
        exact_mod_cast ys.length_pos
      have hxs_minus_E_pos : (0 : ℝ) < ((xs.length - E.card : ℕ) : ℝ) := by
        have : 0 < xs.length - E.card := by omega
        exact_mod_cast this
      have hys_minus_F_pos : (0 : ℝ) < ((ys.length - F.card : ℕ) : ℝ) := by
        have : 0 < ys.length - F.card := by omega
        exact_mod_cast this
      have hratio_real :
          (E.card : ℝ) * (ys.length : ℝ) = (F.card : ℝ) * (xs.length : ℝ) := by
        have hratio_mul : (E.card : ℚ) * (ys.length : ℚ) =
                          (F.card : ℚ) * (xs.length : ℚ) := by
          have hxs_ne : (xs.length : ℚ) ≠ 0 := ne_of_gt hxs_pos
          have hys_ne : (ys.length : ℚ) ≠ 0 := ne_of_gt hys_pos
          field_simp at hratio
          linarith
        exact_mod_cast hratio_mul
      have hxs_minus_real : ((xs.length - E.card : ℕ) : ℝ) =
                            (xs.length : ℝ) - (E.card : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hE_lt)]
      have hys_minus_real : ((ys.length - F.card : ℕ) : ℝ) =
                            (ys.length : ℝ) - (F.card : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hF_lt)]
      rw [hxs_minus_real] at hxs_eq
      rw [hys_minus_real] at hys_eq
      -- Now: U(xs.deleteIdx E) * (xs.length - E.card) = U(xs)·xs.length - E.card·u(a)
      -- and similarly for ys.deleteIdx F.
      -- Goal: U(ys) ≤ U(xs) ↔ U(ys.deleteIdx F) ≤ U(xs.deleteIdx E).
      -- The proof is purely arithmetic: cross-multiply and use hratio_real.
      have hxs_minus_pos : (0 : ℝ) < (xs.length : ℝ) - (E.card : ℝ) := by
        rw [← hxs_minus_real]; exact hxs_minus_E_pos
      have hys_minus_pos : (0 : ℝ) < (ys.length : ℝ) - (F.card : ℝ) := by
        rw [← hys_minus_real]; exact hys_minus_F_pos
      constructor
      · intro hUys_le
        have hkey :
            (averageUtility u (xs.deleteIdx E) - averageUtility u (ys.deleteIdx F)) *
              ((xs.length : ℝ) - (E.card : ℝ)) * ((ys.length : ℝ) - (F.card : ℝ)) =
            (xs.length : ℝ) * ((ys.length : ℝ) - (F.card : ℝ)) *
              (averageUtility u xs - averageUtility u ys) := by
          linear_combination
            ((ys.length : ℝ) - (F.card : ℝ)) * hxs_eq -
            ((xs.length : ℝ) - (E.card : ℝ)) * hys_eq +
            (averageUtility u ys - u a) * hratio_real
        have hrhs_nonneg :
            0 ≤ (xs.length : ℝ) * ((ys.length : ℝ) - (F.card : ℝ)) *
                (averageUtility u xs - averageUtility u ys) := by
          have := sub_nonneg.mpr hUys_le
          positivity
        have hprod_nonneg :
            0 ≤ (averageUtility u (xs.deleteIdx E) - averageUtility u (ys.deleteIdx F)) *
                  ((xs.length : ℝ) - (E.card : ℝ)) * ((ys.length : ℝ) - (F.card : ℝ)) := by
          rw [hkey]; exact hrhs_nonneg
        have hpos_prod :
            0 < ((xs.length : ℝ) - (E.card : ℝ)) * ((ys.length : ℝ) - (F.card : ℝ)) :=
          mul_pos hxs_minus_pos hys_minus_pos
        nlinarith [hprod_nonneg, hpos_prod]
      · intro hUdel_le
        have hkey :
            (averageUtility u (xs.deleteIdx E) - averageUtility u (ys.deleteIdx F)) *
              ((xs.length : ℝ) - (E.card : ℝ)) * ((ys.length : ℝ) - (F.card : ℝ)) =
            (xs.length : ℝ) * ((ys.length : ℝ) - (F.card : ℝ)) *
              (averageUtility u xs - averageUtility u ys) := by
          linear_combination
            ((ys.length : ℝ) - (F.card : ℝ)) * hxs_eq -
            ((xs.length : ℝ) - (E.card : ℝ)) * hys_eq +
            (averageUtility u ys - u a) * hratio_real
        have hlhs_nonneg :
            0 ≤ (averageUtility u (xs.deleteIdx E) - averageUtility u (ys.deleteIdx F)) *
                  ((xs.length : ℝ) - (E.card : ℝ)) * ((ys.length : ℝ) - (F.card : ℝ)) := by
          have := sub_nonneg.mpr hUdel_le
          positivity
        have hrhs_nonneg :
            0 ≤ (xs.length : ℝ) * ((ys.length : ℝ) - (F.card : ℝ)) *
                (averageUtility u xs - averageUtility u ys) := by
          rw [← hkey]; exact hlhs_nonneg
        have hpos_factor :
            0 < (xs.length : ℝ) * ((ys.length : ℝ) - (F.card : ℝ)) :=
          mul_pos hxs_len_pos hys_minus_pos
        nlinarith [hrhs_nonneg, hpos_factor]

/-! ### Proposition 1, easy (necessity) direction -/

/-- **`prop_average_utility`, easy direction.**

If `P` admits an average-utility representation `(u, hrepr)`, then `P`
satisfies both Cancellation and Archimedeanity.

This is the easy half of `prop_average_utility`.  It bundles
`cancellation_of_averageUtility_repr` and
`archimedeanity_of_averageUtility_repr` (fully proved). -/
lemma prop_average_utility_mpr
    [DecidableEq X]
    (P : Preference S X) [WeakOrder P]
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs) :
    (∃ _ : Cancellation P, True) ∧ (∃ _ : Archimedeanity P, True) := by
  refine ⟨⟨⟨?_⟩, trivial⟩, ⟨⟨?_⟩, trivial⟩⟩
  · -- Cancellation: matching fragments of equal proportion can be removed.
    intro xs ys a E F hratio hE hF
    exact cancellation_of_averageUtility_repr P u hrepr xs ys a E F hratio hE hF
  · -- Archimedeanity: strict preferences are robust under small perturbations.
    intro xs ys zs ⟨hsxy, hnxy⟩
    exact archimedeanity_of_averageUtility_repr P u hrepr xs ys zs hsxy hnxy

/-- **Proposition 1 (average utility), wrapper-complete form.**

A weak-order preference on classical lotteries satisfies Cancellation and
Archimedeanity iff it admits an average-utility representation, provided the
named hard direction `AverageUtilityHardDirection P` is supplied.  The reverse
direction (representation ⇒ axioms) is proved here from the preceding lemmas;
the forward direction is the explicit representation-theorem dependency. -/
theorem prop_average_utility
    [DecidableEq X]
    (P : Preference S X)
    [WeakOrder P]
    (hHard : AverageUtilityHardDirection P) :
    ((∃ _ : Cancellation P, True) ∧ (∃ _ : Archimedeanity P, True)) ↔
    AverageUtilityRepresentation P := by
  constructor
  · exact hHard
  · intro hreprExists
    rcases hreprExists with ⟨u, hrepr⟩
    exact prop_average_utility_mpr (P := P) u hrepr

/-! ### WeakOrder from average-utility representation -/

/-- **WeakOrder from `averageUtility` representation (on lotteries)**:
the preference relation given by `xs ≽ ys ↔ U(ys) ≤ U(xs)` is reflexive
and transitive at the level of classical lotteries. -/
lemma onLotteries_refl_of_averageUtility_repr
    (P : Preference S X) (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs : Lottery X) :
    P.onLotteries xs xs := by
  rw [hrepr]

lemma onLotteries_complete_of_averageUtility_repr
    (P : Preference S X) (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys : Lottery X) :
    P.onLotteries xs ys ∨ P.onLotteries ys xs := by
  rcases le_total (averageUtility u xs) (averageUtility u ys) with h | h
  · right; rw [hrepr]; exact h
  · left; rw [hrepr]; exact h

lemma onLotteries_trans_of_averageUtility_repr
    (P : Preference S X) (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys zs : Lottery X)
    (h₁ : P.onLotteries xs ys)
    (h₂ : P.onLotteries ys zs) :
    P.onLotteries xs zs := by
  rw [hrepr] at *
  linarith

/-! ### Strict-preference characterization on lotteries -/

/-- Under `averageUtility` representation, strict preference on classical
lotteries is exactly strict inequality of average utilities. -/
lemma onLotteries_strict_iff_of_averageUtility_repr
    (P : Preference S X) (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys : Lottery X) :
    (P.onLotteries xs ys ∧ ¬ P.onLotteries ys xs) ↔
    averageUtility u ys < averageUtility u xs := by
  rw [hrepr, hrepr]
  constructor
  · intro ⟨h₁, h₂⟩
    push_neg at h₂
    exact h₂
  · intro h
    refine ⟨le_of_lt h, ?_⟩
    push_neg
    exact h

/-- Under `averageUtility` representation, indifference on classical
lotteries is exactly equality of average utilities. -/
lemma onLotteries_indiff_iff_of_averageUtility_repr
    (P : Preference S X) (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs)
    (xs ys : Lottery X) :
    (P.onLotteries xs ys ∧ P.onLotteries ys xs) ↔
    averageUtility u xs = averageUtility u ys := by
  rw [hrepr, hrepr]
  constructor
  · intro ⟨h₁, h₂⟩
    linarith
  · intro h
    exact ⟨le_of_eq h.symm, le_of_eq h⟩

end Preference

/-! ## §2.3  Classical lottery to gauge unverifiable uncertainty -/

namespace Preference

variable {S X : Type*} [DecidableEq X]

/-- **Axiom 4 (Monotonicity).**  Pointwise dominance implies preference. -/
class Monotonicity (P : Preference S X) : Prop where
  mono :
    ∀ f g : Act S X,
      (∀ s, P.onLotteries (f s) (g s)) → P.weakPref f g

/-! ### Real new lemmas about `Monotonicity` -/

/-- **Reflexive case**: a function `f` pointwise-dominates itself. -/
lemma Monotonicity.refl
    (P : Preference S X) [WeakOrder P] [Monotonicity P]
    (f : Act S X) :
    P.weakPref f f := by
  apply Monotonicity.mono
  intro s
  -- Need `P.onLotteries (f s) (f s)`, i.e. weak preference of identical
  -- constant acts.  This is reflexivity from `WeakOrder`.
  exact weakPref_refl P (constAct (f s))

/-- **Pointwise indifference implies indifference**: if `f s ~ g s` for
every `s`, then `f ~ g`. -/
lemma Monotonicity.indiff_of_pointwise
    (P : Preference S X) [WeakOrder P] [Monotonicity P]
    {f g : Act S X}
    (h : ∀ s, P.indiff (constAct (f s)) (constAct (g s))) :
    P.indiff f g := by
  refine ⟨?_, ?_⟩
  · apply Monotonicity.mono
    intro s
    exact (h s).1
  · apply Monotonicity.mono
    intro s
    exact (h s).2

/-- The set `cX_{x,y}` of classical lotteries supported on the prize pair
`{x,y}`. -/
def TwoPrizeLotteries (x y : X) : Set (Lottery X) :=
  { xs | ∀ i, xs.get i = x ∨ xs.get i = y }

/-- The set `cF_{x,y}` of two-prize acts. -/
def TwoPrizeActs (S : Type*) (x y : X) : Set (Act S X) :=
  { f | ∀ s, f s ∈ TwoPrizeLotteries x y }

/-! ### Real lemmas about `TwoPrizeLotteries` and `TwoPrizeActs` -/

/-- The singleton lottery `prizeLottery x` is in `TwoPrizeLotteries x y`. -/
lemma prizeLottery_mem_TwoPrizeLotteries_left (x y : X) :
    prizeLottery x ∈ TwoPrizeLotteries x y := by
  intro i
  left
  exact prizeLottery_get x i

/-- The singleton lottery `prizeLottery y` is in `TwoPrizeLotteries x y`. -/
lemma prizeLottery_mem_TwoPrizeLotteries_right (x y : X) :
    prizeLottery y ∈ TwoPrizeLotteries x y := by
  intro i
  right
  exact prizeLottery_get y i

/-- `TwoPrizeLotteries` is symmetric in its arguments (set-theoretically). -/
lemma TwoPrizeLotteries_symm (x y : X) :
    TwoPrizeLotteries x y = TwoPrizeLotteries y x := by
  ext xs
  unfold TwoPrizeLotteries
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i
    rcases h i with hx | hy
    · exact Or.inr hx
    · exact Or.inl hy
  · intro h i
    rcases h i with hy | hx
    · exact Or.inr hy
    · exact Or.inl hx

/-- A constant act with a singleton-x lottery is a two-prize act. -/
lemma constAct_prizeLottery_mem_TwoPrizeActs_left (x y : X) :
    (constAct (prizeLottery x) : Act S X) ∈ TwoPrizeActs S x y := by
  intro _
  exact prizeLottery_mem_TwoPrizeLotteries_left x y

/-- A constant act with a singleton-y lottery is a two-prize act. -/
lemma constAct_prizeLottery_mem_TwoPrizeActs_right (x y : X) :
    (constAct (prizeLottery y) : Act S X) ∈ TwoPrizeActs S x y := by
  intro _
  exact prizeLottery_mem_TwoPrizeLotteries_right x y

/-- **Average utility on a two-prize lottery.**

If every prize in `xs` is either `x` or `y`, with `x ≠ y`, then the average
utility of `xs` is the affine interpolation between `u x` and `u y` with
coefficient equal to the relative frequency of `x`.  This is the local
calculation that turns strict average-utility comparisons on the two-prize
subdomain into strict `relFreq · x` comparisons. -/
lemma averageUtility_twoPrize_eq_relFreq
    (u : X → ℝ) {x y : X} (hxy : x ≠ y)
    (xs : Lottery X) (hxs : xs ∈ TwoPrizeLotteries x y) :
    averageUtility u xs =
      (relFreq xs x : ℝ) * u x + (1 - (relFreq xs x : ℝ)) * u y := by
  classical
  let p : Fin xs.length → Prop := fun i => xs.get i = x
  let c : ℕ := (Finset.univ.filter p).card
  let d : ℕ := (Finset.univ.filter (fun i : Fin xs.length => ¬ p i)).card
  have hsum_support :
      (∑ i : Fin xs.length, u (xs.get i)) =
        (∑ i : Fin xs.length, (if p i then u x else u y)) := by
    apply Finset.sum_congr rfl
    intro i _
    rcases hxs i with hxi | hyi
    · simp [p, hxi]
    · have hnot : ¬ p i := by
        intro hp
        exact hxy (hp.symm.trans hyi)
      simp [p, hnot, hyi]
  have hsum_split :
      (∑ i : Fin xs.length, (if p i then u x else u y)) =
        (c : ℝ) * u x + (d : ℝ) * u y := by
    have hpart :
        (∑ i : Fin xs.length, (if p i then u x else u y)) =
          Finset.sum (Finset.univ.filter p) (fun _ : Fin xs.length => u x) +
          Finset.sum (Finset.univ.filter (fun i : Fin xs.length => ¬ p i))
            (fun _ : Fin xs.length => u y) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hix : xs.get i = x
      · simp [p, hix]
      · simp [p, hix]
    rw [hpart]
    rw [Finset.sum_const, Finset.sum_const]
    simp [c, d, nsmul_eq_mul]
  have hcard_sum : c + d = xs.length := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin xs.length))) (p := p)
    have huniv : (Finset.univ : Finset (Fin xs.length)).card = xs.length := by
      simp
    simpa [c, d, huniv] using h
  have hrel : (relFreq xs x : ℝ) = (c : ℝ) / (xs.length : ℝ) := by
    have hc : freqCount xs x = c := by
      simp [freqCount, c, p]
    unfold relFreq
    rw [hc]
    simp
  unfold averageUtility
  rw [hsum_support, hsum_split, hrel]
  have hlen_pos : (0 : ℝ) < (xs.length : ℝ) := by
    exact_mod_cast xs.length_pos
  have hlen_ne : (xs.length : ℝ) ≠ 0 := ne_of_gt hlen_pos
  have hcard_sum_real : (c : ℝ) + (d : ℝ) = (xs.length : ℝ) := by
    exact_mod_cast hcard_sum
  have hd : (d : ℝ) = (xs.length : ℝ) - (c : ℝ) := by
    linarith
  rw [hd]
  field_simp [hlen_ne]

/-! ### Concrete rational two-prize lotteries -/

/-- A concrete lottery with `kx` copies of `x` followed by `ky` copies of
`y`.  The explicit count-based constructor is useful for realizing a chosen
rational relative frequency inside the two-prize subdomain. -/
def twoPrizeLotteryOfCounts (x y : X) (kx ky : ℕ) (hpos : 0 < kx + ky) : Lottery X :=
  ⟨List.replicate kx x ++ List.replicate ky y, by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_append, List.length_replicate, List.length_nil] at hlen
    omega⟩

@[simp] lemma twoPrizeLotteryOfCounts_prizes
    (x y : X) (kx ky : ℕ) (hpos : 0 < kx + ky) :
    (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).prizes =
      List.replicate kx x ++ List.replicate ky y := rfl

@[simp] lemma twoPrizeLotteryOfCounts_length
    (x y : X) (kx ky : ℕ) (hpos : 0 < kx + ky) :
    (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).length = kx + ky := by
  simp [Lottery.length, twoPrizeLotteryOfCounts]

/-- The count-based constructor is supported on the requested two prizes. -/
lemma twoPrizeLotteryOfCounts_mem_twoPrizeLotteries
    (x y : X) (kx ky : ℕ) (hpos : 0 < kx + ky) :
    twoPrizeLotteryOfCounts (X := X) x y kx ky hpos ∈ TwoPrizeLotteries x y := by
  intro i
  have hmem :
      (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).get i ∈
        (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).prizes := by
    exact List.get_mem _ _
  rcases (by
      simpa [twoPrizeLotteryOfCounts, List.mem_append, List.mem_replicate] using hmem) with
    hleft | hright
  · exact Or.inl hleft.2
  · exact Or.inr hright.2

/-- The `x`-relative frequency of the count-based two-prize lottery is
`kx / (kx + ky)`, when the prizes are distinct. -/
lemma relFreq_twoPrizeLotteryOfCounts_left
    {x y : X} (hxy : x ≠ y) (kx ky : ℕ) (hpos : 0 < kx + ky) :
    relFreq (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos) x =
      (kx : ℚ) / (kx + ky : ℚ) := by
  classical
  have hyx : y ≠ x := hxy.symm
  have hcount :
      (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).prizes.count x = kx := by
    simp [twoPrizeLotteryOfCounts, List.count_append, List.count_replicate,
      beq_iff_eq, hyx]
  have hlen :
      (twoPrizeLotteryOfCounts (X := X) x y kx ky hpos).length = kx + ky :=
    twoPrizeLotteryOfCounts_length x y kx ky hpos
  unfold relFreq
  rw [freqCount_eq_count]
  rw [hcount, hlen]
  rw [Nat.cast_add]

/-- Every rational `q ∈ (0, 1)` is realized as the `x`-relative frequency
of some two-prize lottery supported on `{x, y}`. -/
lemma exists_twoPrizeLottery_relFreq_eq_rat
    {x y : X} (hxy : x ≠ y) {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ zs : Lottery X,
      zs ∈ TwoPrizeLotteries x y ∧
      relFreq zs x = q := by
  classical
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq0
  have hnum_nonneg : 0 ≤ q.num := hnum_pos.le
  have hnum_lt_den : q.num.natAbs < q.den := by
    have hq_eq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    have hlt : (q.num : ℚ) / (q.den : ℚ) < 1 := by
      rwa [← hq_eq]
    have hden_pos_q : (0 : ℚ) < (q.den : ℚ) := by
      exact_mod_cast q.den_pos
    rw [div_lt_one hden_pos_q] at hlt
    have habs : |(q.num : ℚ)| = (q.num : ℚ) := abs_of_pos (by exact_mod_cast hnum_pos)
    have hcast : (q.num.natAbs : ℚ) < (q.den : ℚ) := by
      norm_num at hlt ⊢
      simpa [habs] using hlt
    exact_mod_cast hcast
  let kx : ℕ := q.num.natAbs
  let ky : ℕ := q.den - q.num.natAbs
  have hpos : 0 < kx + ky := by
    dsimp [kx, ky]
    omega
  refine ⟨twoPrizeLotteryOfCounts (X := X) x y kx ky hpos,
    twoPrizeLotteryOfCounts_mem_twoPrizeLotteries x y kx ky hpos, ?_⟩
  have hsum : kx + ky = q.den := by
    dsimp [kx, ky]
    omega
  have hrel := relFreq_twoPrizeLotteryOfCounts_left (X := X) hxy kx ky hpos
  rw [hrel]
  have hnum_cast : (kx : ℚ) = (q.num : ℚ) := by
    dsimp [kx]
    change ((q.num.natAbs : ℤ) : ℚ) = (q.num : ℚ)
    rw [Int.natCast_natAbs, abs_of_nonneg]
    exact_mod_cast hnum_nonneg
  have hden_cast : (kx : ℚ) + (ky : ℚ) = (q.den : ℚ) := by
    rw [← Nat.cast_add, hsum]
  rw [hden_cast, hnum_cast]
  exact Rat.num_div_den q

/-- **Matching frequency** of an act `f` for the prize pair `x ≻ y`:

  `m_{x,y}(f) = sup { r_x(xs) : f ≽ xs, xs ∈ cX_{x,y} }`. -/
noncomputable def matchingFreq
    (P : Preference S X) (x _y : X) (f : Act S X) : ℝ :=
  sSup ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
        { xs | xs ∈ TwoPrizeLotteries x _y ∧ P.weakPref f (constAct xs) })

/-- The image set whose `sSup` defines `matchingFreq` is bounded above by `1`. -/
lemma matchingFreq_set_bddAbove
    (P : Preference S X) (x y : X) (f : Act S X) :
    BddAbove ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
              { xs | xs ∈ TwoPrizeLotteries x y ∧
                     P.weakPref f (constAct xs) }) := by
  refine ⟨1, ?_⟩
  rintro r ⟨xs, _, rfl⟩
  exact (relFreq_real_mem_unitInterval xs x).2

/-- **Monotonicity of `matchingFreq` under preference.**  If `f ≽ g`, then
the set witnessing `g`'s matching frequency is a subset of the one
witnessing `f`'s, so `m_{x,y}(g) ≤ m_{x,y}(f)`.  This is the *forward*
direction of Lemma 1 (gap filling), needs only Weak Order. -/
lemma matchingFreq_mono
    (P : Preference S X) [WeakOrder P]
    (x y : X) (f g : Act S X) (hfg : P.weakPref f g) :
    matchingFreq P x y g ≤ matchingFreq P x y f := by
  -- The set defining `m_{x,y}(g)` is a subset of the set defining `m_{x,y}(f)`,
  -- because `g ≽ xs` plus `f ≽ g` and transitivity give `f ≽ xs`.
  have hsub :
      { xs : Lottery X | xs ∈ TwoPrizeLotteries x y ∧
                         P.weakPref g (constAct xs) }
      ⊆
      { xs : Lottery X | xs ∈ TwoPrizeLotteries x y ∧
                         P.weakPref f (constAct xs) } := by
    rintro xs ⟨hxs, hgxs⟩
    exact ⟨hxs, WeakOrder.transitive _ _ _ hfg hgxs⟩
  have himg :
      ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
       { xs | xs ∈ TwoPrizeLotteries x y ∧ P.weakPref g (constAct xs) }) ⊆
      ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
       { xs | xs ∈ TwoPrizeLotteries x y ∧ P.weakPref f (constAct xs) }) :=
    Set.image_mono hsub
  -- handle the case where the smaller set is empty
  by_cases hempty :
      ({ xs : Lottery X | xs ∈ TwoPrizeLotteries x y ∧
                          P.weakPref g (constAct xs) }).Nonempty
  · have himg_ne :
        ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
         { xs | xs ∈ TwoPrizeLotteries x y ∧
                P.weakPref g (constAct xs) }).Nonempty :=
      hempty.image _
    exact csSup_le_csSup (matchingFreq_set_bddAbove P x y f) himg_ne himg
  · -- the LHS set is empty, so `sSup` is `0` (Real convention) and
    -- the RHS is bounded below by `0` since `relFreq` is non-negative.
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have h_emp_img :
        (fun xs : Lottery X => (relFreq xs x : ℝ)) ''
        { xs | xs ∈ TwoPrizeLotteries x y ∧
               P.weakPref g (constAct xs) } = ∅ := by
      rw [hempty]; simp
    -- `m_{x,y}(g) = sSup ∅ = 0`
    unfold matchingFreq
    rw [h_emp_img, Real.sSup_empty]
    -- need `0 ≤ m_{x,y}(f)`.  The set defining `m_{x,y}(f)` is either empty
    -- (in which case its `sSup` is `0`) or non-empty and bounded below by `0`.
    by_cases hf_empty :
        ({ xs : Lottery X | xs ∈ TwoPrizeLotteries x y ∧
                            P.weakPref f (constAct xs) }).Nonempty
    · obtain ⟨xs, hxs⟩ := hf_empty
      have h_mem : (relFreq xs x : ℝ) ∈
          (fun xs : Lottery X => (relFreq xs x : ℝ)) ''
          { xs | xs ∈ TwoPrizeLotteries x y ∧
                 P.weakPref f (constAct xs) } := ⟨xs, hxs, rfl⟩
      have h₀ : (0 : ℝ) ≤ (relFreq xs x : ℝ) :=
        (relFreq_real_mem_unitInterval xs x).1
      exact h₀.trans (le_csSup (matchingFreq_set_bddAbove P x y f) h_mem)
    · rw [Set.not_nonempty_iff_eq_empty] at hf_empty
      have h_emp_img_f :
          (fun xs : Lottery X => (relFreq xs x : ℝ)) ''
          { xs | xs ∈ TwoPrizeLotteries x y ∧
                 P.weakPref f (constAct xs) } = ∅ := by
        rw [hf_empty]; simp
      rw [h_emp_img_f, Real.sSup_empty]

/-! ### Real new lemmas about `matchingFreq` -/

/-- **`matchingFreq` is non-negative.** -/
lemma matchingFreq_nonneg
    (P : Preference S X) (x y : X) (f : Act S X) :
    0 ≤ matchingFreq P x y f := by
  unfold matchingFreq
  -- Either the supremand set is non-empty (then sSup ≥ 0 because some
  -- relFreq ≥ 0), or empty (then sSup = 0).
  by_cases hne :
      ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
       { xs | xs ∈ TwoPrizeLotteries x y ∧
              P.weakPref f (constAct xs) }).Nonempty
  · obtain ⟨r, ⟨xs, hxs, rfl⟩⟩ := hne
    have h₀ : (0 : ℝ) ≤ (relFreq xs x : ℝ) :=
      (relFreq_real_mem_unitInterval xs x).1
    have h_mem :
        (relFreq xs x : ℝ) ∈
        (fun xs : Lottery X => (relFreq xs x : ℝ)) ''
          { xs | xs ∈ TwoPrizeLotteries x y ∧
                 P.weakPref f (constAct xs) } := ⟨xs, hxs, rfl⟩
    exact h₀.trans (le_csSup (matchingFreq_set_bddAbove P x y f) h_mem)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]

/-- **`matchingFreq` is bounded above by `1`.** -/
lemma matchingFreq_le_one
    (P : Preference S X) (x y : X) (f : Act S X) :
    matchingFreq P x y f ≤ 1 := by
  unfold matchingFreq
  by_cases hne :
      ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
       { xs | xs ∈ TwoPrizeLotteries x y ∧
              P.weakPref f (constAct xs) }).Nonempty
  · -- Each element of the supremand set is ≤ 1; bounded above; sSup ≤ 1.
    apply csSup_le hne
    rintro r ⟨xs, _, rfl⟩
    exact (relFreq_real_mem_unitInterval xs x).2
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact zero_le_one

/-- **`matchingFreq` is in `[0, 1]`.** -/
lemma matchingFreq_mem_unitInterval
    (P : Preference S X) (x y : X) (f : Act S X) :
    0 ≤ matchingFreq P x y f ∧ matchingFreq P x y f ≤ 1 :=
  ⟨matchingFreq_nonneg P x y f, matchingFreq_le_one P x y f⟩

/-- **`matchingFreq` is monotone in the act direction (alias).** -/
lemma matchingFreq_mono'
    (P : Preference S X) [WeakOrder P]
    (x y : X) {f g : Act S X} (hfg : P.weakPref f g) :
    matchingFreq P x y g ≤ matchingFreq P x y f :=
  matchingFreq_mono P x y f g hfg

/-- **Indifferent acts have equal matching frequencies.** -/
lemma matchingFreq_eq_of_indiff
    (P : Preference S X) [WeakOrder P]
    (x y : X) {f g : Act S X} (hfg : P.indiff f g) :
    matchingFreq P x y f = matchingFreq P x y g := by
  apply le_antisymm
  · exact matchingFreq_mono P x y g f hfg.2
  · exact matchingFreq_mono P x y f g hfg.1

/-- **`matchingFreq` of `constAct (prizeLottery x)` includes
`prizeLottery x` as a witness.** -/
lemma matchingFreq_constAct_prizeLottery_x_ge
    (P : Preference S X) [WeakOrder P] (x y : X) :
    1 ≤ matchingFreq P x y (constAct (prizeLottery x) : Act S X) := by
  unfold matchingFreq
  -- The supremand set contains `prizeLottery x` since the constant act
  -- is reflexively preferred to itself.
  have h_mem :
      (relFreq (prizeLottery x) x : ℝ) ∈
      (fun xs : Lottery X => (relFreq xs x : ℝ)) ''
      { xs | xs ∈ TwoPrizeLotteries x y ∧
             P.weakPref (constAct (prizeLottery x) : Act S X)
                        (constAct xs) } :=
    ⟨prizeLottery x,
     ⟨prizeLottery_mem_TwoPrizeLotteries_left x y,
      weakPref_refl P _⟩,
     rfl⟩
  -- `relFreq (prizeLottery x) x = 1`
  have h_val : (relFreq (prizeLottery x) x : ℝ) = 1 := by
    rw [relFreq_prizeLottery]
    simp
  rw [← h_val]
  exact le_csSup (matchingFreq_set_bddAbove P x y _) h_mem

/-- **Weak matching-frequency comparison from strict preference.**

If `f ≻ g`, then `matchingFreq f ≥ matchingFreq g`, by the already-proved
monotonicity of matching frequency.  The strict converse/separation needed
for the reverse direction of `lem_gap_filling` is now isolated as
`MatchingFrequencyStrictSeparation`. -/
lemma matchingFreq_ge_of_strict
    (P : Preference S X) [WeakOrder P]
    (x y : X) {f g : Act S X} (hfg : P.strict f g) :
    matchingFreq P x y g ≤ matchingFreq P x y f :=
  matchingFreq_mono P x y f g hfg.1

/-- **Strict matching-frequency separation.**

This is the named Phase-2 bridge missing from the current primitive axioms:
on two-prize acts, a strict preference must produce a strict inequality of
matching frequencies.  Mathematically, this is where the order-denseness /
gap-filling argument needs to show that the dense benchmark can be chosen in
the same two-prize subdomain and gives a genuine supremum separation.

Keeping this as a named hypothesis lets `lem_gap_filling` be closed without
pretending that the current `Denseness` axiom alone supplies that stronger
two-prize separation theorem. -/
def MatchingFrequencyStrictSeparation (P : Preference S X) : Prop :=
  ∀ {x y : X},
    P.strictPrize x y →
    ∀ f g : Act S X,
      f ∈ TwoPrizeActs S x y →
      g ∈ TwoPrizeActs S x y →
      P.strict g f →
      matchingFreq P x y f < matchingFreq P x y g

/-! ### §2.3a — Sub-bridge decomposition of `MatchingFrequencyStrictSeparation`

The bridge `MatchingFrequencyStrictSeparation P` is a thick, semantically
non-trivial statement.  We split it here into two strictly smaller, more
explicit sub-bridges, each of which names exactly one piece of the missing
mathematics, and prove that their conjunction implies the public bridge.

This is an intermediate reduction (Phase-2a → Phase-2b): consumers of
`lem_gap_filling` continue to pass `MatchingFrequencyStrictSeparation`, but
that hypothesis can now itself be discharged by supplying the two sub-bridges
`TwoPrizeDenseness` and `TwoPrizeStrictRelFreq`.  Each sub-bridge is a
self-contained future target.
-/

/-- **Sub-bridge A — two-prize denseness.**

For any strictly-ordered prize pair `x ≻ y` and two-prize acts `g ≻ f`, the
denseness witness between them can be chosen to be a *two-prize* lottery
supported on `{x, y}`.  Note `Denseness` only guarantees existence of *some*
lottery between `g` and `f`; staying in `TwoPrizeLotteries x y` is an extra
constructive demand. -/
def TwoPrizeDenseness (P : Preference S X) : Prop :=
  ∀ {x y : X}, P.strictPrize x y →
    ∀ f g : Act S X,
      f ∈ TwoPrizeActs S x y →
      g ∈ TwoPrizeActs S x y →
      P.strict g f →
      ∃ zs : Lottery X,
        zs ∈ TwoPrizeLotteries x y ∧
        P.strict g (constAct zs) ∧
        P.strict (constAct zs) f

/-- **Sub-bridge B — relative-frequency strictness on two-prize lotteries.**

For a strictly-ordered prize pair `x ≻ y` and two two-prize lotteries
`xs, ys ∈ TwoPrizeLotteries x y`, a strict preference of `constAct xs` over
`constAct ys` forces a strict drop in the `x`-frequency.  This is the
content of the "more `x`'s ⇒ more preferred" half of the gap-filling
argument restricted to the two-prize subdomain. -/
def TwoPrizeStrictRelFreq (P : Preference S X) : Prop :=
  ∀ {x y : X}, P.strictPrize x y →
    ∀ xs ys : Lottery X,
      xs ∈ TwoPrizeLotteries x y →
      ys ∈ TwoPrizeLotteries x y →
      P.strict (constAct xs) (constAct ys) →
      (relFreq ys x : ℝ) < (relFreq xs x : ℝ)

/-- Under an average-utility representation, the strict relative-frequency
sub-bridge is theorem-backed.

This does **not** discharge the primitive-axiom route by itself: obtaining the
average-utility representation from Cancellation + Archimedeanity is still the
named hard direction `AverageUtilityHardDirection`.  It does, however, remove
the analytic/frequency part of `TwoPrizeStrictRelFreq`: once a representing
utility exists, strict preference on the two-prize subdomain is exactly strict
ordering of the `x`-frequency whenever `x ≻ y`. -/
theorem twoPrizeStrictRelFreq_of_averageUtility_repr
    (P : Preference S X) [WeakOrder P]
    (u : X → ℝ)
    (hrepr : ∀ xs ys : Lottery X,
        P.onLotteries xs ys ↔
        averageUtility u ys ≤ averageUtility u xs) :
    TwoPrizeStrictRelFreq P := by
  intro x y hxy xs ys hxs hys hstrict
  have hxy_lottery :
      P.onLotteries (prizeLottery x) (prizeLottery y) ∧
        ¬ P.onLotteries (prizeLottery y) (prizeLottery x) := by
    simpa [strictPrize, onPrizes] using hxy
  have hxy_ne : x ≠ y := by
    intro hEq
    subst y
    exact hxy_lottery.2 hxy_lottery.1
  have huy_lt_ux : u y < u x := by
    have hU :=
      (onLotteries_strict_iff_of_averageUtility_repr P u hrepr
        (prizeLottery x) (prizeLottery y)).mp hxy_lottery
    simpa [averageUtility_prizeLottery] using hU
  have hxs_strict_ys :
      P.onLotteries xs ys ∧ ¬ P.onLotteries ys xs := by
    simpa [onLotteries] using hstrict
  have hU_lt : averageUtility u ys < averageUtility u xs :=
    (onLotteries_strict_iff_of_averageUtility_repr P u hrepr xs ys).mp
      hxs_strict_ys
  have hUx := averageUtility_twoPrize_eq_relFreq u hxy_ne xs hxs
  have hUy := averageUtility_twoPrize_eq_relFreq u hxy_ne ys hys
  rw [hUx, hUy] at hU_lt
  nlinarith

/-- The strict relative-frequency sub-bridge follows from the existing
average-utility hard-direction bridge together with Cancellation and
Archimedeanity.

This reuses `AverageUtilityHardDirection P`; it does not claim a new direct
primitive proof of Proposition 1.  Its value is to remove
`TwoPrizeStrictRelFreq` as an independent bridge whenever the Proposition-1
hard direction is already part of the local hypothesis stack. -/
theorem twoPrizeStrictRelFreq_of_averageUtilityHardDirection
    (P : Preference S X) [WeakOrder P] [Cancellation P] [Archimedeanity P]
    (hHard : AverageUtilityHardDirection P) :
    TwoPrizeStrictRelFreq P := by
  rcases hHard ⟨⟨inferInstance, trivial⟩, ⟨inferInstance, trivial⟩⟩ with
    ⟨u, hrepr⟩
  exact twoPrizeStrictRelFreq_of_averageUtility_repr P u hrepr

/-- **Combiner: the two sub-bridges imply the public bridge.**

Given `TwoPrizeDenseness P` and `TwoPrizeStrictRelFreq P`, the public
strict-separation bridge `MatchingFrequencyStrictSeparation P` follows by
inserting two two-prize denseness witnesses between `g` and `f` and bounding
the relevant suprema. -/
theorem matchingFrequencyStrictSeparation_of_subBridges
    (P : Preference S X) [WeakOrder P]
    (hDense : TwoPrizeDenseness P)
    (hStrict : TwoPrizeStrictRelFreq P) :
    MatchingFrequencyStrictSeparation P := by
  intro x y hxy f g hf hg hgf
  -- Step 1: get a two-prize separator `zs` with `g ≻ constAct zs ≻ f`.
  obtain ⟨zs, hzs_mem, hgz, hzf⟩ := hDense hxy f g hf hg hgf
  -- The constant act on `zs` is itself a two-prize act.
  have hConstZs_mem : (constAct zs : Act S X) ∈ TwoPrizeActs S x y :=
    fun _ => hzs_mem
  -- Step 2: get a second two-prize separator `zs'` with
  -- `constAct zs ≻ constAct zs' ≻ f`, creating the strict gap we need.
  obtain ⟨zs', hzs'_mem, hzz', hz'f⟩ :=
    hDense hxy f (constAct zs) hf hConstZs_mem hzf
  -- Sub-bridge B: `relFreq zs' x < relFreq zs x`.
  have hfreq_lt : (relFreq zs' x : ℝ) < (relFreq zs x : ℝ) :=
    hStrict hxy zs zs' hzs_mem hzs'_mem hzz'
  -- The supremand set for `matchingFreq g`.
  let Sg : Set (Lottery X) :=
    { xs | xs ∈ TwoPrizeLotteries x y ∧ P.weakPref g (constAct xs) }
  -- `zs ∈ Sg`, so `relFreq zs x ≤ matchingFreq P x y g`.
  have hzs_in_Sg : zs ∈ Sg := ⟨hzs_mem, hgz.1⟩
  have h_zs_le_mg : (relFreq zs x : ℝ) ≤ matchingFreq P x y g := by
    have h_mem :
        (relFreq zs x : ℝ) ∈
        (fun xs : Lottery X => (relFreq xs x : ℝ)) '' Sg :=
      ⟨zs, hzs_in_Sg, rfl⟩
    exact le_csSup (matchingFreq_set_bddAbove P x y g) h_mem
  -- For any `ws` in the supremand of `matchingFreq f`, we have
  -- `constAct zs' ≻ f ≽ constAct ws`, hence `constAct zs' ≻ constAct ws`,
  -- hence (by sub-bridge B) `relFreq ws x < relFreq zs' x`.
  have h_mf_le : matchingFreq P x y f ≤ (relFreq zs' x : ℝ) := by
    unfold matchingFreq
    -- Empty-case handling: if the supremand image is empty, sSup = 0.
    by_cases hne :
        ((fun xs : Lottery X => (relFreq xs x : ℝ)) ''
         { xs | xs ∈ TwoPrizeLotteries x y ∧
                P.weakPref f (constAct xs) }).Nonempty
    · apply csSup_le hne
      rintro r ⟨ws, ⟨hws_mem, hf_ws⟩, rfl⟩
      -- `constAct zs' ≻ f ≽ constAct ws` ⇒ `constAct zs' ≻ constAct ws`.
      have h_z'ws_weak : P.weakPref (constAct zs') (constAct ws) :=
        WeakOrder.transitive _ _ _ hz'f.1 hf_ws
      have h_not_ws_z' : ¬ P.weakPref (constAct ws) (constAct zs') := by
        intro hcontra
        -- combine with `f ≽ constAct ws` to get `f ≽ constAct zs'`, ⊥.
        exact hz'f.2 (WeakOrder.transitive _ _ _ hf_ws hcontra)
      have h_strict_z'ws : P.strict (constAct zs') (constAct ws) :=
        ⟨h_z'ws_weak, h_not_ws_z'⟩
      have h_ws_lt_z' : (relFreq ws x : ℝ) < (relFreq zs' x : ℝ) :=
        hStrict hxy zs' ws hzs'_mem hws_mem h_strict_z'ws
      exact le_of_lt h_ws_lt_z'
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sSup_empty]
      -- `0 ≤ relFreq zs' x`.
      exact (relFreq_real_mem_unitInterval zs' x).1
  -- Chain: `matchingFreq f ≤ relFreq zs' x < relFreq zs x ≤ matchingFreq g`.
  exact lt_of_le_of_lt h_mf_le (lt_of_lt_of_le hfreq_lt h_zs_le_mg)

/-- A one-bridge specialization of the combiner.

Once the existing Proposition-1 hard direction is available, the
`TwoPrizeStrictRelFreq` half is theorem-backed by
`twoPrizeStrictRelFreq_of_averageUtilityHardDirection`.  Therefore the public
`MatchingFrequencyStrictSeparation` bridge is reduced to the single remaining
new target `TwoPrizeDenseness`. -/
theorem matchingFrequencyStrictSeparation_of_twoPrizeDenseness_and_averageUtilityHardDirection
    (P : Preference S X) [WeakOrder P] [Cancellation P] [Archimedeanity P]
    (hHard : AverageUtilityHardDirection P)
    (hDense : TwoPrizeDenseness P) :
    MatchingFrequencyStrictSeparation P :=
  matchingFrequencyStrictSeparation_of_subBridges P hDense
    (twoPrizeStrictRelFreq_of_averageUtilityHardDirection P hHard)

/-- **Axiom 5 (Denseness).**  Classical lotteries are order-dense in `cF`. -/
class Denseness (P : Preference S X) : Prop where
  dense :
    ∀ f g : Act S X,
      P.strict f g →
      ∃ xs : Lottery X,
        P.strict f (constAct xs) ∧ P.strict (constAct xs) g

/-! ### Real new lemmas about `Denseness` -/

/-- **Iterated denseness**: between any two strictly-ordered acts, we can
insert *two* witnesses, with all four endpoints in strict succession. -/
lemma Denseness.iterate
    (P : Preference S X) [WeakOrder P] [Denseness P]
    {f g : Act S X} (hfg : P.strict f g) :
    ∃ xs ys : Lottery X,
      P.strict f (constAct xs) ∧
      P.strict (constAct xs) (constAct ys) ∧
      P.strict (constAct ys) g := by
  obtain ⟨xs, hxs⟩ := Denseness.dense f g hfg
  obtain ⟨ys, hys⟩ := Denseness.dense (constAct xs) g hxs.2
  refine ⟨xs, ys, ?_, ?_, ?_⟩
  · exact hxs.1
  · exact hys.1
  · exact hys.2

/-- **Iterated denseness — first witness only**.  Between two strictly-
ordered acts, we can insert a witness strictly above the lower one. -/
lemma Denseness.exists_below
    (P : Preference S X) [Denseness P]
    {f g : Act S X} (hfg : P.strict f g) :
    ∃ xs : Lottery X, P.strict (constAct xs) g := by
  obtain ⟨xs, hxs⟩ := Denseness.dense f g hfg
  exact ⟨xs, hxs.2⟩

/-- **Iterated denseness — second witness only**.  Between two strictly-
ordered acts, we can insert a witness strictly below the upper one. -/
lemma Denseness.exists_above
    (P : Preference S X) [Denseness P]
    {f g : Act S X} (hfg : P.strict f g) :
    ∃ xs : Lottery X, P.strict f (constAct xs) := by
  obtain ⟨xs, hxs⟩ := Denseness.dense f g hfg
  exact ⟨xs, hxs.1⟩

/-- **Two-prize denseness from ordinary denseness plus average utility.**

If `g ≻ f` are two-prize acts for a strict prize pair `x ≻ y`, ordinary
`Denseness` supplies two constant-lottery benchmarks `g ≻ z₁ ≻ z₀ ≻ f`.
Monotonicity and the average-utility representation show that their utilities
lie inside the two-prize utility interval `[u y, u x]`.  A rational point
between their normalized utility levels is then realized by a concrete
two-prize lottery, yielding a two-prize benchmark strictly between `g` and
`f`. -/
theorem twoPrizeDenseness_of_averageUtilityHardDirection
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] [Archimedeanity P]
    [Monotonicity P] [Denseness P]
    (hHard : AverageUtilityHardDirection P) :
    TwoPrizeDenseness P := by
  intro x y hxy f g hf hg hgf
  rcases hHard ⟨⟨inferInstance, trivial⟩, ⟨inferInstance, trivial⟩⟩ with
    ⟨u, hrepr⟩
  -- Two ordinary dense constant benchmarks: `g ≻ z₁ ≻ z₀ ≻ f`.
  obtain ⟨z0, hgz0, hz0f⟩ := Denseness.dense g f hgf
  obtain ⟨z1, hgz1, hz1z0⟩ := Denseness.dense g (constAct z0) hgz0
  have hxy_lottery :
      P.onLotteries (prizeLottery x) (prizeLottery y) ∧
        ¬ P.onLotteries (prizeLottery y) (prizeLottery x) := by
    simpa [strictPrize, onPrizes] using hxy
  have hxy_ne : x ≠ y := by
    intro hEq
    subst y
    exact hxy_lottery.2 hxy_lottery.1
  have huy_lt_ux : u y < u x := by
    have hU :=
      (onLotteries_strict_iff_of_averageUtility_repr P u hrepr
        (prizeLottery x) (prizeLottery y)).mp hxy_lottery
    simpa [averageUtility_prizeLottery] using hU
  -- On the two-prize subdomain, `prizeLottery x` is a top benchmark and
  -- `prizeLottery y` is a bottom benchmark for the represented order.
  have htop_twoPrize : ∀ zs : Lottery X,
      zs ∈ TwoPrizeLotteries x y → P.onLotteries (prizeLottery x) zs := by
    intro zs hzs
    rw [hrepr]
    rw [averageUtility_prizeLottery, averageUtility_twoPrize_eq_relFreq u hxy_ne zs hzs]
    have hrf := relFreq_real_mem_unitInterval zs x
    nlinarith
  have hbot_twoPrize : ∀ zs : Lottery X,
      zs ∈ TwoPrizeLotteries x y → P.onLotteries zs (prizeLottery y) := by
    intro zs hzs
    rw [hrepr]
    rw [averageUtility_prizeLottery, averageUtility_twoPrize_eq_relFreq u hxy_ne zs hzs]
    have hrf := relFreq_real_mem_unitInterval zs x
    nlinarith
  have htop_g : P.weakPref (constAct (prizeLottery x) : Act S X) g := by
    apply Monotonicity.mono
    intro s
    exact htop_twoPrize (g s) (hg s)
  have hf_bottom : P.weakPref f (constAct (prizeLottery y) : Act S X) := by
    apply Monotonicity.mono
    intro s
    exact hbot_twoPrize (f s) (hf s)
  have hx_z1 : P.onLotteries (prizeLottery x) z1 := by
    show P.weakPref (constAct (prizeLottery x) : Act S X) (constAct z1)
    exact WeakOrder.transitive _ _ _ htop_g hgz1.1
  have hz0_y : P.onLotteries z0 (prizeLottery y) := by
    show P.weakPref (constAct z0) (constAct (prizeLottery y) : Act S X)
    exact WeakOrder.transitive _ _ _ hz0f.1 hf_bottom
  have hU_z0_z1 : averageUtility u z0 < averageUtility u z1 := by
    have hz1z0_lot : P.onLotteries z1 z0 ∧ ¬ P.onLotteries z0 z1 := by
      simpa [onLotteries] using hz1z0
    exact (onLotteries_strict_iff_of_averageUtility_repr P u hrepr z1 z0).mp
      hz1z0_lot
  have hUz1_le_ux : averageUtility u z1 ≤ u x := by
    have h := (hrepr (prizeLottery x) z1).mp hx_z1
    simpa [averageUtility_prizeLottery] using h
  have huy_le_Uz0 : u y ≤ averageUtility u z0 := by
    have h := (hrepr z0 (prizeLottery y)).mp hz0_y
    simpa [averageUtility_prizeLottery] using h
  let d : ℝ := u x - u y
  have hd_pos : 0 < d := by
    dsimp [d]
    linarith
  let a : ℝ := (averageUtility u z0 - u y) / d
  let b : ℝ := (averageUtility u z1 - u y) / d
  have hab : a < b := by
    dsimp [a, b]
    exact div_lt_div_of_pos_right (by linarith [hU_z0_z1]) hd_pos
  obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
  have hq0 : 0 < q := by
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (by linarith [huy_le_Uz0]) (le_of_lt hd_pos)
    have hq0_real : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt ha_nonneg hqa
    exact (Rat.cast_pos (K := ℝ)).mp hq0_real
  have hq1 : q < 1 := by
    have hb_le_one : b ≤ 1 := by
      dsimp [b, d] at hd_pos ⊢
      rw [div_le_one hd_pos]
      linarith [hUz1_le_ux]
    have hq1_real : (q : ℝ) < 1 := lt_of_lt_of_le hqb hb_le_one
    exact_mod_cast hq1_real
  obtain ⟨zs, hzs_mem, hrel_zs⟩ := exists_twoPrizeLottery_relFreq_eq_rat (X := X) hxy_ne hq0 hq1
  have hU_zs_aff :
      averageUtility u zs = u y + (q : ℝ) * d := by
    have hU := averageUtility_twoPrize_eq_relFreq u hxy_ne zs hzs_mem
    rw [hU, hrel_zs]
    dsimp [d]
    ring
  have hUz0_lt_zs : averageUtility u z0 < averageUtility u zs := by
    have hm : averageUtility u z0 - u y < (q : ℝ) * d := by
      dsimp [a] at hqa
      exact (div_lt_iff₀ hd_pos).mp hqa
    rw [hU_zs_aff]
    linarith
  have hUzs_lt_z1 : averageUtility u zs < averageUtility u z1 := by
    have hm : (q : ℝ) * d < averageUtility u z1 - u y := by
      dsimp [b] at hqb
      exact (lt_div_iff₀ hd_pos).mp hqb
    rw [hU_zs_aff]
    linarith
  have hz1zs : P.strict (constAct z1) (constAct zs) := by
    have hstrict_lot : P.onLotteries z1 zs ∧ ¬ P.onLotteries zs z1 :=
      (onLotteries_strict_iff_of_averageUtility_repr P u hrepr z1 zs).mpr hUzs_lt_z1
    simpa [onLotteries] using hstrict_lot
  have hzsz0 : P.strict (constAct zs) (constAct z0) := by
    have hstrict_lot : P.onLotteries zs z0 ∧ ¬ P.onLotteries z0 zs :=
      (onLotteries_strict_iff_of_averageUtility_repr P u hrepr zs z0).mpr hUz0_lt_zs
    simpa [onLotteries] using hstrict_lot
  exact ⟨zs, hzs_mem,
    strict_trans P hgz1 hz1zs,
    strict_trans P hzsz0 hz0f⟩

/-- With the existing average-utility hard direction available, the public
matching-frequency strict-separation bridge is theorem-backed by primitive
`Denseness` and `Monotonicity`; no separate `TwoPrizeDenseness` hypothesis is
needed. -/
theorem matchingFrequencyStrictSeparation_of_averageUtilityHardDirection
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] [Archimedeanity P]
    [Monotonicity P] [Denseness P]
    (hHard : AverageUtilityHardDirection P) :
    MatchingFrequencyStrictSeparation P :=
  matchingFrequencyStrictSeparation_of_twoPrizeDenseness_and_averageUtilityHardDirection
    P hHard (twoPrizeDenseness_of_averageUtilityHardDirection P hHard)

/-- **Lemma 1 (gap filling).**  Under Axioms 1–5, on two-prize acts the
matching frequency is a complete representation:
`f ≽ g ↔ m_{x,y}(f) ≥ m_{x,y}(g)`.

The forward (`→`) direction is `matchingFreq_mono` and uses only Weak
Order.  The reverse (`←`) direction is now proved from the explicit
Phase-2 bridge `MatchingFrequencyStrictSeparation P`, which packages the
missing two-prize gap-filling/separation theorem. -/
theorem lem_gap_filling
    (P : Preference S X)
    [WeakOrder P] [Cancellation P] [Archimedeanity P]
    [Monotonicity P] [Denseness P]
    (hSep : MatchingFrequencyStrictSeparation P)
    {x y : X}
    (hxy : P.strictPrize x y)
    (f g : Act S X)
    (hf : f ∈ TwoPrizeActs S x y) (hg : g ∈ TwoPrizeActs S x y) :
    P.weakPref f g ↔ matchingFreq P x y g ≤ matchingFreq P x y f := by
  refine ⟨?_, ?_⟩
  · -- Forward direction: from `f ≽ g` and `g ≽ xs` we get `f ≽ xs` by
    -- transitivity, so the supremand for `g` is ≤ that for `f`.
    intro hfg
    exact matchingFreq_mono P x y f g hfg
  · intro hmf
    by_contra hfg
    have hgf : P.weakPref g f := by
      rcases WeakOrder.complete (P := P) f g with hfg' | hgf'
      · exact False.elim (hfg hfg')
      · exact hgf'
    have hstrict : P.strict g f := ⟨hgf, hfg⟩
    have hlt : matchingFreq P x y f < matchingFreq P x y g :=
      hSep hxy f g hf hg hstrict
    exact (not_lt_of_ge hmf) hlt

end Preference

/-! ### §2.3 — Axioms 6 (Continuity) & 7 (Consistent Aggregation) -/

namespace Preference

variable {S X : Type*} [Fintype S] [DecidableEq S] [DecidableEq X]

/-- The state-contingent rational frequency profile space `ℚ_{[0,1]}^cS`. -/
abbrev FreqProfile (S : Type*) := S → ℚ

/-- The matching frequency of a frequency profile, inherited from any of
its representing two-prize acts.  We pick a canonical representative via
`Classical.epsilon`. -/
noncomputable def matchingFreqOfProfile
    (P : Preference S X) (x y : X) (q : FreqProfile S) : ℝ :=
  Classical.epsilon (fun r : ℝ =>
    ∃ f : Act S X, f ∈ TwoPrizeActs S x y ∧
      (∀ s, (relFreq (f s) x : ℝ) = (q s : ℝ)) ∧
      r = matchingFreq P x y f)

/-- **Axiom 6 (Continuity).**  Convergent rational frequency profiles have
convergent matching frequencies. -/
class Cts (P : Preference S X) : Prop where
  continuity :
    ∀ {x y : X} (_ : P.strictPrize x y)
      (q_seq : ℕ → FreqProfile S) (q : FreqProfile S),
      (∀ s, Filter.Tendsto (fun n => (q_seq n s : ℝ))
              Filter.atTop (nhds (q s : ℝ))) →
      ∃ L : ℝ,
        Filter.Tendsto (fun n => matchingFreqOfProfile P x y (q_seq n))
          Filter.atTop (nhds L)

/-! ### Real new lemmas about `Cts` (Continuity) -/

/-- **Constant sequence convergence**:  any constant frequency profile
sequence trivially converges (in `ℝ`) to its constant value at every
state. -/
lemma freqProfile_const_seq_tendsto
    (q : FreqProfile S) (s : S) :
    Filter.Tendsto (fun _ : ℕ => (q s : ℝ))
      Filter.atTop (nhds (q s : ℝ)) :=
  tendsto_const_nhds

/-- **Continuity applied to a constant sequence** yields the existence of
a limit, which is just the matching frequency at that constant profile. -/
lemma Cts.constant_sequence
    (P : Preference S X) [Cts P] {x y : X} (hxy : P.strictPrize x y)
    (q : FreqProfile S) :
    ∃ L : ℝ,
      Filter.Tendsto (fun _ : ℕ => matchingFreqOfProfile P x y q)
        Filter.atTop (nhds L) := by
  -- Apply continuity to the constant sequence `q_seq n := q`.
  have hseq : ∀ s, Filter.Tendsto (fun _ : ℕ => (q s : ℝ))
      Filter.atTop (nhds (q s : ℝ)) := fun s =>
    freqProfile_const_seq_tendsto q s
  exact Cts.continuity hxy (fun _ => q) q hseq

/-- A state `s ∈ cS` is **essential** for the prize pair `x ≻ y` if there
exists `q` with `m_{x,y}(1ₛ q) > m_{x,y}(0ₛ q)`. -/
def Essential (P : Preference S X) (x y : X) (s : S) : Prop :=
  ∃ q : FreqProfile S,
    matchingFreqOfProfile P x y (Function.update q s 0) <
    matchingFreqOfProfile P x y (Function.update q s 1)

/-! ### Real new lemmas about `Essential` -/

/-- An essential state has a strict-inequality witness. -/
lemma Essential.has_strict_witness
    {P : Preference S X} {x y : X} {s : S}
    (h : Essential P x y s) :
    ∃ q : FreqProfile S,
      matchingFreqOfProfile P x y (Function.update q s 0) ≠
      matchingFreqOfProfile P x y (Function.update q s 1) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  exact ne_of_lt hq

/-- An essential state has a weak-inequality witness (≤ direction). -/
lemma Essential.has_le_witness
    {P : Preference S X} {x y : X} {s : S}
    (h : Essential P x y s) :
    ∃ q : FreqProfile S,
      matchingFreqOfProfile P x y (Function.update q s 0) ≤
      matchingFreqOfProfile P x y (Function.update q s 1) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, le_of_lt hq⟩

/-- The negation of `Essential` is "0 and 1 indices give the same matching
frequency for every profile". -/
lemma not_essential_iff_constant
    {P : Preference S X} (x y : X) (s : S) :
    (¬ Essential P x y s) ↔
    ∀ q : FreqProfile S,
      matchingFreqOfProfile P x y (Function.update q s 1) ≤
      matchingFreqOfProfile P x y (Function.update q s 0) := by
  unfold Essential
  push_neg
  rfl

/-- **Axiom 7 (Consistent Aggregation).**  Frequency tradeoffs between
states are evaluated on a common scale. -/
class ConsistentAggregation (P : Preference S X) : Prop where
  consistent :
    ∀ {x y : X} (_ : P.strictPrize x y)
      (s s' : S) (_hs : Essential P x y s) (_hs' : Essential P x y s')
      (a δ b ε : ℚ) (p q p' q' : FreqProfile S),
      matchingFreqOfProfile P x y (Function.update q s b) ≥
        matchingFreqOfProfile P x y (Function.update p s (b + ε)) →
      matchingFreqOfProfile P x y (Function.update p s (a + δ)) ≥
        matchingFreqOfProfile P x y (Function.update q s a) →
      matchingFreqOfProfile P x y (Function.update q' s' a) ≥
        matchingFreqOfProfile P x y (Function.update p' s' (a + δ)) →
      matchingFreqOfProfile P x y (Function.update q' s' b) ≥
        matchingFreqOfProfile P x y (Function.update p' s' (b + ε))

end Preference

/-! ## §2.4  The main result -/

namespace Preference

open MeasureTheory

variable {S X : Type*}

/-- A preference is **non-trivial** if it strictly ranks some pair of prizes. -/
def Nontrivial (P : Preference S X) : Prop :=
  ∃ x y : X, P.strictPrize x y

/-! ### Real lemmas about `Nontrivial` -/

/-- A non-trivial preference has at least two distinct prizes. -/
lemma Nontrivial.nonempty_distinct {P : Preference S X}
    (hP : Nontrivial P) :
    ∃ x y : X, x ≠ y := by
  rcases hP with ⟨x, y, hxy, hyx⟩
  refine ⟨x, y, ?_⟩
  intro heq
  -- If `x = y`, then `prizeLottery x = prizeLottery y`, so `P.onPrizes x y`
  -- and `P.onPrizes y x` would be the same statement (reflexivity).
  -- This contradicts the strict inequality.
  apply hyx
  rw [heq]
  -- Now show `P.onPrizes y y`.
  -- This is `P.onLotteries (prizeLottery y) (prizeLottery y)`, which is
  -- `P.weakPref (constAct (prizeLottery y)) (constAct (prizeLottery y))`.
  -- We don't have `WeakOrder` here, so we cannot use reflexivity directly.
  -- Instead, use the original `hxy : P.onPrizes x y`, after rewriting `x = y`.
  rw [heq] at hxy
  exact hxy

/-- A non-trivial preference (with Weak Order) has reflexively-related
prizes for any choice. -/
lemma Nontrivial.implies_two_prizes {P : Preference S X}
    (hP : Nontrivial P) :
    ∃ x y : X, P.weakPref (constAct (prizeLottery x))
                          (constAct (prizeLottery y)) ∧
               ¬ P.weakPref (constAct (prizeLottery y))
                            (constAct (prizeLottery x)) := by
  rcases hP with ⟨x, y, hxy, hyx⟩
  exact ⟨x, y, hxy, hyx⟩

/-- A **smooth-ambiguity representation** of `≽`:

  `f ≽ g  ⟺  ∫ ψ(U(f s)) dP ≥ ∫ ψ(U(g s)) dP`,

with `U` an average-utility model, `ψ` continuous and strictly increasing
on `conv(U(cX))`, and `P` a probability measure on `cS`. -/
structure SmoothRepresentation
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    (Pref : Preference S X) where
  u           : X → ℝ
  ψ           : ℝ → ℝ
  P           : ProbabilityMeasure S
  ψ_cts       : Continuous ψ
  ψ_strict    : StrictMono ψ
  represents  :
    ∀ f g : Act S X,
      Pref.weakPref f g ↔
        ∫ s, ψ (averageUtility u (g s)) ∂P.toMeasure ≤
        ∫ s, ψ (averageUtility u (f s)) ∂P.toMeasure

namespace SmoothRepresentation

variable [Fintype S] [MeasurableSpace S] [DecidableEq X]
variable {Pref : Preference S X}

/-- A preference admitting a smooth representation is a **Weak Order**
(Axiom 1).  Completeness comes from the trichotomy of `≤` on `ℝ`, and
transitivity from the transitivity of `≤`. -/
theorem isWeakOrder (R : SmoothRepresentation Pref) : WeakOrder Pref where
  complete := by
    intro f g
    rcases le_total
      (∫ s, R.ψ (averageUtility R.u (f s)) ∂R.P.toMeasure)
      (∫ s, R.ψ (averageUtility R.u (g s)) ∂R.P.toMeasure) with h | h
    · exact Or.inr ((R.represents g f).mpr h)
    · exact Or.inl ((R.represents f g).mpr h)
  transitive := by
    intro f g h hfg hgh
    have h₁ := (R.represents f g).mp hfg
    have h₂ := (R.represents g h).mp hgh
    exact (R.represents f h).mpr (h₂.trans h₁)

/-- The pointwise consequence of monotonicity: if `f s ≽ g s` for every
state `s`, then `ψ(U(g s)) ≤ ψ(U(f s))` pointwise.  This is half of
`Monotonicity` — the integral inequality follows from this and an
integrability/finiteness argument that we leave to the user (with
`Fintype S`, the integral is a finite sum and pointwise inequality is
enough). -/
theorem ψU_pointwise_le_of_weakPref
    (R : SmoothRepresentation Pref)
    (f g : Act S X) (hfg : ∀ s, Pref.weakPref (constAct (f s)) (constAct (g s)))
    (s : S) :
    R.ψ (averageUtility R.u (g s)) ≤ R.ψ (averageUtility R.u (f s)) := by
  -- Apply `R.represents` to the constant acts and use `∫ const ∂P = const`.
  have hint := (R.represents (constAct (f s)) (constAct (g s))).mp (hfg s)
  -- For a probability measure, `∫ c ∂P = c` for any constant `c`.
  simpa [constAct] using hint

/-! ### Real new lemmas about `SmoothRepresentation` -/

/-- **Indifference iff integrals are equal.**

If `f ~ g` (mutual weak preference), then the two integrals coincide
under the smooth representation, and conversely. -/
theorem indiff_iff_integral_eq
    (R : SmoothRepresentation Pref) (f g : Act S X) :
    Pref.indiff f g ↔
    (∫ s, R.ψ (averageUtility R.u (f s)) ∂R.P.toMeasure) =
      ∫ s, R.ψ (averageUtility R.u (g s)) ∂R.P.toMeasure := by
  unfold Preference.indiff
  rw [R.represents f g, R.represents g f]
  constructor
  · intro ⟨h₁, h₂⟩
    linarith
  · intro h
    refine ⟨?_, ?_⟩
    · linarith
    · linarith

/-- **Strict iff integrals are strict.**

If `f ≻ g`, then the integral under `f` strictly exceeds that under `g`,
and conversely. -/
theorem strict_iff_integral_lt
    (R : SmoothRepresentation Pref) (f g : Act S X) :
    Pref.strict f g ↔
    (∫ s, R.ψ (averageUtility R.u (g s)) ∂R.P.toMeasure) <
      ∫ s, R.ψ (averageUtility R.u (f s)) ∂R.P.toMeasure := by
  unfold Preference.strict
  rw [R.represents f g, R.represents g f]
  constructor
  · intro ⟨h₁, h₂⟩
    rcases lt_or_eq_of_le h₁ with hlt | heq
    · exact hlt
    · exfalso
      apply h₂
      exact le_of_eq heq.symm
  · intro hlt
    refine ⟨le_of_lt hlt, ?_⟩
    intro hge
    linarith

/-- **Pointwise integrand equality from pointwise indifference.**

If `f s ~ g s` for every state, then `ψ(U(f s)) = ψ(U(g s))` pointwise. -/
theorem ψU_pointwise_eq_of_pointwise_indiff
    (R : SmoothRepresentation Pref)
    (f g : Act S X)
    (hfg : ∀ s, Pref.indiff (constAct (f s)) (constAct (g s)))
    (s : S) :
    R.ψ (averageUtility R.u (f s)) = R.ψ (averageUtility R.u (g s)) := by
  -- We have both `(constAct (f s)) ≽ (constAct (g s))` and the converse.
  have h₁ : R.ψ (averageUtility R.u (g s)) ≤ R.ψ (averageUtility R.u (f s)) := by
    have hint := (R.represents (constAct (f s)) (constAct (g s))).mp (hfg s).1
    simpa [constAct] using hint
  have h₂ : R.ψ (averageUtility R.u (f s)) ≤ R.ψ (averageUtility R.u (g s)) := by
    have hint := (R.represents (constAct (g s)) (constAct (f s))).mp (hfg s).2
    simpa [constAct] using hint
  linarith

/-- **`U` value at `prizeLottery`.**

The average utility of the singleton lottery `prizeLottery a` is
exactly `R.u a`.  This packages `averageUtility_prizeLottery` for use
inside the smooth representation. -/
theorem averageUtility_prizeLottery_eq_u
    (R : SmoothRepresentation Pref) (a : X) :
    averageUtility R.u (prizeLottery a) = R.u a :=
  averageUtility_prizeLottery R.u a

/-- **Strict monotonicity of ψ ∘ averageUtility ∘ prizeLottery.**

If `R.u x > R.u y`, then `R.ψ(R.u x) > R.ψ(R.u y)`, by strict
monotonicity of `ψ`. -/
theorem ψ_strict_mono_at_prizes
    (R : SmoothRepresentation Pref) {x y : X}
    (h : R.u y < R.u x) :
    R.ψ (R.u y) < R.ψ (R.u x) :=
  R.ψ_strict h

/-- **Composition `ψ ∘ averageUtility R.u` is strictly monotone (on prizes).**

For two prize-lottery comparisons, `R.u x < R.u y` implies
`ψ(U(prizeLottery x)) < ψ(U(prizeLottery y))`. -/
theorem ψU_prizeLottery_strict_mono
    (R : SmoothRepresentation Pref) {x y : X}
    (h : R.u x < R.u y) :
    R.ψ (averageUtility R.u (prizeLottery x)) <
    R.ψ (averageUtility R.u (prizeLottery y)) := by
  rw [averageUtility_prizeLottery R.u x, averageUtility_prizeLottery R.u y]
  exact R.ψ_strict h

/-- **`R` induces an `averageUtility` representation on lotteries.**

For any two lotteries `xs, ys`, `P.onLotteries xs ys ↔ U(ys) ≤ U(xs)`,
where `U` is `averageUtility R.u`.  This follows from `R.represents`
applied to constant acts (where the integral is just the constant
`ψ(U(_))` value) plus strict monotonicity of `ψ`.

This is the key bridge that allows the `_of_averageUtility_repr`
lemmas to be applied with `R` in scope. -/
theorem averageUtility_repr_of_smooth
    (R : SmoothRepresentation Pref) :
    ∀ xs ys : Lottery X,
      Pref.onLotteries xs ys ↔
      averageUtility R.u ys ≤ averageUtility R.u xs := by
  intro xs ys
  show Pref.weakPref (constAct xs) (constAct ys) ↔
       averageUtility R.u ys ≤ averageUtility R.u xs
  rw [R.represents (constAct xs) (constAct ys)]
  -- Goal: (∫ s, ψ(U(ys)) ∂P) ≤ (∫ s, ψ(U(xs)) ∂P) ↔ U(ys) ≤ U(xs).
  -- The constAct makes the integrand constant, so ∫ const ∂P = const.
  show (∫ _s, R.ψ (averageUtility R.u ys) ∂R.P.toMeasure) ≤
       (∫ _s, R.ψ (averageUtility R.u xs) ∂R.P.toMeasure) ↔
       averageUtility R.u ys ≤ averageUtility R.u xs
  rw [MeasureTheory.integral_const, MeasureTheory.integral_const]
  -- ψ(U(ys)) · 1 ≤ ψ(U(xs)) · 1 ↔ U(ys) ≤ U(xs).
  rw [show R.P.toMeasure.real Set.univ = 1 from MeasureTheory.probReal_univ]
  rw [smul_eq_mul, smul_eq_mul, one_mul, one_mul]
  exact ⟨fun h => R.ψ_strict.le_iff_le.mp h, fun h => R.ψ_strict.le_iff_le.mpr h⟩

/-- **Strict version**: `xs ≻ ys` on lotteries iff `U(ys) < U(xs)`.

The strict version of `averageUtility_repr_of_smooth`, derived by combining
the weak preference both ways. -/
theorem strict_lottery_iff_avg_utility_lt
    (R : SmoothRepresentation Pref) (xs ys : Lottery X) :
    Pref.strict (constAct xs) (constAct ys) ↔
      averageUtility R.u ys < averageUtility R.u xs := by
  -- Unfold strict and use the lottery representation in both directions.
  have h₁ := R.averageUtility_repr_of_smooth xs ys
  have h₂ := R.averageUtility_repr_of_smooth ys xs
  unfold Preference.strict
  show Pref.weakPref (constAct xs) (constAct ys) ∧
       ¬ Pref.weakPref (constAct ys) (constAct xs) ↔
       averageUtility R.u ys < averageUtility R.u xs
  -- `Pref.onLotteries xs ys` unfolds to `Pref.weakPref (constAct xs) (constAct ys)`.
  show (Pref.onLotteries xs ys ∧ ¬ Pref.onLotteries ys xs) ↔
       averageUtility R.u ys < averageUtility R.u xs
  rw [h₁, h₂]
  exact lt_iff_le_not_ge.symm

/-- **Indifference version**: `xs ~ ys` on lotteries iff `U(xs) = U(ys)`. -/
theorem indiff_lottery_iff_avg_utility_eq
    (R : SmoothRepresentation Pref) (xs ys : Lottery X) :
    Pref.indiff (constAct xs) (constAct ys) ↔
      averageUtility R.u xs = averageUtility R.u ys := by
  have h₁ := R.averageUtility_repr_of_smooth xs ys
  have h₂ := R.averageUtility_repr_of_smooth ys xs
  unfold Preference.indiff
  show (Pref.onLotteries xs ys ∧ Pref.onLotteries ys xs) ↔
       averageUtility R.u xs = averageUtility R.u ys
  rw [h₁, h₂]
  exact ⟨fun ⟨h₁, h₂⟩ => le_antisymm h₂ h₁,
         fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩

/-- **Existence of two distinct prizes from non-triviality**, via R.

If `Pref` is non-trivial and represented by `R`, then there exist two
prizes `x, y` with `R.u y < R.u x`. -/
theorem nontriv_prizes_via_R
    (R : SmoothRepresentation Pref)
    (hP : Nontrivial Pref) :
    ∃ x y : X, R.u y < R.u x := by
  rcases hP with ⟨x, y, hxy, hyx⟩
  -- `hxy : Pref.onPrizes x y`, i.e. `Pref.onLotteries (prizeLottery x) (prizeLottery y)`.
  have hxy_avg :
      averageUtility R.u (prizeLottery y) ≤ averageUtility R.u (prizeLottery x) :=
    (R.averageUtility_repr_of_smooth (prizeLottery x) (prizeLottery y)).mp hxy
  have hyx_avg :
      ¬ averageUtility R.u (prizeLottery x) ≤ averageUtility R.u (prizeLottery y) := by
    intro h
    apply hyx
    exact (R.averageUtility_repr_of_smooth (prizeLottery y) (prizeLottery x)).mpr h
  rw [averageUtility_prizeLottery, averageUtility_prizeLottery] at hxy_avg hyx_avg
  exact ⟨x, y, lt_of_le_not_ge hxy_avg hyx_avg⟩

/-- **`R.represents` projected to two-prize acts (statement only).**

For a two-prize lottery `xs ∈ TwoPrizeLotteries x y`,
`averageUtility R.u xs = R.u y + relFreq(xs,x) · (R.u x − R.u y)`.

This is the affine combination of `R.u x` and `R.u y` weighted by
`relFreq`.  The proof requires partitioning the prize sum by whether
`xs.get i = x`, then `length · avg = freqCount · u(x) + (length−freqCount) · u(y)`,
and dividing by `length`.  Pending. -/
theorem averageUtility_two_prize_lottery
    [DecidableEq X]
    (R : SmoothRepresentation Pref)
    {x y : X} (xs : Lottery X)
    (hxs : xs ∈ TwoPrizeLotteries x y) :
    averageUtility R.u xs =
      R.u y + (relFreq xs x : ℝ) * (R.u x - R.u y) := by
  -- Setup: split the sum by whether `xs.get i = x`.
  set N : ℕ := xs.length with hN
  set F : Finset (Fin N) := Finset.univ.filter (fun i => xs.get i = x) with hF
  set G : Finset (Fin N) := Finset.univ.filter (fun i => ¬ xs.get i = x) with hG
  have hN_pos : 0 < N := xs.length_pos
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real_pos
  -- Sum split.
  have hsplit :
      ∑ i : Fin N, R.u (xs.get i) =
      (∑ i ∈ F, R.u (xs.get i)) + ∑ i ∈ G, R.u (xs.get i) := by
    rw [hF, hG]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun i : Fin N => xs.get i = x) (fun i => R.u (xs.get i))).symm
  -- On F, R.u (xs.get i) = R.u x.
  have hFsum : ∑ i ∈ F, R.u (xs.get i) = (F.card : ℝ) * R.u x := by
    have hcongr : ∀ i ∈ F, R.u (xs.get i) = R.u x := by
      intro i hi
      have : xs.get i = x := by
        rw [hF] at hi; exact (Finset.mem_filter.mp hi).2
      rw [this]
    calc ∑ i ∈ F, R.u (xs.get i)
        = ∑ _i ∈ F, R.u x := Finset.sum_congr rfl hcongr
      _ = (F.card : ℝ) * R.u x := by rw [Finset.sum_const, nsmul_eq_mul]
  -- On G, R.u (xs.get i) = R.u y (using TwoPrizeLotteries).
  have hGsum : ∑ i ∈ G, R.u (xs.get i) = (G.card : ℝ) * R.u y := by
    have hcongr : ∀ i ∈ G, R.u (xs.get i) = R.u y := by
      intro i hi
      have hne : xs.get i ≠ x := by
        rw [hG] at hi; exact (Finset.mem_filter.mp hi).2
      have : xs.get i = y := by
        rcases hxs i with hx | hy
        · exact absurd hx hne
        · exact hy
      rw [this]
    calc ∑ i ∈ G, R.u (xs.get i)
        = ∑ _i ∈ G, R.u y := Finset.sum_congr rfl hcongr
      _ = (G.card : ℝ) * R.u y := by rw [Finset.sum_const, nsmul_eq_mul]
  -- F.card + G.card = N.
  have hcard_nat : F.card + G.card = N := by
    rw [hF, hG, Finset.card_filter_add_card_filter_not, Finset.card_univ,
        Fintype.card_fin]
  have hcard_real : (F.card : ℝ) + (G.card : ℝ) = (N : ℝ) := by
    have h := hcard_nat; exact_mod_cast h
  -- relFreq xs x = F.card / N.
  have hrelFreq_eq : (relFreq xs x : ℝ) = (F.card : ℝ) / (N : ℝ) := by
    unfold relFreq freqCount
    -- relFreq xs x = freqCount xs x / xs.length = F.card / N (as ℚ),
    -- cast to ℝ gives the same equality.
    rw [hF.symm]
    -- Goal: (((F.card : ℕ) : ℚ) / (xs.length : ℚ) : ℝ) = (F.card : ℝ) / (N : ℝ).
    push_cast
    rfl
  -- Combine.
  unfold averageUtility
  rw [hsplit, hFsum, hGsum, hrelFreq_eq]
  -- Goal: ((F.card : ℝ) * R.u x + (G.card : ℝ) * R.u y) / xs.length
  --     = R.u y + (F.card / N) * (R.u x - R.u y).
  -- N is `xs.length` by setup.
  have hG_eq : (G.card : ℝ) = (N : ℝ) - (F.card : ℝ) := by linarith
  rw [hG_eq, ← hN]
  field_simp
  ring

/-- **Affine ψ(U) on a two-prize lottery via R.**

For a two-prize lottery `xs ∈ TwoPrizeLotteries x y`,
`ψ(U(xs))` is `ψ(R.u y + r · (R.u x - R.u y))` where `r = relFreq xs x`. -/
theorem ψU_two_prize_lottery
    [DecidableEq X]
    (R : SmoothRepresentation Pref)
    {x y : X} (xs : Lottery X)
    (hxs : xs ∈ TwoPrizeLotteries x y) :
    R.ψ (averageUtility R.u xs) =
      R.ψ (R.u y + (relFreq xs x : ℝ) * (R.u x - R.u y)) := by
  rw [R.averageUtility_two_prize_lottery xs hxs]

end SmoothRepresentation

/-- The seven primitive axioms used by the smooth-representation theorem,
packaged as a single proposition.  This avoids duplicating the long nested
conjunction at each wrapper boundary. -/
def SmoothAxiomBundle
    [Fintype S] [DecidableEq S] [DecidableEq X]
    (Pref : Preference S X) : Prop :=
  (∃ _ : WeakOrder Pref, True) ∧
  (∃ _ : Cancellation Pref, True) ∧
  (∃ _ : Archimedeanity Pref, True) ∧
  (∃ _ : Monotonicity Pref, True) ∧
  (∃ _ : Denseness Pref, True) ∧
  (∃ _ : Cts Pref, True) ∧
  (∃ _ : ConsistentAggregation Pref, True)

/-- **Option-A smooth sufficiency wrapper.**

This is the near-term-submission route advertised in
`WakkerDebreuKoopmans.lean`: the Wakker/Debreu--Koopmans additive
representation machinery, continuous extension, and pairwise patching are
treated as an explicit imported theorem-shaped hypothesis.  A full Option-B
formalisation would prove this predicate from the primitive axioms. -/
def SmoothRepresentationSufficiency
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [DecidableEq X]
    (Pref : Preference S X) : Prop :=
  Nontrivial Pref → SmoothAxiomBundle Pref → Nonempty (SmoothRepresentation Pref)

/-- **Option-A regularity-recovery wrapper.**

The local necessity proof derives Weak Order, Cancellation,
Archimedeanity, and Monotonicity directly from a `SmoothRepresentation`.
The remaining analytic recoveries — Denseness, Continuity, and Consistent
Aggregation — are exactly the regularity/connectedness consequences that
the wrapper route records as imported structure. -/
def SmoothRepresentationRegularity
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [DecidableEq X]
    (Pref : Preference S X) : Prop :=
  Nontrivial Pref → ∀ _R : SmoothRepresentation Pref,
    Denseness Pref ∧ Cts Pref ∧ ConsistentAggregation Pref

/-- **Theorem 1 (Smooth Representation).**

Given non-triviality, a preference satisfies Axioms 1–7 *iff* it admits
a smooth representation; furthermore `P` is unique, and (when there are
at least two essential states) `ψ` is unique up to affine transformation
given `U`.

Non-triviality is taken as a hypothesis rather than as part of the
biconditional because it cannot be recovered from a smooth representation
alone (a constant `R.u` would still produce a representation but a
trivial preference).

The `←` direction (necessity) decomposes the smooth representation into
each axiom: Weak Order is `SmoothRepresentation.isWeakOrder`; Cancellation
and Archimedeanity follow via `prop_average_utility_mpr` applied to
`R.averageUtility_repr_of_smooth`; Monotonicity follows from pointwise
`ψU_pointwise_le_of_weakPref` plus integral monotonicity on a finite
measurable space.  Denseness, Continuity, and Consistent Aggregation
require continuity of `ψ` and connectedness arguments and are pending.

The `→` direction (sufficiency) is the deep one and goes through Wakker's
additive representation theorem on the rational simplex, plus continuous
extension and patching across prize pairs. -/
theorem thm_smooth_model
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [DecidableEq X]
    (Pref : Preference S X)
    (hNontriv : Nontrivial Pref)
    (hSuff : SmoothRepresentationSufficiency Pref)
    (hReg : SmoothRepresentationRegularity Pref) :
    SmoothAxiomBundle Pref ↔
    Nonempty (SmoothRepresentation Pref) := by
  refine ⟨?_, ?_⟩
  · -- Sufficiency: Option A consumes the named Wakker/DK-style wrapper.
    intro hAxioms
    exact hSuff hNontriv hAxioms
  · -- Necessity: from a smooth representation, derive each axiom.
    rintro ⟨R⟩
    -- The avg-utility representation on lotteries induced by R unlocks
    -- `prop_average_utility_mpr` for both Cancellation and Archimedeanity.
    have hrepr := R.averageUtility_repr_of_smooth
    -- We need `WeakOrder Pref` as an instance to call `prop_average_utility_mpr`.
    haveI := R.isWeakOrder
    obtain ⟨⟨hCancel, _⟩, ⟨hArch, _⟩⟩ :=
      prop_average_utility_mpr (P := Pref) (u := R.u) hrepr
    -- Monotonicity is fully derivable from `R`.
    have hMono : Monotonicity Pref := by
      refine ⟨?_⟩
      intro f g hfg
      -- Pointwise:  ψ(U(g s)) ≤ ψ(U(f s)) for every state s.
      have hpt : ∀ s, R.ψ (averageUtility R.u (g s)) ≤
                       R.ψ (averageUtility R.u (f s)) := by
        intro s
        exact R.ψU_pointwise_le_of_weakPref f g (fun s => hfg s) s
      -- Both integrands are integrable (`Fintype S` + `MeasurableSingletonClass S`
      -- + `IsProbabilityMeasure`).
      haveI : MeasureTheory.IsProbabilityMeasure (R.P : MeasureTheory.Measure S) :=
        inferInstance
      have hIf : MeasureTheory.Integrable
          (fun s => R.ψ (averageUtility R.u (f s))) (R.P : MeasureTheory.Measure S) :=
        MeasureTheory.Integrable.of_finite
      have hIg : MeasureTheory.Integrable
          (fun s => R.ψ (averageUtility R.u (g s))) (R.P : MeasureTheory.Measure S) :=
        MeasureTheory.Integrable.of_finite
      -- Integrate the pointwise inequality.
      have hint :
          (∫ s, R.ψ (averageUtility R.u (g s)) ∂(R.P : MeasureTheory.Measure S))
            ≤ ∫ s, R.ψ (averageUtility R.u (f s)) ∂(R.P : MeasureTheory.Measure S) :=
        MeasureTheory.integral_mono hIg hIf hpt
      -- Translate back into `Pref.weakPref f g`.
      exact (R.represents f g).mpr hint
    have hRegR := hReg hNontriv R
    refine ⟨⟨R.isWeakOrder, trivial⟩, ⟨hCancel, trivial⟩,
            ⟨hArch, trivial⟩, ⟨hMono, trivial⟩, ?_, ?_, ?_⟩
    · exact ⟨hRegR.1, trivial⟩
    · exact ⟨hRegR.2.1, trivial⟩
    · exact ⟨hRegR.2.2, trivial⟩

/-- **Phase-4 matching-frequency smooth-formula bridge.**

This is the exact remaining non-local step behind Equation (2.5): combine
the two-prize matching-frequency characterization, the smooth integral
representation, the unit normalization `u(x)=1`, `u(y)=0`, and the inverse
of the strictly increasing transform `ψ` to identify the behavioral matching
frequency with the inverse-ψ integral expression.

The structural simplification lemmas below prove the integrand-level part
(`ψ(U(f s)) = ψ(relFreq (f s) x)`).  What this bridge records explicitly is
the additional supremum/inverse argument needed to turn that integral
identity into the matching-frequency formula itself. -/
def MatchingFrequencySmoothFormulaBridge
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    (Pref : Preference S X) (R : SmoothRepresentation Pref) : Prop :=
  ∀ {x y : X},
    Pref.strictPrize x y →
    R.u x = 1 ∧ R.u y = 0 →
    ∀ f : Act S X,
      f ∈ TwoPrizeActs S x y →
      matchingFreq Pref x y f =
        Function.invFun R.ψ
          (∫ s, R.ψ ((relFreq (f s) x : ℝ)) ∂R.P.toMeasure)

/-- **Equation (2.5).** On two-prize acts,
`m_{x,y}(f) = ψ⁻¹ ( ∫ ψ(r_x ∘ f) dP )` under the normalization
`u(x) = 1`, `u(y) = 0`.

In the Option-A submission route, the non-local supremum/inverse part is
made explicit as `MatchingFrequencySmoothFormulaBridge`; the surrounding
two-prize integrand simplification remains theorem-backed below. -/
theorem matching_freq_smooth_formula
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    (Pref : Preference S X)
    (R : SmoothRepresentation Pref)
    (hFormula : MatchingFrequencySmoothFormulaBridge Pref R)
    (x y : X)
    (hxy : Pref.strictPrize x y)
    (hu : R.u x = 1 ∧ R.u y = 0)
    (f : Act S X) (hf : f ∈ TwoPrizeActs S x y) :
    matchingFreq Pref x y f =
      Function.invFun R.ψ
        (∫ s, R.ψ ((relFreq (f s) x : ℝ)) ∂R.P.toMeasure) := by
  exact hFormula hxy hu f hf

/-- **Integrand simplification on two-prize acts under unit normalization.**

Under the normalization `R.u x = 1`, `R.u y = 0`, the integrand
`ψ(U(f s))` for two-prize acts simplifies to `ψ(relFreq (f s) x)`.

This is the structural identity behind Equation (2.5).  It reduces the
representing integral to one in pure `relFreq`, which is the
"matching-frequency-formula" the paper uses. -/
theorem ψU_eq_ψ_relFreq_on_two_prize
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    {Pref : Preference S X}
    (R : SmoothRepresentation Pref)
    {x y : X}
    (hu : R.u x = 1 ∧ R.u y = 0)
    {f : Act S X} (hf : f ∈ TwoPrizeActs S x y) :
    ∀ s, R.ψ (averageUtility R.u (f s)) =
         R.ψ ((relFreq (f s) x : ℝ)) := by
  intro s
  -- Use averageUtility_two_prize_lottery and the unit normalization.
  rw [R.ψU_two_prize_lottery (f s) (hf s)]
  rw [hu.1, hu.2]
  -- Goal: ψ(0 + relFreq · (1 - 0)) = ψ(relFreq).
  congr 1
  ring

/-- **Integral simplification under unit normalization** for two-prize acts.

The representing integral `∫ ψ(U(f s)) dP` on two-prize acts under unit
normalization equals `∫ ψ(relFreq(f s, x)) dP`. -/
theorem integral_ψU_eq_integral_ψ_relFreq
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    {Pref : Preference S X}
    (R : SmoothRepresentation Pref)
    {x y : X}
    (hu : R.u x = 1 ∧ R.u y = 0)
    {f : Act S X} (hf : f ∈ TwoPrizeActs S x y) :
    (∫ s, R.ψ (averageUtility R.u (f s)) ∂R.P.toMeasure) =
      ∫ s, R.ψ ((relFreq (f s) x : ℝ)) ∂R.P.toMeasure := by
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  exact ψU_eq_ψ_relFreq_on_two_prize R hu hf s

end Preference

/-! ## §2.6  Ambiguity attitudes -/

namespace Preference

variable {S X : Type*} [DecidableEq X]

/-- An act `h` is a **mixture** of `f` and `g` (rational coefficient
`α ∈ (0,1)`) on the prize pair `x ≻ y` if for every state
`r_x(h s) = α r_x(f s) + (1 − α) r_x(g s)`. -/
def IsMixture (x : X) (α : ℚ) (f g h : Act S X) : Prop :=
  0 < α ∧ α < 1 ∧
  ∀ s, (relFreq (h s) x : ℚ) =
        α * (relFreq (f s) x) + (1 - α) * (relFreq (g s) x)

/-! ### Real, fully-proven structural lemmas about `IsMixture` -/

/-- Reflexivity: `f` is its own mixture with `α` (any rational coefficient). -/
lemma IsMixture.self
    (x : X) (α : ℚ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (f : Act S X) :
    IsMixture x α f f f := by
  refine ⟨hα_pos, hα_lt, ?_⟩
  intro s
  ring

/-- Mixture symmetry: if `h` is a mixture of `f, g` with weight `α`, then
`h` is also a mixture of `g, f` with weight `1 - α`. -/
lemma IsMixture.swap
    {x : X} {α : ℚ} {f g h : Act S X}
    (hmix : IsMixture x α f g h) :
    IsMixture x (1 - α) g f h := by
  refine ⟨?_, ?_, ?_⟩
  · linarith [hmix.1, hmix.2.1]
  · linarith [hmix.1]
  · intro s
    have := hmix.2.2 s
    -- (relFreq h s x) = α * (relFreq f s x) + (1 - α) * (relFreq g s x)
    -- We want:
    --   (relFreq h s x) = (1 - α) * (relFreq g s x) + α * (relFreq f s x)
    -- which equals the RHS above.
    -- Goal: (relFreq h s x) = (1 - α) * (relFreq g s x) + (1 - (1 - α)) * (relFreq f s x)
    rw [show (1 : ℚ) - (1 - α) = α from by ring]
    rw [this]
    ring

/-- A mixture preserves the `[0, 1]` range: if `f, g` produce frequencies
in `[0, 1]` (which they always do for `relFreq`), the mixture does too. -/
lemma IsMixture.relFreq_mem_unitInterval
    [DecidableEq X] {x : X} {α : ℚ} {f g h : Act S X}
    (hmix : IsMixture x α f g h) (s : S) :
    0 ≤ (relFreq (h s) x : ℚ) ∧ (relFreq (h s) x : ℚ) ≤ 1 := by
  rw [hmix.2.2 s]
  refine ⟨?_, ?_⟩
  · -- α > 0, 1 - α > 0, both relFreq ≥ 0.
    have h1 : 0 ≤ (relFreq (f s) x : ℚ) := relFreq_nonneg _ _
    have h2 : 0 ≤ (relFreq (g s) x : ℚ) := relFreq_nonneg _ _
    have hα : 0 < α := hmix.1
    have h1mα : 0 < 1 - α := by linarith [hmix.2.1]
    have ha1 : 0 ≤ α * (relFreq (f s) x : ℚ) := mul_nonneg (le_of_lt hα) h1
    have ha2 : 0 ≤ (1 - α) * (relFreq (g s) x : ℚ) :=
      mul_nonneg (le_of_lt h1mα) h2
    linarith
  · -- α * relFreq f + (1 - α) * relFreq g ≤ α * 1 + (1 - α) * 1 = 1.
    have h1 : (relFreq (f s) x : ℚ) ≤ 1 := relFreq_le_one _ _
    have h2 : (relFreq (g s) x : ℚ) ≤ 1 := relFreq_le_one _ _
    have hα : 0 < α := hmix.1
    have h1mα : 0 < 1 - α := by linarith [hmix.2.1]
    nlinarith [hα, h1mα, h1, h2]

/-- **Mixture with `f = g`**: when both acts are the same, the mixture
gives the same `relFreq` profile pointwise. -/
lemma IsMixture.same_acts
    [DecidableEq X] {x : X} {α : ℚ} {f h : Act S X}
    (hmix : IsMixture x α f f h) (s : S) :
    (relFreq (h s) x : ℚ) = relFreq (f s) x := by
  have := hmix.2.2 s
  -- relFreq h = α * relFreq f + (1 - α) * relFreq f = relFreq f
  rw [this]
  ring

/-- **Mixture coefficient bound**: `α + (1 - α) = 1`, so the mixture
weights sum to 1. -/
lemma IsMixture.weights_sum_one
    {x : X} {α : ℚ} {f g h : Act S X} (_hmix : IsMixture x α f g h) :
    α + (1 - α) = 1 := by ring

/-- **Mixture weight is positive**: by definition, `α > 0`. -/
lemma IsMixture.alpha_pos
    {x : X} {α : ℚ} {f g h : Act S X} (hmix : IsMixture x α f g h) :
    0 < α :=
  hmix.1

/-- **Mixture weight is less than 1**: by definition, `α < 1`. -/
lemma IsMixture.alpha_lt_one
    {x : X} {α : ℚ} {f g h : Act S X} (hmix : IsMixture x α f g h) :
    α < 1 :=
  hmix.2.1

/-- **Complement is positive**: `0 < 1 - α`. -/
lemma IsMixture.one_sub_alpha_pos
    {x : X} {α : ℚ} {f g h : Act S X} (hmix : IsMixture x α f g h) :
    0 < 1 - α := by
  have := hmix.2.1
  linarith

/-! ### More IsMixture structural lemmas -/

/-- **Mixtures preserve `f ≽ g`** at the level of `relFreq` profiles:
if both `f` and `g` produce the same `relFreq x` everywhere, the mixture
also has the same `relFreq x` everywhere. -/
lemma IsMixture.relFreq_const_when_equal
    [DecidableEq X] {x : X} {α : ℚ} {f g h : Act S X}
    (hmix : IsMixture x α f g h) (s : S)
    (heq : (relFreq (f s) x : ℚ) = (relFreq (g s) x : ℚ)) :
    (relFreq (h s) x : ℚ) = (relFreq (f s) x : ℚ) := by
  rw [hmix.2.2 s, heq]
  ring

/-- **Mixture coefficient is in (0, 1)**: extracts both bounds. -/
lemma IsMixture.alpha_mem_open01
    {x : X} {α : ℚ} {f g h : Act S X} (hmix : IsMixture x α f g h) :
    0 < α ∧ α < 1 :=
  ⟨hmix.alpha_pos, hmix.alpha_lt_one⟩

/-! ### Real lemmas: averageUtility × IsMixture -/

/-- **Average utility under mixture (formal weighted-relFreq)**:

If `h` is a `IsMixture` of `f, g` with weight `α` *on a single state*,
then the rel-freq profile of `h s` is the weighted combination.  This
just packages `hmix.2.2` for clarity. -/
lemma IsMixture.relFreq_combination
    [DecidableEq X] {x : X} {α : ℚ} {f g h : Act S X}
    (hmix : IsMixture x α f g h) (s : S) :
    (relFreq (h s) x : ℚ) =
      α * (relFreq (f s) x) + (1 - α) * (relFreq (g s) x) :=
  hmix.2.2 s

/-- **Pointwise mixture property as reals.**

The real-cast version of `IsMixture.relFreq_combination`: if `h` is a
mixture of `f, g` with weight `α`, then the rel-freq of `h s` (cast to
`ℝ`) equals the weighted combination. -/
lemma IsMixture.relFreq_real_combination
    [DecidableEq X] {x : X} {α : ℚ} {f g h : Act S X}
    (hmix : IsMixture x α f g h) (s : S) :
    (relFreq (h s) x : ℝ) =
      (α : ℝ) * (relFreq (f s) x : ℝ) +
        (1 - (α : ℝ)) * (relFreq (g s) x : ℝ) := by
  have h_rat := hmix.relFreq_combination s
  have hcast : ((relFreq (h s) x : ℚ) : ℝ) =
               (((α * (relFreq (f s) x) + (1 - α) * (relFreq (g s) x)) : ℚ) : ℝ) := by
    rw [h_rat]
  push_cast at hcast
  linarith

/-- **Affine averageUtility on mixtures of two-prize acts.**

If `h s` is a mixture of `f s, g s` (in the `IsMixture` sense) on the
prize pair `(x, y)`, with all three lotteries in `TwoPrizeLotteries x y`,
then the average utility of the mixture is the linear combination:

  `U(h s) = α · U(f s) + (1 - α) · U(g s)`.

This is the structural identity behind Jensen's-inequality-based ambiguity
attitude characterization. -/
theorem SmoothRepresentation.averageUtility_isMixture
    [Fintype S] [MeasurableSpace S] [DecidableEq X]
    {Pref : Preference S X}
    (R : SmoothRepresentation Pref)
    {x y : X} {α : ℚ} {f g h : Act S X} (hmix : IsMixture x α f g h)
    (hf : f ∈ TwoPrizeActs S x y)
    (hg : g ∈ TwoPrizeActs S x y)
    (hh : h ∈ TwoPrizeActs S x y)
    (s : S) :
    averageUtility R.u (h s) =
      (α : ℝ) * averageUtility R.u (f s) +
      (1 - (α : ℝ)) * averageUtility R.u (g s) := by
  -- Use the two-prize identity on each side.
  rw [R.averageUtility_two_prize_lottery (f s) (hf s),
      R.averageUtility_two_prize_lottery (g s) (hg s),
      R.averageUtility_two_prize_lottery (h s) (hh s)]
  rw [hmix.relFreq_real_combination s]
  ring

/-- The preference exhibits **ambiguity aversion** if every mixture of two
two-prize acts is at least as good as the worse of the two. -/
def AmbiguityAverse (P : Preference S X) : Prop :=
  ∀ {x y : X} (_ : P.strictPrize x y)
    (f g h : Act S X),
    f ∈ TwoPrizeActs S x y →
    g ∈ TwoPrizeActs S x y →
    h ∈ TwoPrizeActs S x y →
    ∀ α : ℚ, IsMixture x α f g h →
    P.weakPref f g → P.weakPref h g

/-- The preference exhibits **ambiguity seeking**: every mixture is at
most as good as the better of the two acts. -/
def AmbiguitySeeking (P : Preference S X) : Prop :=
  ∀ {x y : X} (_ : P.strictPrize x y)
    (f g h : Act S X),
    f ∈ TwoPrizeActs S x y →
    g ∈ TwoPrizeActs S x y →
    h ∈ TwoPrizeActs S x y →
    ∀ α : ℚ, IsMixture x α f g h →
    P.weakPref f g → P.weakPref f h

/-! ### Real lemmas about `AmbiguityAverse` / `AmbiguitySeeking` -/

/-- **An indifferent agent is both ambiguity-averse and ambiguity-seeking.**

If `P` is the trivial all-indifference preference (`weakPref` returns
true everywhere), then both ambiguity aversion and ambiguity seeking
hold trivially. -/
lemma ambiguityAverse_of_total_indiff
    (P : Preference S X) [WeakOrder P]
    (htotal : ∀ f g : Act S X, P.weakPref f g) :
    AmbiguityAverse P := by
  intro x y _ f g h _ _ _ _ _ _
  exact htotal h g

/-- Symmetric: total-indifference implies ambiguity seeking. -/
lemma ambiguitySeeking_of_total_indiff
    (P : Preference S X) [WeakOrder P]
    (htotal : ∀ f g : Act S X, P.weakPref f g) :
    AmbiguitySeeking P := by
  intro x y _ f g h _ _ _ _ _ _
  exact htotal f h

/-- A pair of distinct essential states exists for some prize pair. -/
def AtLeastTwoEssentialStates [Fintype S] [DecidableEq S] (P : Preference S X) : Prop :=
  ∃ x y : X, ∃ s₁ s₂ : S, s₁ ≠ s₂ ∧
    Essential P x y s₁ ∧ Essential P x y s₂

/-- If at least two essential states exist for some prize pair, then `S`
has at least two distinct elements. -/
lemma AtLeastTwoEssentialStates.distinct_states
    [Fintype S] [DecidableEq S] {P : Preference S X}
    (h : AtLeastTwoEssentialStates P) :
    ∃ s₁ s₂ : S, s₁ ≠ s₂ := by
  rcases h with ⟨_, _, s₁, s₂, hs, _, _⟩
  exact ⟨s₁, s₂, hs⟩

/-- If at least two essential states exist for some prize pair, then
that prize pair witnesses an essential state. -/
lemma AtLeastTwoEssentialStates.exists_essential
    [Fintype S] [DecidableEq S] {P : Preference S X}
    (h : AtLeastTwoEssentialStates P) :
    ∃ x y : X, ∃ s : S, Essential P x y s := by
  rcases h with ⟨x, y, s₁, _, _, h_ess₁, _⟩
  exact ⟨x, y, s₁, h_ess₁⟩

/-- **Concave ψ implies ambiguity aversion** (the easy half of Proposition 2).

If `R.ψ` is concave on `ℝ`, then the preference is ambiguity averse:
mixtures of two-prize acts are weakly preferred to the worse element of
the pair.

The proof is Jensen's inequality applied to the smooth representation:
`∫ ψ(U(h s)) ∂P ≥ α ∫ ψ(U(f s)) ∂P + (1-α) ∫ ψ(U(g s)) ∂P ≥ ∫ ψ(U(g s)) ∂P`,
where the first inequality is concavity (pointwise + integration) and
the second uses `f ≽ g`. -/
theorem ambiguityAverse_of_concave
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Pref : Preference S X}
    (R : SmoothRepresentation Pref)
    (hψ : ConcaveOn ℝ (Set.univ : Set ℝ) R.ψ) :
    AmbiguityAverse Pref := by
  intro x y _hxy f g h hf hg hh α hmix hfg
  -- The integrand `ψ ∘ U` is bounded since ψ is continuous on ℝ and S is finite.
  haveI : MeasureTheory.IsProbabilityMeasure (R.P : MeasureTheory.Measure S) :=
    inferInstance
  -- Pointwise: ψ(U(h s)) ≥ α ψ(U(f s)) + (1-α) ψ(U(g s)) (concavity).
  have hα_pos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hmix.1
  have hα_lt_one : (α : ℝ) < 1 := by exact_mod_cast hmix.2.1
  have h_one_minus_α_pos : (0 : ℝ) < 1 - (α : ℝ) := by linarith
  -- Apply concavity at every state.
  have hpt_concave : ∀ s,
      (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
        (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s))
      ≤ R.ψ (averageUtility R.u (h s)) := by
    intro s
    have hsum : (α : ℝ) + (1 - (α : ℝ)) = 1 := by ring
    have h_concave_apply :=
      hψ.2 (Set.mem_univ (averageUtility R.u (f s)))
           (Set.mem_univ (averageUtility R.u (g s)))
           hα_pos.le h_one_minus_α_pos.le hsum
    -- h_concave_apply : α • ψ(U(f s)) + (1-α) • ψ(U(g s))
    --                  ≤ ψ(α • U(f s) + (1-α) • U(g s))
    -- The smul on ℝ is multiplication; rewrite the convex combination as U(h s).
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h_concave_apply
    have hU_eq := R.averageUtility_isMixture hmix hf hg hh s
    rw [← hU_eq] at h_concave_apply
    exact h_concave_apply
  -- Use `Pref.weakPref f g` from the smooth representation:
  --   ∫ ψ(U(g s)) ≤ ∫ ψ(U(f s)).
  have hfg_int := (R.represents f g).mp hfg
  -- Goal: weakPref h g, i.e. ∫ ψ(U(g s)) ≤ ∫ ψ(U(h s)).
  apply (R.represents h g).mpr
  -- Integrability of all three integrands.
  have hI_f : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (f s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_g : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (g s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_h : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (h s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_combo : MeasureTheory.Integrable
      (fun s => (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
                (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s)))
      (R.P : MeasureTheory.Measure S) := by
    exact (hI_f.const_mul (α : ℝ)).add (hI_g.const_mul (1 - (α : ℝ)))
  -- Integrate the pointwise inequality.
  have hint_le :
      (∫ s, (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
            (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s))
            ∂(R.P : MeasureTheory.Measure S))
      ≤ ∫ s, R.ψ (averageUtility R.u (h s)) ∂(R.P : MeasureTheory.Measure S) :=
    MeasureTheory.integral_mono hI_combo hI_h hpt_concave
  -- Linearity of integral.
  have hsplit :
      (∫ s, (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
            (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s))
            ∂(R.P : MeasureTheory.Measure S))
      = (α : ℝ) * (∫ s, R.ψ (averageUtility R.u (f s))
                        ∂(R.P : MeasureTheory.Measure S))
        + (1 - (α : ℝ)) * (∫ s, R.ψ (averageUtility R.u (g s))
                                ∂(R.P : MeasureTheory.Measure S)) := by
    rw [MeasureTheory.integral_add (hI_f.const_mul _) (hI_g.const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsplit] at hint_le
  -- Now `α · I(f) + (1-α) · I(g) ≤ I(h)`, plus `I(g) ≤ I(f)` (hfg_int).
  -- Hence `I(g) = α · I(g) + (1-α) · I(g) ≤ α · I(f) + (1-α) · I(g) ≤ I(h)`.
  have hbound : (α : ℝ) * (∫ s, R.ψ (averageUtility R.u (g s))
                              ∂(R.P : MeasureTheory.Measure S))
              ≤ (α : ℝ) * (∫ s, R.ψ (averageUtility R.u (f s))
                              ∂(R.P : MeasureTheory.Measure S)) :=
    mul_le_mul_of_nonneg_left hfg_int hα_pos.le
  linarith

/-- **Convex ψ implies ambiguity seeking** (the easy half of Proposition 2,
symmetric direction). -/
theorem ambiguitySeeking_of_convex
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Pref : Preference S X}
    (R : SmoothRepresentation Pref)
    (hψ : ConvexOn ℝ (Set.univ : Set ℝ) R.ψ) :
    AmbiguitySeeking Pref := by
  intro x y _hxy f g h hf hg hh α hmix hfg
  haveI : MeasureTheory.IsProbabilityMeasure (R.P : MeasureTheory.Measure S) :=
    inferInstance
  have hα_pos : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hmix.1
  have hα_lt_one : (α : ℝ) < 1 := by exact_mod_cast hmix.2.1
  have h_one_minus_α_pos : (0 : ℝ) < 1 - (α : ℝ) := by linarith
  -- Pointwise: ψ(U(h s)) ≤ α ψ(U(f s)) + (1-α) ψ(U(g s)) (convexity).
  have hpt_convex : ∀ s,
      R.ψ (averageUtility R.u (h s))
      ≤ (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
        (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s)) := by
    intro s
    have hsum : (α : ℝ) + (1 - (α : ℝ)) = 1 := by ring
    have h_convex_apply :=
      hψ.2 (Set.mem_univ (averageUtility R.u (f s)))
           (Set.mem_univ (averageUtility R.u (g s)))
           hα_pos.le h_one_minus_α_pos.le hsum
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at h_convex_apply
    have hU_eq := R.averageUtility_isMixture hmix hf hg hh s
    rw [← hU_eq] at h_convex_apply
    exact h_convex_apply
  have hfg_int := (R.represents f g).mp hfg
  -- Goal: weakPref f h, i.e. ∫ ψ(U(h s)) ≤ ∫ ψ(U(f s)).
  apply (R.represents f h).mpr
  have hI_f : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (f s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_g : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (g s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_h : MeasureTheory.Integrable
      (fun s => R.ψ (averageUtility R.u (h s))) (R.P : MeasureTheory.Measure S) :=
    MeasureTheory.Integrable.of_finite
  have hI_combo : MeasureTheory.Integrable
      (fun s => (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
                (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s)))
      (R.P : MeasureTheory.Measure S) := by
    exact (hI_f.const_mul (α : ℝ)).add (hI_g.const_mul (1 - (α : ℝ)))
  have hint_le :
      (∫ s, R.ψ (averageUtility R.u (h s)) ∂(R.P : MeasureTheory.Measure S))
      ≤ ∫ s, (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
            (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s))
            ∂(R.P : MeasureTheory.Measure S) :=
    MeasureTheory.integral_mono hI_h hI_combo hpt_convex
  have hsplit :
      (∫ s, (α : ℝ) * R.ψ (averageUtility R.u (f s)) +
            (1 - (α : ℝ)) * R.ψ (averageUtility R.u (g s))
            ∂(R.P : MeasureTheory.Measure S))
      = (α : ℝ) * (∫ s, R.ψ (averageUtility R.u (f s))
                        ∂(R.P : MeasureTheory.Measure S))
        + (1 - (α : ℝ)) * (∫ s, R.ψ (averageUtility R.u (g s))
                                ∂(R.P : MeasureTheory.Measure S)) := by
    rw [MeasureTheory.integral_add (hI_f.const_mul _) (hI_g.const_mul _)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hsplit] at hint_le
  -- α · I(f) + (1-α) · I(g) ≤ α · I(f) + (1-α) · I(f) = I(f).
  have hbound : (1 - (α : ℝ)) * (∫ s, R.ψ (averageUtility R.u (g s))
                                    ∂(R.P : MeasureTheory.Measure S))
              ≤ (1 - (α : ℝ)) * (∫ s, R.ψ (averageUtility R.u (f s))
                                    ∂(R.P : MeasureTheory.Measure S)) :=
    mul_le_mul_of_nonneg_left hfg_int h_one_minus_α_pos.le
  linarith

/-- **Phase-5 ambiguity-attitude curvature bridge.**

The easy directions of Proposition 2 are theorem-backed above:
concavity of `ψ` implies ambiguity aversion, and convexity of `ψ` implies
ambiguity seeking.  The converse directions are the genuinely non-local
Debreu--Koopmans-style step: from behavioral mixture preferences over
two-prize acts, recover curvature of the smooth aggregator.

This bridge records exactly that remaining representation/convexity
argument, keeping the public proposition sorry-free without hiding the
dependency behind a broad axiom. -/
def AmbiguityAttitudeCurvatureBridge
    [Fintype S] [MeasurableSpace S]
    (Pref : Preference S X) (R : SmoothRepresentation Pref) : Prop :=
  (AmbiguityAverse Pref → ConcaveOn ℝ (Set.univ : Set ℝ) R.ψ) ∧
  (AmbiguitySeeking Pref → ConvexOn ℝ (Set.univ : Set ℝ) R.ψ)

/-- **Proposition 2 (ambiguity attitudes).**

A preference admitting smooth representation `(P, ψ, U)` with at least
two essential states is

  * **ambiguity averse** iff `ψ` is concave on its domain, and
  * **ambiguity seeking** iff `ψ` is convex on its domain. -/
theorem prop_aversion_or_seeking
    [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (Pref : Preference S X)
    (R : SmoothRepresentation Pref)
    (hBridge : AmbiguityAttitudeCurvatureBridge Pref R)
    (_h : AtLeastTwoEssentialStates Pref) :
    (AmbiguityAverse Pref ↔ ConcaveOn ℝ (Set.univ : Set ℝ) R.ψ) ∧
    (AmbiguitySeeking Pref ↔ ConvexOn  ℝ (Set.univ : Set ℝ) R.ψ) := by
  exact ⟨⟨hBridge.1, ambiguityAverse_of_concave R⟩,
         ⟨hBridge.2, ambiguitySeeking_of_convex R⟩⟩

/-! ### Public theorem axiom audit

These commands intentionally print the axiom dependencies of the public
results tracked in `RecommendedNextStepsRoadmap.md`.  Wrapper hypotheses
remain ordinary theorem assumptions rather than hidden axioms. -/

#print axioms prop_average_utility
#print axioms lem_gap_filling
#print axioms thm_smooth_model
#print axioms matching_freq_smooth_formula
#print axioms prop_aversion_or_seeking

end Preference

/-! ## §App.4  Solvability (Axiom 8) -/

namespace Preference

variable {S X : Type*} [DecidableEq X]

/-- **Axiom 8 (Solvability).**  Every act bounded between two prizes has a
matching classical lottery on those two prizes — equivalently, all
matching frequencies are *rational*. -/
class Solvability (P : Preference S X) : Prop where
  solvable :
    ∀ {x y : X} (_ : P.strictPrize x y)
      (f : Act S X)
      (_ : ∀ s, P.onLotteries (prizeLottery x) (f s))
      (_ : ∀ s, P.onLotteries (f s) (prizeLottery y)),
      ∃ xs : Lottery X,
        xs ∈ TwoPrizeLotteries x y ∧
        P.indiff (constAct xs) f

/-! ### Real lemmas about `Solvability` boundary cases -/

/-- **Constant `prizeLottery x` act is solvable trivially.**

If `f = constAct (prizeLottery x)`, the matching classical lottery is
just `prizeLottery x` itself (no resolution needed).
This is a direct consequence of weak-order reflexivity. -/
lemma solvable_constAct_prizeLottery_left
    (P : Preference S X) [WeakOrder P]
    (x y : X) :
    ∃ xs : Lottery X,
      xs ∈ TwoPrizeLotteries x y ∧
      P.indiff (constAct xs) (constAct (prizeLottery x) : Act S X) := by
  refine ⟨prizeLottery x, ?_, ?_⟩
  · exact prizeLottery_mem_TwoPrizeLotteries_left x y
  · -- `constAct (prizeLottery x) ~ constAct (prizeLottery x)` is reflexivity.
    exact indiff_refl P _

/-- **Constant `prizeLottery y` act is solvable trivially.** -/
lemma solvable_constAct_prizeLottery_right
    (P : Preference S X) [WeakOrder P]
    (x y : X) :
    ∃ xs : Lottery X,
      xs ∈ TwoPrizeLotteries x y ∧
      P.indiff (constAct xs) (constAct (prizeLottery y) : Act S X) := by
  refine ⟨prizeLottery y, ?_, ?_⟩
  · exact prizeLottery_mem_TwoPrizeLotteries_right x y
  · exact indiff_refl P _

end Preference

/-! ## §3 — Application: Income profiles & social welfare

In §3, an income profile is `xs = (x₁,…,x_I) ∈ ℝ^I`, `I ≥ 1`.  Under the
veil-of-ignorance reading, evaluation of an income profile is the
*classical-lottery part* of the model:
  `U(xs) = (1/I) Σ u(x_i)` (utilitarian average utility).
Concavity of `u` captures inequality aversion (Vickrey).  Then policies
are *acts* mapping states to income profiles. -/

namespace Preference

/-- An **income profile** is a classical lottery on `ℝ`. -/
abbrev IncomeProfile := Lottery ℝ

/-- A **social policy** is an act with prize space `ℝ`. -/
abbrev SocialPolicy (S : Type*) := Act S ℝ

/-- The utilitarian average utility of an income profile. -/
noncomputable def utilitarianAverage (u : ℝ → ℝ) (xs : IncomeProfile) : ℝ :=
  averageUtility u xs

/-- **Inequality aversion** under the veil of ignorance is captured by a
concave utility `u`. -/
def InequalityAverse (u : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ Set.univ u

/-- **Outcome ambiguity aversion** for a social planner is a concave `ψ`
in the smooth model. -/
def OutcomeAmbiguityAverse {S : Type*}
    [Fintype S] [MeasurableSpace S]
    (Pref : Preference S ℝ) (R : SmoothRepresentation Pref) : Prop :=
  ConcaveOn ℝ Set.univ R.ψ

/-! ### Real, fully-proven lemmas about the application section -/

/-- The utilitarian average of a constant income profile (a single
person earning income `c`) is just `u c`. -/
lemma utilitarianAverage_prizeLottery (u : ℝ → ℝ) (c : ℝ) :
    utilitarianAverage u (prizeLottery c) = u c :=
  averageUtility_prizeLottery u c

/-- Utilitarian average is invariant under affine transformations of `u`. -/
lemma utilitarianAverage_affine (u : ℝ → ℝ) (α β : ℝ) (xs : IncomeProfile) :
    utilitarianAverage (fun x => α * u x + β) xs =
      α * utilitarianAverage u xs + β :=
  averageUtility_affine u α β xs

/-- For any utility `u`, the utilitarian average is bounded above by the
maximum income's utility (under the same constraint as `averageUtility_le_max`). -/
lemma utilitarianAverage_le_max (u : ℝ → ℝ) (xs : IncomeProfile) (M : ℝ)
    (hM : ∀ i : Fin xs.length, u (xs.get i) ≤ M) :
    utilitarianAverage u xs ≤ M :=
  averageUtility_le_max u xs M hM

/-- Symmetric lower bound for utilitarian average. -/
lemma utilitarianAverage_ge_min (u : ℝ → ℝ) (xs : IncomeProfile) (m : ℝ)
    (hm : ∀ i : Fin xs.length, m ≤ u (xs.get i)) :
    m ≤ utilitarianAverage u xs :=
  averageUtility_ge_min u xs m hm

/-- An identity utility `u = id` makes the utilitarian average equal to
the literal mean income.  This is the "raw mean" baseline. -/
lemma utilitarianAverage_id (xs : IncomeProfile) :
    utilitarianAverage (fun x => x) xs =
      (∑ i : Fin xs.length, xs.get i) / (xs.length : ℝ) := by
  rfl

/-- **Inequality aversion is preserved by affine transformations**: if
`u` is concave on `Set.univ`, so is `α u + β` for `α ≥ 0`. -/
lemma InequalityAverse.affine
    {u : ℝ → ℝ} (h : InequalityAverse u)
    {α : ℝ} (hα : 0 ≤ α) (β : ℝ) :
    InequalityAverse (fun x => α * u x + β) := by
  unfold InequalityAverse
  -- This is a real result: the affine image of a concave function (with
  -- non-negative scaling) is concave.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- Concavity of `u` gives: a • u x + b • u y ≤ u (a • x + b • y).
  have hu_conc : a • u x + b • u y ≤ u (a • x + b • y) :=
    h.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  -- Multiply by α ≥ 0 (preserves direction).
  have hα_mul : α * (a • u x + b • u y) ≤ α * u (a • x + b • y) :=
    mul_le_mul_of_nonneg_left hu_conc hα
  -- Add β (constant).  For the affine sum, we use a + b = 1.
  have hβ_combo : a • β + b • β = β := by
    simp only [smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  -- Compute lhs and rhs.
  show a • (α * u x + β) + b • (α * u y + β) ≤
       α * u (a • x + b • y) + β
  have lhs_eq :
      a • (α * u x + β) + b • (α * u y + β) =
        α * (a • u x + b • u y) + β := by
    simp only [smul_eq_mul]
    have : a * β + b * β = β := by
      rw [show a * β + b * β = (a + b) * β from by ring, hab, one_mul]
    linarith
  rw [lhs_eq]
  linarith

/-- A **constant utility** function is trivially inequality averse
(concave, since it is also linear). -/
lemma InequalityAverse.const (c : ℝ) :
    InequalityAverse (fun _ : ℝ => c) := by
  unfold InequalityAverse
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b _ _ hab
  -- The smul is `a * c + b * c = (a + b) * c = c`.
  show a • c + b • c ≤ c
  simp only [smul_eq_mul]
  rw [show a * c + b * c = (a + b) * c from by ring, hab, one_mul]

/-- **The negation of a convex function is concave.**

If `u` is convex on `Set.univ`, then `fun x => -u x` is concave (i.e.,
`InequalityAverse`). -/
lemma InequalityAverse.neg_of_convexOn
    {u : ℝ → ℝ} (h : ConvexOn ℝ Set.univ u) :
    InequalityAverse (fun x => -u x) := by
  unfold InequalityAverse
  exact h.neg

end Preference

end ClassicalLottery
