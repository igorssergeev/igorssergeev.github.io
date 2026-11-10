import Mathlib
import GF2Reduced

/-!
# Theorem 2 of Section 5: the independence index and the reduced complexity

Formalization of Theorem 2 of I. S. Sergeev, *Lower bounds on the additive complexity of
linear operators and bilinear algorithms* (Section 5), on top of the Section 1--2 material of
`GF2Reduced.lean` (vectors, chains, extended chains, the type of a step and the
reduced complexity `L*`).  Apart from `Mathlib` and `GF2Reduced.lean` the file has no
imports.

## Statement

The main result is `theorem2`.  Let `c` be an extended addition chain over `m` variables with
reduced complexity `c.reducedComplexity`, and let `B` be a finite set of row vectors computed by
`c` (`c.ComputesVecs B`: every row of `B` is an output of the chain and has type `0`).  Put
`C₀ = B ∪ γI_m`, where the rows of `I_m` are the unit vectors of the essential coordinates, and
let `inputSlack c.aux γ` be `|aux|` for `γ = 1` and `m` for `γ = 0` (this is `(1-γ)m` in the
paper's setting `aux = ∅`).  Assume that no row of `B` has weight `1`, that `k ≥ 2` and
`ind C₀ ≥ 2k + 2`, and that `m ≤ |B|`.  Then

`|B| + (2k-2)/(2k+1) · |B|^(k/(k+1)) - inputSlack c.aux γ ≤ L*(c)`.

## Organization

* The primitives -- vectors `Vec`, basis vectors `basisVec`, the chain pool `chainPool`,
  projections `proj`, weights `weight`, extended chains `ExtChain` with their types and reduced
  complexity `ExtChain.reducedComplexity` -- are those of `GF2Reduced.lean`.
* This file proves Section 5: the unit vectors and the set `C₀ = B ∪ γI_m`, the hierarchy of
  sets `Bᵢ`, `Cᵢ`, the canonical decomposition of a row of `Bᵢ`, the properties established in
  points 1 and 2 of the proof, and the counting argument of point 3 in its two cases
  (`case31`, `case32`), concluding with `theorem2`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

/-! ### 

This section provides the Moore bound of Theorem 1 of
Alon--Hoory--Linial, the independence index `Indep`/`AllIndep`/`ind`, the Minkowski sums
`minkowski`/`msum` and Lemma 4 (`lemma4`), which is what the proof of Theorem 2 invokes. -/

namespace MooreBound

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]


/-!
## Part 1. Non-backtracking walks

A non-backtracking walk is encoded as a sequence of darts in which consecutive
darts are adjacent and no dart is followed by its opposite.  The encoding is
indexed by the starting dart and by the length, which makes the successor
structure definitional.

## Main definitions and results

* `MooreBound.Succ` : the darts that can follow a given dart;
* `MooreBound.NbWalk` : non-backtracking walks, encoded as sequences of darts;
* `MooreBound.NbWalk.darts` : the darts of a walk, excluding the starting dart;
* `MooreBound.NbWalk.at`, `MooreBound.NbWalk.endV`, `MooreBound.NbWalk.lastDart` :
  the dart at a given time, the final vertex and the final dart;
* `MooreBound.NbWalk.toWalkFrom`, `MooreBound.NbWalk.toWalk` : the underlying walk
  of the graph, as a walk starting at a vertex or at a dart.
-/

set_option maxHeartbeats 1000000

/-! ### Non-backtracking walks on darts -/

section Walks

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The set of possible successors of a dart `e = uv⃗`, namely the vertices `w`
adjacent to `v` with `w ≠ u`. -/
abbrev Succ (e : G.Dart) : Type u := {w : V // G.Adj e.snd w ∧ w ≠ e.fst}

instance (e : G.Dart) : Fintype (Succ G e) := by unfold Succ; infer_instance

instance (e : G.Dart) : DecidableEq (Succ G e) := by unfold Succ; infer_instance

/-- The dart `vw⃗` determined by a successor `w` of the dart `e = uv⃗`. -/
@[reducible] def nextDart (e : G.Dart) (w : Succ G e) : G.Dart := ⟨(e.snd, w.1), w.2.1⟩

@[simp] theorem nextDart_fst (e : G.Dart) (w : Succ G e) : (nextDart G e w).fst = e.snd := rfl
@[simp] theorem nextDart_snd (e : G.Dart) (w : Succ G e) : (nextDart G e w).snd = w.1 := rfl
@[simp] theorem nextDart_toProd (e : G.Dart) (w : Succ G e) :
    (nextDart G e w).toProd = (e.snd, w.1) := rfl

/-- Non-backtracking walks of length `l` starting with the dart `e`, encoded as the
sequence of the `l` following darts. -/
@[reducible] def NbWalk : G.Dart → ℕ → Type u
  | e, 0 => PUnit
  | e, l + 1 => Sigma fun w : Succ G e => NbWalk (nextDart G e w) l

def NbWalk.instFintype : ∀ (e : G.Dart) (l : ℕ), Fintype (NbWalk G e l)
  | e, 0 => inferInstanceAs (Fintype PUnit)
  | e, l + 1 =>
      letI : ∀ w : Succ G e, Fintype (NbWalk G (nextDart G e w) l) :=
        fun w => NbWalk.instFintype (nextDart G e w) l
      inferInstanceAs (Fintype (Sigma fun w : Succ G e => NbWalk G (nextDart G e w) l))
attribute [instance] NbWalk.instFintype

/-- The list of darts traversed after the initial dart. -/
def NbWalk.darts : (e : G.Dart) → (l : ℕ) → NbWalk G e l → List G.Dart
  | e, 0, _ => []
  | e, l + 1, ω => nextDart G e ω.1 :: NbWalk.darts (nextDart G e ω.1) l ω.2

@[simp] theorem NbWalk.darts_zero (e : G.Dart) (ω : NbWalk G e 0) :
    NbWalk.darts G e 0 ω = [] := rfl

theorem NbWalk.darts_succ (e : G.Dart) (l : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.darts G e (l + 1) ω =
      nextDart G e ω.1 :: NbWalk.darts G (nextDart G e ω.1) l ω.2 := rfl

@[simp] theorem NbWalk.darts_length (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.darts G e l ω).length = l := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih => rw [NbWalk.darts_succ, List.length_cons, ih]

/-- The vertex at which a non-backtracking walk ends. -/
@[reducible] def NbWalk.endV : (e : G.Dart) → (l : ℕ) → NbWalk G e l → V
  | e, 0, _ => e.snd
  | e, l + 1, ω => NbWalk.endV (nextDart G e ω.1) l ω.2

@[simp] theorem NbWalk.endV_zero (e : G.Dart) (ω : NbWalk G e 0) :
    NbWalk.endV G e 0 ω = e.snd := rfl

theorem NbWalk.endV_succ (e : G.Dart) (l : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.endV G e (l + 1) ω = NbWalk.endV G (nextDart G e ω.1) l ω.2 := rfl

/-- The last dart of a non-backtracking walk (the initial dart for length zero). -/
def NbWalk.lastDart : (e : G.Dart) → (l : ℕ) → NbWalk G e l → G.Dart
  | e, 0, _ => e
  | e, l + 1, ω => NbWalk.lastDart (nextDart G e ω.1) l ω.2

@[simp] theorem NbWalk.lastDart_zero (e : G.Dart) (ω : NbWalk G e 0) :
    NbWalk.lastDart G e 0 ω = e := rfl

theorem NbWalk.lastDart_succ (e : G.Dart) (l : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.lastDart G e (l + 1) ω = NbWalk.lastDart G (nextDart G e ω.1) l ω.2 := rfl

/-- The dart at position `k` of the walk (the initial dart when `k = 0`). -/
def NbWalk.at : (e : G.Dart) → (l : ℕ) → (k : ℕ) → NbWalk G e l → G.Dart
  | e, 0, _, _ => e
  | e, l + 1, 0, _ => e
  | e, l + 1, k + 1, ω => NbWalk.at (nextDart G e ω.1) l k ω.2

@[simp] theorem NbWalk.at_zero (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    NbWalk.at G e l 0 ω = e := by
  cases l with
  | zero => rfl
  | succ l => rfl

theorem NbWalk.at_succ (e : G.Dart) (l k : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.at G e (l + 1) (k + 1) ω = NbWalk.at G (nextDart G e ω.1) l k ω.2 := rfl

theorem NbWalk.at_lastDart (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    NbWalk.at G e l l ω = NbWalk.lastDart G e l ω := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih =>
      rw [NbWalk.at_succ, NbWalk.lastDart_succ, ih]

/-- The darts of a walk, including the initial dart. -/
def NbWalk.allDarts (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) : List G.Dart :=
  e :: NbWalk.darts G e l ω

@[simp] theorem NbWalk.allDarts_length (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.allDarts G e l ω).length = l + 1 := by
  simp [NbWalk.allDarts]

@[simp] theorem NbWalk.allDarts_zero (e : G.Dart) (ω : NbWalk G e 0) :
    NbWalk.allDarts G e 0 ω = [e] := rfl


/-- The same non-backtracking walk, seen as a walk of the graph starting at the
*second* vertex of the initial dart (i.e. with the initial dart dropped). -/
def NbWalk.toWalkFrom : (e : G.Dart) → (l : ℕ) → (ω : NbWalk G e l) →
    G.Walk e.snd (NbWalk.endV G e l ω)
  | _, 0, _ => SimpleGraph.Walk.nil
  | e, l + 1, ω =>
      SimpleGraph.Walk.cons ω.1.2.1 (NbWalk.toWalkFrom (nextDart G e ω.1) l ω.2)

@[simp] theorem NbWalk.toWalkFrom_length (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.toWalkFrom G e l ω).length = l := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih =>
      rw [show NbWalk.toWalkFrom G e (l + 1) ω =
        SimpleGraph.Walk.cons ω.1.2.1 (NbWalk.toWalkFrom G (nextDart G e ω.1) l ω.2)
        from rfl, SimpleGraph.Walk.length_cons, ih]

theorem NbWalk.toWalkFrom_darts (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.toWalkFrom G e l ω).darts = NbWalk.darts G e l ω := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih =>
      rw [show NbWalk.toWalkFrom G e (l + 1) ω =
        SimpleGraph.Walk.cons ω.1.2.1 (NbWalk.toWalkFrom G (nextDart G e ω.1) l ω.2)
        from rfl, SimpleGraph.Walk.darts_cons, ih, NbWalk.darts_succ]

/-- Two non-backtracking walks with the same sequence of darts are equal. -/
theorem NbWalk.darts_injective (e : G.Dart) (l : ℕ) :
    Function.Injective (NbWalk.darts G e l) := by
  induction l generalizing e with
  | zero =>
      intro a b _
      exact Subsingleton.elim a b
  | succ l ih =>
      rintro ⟨w, ω⟩ ⟨w', ω'⟩ h
      rw [NbWalk.darts_succ, NbWalk.darts_succ, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hw : w = w' := by
        have := congrArg SimpleGraph.Dart.toProd h1
        simp only [nextDart_toProd, Prod.mk.injEq] at this
        exact Subtype.ext this.2
      subst hw
      have h3 : ω = ω' := ih (nextDart G e w) h2
      subst h3
      rfl

/-- The non-backtracking walk as a walk of the graph, with `l + 1` edges starting
at the first vertex of the initial dart. -/
def NbWalk.toWalk : (e : G.Dart) → (l : ℕ) → (ω : NbWalk G e l) →
    G.Walk e.fst (NbWalk.endV G e l ω)
  | e, 0, _ => SimpleGraph.Walk.cons e.adj SimpleGraph.Walk.nil
  | e, l + 1, ω => SimpleGraph.Walk.cons e.adj (NbWalk.toWalk (nextDart G e ω.1) l ω.2)

@[simp] theorem NbWalk.toWalk_length (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.toWalk G e l ω).length = l + 1 := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih =>
      rw [show NbWalk.toWalk G e (l + 1) ω =
        SimpleGraph.Walk.cons e.adj (NbWalk.toWalk G (nextDart G e ω.1) l ω.2) from rfl,
        SimpleGraph.Walk.length_cons, ih]

theorem NbWalk.darts_toWalk (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    (NbWalk.toWalk G e l ω).darts = e :: NbWalk.darts G e l ω := by
  induction l generalizing e with
  | zero => rfl
  | succ l ih =>
      rw [show NbWalk.toWalk G e (l + 1) ω =
        SimpleGraph.Walk.cons e.adj (NbWalk.toWalk G (nextDart G e ω.1) l ω.2) from rfl,
        SimpleGraph.Walk.darts_cons, ih, NbWalk.darts_succ]

end Walks


/-!
## Part 2. Transition probabilities

The weight of a non-backtracking walk is the product of the reciprocals of
`deg - 1` over its transitions.  The weights of the walks leaving a fixed dart
sum to one, and the reciprocal weight `Q` multiplies `wt` to one.

## Main definitions and results

* `MooreBound.Nb` : the number of non-backtracking walks of length `l` from a dart;
* `MooreBound.Nb_succ` : `Nb e (l + 1) = ∑ w, Nb (nextDart e w) l`;
* `MooreBound.card_succ` : a dart has `deg - 1` successors;
* `MooreBound.NbWalk.wt` : the transition probability of a walk;
* `MooreBound.NbWalk.wt_sum` : the weights of the walks leaving a dart sum to one;
* `MooreBound.NbWalk.Q`, `MooreBound.NbWalk.Q_mul_wt` : the reciprocal weight,
  with `Q ω * wt ω = 1`.
-/

set_option maxHeartbeats 1000000

section Walks

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Counting walks and successors -/

/-- The number of non-backtracking walks of `l` steps starting at the dart `e`. -/
def Nb (e : G.Dart) (l : ℕ) : ℕ := Fintype.card (NbWalk G e l)

@[simp] theorem Nb_zero (e : G.Dart) : Nb G e 0 = 1 := rfl

theorem Nb_succ (e : G.Dart) (l : ℕ) :
    Nb G e (l + 1) = ∑ w : Succ G e, Nb G (nextDart G e w) l := by
  unfold Nb
  change Fintype.card (Sigma fun w : Succ G e => NbWalk G (nextDart G e w) l) = _
  rw [Fintype.card_sigma]

/-- The successor set of a dart has cardinality `deg - 1`. -/
theorem card_succ (e : G.Dart) : Fintype.card (Succ G e) + 1 = G.degree e.snd := by
  have h1 : Fintype.card (Succ G e) = (G.neighborFinset e.snd \ {e.fst}).card := by
    unfold Succ
    rw [Fintype.card_subtype]
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [h1, ← SimpleGraph.card_neighborFinset_eq_degree G e.snd]
  rw [Finset.sdiff_singleton_eq_erase]
  exact Finset.card_erase_add_one
    (by rw [SimpleGraph.mem_neighborFinset]; exact e.adj.symm)

theorem card_succ' (e : G.Dart) : Fintype.card (Succ G e) = G.degree e.snd - 1 :=
  Nat.eq_sub_of_add_eq (card_succ G e)

/-! ### The walk weights -/

/-- Weight of a walk: the product of `1 / (deg - 1)` over its transitions. -/
 noncomputable def NbWalk.wt : (e : G.Dart) → (l : ℕ) → NbWalk G e l → ℝ
  | e, 0, _ => 1
  | e, l + 1, ω => (1 / ((G.degree e.snd : ℝ) - 1)) * NbWalk.wt (nextDart G e ω.1) l ω.2

/-- The reciprocal weight `Q`: the product of `(deg - 1)` over its transitions. -/
noncomputable def NbWalk.Q : (e : G.Dart) → (l : ℕ) → NbWalk G e l → ℝ
  | e, 0, _ => 1
  | e, l + 1, ω => ((G.degree e.snd : ℝ) - 1) * NbWalk.Q (nextDart G e ω.1) l ω.2

theorem NbWalk.wt_succ (e : G.Dart) (l : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.wt G e (l + 1) ω =
      (1 / ((G.degree e.snd : ℝ) - 1)) * NbWalk.wt G (nextDart G e ω.1) l ω.2 := rfl

theorem NbWalk.Q_succ (e : G.Dart) (l : ℕ) (ω : NbWalk G e (l + 1)) :
    NbWalk.Q G e (l + 1) ω =
      ((G.degree e.snd : ℝ) - 1) * NbWalk.Q G (nextDart G e ω.1) l ω.2 := rfl

theorem degree_sub_one_pos (hdeg : ∀ v, 2 ≤ G.degree v) (v : V) :
    (0 : ℝ) < (G.degree v : ℝ) - 1 := by
  have h : (2 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hdeg v
  linarith

theorem degree_sub_one_ne (hdeg : ∀ v, 2 ≤ G.degree v) (v : V) :
    ((G.degree v : ℝ) - 1) ≠ 0 := ne_of_gt (degree_sub_one_pos G hdeg v)

/-- The weights of all non-backtracking walks from a fixed dart sum to one. -/
theorem NbWalk.wt_sum (hdeg : ∀ v, 2 ≤ G.degree v) (e : G.Dart) (l : ℕ) :
    ∑ ω : NbWalk G e l, NbWalk.wt G e l ω = 1 := by
  induction l generalizing e with
  | zero => simp [NbWalk.wt]
  | succ l ih =>
      change (∑ x : Sigma fun w : Succ G e => NbWalk G (nextDart G e w) l,
        NbWalk.wt G e (l + 1) x) = 1
      rw [Fintype.sum_sigma]
      have h1 : ∀ w : Succ G e,
          (∑ ω' : NbWalk G (nextDart G e w) l, NbWalk.wt G e (l + 1) ⟨w, ω'⟩)
            = 1 / ((G.degree e.snd : ℝ) - 1) := by
        intro w
        rw [Finset.sum_congr rfl (fun ω' _ => NbWalk.wt_succ G e l ⟨w, ω'⟩)]
        rw [← Finset.mul_sum, ih (nextDart G e w), mul_one]
      rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      have hcard : ((Fintype.card (Succ G e) : ℕ) : ℝ) = (G.degree e.snd : ℝ) - 1 := by
        have h := card_succ G e
        have h2 : ((Fintype.card (Succ G e) : ℕ) : ℝ) + 1 = (G.degree e.snd : ℝ) := by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
        linarith
      rw [hcard, mul_one_div, div_self (degree_sub_one_ne G hdeg e.snd)]

/-- `Q` is the reciprocal of the weight of a walk. -/
theorem NbWalk.Q_mul_wt (hdeg : ∀ v, 2 ≤ G.degree v) (e : G.Dart) (l : ℕ)
    (ω : NbWalk G e l) : NbWalk.Q G e l ω * NbWalk.wt G e l ω = 1 := by
  induction l generalizing e with
  | zero => simp [NbWalk.Q, NbWalk.wt]
  | succ l ih =>
      rw [NbWalk.Q_succ, NbWalk.wt_succ]
      have hd := degree_sub_one_ne G hdeg e.snd
      calc ((G.degree e.snd : ℝ) - 1) * NbWalk.Q G (nextDart G e ω.1) l ω.2 *
              ((1 / ((G.degree e.snd : ℝ) - 1)) * NbWalk.wt G (nextDart G e ω.1) l ω.2)
            = (((G.degree e.snd : ℝ) - 1) * (1 / ((G.degree e.snd : ℝ) - 1))) *
              (NbWalk.Q G (nextDart G e ω.1) l ω.2 *
                NbWalk.wt G (nextDart G e ω.1) l ω.2) := by ring
        _ = 1 := by
          rw [ih (nextDart G e ω.1) ω.2, mul_one]
          field_simp

theorem NbWalk.wt_pos (hdeg : ∀ v, 2 ≤ G.degree v) (e : G.Dart) (l : ℕ)
    (ω : NbWalk G e l) : 0 < NbWalk.wt G e l ω := by
  induction l generalizing e with
  | zero => simp [NbWalk.wt]
  | succ l ih =>
      rw [NbWalk.wt_succ]
      exact mul_pos (one_div_pos.mpr (degree_sub_one_pos G hdeg e.snd))
        (ih (nextDart G e ω.1) ω.2)

theorem NbWalk.Q_pos (hdeg : ∀ v, 2 ≤ G.degree v) (e : G.Dart) (l : ℕ)
    (ω : NbWalk G e l) : 0 < NbWalk.Q G e l ω := by
  induction l generalizing e with
  | zero => simp [NbWalk.Q]
  | succ l ih =>
      rw [NbWalk.Q_succ]
      exact mul_pos (degree_sub_one_pos G hdeg e.snd) (ih (nextDart G e ω.1) ω.2)


end Walks


/-!
## Part 3. The transfer operator on darts

A dart has as many predecessors as successors, and dropping the first dart of a
non-backtracking walk is a bijection between the walks of length `l + 1` leaving
a dart and the walks of length `l` leaving its successors.  Consequently the
non-backtracking transition matrix on darts is column stochastic, and the uniform
distribution on darts is stationary.

## Main definitions and results

* `MooreBound.card_preds` : a dart has `deg - 1` predecessors;
* `MooreBound.sum_succ_eq` : the non-backtracking transition matrix is column
  stochastic;
* `MooreBound.nu` : the expected number of visits to a dart at time `k`, starting
  from a uniformly random dart;
* `MooreBound.nu_eq_one` : the position after `k` steps is uniform on the darts.
-/

set_option maxHeartbeats 1000000

/-! ### Counting darts -/

section Walks

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The second vertex of the reverse of a dart. -/
theorem snd_symm (d : G.Dart) : d.symm.snd = d.fst := by
  have := SimpleGraph.Dart.fst_symm d.symm
  rwa [SimpleGraph.Dart.symm_symm] at this

/-- Reversing orientation is an involution, in `toProd` form. -/
theorem symm_eq_iff (d e : G.Dart) (h1 : d.fst = e.snd) (h2 : d.snd = e.fst) :
    d = e.symm := by
  have hh : d.toProd = e.symm.toProd := by
    rw [SimpleGraph.Dart.symm_toProd]
    exact Prod.ext h1 h2
  exact SimpleGraph.Dart.ext _ _ hh

/-- The darts whose second vertex is `v` are `deg v` in number. -/
theorem card_snd_fiber (v : V) :
    (univ.filter (fun d : G.Dart => d.snd = v)).card = G.degree v := by
  have hinj : Function.Injective (SimpleGraph.Dart.symm (G := G)) :=
    SimpleGraph.Dart.symm_involutive.injective
  have himg : (univ.filter (fun d : G.Dart => d.fst = v)).image SimpleGraph.Dart.symm
      = univ.filter (fun d : G.Dart => d.snd = v) := by
    ext d
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      rwa [snd_symm]
    · intro hd
      exact ⟨d.symm, by rwa [SimpleGraph.Dart.fst_symm], SimpleGraph.Dart.symm_symm d⟩
  rw [← himg, card_image_of_injective _ hinj, SimpleGraph.dart_fst_fiber_card_eq_degree]

/-- The darts `e` with `e.snd = f.fst` other than the reverse of `f` are `deg f.fst - 1`
in number. -/
theorem card_preds (f : G.Dart) :
    (univ.filter (fun e : G.Dart => e.snd = f.fst ∧ e.fst ≠ f.snd)).card
      = G.degree f.fst - 1 := by
  have hQ : (univ.filter (fun e : G.Dart => e.snd = f.fst))
      = insert f.symm (univ.filter (fun e : G.Dart => e.snd = f.fst ∧ e.fst ≠ f.snd)) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro he
      by_cases h : e.fst = f.snd
      · exact Or.inl (symm_eq_iff G e f h he)
      · exact Or.inr ⟨he, h⟩
    · rintro (rfl | ⟨h1, _⟩)
      · rw [snd_symm]
      · exact h1
  have hnot : f.symm ∉ univ.filter (fun e : G.Dart => e.snd = f.fst ∧ e.fst ≠ f.snd) := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro _
    rw [SimpleGraph.Dart.fst_symm]
    simp
  have hcard : (insert f.symm
      (univ.filter (fun e : G.Dart => e.snd = f.fst ∧ e.fst ≠ f.snd))).card
      = G.degree f.fst := by
    rw [← hQ]; exact card_snd_fiber G f.fst
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

/-! ### Summing over successors -/

/-- Summing over the successors of a dart is summing over the darts leaving its head,
except for the reverse dart. -/
theorem sum_succ_eq_sum_filter (e : G.Dart) (h : G.Dart → ℝ) :
    (∑ w : Succ G e, h (nextDart G e w))
      = ∑ f ∈ univ.filter (fun f : G.Dart => f.fst = e.snd ∧ f.snd ≠ e.fst), h f := by
  refine Finset.sum_bij (fun w _ => nextDart G e w) ?_ ?_ ?_ ?_
  · intro w _
    simp only [mem_filter, mem_univ, true_and]
    exact w.2.2
  · intro w₁ _ w₂ _ hEq
    have hp := congrArg SimpleGraph.Dart.toProd hEq
    simp only [nextDart_toProd, Prod.mk.injEq] at hp
    exact Subtype.ext hp.2
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨h1, h2⟩ := hf
    refine ⟨⟨f.snd, ?_, h2⟩, mem_univ _, ?_⟩
    · rw [← h1]; exact f.adj
    · have hh : (nextDart G e (⟨f.snd, by rw [← h1]; exact f.adj, h2⟩ : Succ G e)).toProd
          = f.toProd := by
        apply Prod.ext
        · rw [nextDart_toProd]; exact h1.symm
        · rw [nextDart_toProd]
      exact SimpleGraph.Dart.ext _ _ hh
  · intro w _; rfl

/-- **Column stochasticity.** Averaging the transition probabilities over all darts
starting a walk gives the average over all darts of the target function. -/
theorem sum_succ_eq (hdeg : ∀ v, 2 ≤ G.degree v) (h : G.Dart → ℝ) :
    (∑ e : G.Dart, ∑ w : Succ G e, (1 / ((G.degree e.snd : ℝ) - 1)) * h (nextDart G e w))
      = ∑ f : G.Dart, h f := by
  have step1 : ∀ e : G.Dart,
      (∑ w : Succ G e, (1 / ((G.degree e.snd : ℝ) - 1)) * h (nextDart G e w))
      = ∑ f : G.Dart,
          if (f.fst = e.snd ∧ f.snd ≠ e.fst) then
            (1 / ((G.degree e.snd : ℝ) - 1)) * h f else 0 := by
    intro e
    rw [sum_succ_eq_sum_filter G e (fun g => (1 / ((G.degree e.snd : ℝ) - 1)) * h g),
      Finset.sum_filter]
  have step2 : ∀ (f : G.Dart) (e : G.Dart),
      (if (f.fst = e.snd ∧ f.snd ≠ e.fst) then
          (1 / ((G.degree e.snd : ℝ) - 1)) * h f else 0)
        = if (e.snd = f.fst ∧ e.fst ≠ f.snd) then
            (1 / ((G.degree f.fst : ℝ) - 1)) * h f else 0 := by
    intro f e
    by_cases c : (f.fst = e.snd ∧ f.snd ≠ e.fst)
    · have hd : e.snd = f.fst := c.1.symm
      have c' : (e.snd = f.fst ∧ e.fst ≠ f.snd) := ⟨hd, fun hh => c.2 hh.symm⟩
      rw [ite_eq_left c, ite_eq_left c', hd]
    · have c' : ¬ (e.snd = f.fst ∧ e.fst ≠ f.snd) :=
        fun hh => c ⟨hh.1.symm, fun hh2 => hh.2 hh2.symm⟩
      rw [ite_eq_right c, ite_eq_right c']
  calc (∑ e : G.Dart, ∑ w : Succ G e, (1 / ((G.degree e.snd : ℝ) - 1)) * h (nextDart G e w))
      = ∑ e : G.Dart, ∑ f : G.Dart,
          if (f.fst = e.snd ∧ f.snd ≠ e.fst) then
            (1 / ((G.degree e.snd : ℝ) - 1)) * h f else 0 :=
        Finset.sum_congr rfl (fun e _ => step1 e)
    _ = ∑ f : G.Dart, ∑ e : G.Dart,
          if (f.fst = e.snd ∧ f.snd ≠ e.fst) then
            (1 / ((G.degree e.snd : ℝ) - 1)) * h f else 0 := Finset.sum_comm
    _ = ∑ f : G.Dart, h f := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Finset.sum_congr rfl (fun e _ => step2 f e), ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul]
        have hc : ((univ.filter (fun e : G.Dart => e.snd = f.fst ∧ e.fst ≠ f.snd)).card : ℝ)
            = (G.degree f.fst : ℝ) - 1 := by
          rw [card_preds G f]
          have h2 : 1 ≤ G.degree f.fst := by have := hdeg f.fst; omega
          rw [Nat.cast_sub h2, Nat.cast_one]
        rw [hc]
        field_simp [degree_sub_one_ne G hdeg f.fst]

/-! ### The visit distribution -/

/-- Weighted number of walks of length `l` from `e` that are at the dart `f` at time `k`. -/
noncomputable def nuFrom (f : G.Dart) (e : G.Dart) (l k : ℕ) : ℝ :=
  ∑ ω : NbWalk G e l, if NbWalk.at G e l k ω = f then NbWalk.wt G e l ω else 0

/-- Expected number of visits to the dart `f` at time `k`, starting uniformly. -/
noncomputable def nu (f : G.Dart) (l k : ℕ) : ℝ := ∑ e, nuFrom G f e l k

theorem nuFrom_succ (e : G.Dart) (l k : ℕ) (f : G.Dart) :
    nuFrom G f e (l + 1) (k + 1)
      = ∑ w : Succ G e,
          (1 / ((G.degree e.snd : ℝ) - 1)) * nuFrom G f (nextDart G e w) l k := by
  unfold nuFrom
  change (∑ x : Sigma (fun w : Succ G e => NbWalk G (nextDart G e w) l),
      (if NbWalk.at G e (l + 1) (k + 1) x = f then NbWalk.wt G e (l + 1) x else 0)) = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω' _ => ?_)
  rw [NbWalk.at_succ, NbWalk.wt_succ]
  by_cases h : NbWalk.at G (nextDart G e w) l k ω' = f
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

theorem nu_succ (hdeg : ∀ v, 2 ≤ G.degree v) (l k : ℕ) (hk : k < l) (f : G.Dart) :
    nu G f (l + 1) (k + 1) = nu G f l k := by
  unfold nu
  rw [Finset.sum_congr rfl (fun e _ => nuFrom_succ G e l k f)]
  exact sum_succ_eq G hdeg (fun g => nuFrom G f g l k)

theorem nu_zero (hdeg : ∀ v, 2 ≤ G.degree v) (l : ℕ) (f : G.Dart) : nu G f l 0 = 1 := by
  have key : ∀ e : G.Dart, nuFrom G f e l 0 = if e = f then 1 else 0 := by
    intro e
    unfold nuFrom
    by_cases h : e = f
    · subst h
      rw [ite_eq_left rfl]
      have : ∀ ω : NbWalk G e l,
          (if NbWalk.at G e l 0 ω = e then NbWalk.wt G e l ω else 0) = NbWalk.wt G e l ω := by
        intro ω; rw [NbWalk.at_zero]; simp
      rw [Finset.sum_congr rfl (fun ω _ => this ω)]
      exact NbWalk.wt_sum G hdeg e l
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero (fun ω _ => ?_)
      rw [ite_eq_right]
      intro hh
      rw [NbWalk.at_zero] at hh
      exact h hh
  unfold nu
  rw [Finset.sum_congr rfl (fun e _ => key e), Finset.sum_ite_eq', ite_eq_left (mem_univ f)]

/-- **Stationarity.** Starting from the uniform distribution on darts, the non-backtracking
walk is uniformly distributed at every time step. -/
theorem nu_eq_one (hdeg : ∀ v, 2 ≤ G.degree v) {l k : ℕ} (hk : k < l) (f : G.Dart) :
    nu G f l k = 1 := by
  induction k generalizing l with
  | zero => exact nu_zero G hdeg l f
  | succ k ih =>
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      rw [nu_succ G hdeg l' k (by omega) f]
      exact ih (by omega)

end Walks


/-!
## Part 4. The arithmetic-geometric mean bound on the number of walks

This section contains the analytic heart of the proof: the number `Nl` of
non-backtracking walks of length `l` from a uniformly random initial dart is
bounded from below by `Λ ^ l`, where `Λ = ∏_v (d_v - 1) ^ (d_v / nd)`.
The bound is the weighted arithmetic-geometric mean inequality applied to the
probabilities `p(ω)` of the walks, combined with the stationarity of the uniform
distribution on darts (`nu_eq_one`).

## Main definitions and results

* `MooreBound.nDart` : the number of directed edges of `G`;
* `MooreBound.Nl` : the average number of non-backtracking walks of length `l`;
* `MooreBound.Lam` : the growth rate `Λ = ∏_v (d_v - 1) ^ (d_v / nd)`;
* `MooreBound.NbWalk.Q_eq_prod` : `Q` is the product of the `deg - 1` along a walk;
* `MooreBound.Lam_pow_le_Nl` : `Λ ^ l ≤ Nl l`.
-/


section Counts

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of darts (directed edges) of `G`. -/
def nDart : ℕ := Fintype.card G.Dart

theorem nDart_pos [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) : 0 < nDart G := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h2 : 0 < G.degree v := by
    have h := hdeg v
    omega
  obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj G v).1 h2
  rw [nDart, Fintype.card_pos_iff]
  exact ⟨⟨(v, w), hw⟩⟩

/-- The expected number of non-backtracking walks of length `l` starting at a
uniformly random dart. -/
noncomputable def Nl (l : ℕ) : ℝ :=
  (1 / (nDart G : ℝ)) * ∑ e : G.Dart, (Nb G e l : ℝ)

/-- The base `Λ` of the exponential growth of `Nl`, namely
`Λ = ∏_v (deg v - 1) ^ (deg v / nd)`. -/
noncomputable def Lam : ℝ :=
  ∏ v : V, ((G.degree v : ℝ) - 1) ^ ((G.degree v : ℝ) / (nDart G : ℝ))

/-- A product of nonnegative reals raised to a nonnegative power is the product
of the powers. -/
theorem finset_prod_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (z : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hz : 0 ≤ z) :
    (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, f i ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.mul_rpow (hf a (Finset.mem_insert_self a s))
          (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- A product of powers with the same positive base is a power of the sum of the
exponents. -/
theorem finset_prod_rpow_sum {ι : Type*} (s : Finset ι) (a : ℝ) (ha : 0 < a) (g : ι → ℝ) :
    (∏ i ∈ s, a ^ g i) = a ^ ∑ i ∈ s, g i :=
  (Real.rpow_sum_of_pos ha g s).symm

/-- `Q` is the product of `deg - 1` over the vertices at which the walk sits,
i.e. over the heads of the darts `e, e₁, …, e_{l-1}`. -/
theorem NbWalk.Q_eq_prod (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    NbWalk.Q G e l ω
      = ∏ j ∈ Finset.range l, ((G.degree (NbWalk.at G e l j ω).snd : ℝ) - 1) := by
  induction l generalizing e with
  | zero => simp [NbWalk.Q]
  | succ l ih =>
      rw [NbWalk.Q_succ, Finset.prod_range_succ']
      have h0 : ((G.degree (NbWalk.at G e (l + 1) 0 ω).snd : ℝ) - 1)
          = ((G.degree e.snd : ℝ) - 1) := by rw [NbWalk.at_zero]
      rw [h0]
      have h1 : (∏ k ∈ Finset.range l,
          ((G.degree (NbWalk.at G e (l + 1) (k + 1) ω).snd : ℝ) - 1))
          = ∏ k ∈ Finset.range l,
            ((G.degree (NbWalk.at G (nextDart G e ω.1) l k ω.2).snd : ℝ) - 1) := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [NbWalk.at_succ]
      rw [h1, ← ih (nextDart G e ω.1) ω.2, mul_comm]

/-- **The AM–GM bound.** The average number of non-backtracking walks of length
`l` grows at least like `Λ ^ l`. -/
theorem Lam_pow_le_Nl [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) (l : ℕ) :
    Lam G ^ l ≤ Nl G l := by
  classical
  have hnd : 0 < nDart G := nDart_pos G hdeg
  have hndR : (0 : ℝ) < (nDart G : ℝ) := by exact_mod_cast hnd
  have hndne : (nDart G : ℝ) ≠ 0 := ne_of_gt hndR
  have hbase : ∀ v : V, 0 ≤ (G.degree v : ℝ) - 1 := by
    intro v
    have h : (2 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hdeg v
    linarith
  -- the weights are nonnegative and sum to one
  have hw : ∀ i : (Σ e : G.Dart, NbWalk G e l),
      0 ≤ (1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2 := by
    intro i
    exact mul_nonneg (by positivity) (le_of_lt (NbWalk.wt_pos G hdeg i.1 l i.2))
  have hwsum : ∑ i : (Σ e : G.Dart, NbWalk G e l),
      (1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2 = 1 := by
    rw [Fintype.sum_sigma]
    have h1 : ∀ e : G.Dart,
        ∑ ω : NbWalk G e l, (1 / (nDart G : ℝ)) * NbWalk.wt G e l ω
          = 1 / (nDart G : ℝ) := by
      intro e
      rw [← Finset.mul_sum, NbWalk.wt_sum G hdeg e l, mul_one]
    rw [Finset.sum_congr rfl (fun e _ => h1 e), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [show ((Fintype.card G.Dart : ℕ) : ℝ) = (nDart G : ℝ) from by rw [nDart]]
    field_simp
  have hz : ∀ i : (Σ e : G.Dart, NbWalk G e l), 0 ≤ NbWalk.Q G i.1 l i.2 :=
    fun i => le_of_lt (NbWalk.Q_pos G hdeg i.1 l i.2)
  have hamgm := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l))
    (fun i => (1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)
    (fun i => NbWalk.Q G i.1 l i.2) (fun i _ => hw i) hwsum (fun i _ => hz i)
  -- right-hand side
  have hterm : ∀ (e : G.Dart) (ω : NbWalk G e l),
      ((1 / (nDart G : ℝ)) * NbWalk.wt G e l ω) * NbWalk.Q G e l ω
        = 1 / (nDart G : ℝ) := by
    intro e ω
    rw [mul_assoc, mul_comm (NbWalk.wt G e l ω) (NbWalk.Q G e l ω),
      NbWalk.Q_mul_wt G hdeg, mul_one]
  have hR : ∑ i : (Σ e : G.Dart, NbWalk G e l),
      ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2) * NbWalk.Q G i.1 l i.2
        = Nl G l := by
    rw [Fintype.sum_sigma]
    have h1 : ∀ e : G.Dart,
        ∑ ω : NbWalk G e l, (1 / (nDart G : ℝ)) = (Nb G e l : ℝ) * (1 / (nDart G : ℝ)) := by
      intro e
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nb]
    rw [Finset.sum_congr rfl (fun e _ =>
      Finset.sum_congr rfl (fun ω _ => hterm e ω)), Finset.sum_congr rfl (fun e _ => h1 e),
      ← Finset.sum_mul, Nl, mul_comm]
  -- left-hand side
  have hstep1 : ∀ i : (Σ e : G.Dart, NbWalk G e l),
      (NbWalk.Q G i.1 l i.2) ^ ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)
        = ∏ j ∈ Finset.range l,
            (((G.degree (NbWalk.at G i.1 l j i.2).snd : ℝ) - 1) ^
              ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)) := by
    intro i
    rw [NbWalk.Q_eq_prod]
    exact finset_prod_rpow _ _ _
      (fun j _ => hbase (NbWalk.at G i.1 l j i.2).snd) (hw i)
  -- fibre sum: each dart receives weight `1 / nd`
  have hfiber : ∀ (j : ℕ), j < l → ∀ (f : G.Dart),
      (∑ i ∈ (Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l)).filter
          (fun i => NbWalk.at G i.1 l j i.2 = f),
        (1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2) = 1 / (nDart G : ℝ) := by
    intro j hj f
    have hinner : (∑ i ∈ (Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l)).filter
        (fun i => NbWalk.at G i.1 l j i.2 = f),
        NbWalk.wt G i.1 l i.2) = 1 := by
      rw [Finset.sum_filter, Fintype.sum_sigma]
      have h2 : (∑ e : G.Dart, ∑ ω : NbWalk G e l,
          (if NbWalk.at G e l j ω = f then NbWalk.wt G e l ω else 0))
          = nu G f l j := rfl
      rw [h2, nu_eq_one G hdeg hj f]
    rw [← Finset.mul_sum, hinner, mul_one]
  have hfiber2 : ∀ j ∈ Finset.range l,
      (∏ i : (Σ e : G.Dart, NbWalk G e l),
        (((G.degree (NbWalk.at G i.1 l j i.2).snd : ℝ) - 1) ^
          ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)))
        = ∏ f : G.Dart, (((G.degree f.snd : ℝ) - 1) ^ (1 / (nDart G : ℝ))) := by
    intro j hj
    have key := Finset.prod_fiberwise (Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l))
      (fun i => NbWalk.at G i.1 l j i.2)
      (fun i => (((G.degree (NbWalk.at G i.1 l j i.2).snd : ℝ) - 1) ^
        ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)))
    rw [← key]
    refine Finset.prod_congr rfl (fun f _ => ?_)
    have hconst : ∀ i ∈ (Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l)).filter
        (fun i => NbWalk.at G i.1 l j i.2 = f),
        (((G.degree (NbWalk.at G i.1 l j i.2).snd : ℝ) - 1) ^
          ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2))
          = ((G.degree f.snd : ℝ) - 1) ^ ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    rw [Finset.prod_congr rfl hconst,
      finset_prod_rpow_sum ((Finset.univ : Finset (Σ e : G.Dart, NbWalk G e l)).filter
        (fun i => NbWalk.at G i.1 l j i.2 = f)) ((G.degree f.snd : ℝ) - 1)
        (by have h : (2 : ℝ) ≤ (G.degree f.snd : ℝ) := by exact_mod_cast hdeg f.snd
            linarith)
        (fun i => (1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2)]
    rw [hfiber j (Finset.mem_range.1 hj) f]
  have hlam : (∏ f ∈ (Finset.univ : Finset G.Dart),
      (((G.degree f.snd : ℝ) - 1) ^ (1 / (nDart G : ℝ)))) = Lam G := by
    have key := Finset.prod_fiberwise (Finset.univ : Finset G.Dart) (fun f : G.Dart => f.snd)
      (fun f => (((G.degree f.snd : ℝ) - 1) ^ (1 / (nDart G : ℝ))))
    rw [← key]
    rw [Lam]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    have hconst : ∀ f ∈ (Finset.univ : Finset G.Dart).filter (fun f : G.Dart => f.snd = v),
        (((G.degree f.snd : ℝ) - 1) ^ (1 / (nDart G : ℝ)))
          = ((G.degree v : ℝ) - 1) ^ (1 / (nDart G : ℝ)) := by
      intro f hf
      rw [Finset.mem_filter] at hf
      rw [hf.2]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, card_snd_fiber]
    rw [← Real.rpow_natCast (((G.degree v : ℝ) - 1) ^ (1 / (nDart G : ℝ))) (G.degree v)]
    rw [← Real.rpow_mul (hbase v) (1 / (nDart G : ℝ)) (G.degree v : ℝ)]
    congr 1
    field_simp
  have hL : (∏ i : (Σ e : G.Dart, NbWalk G e l),
        (NbWalk.Q G i.1 l i.2) ^ ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2))
      = Lam G ^ l := by
    rw [Finset.prod_congr rfl (fun i _ => hstep1 i), Finset.prod_comm]
    rw [Finset.prod_congr rfl hfiber2, Finset.prod_const, Finset.card_range, hlam]
  calc Lam G ^ l
      = ∏ i : (Σ e : G.Dart, NbWalk G e l),
          (NbWalk.Q G i.1 l i.2) ^ ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2) := hL.symm
    _ ≤ ∑ i : (Σ e : G.Dart, NbWalk G e l),
          ((1 / (nDart G : ℝ)) * NbWalk.wt G i.1 l i.2) * NbWalk.Q G i.1 l i.2 := hamgm
    _ = Nl G l := hR

end Counts


/-!
## Part 5. Short non-backtracking walks are paths

Non-backtracking walks and the two counting lemmas used in the proof of
Theorem 1 of Alon, Hoory and Linial: a non-backtracking walk of length smaller
than the girth is a path, and hence two short non-backtracking walks from the
same dart with the same endpoint coincide.

## Main definitions and results

* `MooreBound.NB` : the predicate that a walk never traverses a dart and then its opposite;
* `MooreBound.NB.length_ne_one`, `MooreBound.NB.length_ne_two` : a closed non-backtracking
  walk has no cycle of length `1` or `2`;
* `MooreBound.exists_isCycle_length_le_of_nb_closed` : a nonempty closed non-backtracking
  walk contains a cycle of length at most its own length;
* `MooreBound.isPath_of_nb_length_lt_girth` : a non-backtracking walk shorter than the
  girth is a path.
-/

set_option maxHeartbeats 1000000

section ShortWalks

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A walk is *non-backtracking* when no two consecutive darts are opposite. -/
def NB {u v : V} (p : G.Walk u v) : Prop :=
  p.darts.IsChain (fun a b : G.Dart => b ≠ a.symm)

theorem NB.nil {u : V} : NB G (SimpleGraph.Walk.nil : G.Walk u u) := by
  simp [NB]

theorem NB.tail {u v : V} {p : G.Walk u v} (h : NB G p) : NB G p.tail := by
  rw [NB, SimpleGraph.Walk.darts_tail]
  exact List.IsChain.tail h

theorem NB.take {u v : V} {p : G.Walk u v} (h : NB G p) (n : ℕ) : NB G (p.take n) := by
  rw [NB, SimpleGraph.Walk.darts_take]
  exact List.IsChain.take h n

theorem NB.drop {u v : V} {p : G.Walk u v} (h : NB G p) (n : ℕ) : NB G (p.drop n) := by
  rw [NB, SimpleGraph.Walk.darts_drop]
  exact List.IsChain.drop h n

theorem NB.copy {u v u' v' : V} {p : G.Walk u v} (h : NB G p) (hu : u = u') (hv : v = v') :
    NB G (p.copy hu hv) := by
  subst_vars
  simpa using h

theorem NB.of_isSubwalk {u v u' v' : V} {p : G.Walk u v} {q : G.Walk u' v'}
    (h : NB G q) (hpq : p.IsSubwalk q) : NB G p := by
  rw [NB] at h ⊢
  exact h.infix hpq.darts_isInfix

/-- The darts of a non-backtracking walk are closed under reversal of the walk. -/
theorem NB.reverse {u v : V} {p : G.Walk u v} (h : NB G p) : NB G p.reverse := by
  rw [NB] at h ⊢
  rw [SimpleGraph.Walk.darts_reverse]
  refine List.isChain_reverse.mpr ?_
  rw [List.isChain_map (f := SimpleGraph.Dart.symm)]
  exact h.imp fun a b hab => ne_comm.mp hab

/-- A closed non-backtracking walk cannot have length one. -/
theorem NB.length_ne_one {x : V} {p : G.Walk x x} (hNB : NB G p) : p.length ≠ 1 := by
  intro h1
  cases p with
  | nil => simp at h1
  | cons h q =>
      cases q with
      | nil => exact G.irrefl h
      | cons _ _ => simp at h1

/-- A closed non-backtracking walk cannot have length two. -/
theorem NB.length_ne_two {x : V} {p : G.Walk x x} (hNB : NB G p) : p.length ≠ 2 := by
  intro h2
  cases p with
  | nil => simp at h2
  | cons h q =>
      cases q with
      | nil => simp at h2
      | cons h' q' =>
          cases q' with
          | nil =>
              rw [NB] at hNB
              have hd := (List.isChain_cons_cons.mp hNB).1
              exact hd (SimpleGraph.Dart.ext _ _ rfl)
          | cons _ _ => simp at h2

/-- A nonempty closed non-backtracking walk contains a cycle of length at most its own
length. -/
theorem exists_isCycle_length_le_of_nb_closed {x : V} {p : G.Walk x x}
    (hNB : NB G p) (hpos : 0 < p.length) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ c.length ≤ p.length := by
  classical
  have hex : ∃ d : ℕ, 0 < d ∧ ∃ i, i + d ≤ p.length ∧ p.getVert i = p.getVert (i + d) := by
    refine ⟨p.length, hpos, 0, by simp, ?_⟩
    rw [Nat.zero_add, SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length]
  set d := Nat.find hex with hddef
  obtain ⟨hdpos, i, hile, hig⟩ := Nat.find_spec hex
  have hdmin : ∀ d' < d, ¬ (0 < d' ∧ ∃ i, i + d' ≤ p.length ∧ p.getVert i = p.getVert (i + d')) := by
    intro d' hlt
    exact Nat.find_min hex (by rwa [hddef] at hlt)
  have hd_le : d ≤ (p.drop i).length := by
    rw [SimpleGraph.Walk.drop_length]
    omega
  let q : G.Walk (p.getVert i) x := p.drop i
  have hqend : q.getVert d = p.getVert i := by
    rw [show q.getVert d = p.getVert (i + d) from SimpleGraph.Walk.drop_getVert p i d]
    exact hig.symm
  let w : G.Walk (p.getVert i) (p.getVert i) := (q.take d).copy rfl hqend
  have hwlen : w.length = d := by
    show ((q.take d).copy rfl hqend).length = d
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length, Nat.min_eq_left hd_le]
  have hwNB : NB G w := by
    have h1 : NB G (p.drop i) := NB.drop G hNB i
    have h2 : NB G ((p.drop i).take d) := NB.take G h1 d
    exact NB.copy G h2 rfl hqend
  have hsupp : (w.tail.support).length = d := by
    rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_tail, hwlen]
    omega
  have hwtail : w.tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, List.nodup_iff_injective_getElem]
    intro a b hab
    by_contra hne
    have hvalne : a.1 ≠ b.1 := fun h => hne (Fin.ext h)
    have key : ∀ (k l : ℕ) (hk : k < (w.tail.support).length) (hl : l < (w.tail.support).length),
        k < l → (w.tail.support)[k] ≠ (w.tail.support)[l] := by
      intro k l hk hl hkl heq
      have hk' : k ≤ (w.tail).length := by
        rw [SimpleGraph.Walk.length_support] at hk; omega
      have hl' : l ≤ (w.tail).length := by
        rw [SimpleGraph.Walk.length_support] at hl; omega
      have htl : (w.tail).length + 1 = d := by
        rw [SimpleGraph.Walk.length_tail, hwlen]
        omega
      have hW : ∀ m : ℕ, m ≤ (w.tail).length →
          (w.tail).getVert m = p.getVert (i + (m + 1)) := by
        intro m hm
        rw [SimpleGraph.Walk.getVert_tail]
        show ((q.take d).copy rfl hqend).getVert (m + 1) = p.getVert (i + (m + 1))
        rw [SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.take_getVert,
          Nat.min_eq_right (by omega)]
        exact SimpleGraph.Walk.drop_getVert p i (m + 1)
      have hab' : p.getVert (i + (k + 1)) = p.getVert (i + (l + 1)) := by
        have e1 : (w.tail).getVert k = p.getVert (i + (k + 1)) := hW k hk'
        have e2 : (w.tail).getVert l = p.getVert (i + (l + 1)) := hW l hl'
        have e3 : (w.tail).getVert k = (w.tail).getVert l := by
          rw [← SimpleGraph.Walk.support_getElem_eq_getVert (w.tail) hk,
            ← SimpleGraph.Walk.support_getElem_eq_getVert (w.tail) hl]
          exact heq
        exact e1.symm.trans (e3.trans e2)
      have hlt : l - k < d := by
        have hl'' : l < d := hsupp ▸ hl
        omega
      refine hdmin (l - k) hlt ⟨by omega, i + (k + 1), by omega, ?_⟩
      rw [show i + (k + 1) + (l - k) = i + (l + 1) by omega]
      exact hab'
    rcases Nat.lt_or_gt_of_ne hvalne with hlt | hgt
    · exact (key a.1 b.1 a.2 b.2 hlt hab).elim
    · exact (key b.1 a.1 b.2 a.2 hgt hab.symm).elim
  have hw3 : 3 ≤ w.length := by
    have hdn1 : d ≠ 1 := by
      intro h1
      exact NB.length_ne_one G hwNB (by rw [hwlen, h1])
    have hdn2 : d ≠ 2 := by
      intro h2
      exact NB.length_ne_two G hwNB (by rw [hwlen, h2])
    rw [hwlen]
    omega
  exact ⟨p.getVert i, w,
    SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hwtail, hw3⟩,
    by rw [hwlen]; omega⟩

/-- A non-backtracking walk of length smaller than the girth is a path. -/
theorem isPath_of_nb_length_lt_girth {u v : V} {p : G.Walk u v}
    (hNB : NB G p) (hlt : p.length < G.girth) : p.IsPath := by
  rw [SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil]
  intro x w hwsub
  rw [← SimpleGraph.Walk.length_eq_zero_iff]
  by_contra hlen
  have hpos : 0 < w.length := Nat.pos_of_ne_zero hlen
  have hNBw : NB G w := NB.of_isSubwalk G hNB hwsub
  obtain ⟨y, c, hc, hclen⟩ := exists_isCycle_length_le_of_nb_closed G hNBw hpos
  have h1 : G.girth ≤ c.length := hc.girth_le_length
  have h2 : c.length ≤ w.length := hclen
  have h3 : w.length ≤ p.length := SimpleGraph.Walk.length_le_of_isSubwalk hwsub
  omega

end ShortWalks


/-!
## Part 6. Injective counting of endpoints

The injective counting step in the proof of Theorem 1 of Alon, Hoory and Linial.
Two classes of short non-backtracking walks, one starting at a dart `e` and one
starting at the opposite dart `e.symm`, can be followed by their endpoints; the
resulting map into the vertex set is injective, because two short
non-backtracking walks with a common endpoint coincide.

## Main definitions and results

* `MooreBound.NB.eq_of_length_add_lt_girth` : two non-backtracking walks with a common start
  and end whose lengths sum to less than the girth coincide;
* `MooreBound.NbWalk.endV_injective_fin` : the endpoint map on non-backtracking walks of
  length at most `r` is injective when `2r` is less than the girth;
* `MooreBound.card_two_class_le` : the two classes of walks have at most `n` walks in total;
* `MooreBound.Nl_two_le` : the analogous inequality for the averages `Nl`.
-/

set_option maxHeartbeats 800000

section Injections

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem nextDart_ne_symm (e : G.Dart) (w : Succ G e) : nextDart G e w ≠ e.symm := by
  intro h
  have h2 : (nextDart G e w).snd = e.symm.snd := congrArg (fun d : G.Dart => d.snd) h
  have h3 : w.1 = e.fst := by simpa using h2
  exact w.2.2 h3

theorem NbWalk.toWalk_nb (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    NB G (NbWalk.toWalk G e l ω) := by
  rw [NB, NbWalk.darts_toWalk]
  induction l generalizing e with
  | zero => exact List.isChain_singleton e
  | succ l ih =>
      rw [NbWalk.darts_succ]
      exact List.isChain_cons_cons.mpr ⟨nextDart_ne_symm G e ω.1, ih (nextDart G e ω.1) ω.2⟩

theorem NbWalk.toWalkFrom_nb (e : G.Dart) (l : ℕ) (ω : NbWalk G e l) :
    NB G (NbWalk.toWalkFrom G e l ω) := by
  rw [NB, NbWalk.toWalkFrom_darts]
  have h := NbWalk.toWalk_nb G e l ω
  rw [NB, NbWalk.darts_toWalk] at h
  exact h.tail

theorem NB.eq_of_length_add_lt_girth {u v : V} {p q : G.Walk u v}
    (hp : NB G p) (hq : NB G q) (h : p.length + q.length < G.girth) : p = q := by
  by_contra hne
  have hpp : p.IsPath := isPath_of_nb_length_lt_girth G hp (by omega)
  have hqp : q.IsPath := isPath_of_nb_length_lt_girth G hq (by omega)
  obtain ⟨_, _, _, c, hc, hclen⟩ :=
    SimpleGraph.Walk.IsPath.exists_isCycle_length_le_add_of_ne hpp hqp hne
  have := hc.girth_le_length
  omega

theorem NbWalk.darts_eq_of_endV_eq {e : G.Dart} {l₁ l₂ : ℕ}
    {ω₁ : NbWalk G e l₁} {ω₂ : NbWalk G e l₂}
    (h : NbWalk.endV G e l₁ ω₁ = NbWalk.endV G e l₂ ω₂)
    (hg : l₁ + l₂ < G.girth) :
    NbWalk.darts G e l₁ ω₁ = NbWalk.darts G e l₂ ω₂ := by
  let q' : G.Walk e.snd (NbWalk.endV G e l₁ ω₁) :=
    (NbWalk.toWalkFrom G e l₂ ω₂).copy rfl h.symm
  have hq'nb : NB G q' := NB.copy G (NbWalk.toWalkFrom_nb G e l₂ ω₂) rfl h.symm
  have hq'len : q'.length = l₂ := by
    rw [show q'.length = (NbWalk.toWalkFrom G e l₂ ω₂).length from SimpleGraph.Walk.length_copy _ _ _,
      NbWalk.toWalkFrom_length]
  have heq : NbWalk.toWalkFrom G e l₁ ω₁ = q' :=
    NB.eq_of_length_add_lt_girth G (NbWalk.toWalkFrom_nb G e l₁ ω₁) hq'nb
      (by rw [NbWalk.toWalkFrom_length, hq'len]; exact hg)
  have hd := congrArg SimpleGraph.Walk.darts heq
  rw [NbWalk.toWalkFrom_darts, SimpleGraph.Walk.darts_copy, NbWalk.toWalkFrom_darts] at hd
  exact hd

theorem NbWalk.eq_of_endV_eq {e : G.Dart} {l₁ l₂ : ℕ}
    {ω₁ : NbWalk G e l₁} {ω₂ : NbWalk G e l₂}
    (h : NbWalk.endV G e l₁ ω₁ = NbWalk.endV G e l₂ ω₂)
    (hg : l₁ + l₂ < G.girth) : l₁ = l₂ ∧ HEq ω₁ ω₂ := by
  have hd := NbWalk.darts_eq_of_endV_eq G h hg
  have hnat : l₁ = l₂ := by
    have := congrArg List.length hd
    rwa [NbWalk.darts_length, NbWalk.darts_length] at this
  subst hnat
  have hω : ω₁ = ω₂ := NbWalk.darts_injective G e l₁ hd
  exact ⟨rfl, hω ▸ HEq.rfl⟩

theorem NbWalk.endV_injective_fin {r : ℕ} (hr : 2 * r < G.girth) (e : G.Dart) :
    Function.Injective
      (fun x : (Σ l : Fin (r + 1), NbWalk G e (l : ℕ)) =>
        NbWalk.endV G e (x.1 : ℕ) x.2) := by
  rintro ⟨⟨l₁, h₁⟩, ω₁⟩ ⟨⟨l₂, h₂⟩, ω₂⟩ h
  have h1 : l₁ ≤ r := by omega
  have h2 : l₂ ≤ r := by omega
  have hg : l₁ + l₂ < G.girth := by omega
  obtain ⟨hnat, hheq⟩ := NbWalk.eq_of_endV_eq G h hg
  refine Sigma.ext ?_ hheq
  exact Fin.ext hnat

theorem card_sigma_fin (e : G.Dart) (m : ℕ) :
    Fintype.card (Σ l : Fin (m + 1), NbWalk G e (l : ℕ)) =
      ∑ l ∈ Finset.range (m + 1), Nb G e l := by
  rw [Fintype.card_sigma]
  exact Fin.sum_univ_eq_sum_range (fun l => Nb G e l) (m + 1)

theorem no_cross {a b : ℕ} (e : G.Dart) (hab : a + b + 1 < G.girth)
    {l₁ : ℕ} (h₁ : l₁ ≤ a) {ω₁ : NbWalk G e l₁}
    {l₂ : ℕ} (h₂ : l₂ ≤ b) {ω₂ : NbWalk G e.symm l₂}
    (h : NbWalk.endV G e l₁ ω₁ = NbWalk.endV G e.symm l₂ ω₂) : False := by
  have hg : l₁ + (l₂ + 1) < G.girth := by omega
  let q' : G.Walk e.snd (NbWalk.endV G e l₁ ω₁) :=
    (NbWalk.toWalk G e.symm l₂ ω₂).copy (SimpleGraph.Dart.fst_symm e) h.symm
  have hq'nb : NB G q' :=
    NB.copy G (NbWalk.toWalk_nb G e.symm l₂ ω₂) (SimpleGraph.Dart.fst_symm e) h.symm
  have hq'len : q'.length = l₂ + 1 := by
    rw [show q'.length = (NbWalk.toWalk G e.symm l₂ ω₂).length from SimpleGraph.Walk.length_copy _ _ _,
      NbWalk.toWalk_length]
  have heq : NbWalk.toWalkFrom G e l₁ ω₁ = q' :=
    NB.eq_of_length_add_lt_girth G (NbWalk.toWalkFrom_nb G e l₁ ω₁) hq'nb
      (by rw [NbWalk.toWalkFrom_length, hq'len]; exact hg)
  have hd := congrArg SimpleGraph.Walk.darts heq
  dsimp only [q'] at hd
  rw [NbWalk.toWalkFrom_darts, SimpleGraph.Walk.darts_copy, NbWalk.darts_toWalk] at hd
  rcases l₁ with _ | l₁'
  · simp [NbWalk.darts_zero] at hd
  · rw [NbWalk.darts_succ] at hd
    have hhead := (List.cons.injEq _ _ _ _).mp hd |>.1
    exact nextDart_ne_symm G e ω₁.1 hhead

theorem card_two_class_le {a b : ℕ} (e : G.Dart)
    (ha : 2 * a < G.girth) (hb : 2 * b < G.girth) (hab : a + b + 1 < G.girth) :
    (∑ l ∈ Finset.range (a + 1), Nb G e l) + (∑ l ∈ Finset.range (b + 1), Nb G e.symm l)
      ≤ Fintype.card V := by
  classical
  have hcard : Fintype.card
      ((Σ l : Fin (a + 1), NbWalk G e l) ⊕ (Σ l : Fin (b + 1), NbWalk G e.symm l))
      = (∑ l ∈ Finset.range (a + 1), Nb G e l) + (∑ l ∈ Finset.range (b + 1), Nb G e.symm l) := by
    rw [Fintype.card_sum, card_sigma_fin, card_sigma_fin]
  rw [← hcard]
  let f : ((Σ l : Fin (a + 1), NbWalk G e l) ⊕ (Σ l : Fin (b + 1), NbWalk G e.symm l)) → V :=
    Sum.elim (fun x => NbWalk.endV G e (x.1 : ℕ) x.2)
      (fun x => NbWalk.endV G e.symm (x.1 : ℕ) x.2)
  refine Fintype.card_le_of_injective f ?_
  rintro (⟨⟨l₁, hl₁⟩, ω₁⟩ | ⟨⟨l₁, hl₁⟩, ω₁⟩) (⟨⟨l₂, hl₂⟩, ω₂⟩ | ⟨⟨l₂, hl₂⟩, ω₂⟩) h
  · exact congrArg Sum.inl (NbWalk.endV_injective_fin G ha e h)
  · exfalso
    exact no_cross G e hab (by omega) (by omega) h
  · exfalso
    exact no_cross G e hab (by omega) (by omega) h.symm
  · exact congrArg Sum.inr (NbWalk.endV_injective_fin G hb e.symm h)


theorem sum_e_Nb [Nonempty V] (l : ℕ) (hdeg : ∀ v, 2 ≤ G.degree v) :
    (∑ e : G.Dart, (Nb G e l : ℝ)) = (nDart G : ℝ) * Nl G l := by
  have hnd : 0 < nDart G := nDart_pos G hdeg
  have hne : (nDart G : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.1 hnd
  rw [Nl]
  field_simp

theorem sum_e_Nb_symm (l : ℕ) :
    (∑ e : G.Dart, (Nb G e.symm l : ℝ)) = ∑ e : G.Dart, (Nb G e l : ℝ) := by
  let σ : G.Dart ≃ G.Dart :=
    { toFun := SimpleGraph.Dart.symm, invFun := SimpleGraph.Dart.symm,
      left_inv := SimpleGraph.Dart.symm_symm, right_inv := SimpleGraph.Dart.symm_symm }
  have := Equiv.sum_comp σ (fun e : G.Dart => (Nb G e l : ℝ))
  simpa [σ] using this

theorem Nl_two_le [Nonempty V] {a b : ℕ} (hdeg : ∀ v, 2 ≤ G.degree v)
    (ha : 2 * a < G.girth) (hb : 2 * b < G.girth) (hab : a + b + 1 < G.girth) :
    (∑ l ∈ Finset.range (a + 1), Nl G l) + (∑ l ∈ Finset.range (b + 1), Nl G l)
      ≤ (Fintype.card V : ℝ) := by
  classical
  have hnd : 0 < nDart G := nDart_pos G hdeg
  have hndR : (0 : ℝ) < (nDart G : ℝ) := by exact_mod_cast hnd
  have hnat : (∑ e : G.Dart,
      ((∑ l ∈ Finset.range (a + 1), Nb G e l) + (∑ l ∈ Finset.range (b + 1), Nb G e.symm l)))
      ≤ (nDart G) * Fintype.card V := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => card_two_class_le G e ha hb hab)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nDart] using h
  have hcast : ((∑ e : G.Dart,
      ((∑ l ∈ Finset.range (a + 1), Nb G e l) + (∑ l ∈ Finset.range (b + 1), Nb G e.symm l)) : ℕ) : ℝ)
      ≤ (nDart G : ℝ) * (Fintype.card V : ℝ) := by
    exact_mod_cast hnat
  push_cast at hcast
  have hA : (∑ e : G.Dart, ∑ l ∈ Finset.range (a + 1), (Nb G e l : ℝ))
      = ∑ l ∈ Finset.range (a + 1), ∑ e : G.Dart, (Nb G e l : ℝ) := Finset.sum_comm
  have hB : (∑ e : G.Dart, ∑ l ∈ Finset.range (b + 1), (Nb G e.symm l : ℝ))
      = ∑ l ∈ Finset.range (b + 1), ∑ e : G.Dart, (Nb G e.symm l : ℝ) := Finset.sum_comm
  have h2 : ∀ l : ℕ, (∑ e : G.Dart, (Nb G e.symm l : ℝ)) = (nDart G : ℝ) * Nl G l := by
    intro l
    rw [sum_e_Nb_symm G l, sum_e_Nb G l hdeg]
  have h3 : ∀ l : ℕ, (∑ e : G.Dart, (Nb G e l : ℝ)) = (nDart G : ℝ) * Nl G l :=
    fun l => sum_e_Nb G l hdeg
  rw [Finset.sum_add_distrib, hA, hB] at hcast
  simp only [h2, h3] at hcast
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add] at hcast
  exact le_of_mul_le_mul_left hcast hndR

end Injections


/-!
## Part 7. The growth rate is at least the average degree minus one

This section proves that the growth rate `Λ = ∏_v (d_v - 1)^(d_v / nd)` of the
number of non-backtracking walks is at least the average degree minus one.
The proof is the one given in the paper: the function `d ↦ (d - 1)^d` is
log-convex for `d ≥ 2`, so by Jensen's inequality
`(1/n) ∑_v d_v log (d_v - 1) ≥ d̄ log (d̄ - 1)` where `d̄ = nd / n`, whence
`Λ ≥ d̄ - 1`.

## Main definitions and results

* `MooreBound.convexOn_add_one_mul_log` : `x ↦ (x + 1) log x` is convex on
  `[1, ∞)`, which is log-convexity of `d ↦ (d - 1)^d` on `[2, ∞)`;
* `MooreBound.sum_degree_eq_nDart` : the degree sum is the number of darts;
* `MooreBound.sum_deg_sub_one` : `∑_v (d_v - 1) = nd - n`;
* `MooreBound.Lam_ge_avg` : `Λ ≥ nd / n - 1`;
* `MooreBound.Lam_ge` : `Λ ≥ d - 1` for any `d` with `n d ≤ nd`.
-/


section Growth

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The function `x ↦ (x + 1) log x` is convex on `[1, ∞)`; equivalently the
function `d ↦ (d - 1) ^ d` is log-convex on `[2, ∞)`. -/
theorem convexOn_add_one_mul_log :
    ConvexOn ℝ (Set.Ici (1:ℝ)) (fun x : ℝ => (x + 1) * Real.log x) := by
  have hcont : ContinuousOn (fun x : ℝ => (x + 1) * Real.log x) (Set.Ici (1:ℝ)) := by
    apply ContinuousOn.mul
    · exact (continuous_id.add continuous_const).continuousOn
    · apply Real.continuousOn_log.mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (1:ℝ) ≤ x := hx
      linarith
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici (1:ℝ)) hcont
    (f' := fun x => Real.log x + 1 + 1/x)
    (f'' := fun x => (x - 1)/x^2) ?_ ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1:ℝ) < x := hx
    have hx0 : x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
    have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have hprod : HasDerivAt (fun y : ℝ => (y + 1) * Real.log y)
        (1 * Real.log x + (x+1) * x⁻¹) x := h1.mul h2
    have hd : (1 * Real.log x + (x+1) * x⁻¹) = Real.log x + 1 + 1/x := by
      field_simp
      ring
    exact (hprod.congr_deriv hd).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1:ℝ) < x := hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv hx0
    have hconst : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
    have hdiv : HasDerivAt (fun y : ℝ => (1:ℝ)/y) (-(x^2)⁻¹) x := by
      simpa [one_div] using hinv
    have hsum : HasDerivAt (fun y : ℝ => Real.log y + 1 + 1/y)
        (x⁻¹ + 0 + (-(x^2)⁻¹)) x := (hlog.add hconst).add hdiv
    have hd : (x⁻¹ + 0 + (-(x^2)⁻¹)) = (x - 1)/x^2 := by
      field_simp
      ring
    exact (hsum.congr_deriv hd).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1:ℝ) < x := hx
    exact div_nonneg (by linarith) (by positivity)

/-- The sum of the degrees equals the number of darts. -/
theorem sum_degree_eq_nDart : ∑ v : V, G.degree v = nDart G := by
  rw [nDart]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset G.Dart)) (t := (Finset.univ : Finset V))
    (f := fun d : G.Dart => d.snd) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  exact Finset.sum_congr rfl (fun v _ => (card_snd_fiber G v).symm)

/-- The sum over the vertices of `deg v - 1` is the number of darts minus the
number of vertices. -/
theorem sum_deg_sub_one :
    ∑ v : V, ((G.degree v : ℝ) - 1) = (nDart G : ℝ) - (Fintype.card V : ℝ) := by
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ v : V, (G.degree v : ℝ) = (nDart G : ℝ) := by
    rw [← Nat.cast_sum, sum_degree_eq_nDart]
  have h2 : ∑ _v : V, (1:ℝ) = (Fintype.card V : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [h1, h2]

/-- The growth rate `Λ` is at least the average degree minus one. -/
theorem Lam_ge_avg [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) :
    (nDart G : ℝ) / (Fintype.card V : ℝ) - 1 ≤ Lam G := by
  classical
  have hnpos : (0:ℝ) < (Fintype.card V : ℝ) := by
    have h : 0 < Fintype.card V := Fintype.card_pos_iff.2 (inferInstance : Nonempty V)
    exact_mod_cast h
  have hndpos : (0:ℝ) < (nDart G : ℝ) := by
    have h : 0 < nDart G := nDart_pos G hdeg
    exact_mod_cast h
  have hnne : (Fintype.card V : ℝ) ≠ 0 := ne_of_gt hnpos
  have hndne : (nDart G : ℝ) ≠ 0 := ne_of_gt hndpos
  have hdegR : ∀ v : V, (2:ℝ) ≤ (G.degree v : ℝ) := fun v => by exact_mod_cast hdeg v
  have h2n : 2 * Fintype.card V ≤ nDart G := by
    rw [← sum_degree_eq_nDart]
    calc 2 * Fintype.card V = ∑ _v : V, 2 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum (fun v _ => hdeg v)
  have h2nR : (2:ℝ) * (Fintype.card V : ℝ) ≤ (nDart G : ℝ) := by
    have : ((2 * Fintype.card V : ℕ) : ℝ) ≤ ((nDart G : ℕ) : ℝ) := by exact_mod_cast h2n
    push_cast at this
    linarith
  have hnle : (Fintype.card V : ℝ) ≤ (nDart G : ℝ) := by linarith
  -- Jensen with the convex function `x ↦ (x + 1) log x` at the points `deg v - 1`
  have hJ := convexOn_add_one_mul_log.map_sum_le
    (t := (Finset.univ : Finset V))
    (w := fun _ : V => (1:ℝ) / (Fintype.card V : ℝ))
    (p := fun v : V => ((G.degree v : ℝ) - 1))
    (fun v _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun v _ => by rw [Set.mem_Ici]; linarith [hdegR v])
  simp only [smul_eq_mul] at hJ
  have hmean : ∑ v : V, ((1:ℝ) / (Fintype.card V : ℝ)) * ((G.degree v : ℝ) - 1)
      = ((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ) := by
    rw [← Finset.mul_sum, sum_deg_sub_one G]
    field_simp
  have hrhs : ∑ v : V, ((1:ℝ) / (Fintype.card V : ℝ))
      * ((((G.degree v : ℝ) - 1) + 1) * Real.log ((G.degree v : ℝ) - 1))
      = ((1:ℝ) / (Fintype.card V : ℝ)) *
        ∑ v : V, ((G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    ring_nf
  rw [hmean, hrhs] at hJ
  have hmain : (nDart G : ℝ)
      * Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ))
      ≤ ∑ v : V, ((G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left hJ (le_of_lt hnpos)
    have h2 : (Fintype.card V : ℝ) *
        ((((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ) + 1)
          * Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)))
        = (nDart G : ℝ) *
          Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) := by
      field_simp
      ring
    have h3 : (Fintype.card V : ℝ) *
        ((1:ℝ) / (Fintype.card V : ℝ)
          * ∑ v : V, ((G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)))
        = ∑ v : V, ((G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) := by
      field_simp
    rw [h2, h3] at h1
    exact h1
  have hlogLam : Real.log (Lam G) = (1 / (nDart G : ℝ))
      * ∑ v : V, ((G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) := by
    rw [Lam, Real.log_prod]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Real.log_rpow (by linarith [hdegR v])]
      field_simp
    · intro v _
      exact ne_of_gt (Real.rpow_pos_of_pos (by linarith [hdegR v]) _)
  have hlogineq : Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ))
      ≤ Real.log (Lam G) := by
    rw [hlogLam]
    have h1 := mul_le_mul_of_nonneg_left hmain (by positivity : (0:ℝ) ≤ 1 / (nDart G : ℝ))
    have h2 : (1 / (nDart G : ℝ)) * ((nDart G : ℝ)
        * Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)))
        = Real.log (((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)) := by
      field_simp
    rw [h2] at h1
    exact h1
  have hKpos : (0:ℝ) < ((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ) := by
    apply div_pos _ hnpos
    linarith
  have hLpos : (0:ℝ) < Lam G :=
    Finset.prod_pos (fun v _ => Real.rpow_pos_of_pos (by linarith [hdegR v]) _)
  have h := (Real.log_le_log_iff hKpos hLpos).1 hlogineq
  have hKeq : ((nDart G : ℝ) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)
      = (nDart G : ℝ) / (Fintype.card V : ℝ) - 1 := by
    field_simp
  rw [hKeq] at h
  exact h

/-- `Λ` is at least `d - 1` whenever the average degree is at least `d`. -/
theorem Lam_ge [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) (d : ℝ)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) : d - 1 ≤ Lam G := by
  have hnpos : (0:ℝ) < (Fintype.card V : ℝ) := by
    have h : 0 < Fintype.card V := Fintype.card_pos_iff.2 (inferInstance : Nonempty V)
    exact_mod_cast h
  have hd : d ≤ (nDart G : ℝ) / (Fintype.card V : ℝ) := by
    rw [le_div_iff₀ hnpos, mul_comm]
    exact havg
  have := Lam_ge_avg G hdeg
  linarith

end Growth


/-!
## Part 8. The Moore bound function and graphs of minimum degree at least two

The Moore bound function `n₀` and the analytic part of the proof of Theorem 1 of
Alon, Hoory and Linial, for graphs whose minimum degree is at least two.

## Main definitions and results

* `MooreBound.n0` : the Moore bound `n₀(d, g)`, the size of a ball of radius
  `⌊(g-1)/2⌋` in a `d`-regular graph of girth `g`;
* `MooreBound.n0_mono` : `n₀` is monotone in the degree, for `d ≥ 1`;
* `MooreBound.odd_case`, `MooreBound.even_case` : the two cases of the counting
  argument, for a graph with minimum degree at least two;
* `MooreBound.n0_bound_min_deg` : the Moore bound for a graph with minimum
  degree at least two.
-/

set_option maxHeartbeats 800000

/-! ### The Moore bound function -/

/-- The Moore bound `n₀(d, g)`: the number of vertices in a ball of radius
`⌊(g-1)/2⌋` in a `d`-regular graph of girth `g`. -/
noncomputable def n0 (d : ℝ) (g : ℕ) : ℝ :=
  if g % 2 = 1 then 1 + d * ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i
  else 2 * ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i

theorem n0_odd_form (d : ℝ) {g : ℕ} (h : g % 2 = 1) :
    n0 d g = 1 + d * ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i := by
  rw [n0, ite_eq_left h]

theorem n0_even_form (d : ℝ) {g : ℕ} (h : g % 2 ≠ 1) :
    n0 d g = 2 * ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i := by
  rw [n0, ite_eq_right h]

theorem n0_zero (d : ℝ) : n0 d 0 = 0 := by
  simp [n0]

theorem n0_nonneg {d : ℝ} (hd : 1 ≤ d) (g : ℕ) : 0 ≤ n0 d g := by
  have h1 : (0 : ℝ) ≤ d - 1 := by linarith
  have hS : (0 : ℝ) ≤ ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg h1 i)
  have hd : (0 : ℝ) ≤ d := by linarith
  have hdS : (0 : ℝ) ≤ d * ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i := mul_nonneg hd hS
  rw [n0]
  split_ifs
  · linarith
  · linarith

/-- `n₀` is monotone in the degree, for degrees at least one. -/
theorem n0_mono {d₁ d₂ : ℝ} (hd : 1 ≤ d₁) (h : d₁ ≤ d₂) (g : ℕ) : n0 d₁ g ≤ n0 d₂ g := by
  have h1 : (0 : ℝ) ≤ d₁ - 1 := by linarith
  have h2 : d₁ - 1 ≤ d₂ - 1 := by linarith
  have hsum : (∑ i ∈ Finset.range (g / 2), (d₁ - 1) ^ i)
      ≤ ∑ i ∈ Finset.range (g / 2), (d₂ - 1) ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ h1 h2 i)
  have hS0 : (0 : ℝ) ≤ ∑ i ∈ Finset.range (g / 2), (d₁ - 1) ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg h1 i)
  by_cases hg : g % 2 = 1
  · rw [n0_odd_form _ hg, n0_odd_form _ hg]
    have hmul : d₁ * (∑ i ∈ Finset.range (g / 2), (d₁ - 1) ^ i)
        ≤ d₂ * ∑ i ∈ Finset.range (g / 2), (d₂ - 1) ^ i :=
      mul_le_mul h hsum hS0 (le_trans (by linarith : (0 : ℝ) ≤ d₁) h)
    linarith
  · rw [n0_even_form _ hg, n0_even_form _ hg]
    linarith

/-! ### The counting argument -/

section Bounds

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `Λ ^ l` is a lower bound for the average number `Nl` of walks of length `l`. -/
theorem sum_pow_Lam_le_sum_Nl [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) (m : ℕ) :
    (∑ l ∈ Finset.range m, Lam G ^ l) ≤ ∑ l ∈ Finset.range m, Nl G l :=
  Finset.sum_le_sum (fun l _ => Lam_pow_le_Nl G hdeg l)

/-- The geometric identity behind the odd case of the counting argument:
`(∑_{i < r+1} x^i) + ∑_{i < r} x^i = 1 + (x + 1) ∑_{i < r} x^i`. -/
theorem geom_sum_odd (x : ℝ) (r : ℕ) :
    (∑ l ∈ Finset.range (r + 1), x ^ l) + (∑ l ∈ Finset.range r, x ^ l)
      = 1 + (x + 1) * ∑ i ∈ Finset.range r, x ^ i := by
  rw [Finset.sum_range_succ]
  have h := geom_sum_mul_add (x - 1) r
  simp only [sub_add_cancel] at h
  linarith

/-- The odd case of Theorem 1: if the girth of `G` is `2r+1`, then the number of
vertices is at least `n₀(Λ + 1, 2r+1)`. -/
theorem odd_case [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) (r : ℕ)
    (hg : G.girth = 2 * r + 1) :
    n0 (Lam G + 1) G.girth ≤ (Fintype.card V : ℝ) := by
  have hpar : (2 * r + 1) % 2 = 1 := by omega
  have hdiv : (2 * r + 1) / 2 = r := by omega
  rw [hg, n0_odd_form _ hpar, hdiv]
  simp only [add_sub_cancel_right]
  rcases r with _ | r
  · have hcard : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by
      have h : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
      exact_mod_cast h
    simpa using hcard
  · have hle : (∑ l ∈ Finset.range (r + 1 + 1), Nl G l)
        + (∑ l ∈ Finset.range (r + 1), Nl G l) ≤ (Fintype.card V : ℝ) :=
      Nl_two_le G hdeg (a := r + 1) (b := r)
        (by rw [hg]; omega) (by rw [hg]; omega) (by rw [hg]; omega)
    have h1 := sum_pow_Lam_le_sum_Nl G hdeg (r + 1 + 1)
    have h2 := sum_pow_Lam_le_sum_Nl G hdeg (r + 1)
    have hsum : (∑ l ∈ Finset.range (r + 1 + 1), Lam G ^ l)
        + (∑ l ∈ Finset.range (r + 1), Lam G ^ l) ≤ (Fintype.card V : ℝ) := by
      linarith
    have hid := geom_sum_odd (Lam G) (r + 1)
    rw [hid] at hsum
    exact hsum

/-- The even case of Theorem 1: if the girth of `G` is `2r`, then the number of
vertices is at least `n0 (Λ + 1, 2r)`. -/
theorem even_case [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) (r : ℕ)
    (hg : G.girth = 2 * r) :
    n0 (Lam G + 1) G.girth ≤ (Fintype.card V : ℝ) := by
  have hpar : (2 * r) % 2 ≠ 1 := by omega
  have hdiv : (2 * r) / 2 = r := by omega
  rw [hg, n0_even_form _ hpar, hdiv]
  simp only [add_sub_cancel_right]
  rcases r with _ | r
  · rw [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact Nat.cast_nonneg _
  · have hle : 2 * (∑ l ∈ Finset.range (r + 1), Nl G l) ≤ (Fintype.card V : ℝ) := by
      have h := Nl_two_le G hdeg (a := r) (b := r)
        (by rw [hg]; omega) (by rw [hg]; omega) (by rw [hg]; omega)
      linarith
    have h1 := sum_pow_Lam_le_sum_Nl G hdeg (r + 1)
    have h2 : 2 * (∑ l ∈ Finset.range (r + 1), Lam G ^ l) ≤ (Fintype.card V : ℝ) := by
      linarith
    exact h2

/-- **Theorem 1 for graphs of minimum degree at least two.**  A graph on `n`
vertices with girth `g`, all degrees at least two, and average degree at least
`d ≥ 2` has at least `n₀(d, g)` vertices. -/
theorem n0_bound_min_deg [Nonempty V] (hdeg : ∀ v, 2 ≤ G.degree v) {d : ℝ} (hd : 2 ≤ d)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) :
    n0 d G.girth ≤ (Fintype.card V : ℝ) := by
  have hlam : d ≤ Lam G + 1 := by
    have h := Lam_ge G hdeg d havg
    linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  refine (n0_mono hd1 hlam G.girth).trans ?_
  rcases Nat.even_or_odd G.girth with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact even_case G hdeg r (by omega)
  · exact odd_case G hdeg r (by omega)

end Bounds


/-!
## Part 9. Deleting vertices of degree at most one

This section reduces the general case to the case of minimum degree at least two.
Deleting a vertex of degree at most one does not change the girth (provided the
graph has a cycle) and does not decrease the average degree, because such a
vertex is incident with at most one edge.  Iterating this deletion and applying
`n0_bound_min_deg` yields the general bound.

## Main results

* `MooreBound.nDart_induce_compl_add` : deleting a vertex removes `2 · deg v` darts;
* `MooreBound.girth_induce_compl` : deleting a vertex of degree at most one
  preserves the girth of a graph with a cycle;
* `MooreBound.avg_induce_compl` : deleting a vertex of degree at most one does
  not decrease the average degree;
* `MooreBound.n0_bound_aux` : Theorem 1 for a graph with a cycle.
-/

set_option maxHeartbeats 1000000

section Delete

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Counting darts -/

/-- Deleting a vertex `v` removes exactly `2 · deg v` darts, since each edge
incident with `v` gives one outgoing and one incoming dart at `v`. -/
theorem nDart_induce_compl_add (v : V) :
    nDart G = nDart (G.induce ({w | w ≠ v} : Set V)) + 2 * G.degree v := by
  classical
  have hcard : #G.edgeFinset = #(G.induce ({w | w ≠ v} : Set V)).edgeFinset + G.degree v := by
    have hcard' : #(G.induce ({w | w ≠ v} : Set V)).edgeFinset
        = #{e ∈ G.edgeFinset | ¬ v ∈ e} := by
      have hmap := SimpleGraph.map_edgeFinset_induce (G := G) (s := ({w | w ≠ v} : Set V))
      rw [← Finset.card_map (s := (G.induce ({w | w ≠ v} : Set V)).edgeFinset)
        (f := (Function.Embedding.subtype (fun x => x ∈ ({w | w ≠ v} : Set V))).sym2Map), hmap]
      congr 1
      ext e
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_sym2_iff, Set.mem_toFinset,
        Sym2.mem_toFinset]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hv => h2 v hv rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun a ha hav => h2 (hav ▸ ha)⟩
    have hinc : #{e ∈ G.edgeFinset | ¬ v ∈ e} = #G.edgeFinset - G.degree v := by
      have h1 : (G.edgeFinset.filter (fun e => ¬ v ∈ e))
          = G.edgeFinset \ G.incidenceFinset v := by
        ext e
        simp only [mem_filter, mem_sdiff, SimpleGraph.incidenceFinset_eq_filter, mem_filter]
        tauto
      rw [h1, Finset.card_sdiff_of_subset (SimpleGraph.incidenceFinset_subset (G := G) (v := v)),
        SimpleGraph.card_incidenceFinset_eq_degree (G := G) (v := v)]
    have hle : G.degree v ≤ #G.edgeFinset :=
      SimpleGraph.degree_le_card_edgeFinset (G := G) (v := v)
    omega
  rw [nDart, nDart, SimpleGraph.dart_card_eq_twice_card_edges (G := G),
    SimpleGraph.dart_card_eq_twice_card_edges (G := (G.induce ({w | w ≠ v} : Set V)))]
  omega

/-! ### Preserving the girth -/

/-- Every vertex on a cycle has degree at least two. -/
theorem two_le_degree_of_mem_cycle {u : V} {c : G.Walk u u} (hc : c.IsCycle) {x : V}
    (hx : x ∈ c.support) : 2 ≤ G.degree x := by
  have h2 : (c.toSubgraph.neighborSet x).ncard = 2 := hc.ncard_neighborSet_toSubgraph_eq_two hx
  have hsub : c.toSubgraph.neighborSet x ⊆ G.neighborSet x := fun y hy => c.toSubgraph.adj_sub hy
  have hfin : (G.neighborSet x).Finite := Set.toFinite _
  have hle : (c.toSubgraph.neighborSet x).ncard ≤ (G.neighborSet x).ncard :=
    Set.ncard_le_ncard hsub hfin
  rw [h2, SimpleGraph.ncard_neighborSet] at hle
  exact hle

/-- Deleting a vertex of degree at most one preserves the girth, as long as the
graph has a cycle: such a vertex lies on no cycle, and every cycle of `G`
survives in the induced subgraph. -/
theorem girth_induce_compl (v : V) (hT : ¬ G.IsAcyclic) (hv : G.degree v ≤ 1) :
    (G.induce ({w | w ≠ v} : Set V)).girth = G.girth := by
  obtain ⟨a, c, hc, hlen⟩ := SimpleGraph.exists_girth_eq_length.mpr hT
  have hvnot : v ∉ c.support := by
    intro hmem
    have := two_le_degree_of_mem_cycle G hc hmem
    omega
  have hsub : ∀ x ∈ c.support, x ∈ ({w | w ≠ v} : Set V) := by
    intro x hx hxv
    exact hvnot (hxv ▸ hx)
  have hcyc : (c.induce ({w | w ≠ v} : Set V) hsub).IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce (G := G) {w | w ≠ v}).toHom)
    rw [SimpleGraph.Walk.map_induce]
    exact hc
  have hlen' : (c.induce ({w | w ≠ v} : Set V) hsub).length = c.length := by
    have h := congrArg SimpleGraph.Walk.length
      (SimpleGraph.Walk.map_induce (s := ({w | w ≠ v} : Set V)) c hsub)
    rwa [SimpleGraph.Walk.length_map] at h
  have hle1 : (G.induce ({w | w ≠ v} : Set V)).girth ≤ G.girth := by
    have h := hcyc.girth_le_length
    rw [hlen'] at h
    omega
  have hnac : ¬ (G.induce ({w | w ≠ v} : Set V)).IsAcyclic :=
    fun hA => hA (c.induce ({w | w ≠ v} : Set V) hsub) hcyc
  have hle2 : G.girth ≤ (G.induce ({w | w ≠ v} : Set V)).girth := by
    obtain ⟨a', c', hc', hlen2⟩ := SimpleGraph.exists_girth_eq_length.mpr hnac
    have hinj : Function.Injective
        ((SimpleGraph.Embedding.induce (G := G) {w | w ≠ v}).toHom) :=
      fun x y h => (SimpleGraph.Embedding.induce (G := G) {w | w ≠ v}).injective h
    have hcyc' : (c'.map (SimpleGraph.Embedding.induce (G := G) {w | w ≠ v}).toHom).IsCycle :=
      hc'.map hinj
    have h := hcyc'.girth_le_length
    rw [SimpleGraph.Walk.length_map] at h
    omega
  omega

/-! ### Preserving the average degree -/

/-- Deleting a vertex of degree at most one does not decrease the average
degree, since at most one edge is lost. -/
theorem avg_induce_compl {d : ℝ} (v : V) (hv : G.degree v ≤ 1) (hd : 2 ≤ d)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) :
    (Fintype.card {w : V // w ≠ v} : ℝ) * d
      ≤ (nDart (G.induce ({w | w ≠ v} : Set V)) : ℝ) := by
  have hcard : (Fintype.card {w : V // w ≠ v} : ℝ) = (Fintype.card V : ℝ) - 1 := by
    have h0 : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
      have h := Fintype.card_subtype_compl (fun w : V => w = v)
      rw [Fintype.card_subtype_eq] at h
      exact h
    rw [h0]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    have h1 : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
      ring
    rw [h1]
  have hnd : (nDart G : ℝ)
      = (nDart (G.induce ({w | w ≠ v} : Set V)) : ℝ) + 2 * (G.degree v : ℝ) := by
    rw [nDart_induce_compl_add G v]
    push_cast
    ring
  have hvR : (G.degree v : ℝ) ≤ 1 := by exact_mod_cast hv
  calc (Fintype.card {w : V // w ≠ v} : ℝ) * d
      = ((Fintype.card V : ℝ) - 1) * d := by rw [hcard]
    _ = (Fintype.card V : ℝ) * d - d := by ring
    _ ≤ (nDart G : ℝ) - d := by linarith
    _ = (nDart (G.induce ({w | w ≠ v} : Set V)) : ℝ) + 2 * (G.degree v : ℝ) - d := by
          rw [hnd]
    _ ≤ (nDart (G.induce ({w | w ≠ v} : Set V)) : ℝ) + 2 * 1 - 2 := by
          have h2 : 2 * (G.degree v : ℝ) ≤ 2 := by linarith
          linarith
    _ = (nDart (G.induce ({w | w ≠ v} : Set V)) : ℝ) := by ring

end Delete

/-! ### Theorem 1 -/

/-- Auxiliary form of Theorem 1, by induction on the number of vertices: for
every `m`, every graph on at most `m` vertices with average degree at least
`d ≥ 2` has at least `n₀(d, girth)` vertices. -/
theorem n0_bound_aux (m : ℕ) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
      {d : ℝ}, Fintype.card α ≤ m → 2 ≤ d →
      (Fintype.card α : ℝ) * d ≤ (nDart G : ℝ) →
      n0 d G.girth ≤ (Fintype.card α : ℝ) := by
  induction m with
  | zero =>
      intro α _ _ G _ d hcard hd havg
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
      have hacyc : G.IsAcyclic := fun v _ _ => isEmptyElim v
      rw [SimpleGraph.girth_eq_zero.mpr hacyc, n0_zero]
      exact Nat.cast_nonneg _
  | succ m ih =>
      intro α _ _ G _ d hcard hd havg
      by_cases hsmall : Fintype.card α ≤ m
      · exact ih α G hsmall hd havg
      · have hcardα : Fintype.card α = m + 1 := by omega
        by_cases hg : G.girth = 0
        · rw [hg, n0_zero]
          exact Nat.cast_nonneg _
        · have hT : ¬ G.IsAcyclic := fun hA => hg (SimpleGraph.girth_eq_zero.mpr hA)
          by_cases hdeg : ∀ w, 2 ≤ G.degree w
          · haveI : Nonempty α :=
              Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
            exact n0_bound_min_deg G hdeg hd havg
          · push Not at hdeg
            obtain ⟨v, hv⟩ := hdeg
            have hv1 : G.degree v ≤ 1 := by omega
            have hcards : Fintype.card {w : α // w ≠ v} = m := by
              have h := Fintype.card_subtype_compl (fun w : α => w = v)
              rw [Fintype.card_subtype_eq] at h
              show Fintype.card {w : α // ¬ w = v} = m
              omega
            have hcardle : Fintype.card {w : α // w ≠ v} ≤ m := by omega
            have hcineq : (Fintype.card {w : α // w ≠ v} : ℝ)
                * d ≤ (nDart (G.induce ({w | w ≠ v} : Set α)) : ℝ) :=
              avg_induce_compl G v hv1 hd havg
            have hres := ih {w : α // w ≠ v} (G.induce ({w | w ≠ v} : Set α))
              hcardle hd hcineq
            rw [girth_induce_compl G v hT hv1] at hres
            have hle : (Fintype.card {w : α // w ≠ v} : ℝ) ≤ (Fintype.card α : ℝ) := by
              have : Fintype.card {w : α // w ≠ v} ≤ Fintype.card α :=
                Fintype.card_subtype_le _
              exact_mod_cast this
            exact hres.trans hle


/-!
## Part 10. Theorem 1 of Alon, Hoory and Linial

This section states Theorem 1 of N. Alon, S. Hoory and N. Linial, "The Moore bound
for irregular graphs" (2002): a finite simple graph with `n` vertices, girth `g`
and average degree at least `d ≥ 2` has at least `n₀(d, g)` vertices, where

* `n₀(d, 2r+1) = 1 + d ∑_{i<r} (d-1)^i`, and
* `n₀(d, 2r) = 2 ∑_{i<r} (d-1)^i`

is the number of vertices of a ball of radius `⌊(g-1)/2⌋` in a `d`-regular graph
of girth `g`.

The proof first deletes vertices of degree at most one, which keeps the girth and
does not decrease the average degree (`Part 9`), and then
applies the counting argument for graphs of minimum degree at least two
(`Part 8`).

## Main results

* `MooreBound.moore_bound` : Theorem 1, as a real inequality;
* `MooreBound.moore_bound_of_girth` : Theorem 1 with the girth as a parameter;
* `MooreBound.moore_bound_nat` : Theorem 1, with `n₀` rounded up to a natural
  number so that the conclusion is an inequality between natural numbers.
-/

set_option maxHeartbeats 800000

/-- **Theorem 1 of Alon–Hoory–Linial.**  A finite simple graph `G` whose average
degree is at least `d ≥ 2` has at least `n₀(d, g)` vertices, where `g` is its
girth.  In other words, `n(d, g) ≥ n₀(d, g)`. -/
theorem moore_bound (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ} (hd : 2 ≤ d)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) :
    n0 d G.girth ≤ (Fintype.card V : ℝ) :=
  n0_bound_aux (Fintype.card V) V G le_rfl hd havg

/-- **Theorem 1 of Alon–Hoory–Linial**, stated with the girth as a parameter. -/
theorem moore_bound_of_girth (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ} {g : ℕ}
    (hd : 2 ≤ d) (hg : G.girth = g)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) :
    n0 d g ≤ (Fintype.card V : ℝ) := by
  rw [← hg]
  exact moore_bound G hd havg

/-- **Theorem 1 of Alon–Hoory–Linial**, rounded up to a statement about natural
numbers: the number of vertices of `G` is at least `⌈n₀(d, g)⌉`. -/
theorem moore_bound_nat (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ} (hd : 2 ≤ d)
    (havg : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ)) :
    Nat.ceil (n0 d G.girth) ≤ Fintype.card V := by
  rw [Nat.ceil_le]
  exact moore_bound G hd havg

/-!
## Part 11. Graphs without short cycles (Section 4 of [16])

Section 4 of the paper deduces from the Moore bound the edge bounds needed for
Lemma 4.  The key observation is that a graph has no cycle of length
`3, …, g-1` exactly when it is acyclic or has girth at least `g`
(`noCyclesUpTo_iff_le_girth`).  In particular a graph that is not a forest
contains a cycle, so any graph without short cycles is a forest as soon as the
number of vertices is at most the forbidden length.

## Main results

* `MooreBound.NoCyclesUpTo` : the predicate "no cycle of length at most `m`";
* `MooreBound.ncard_edgeSet_le_pred_of_noCycles` : a graph on at most `2k`
  vertices with no shorter cycle has at most `n - 1` edges;
* `MooreBound.ncard_edgeSet_le_rpow` : the Moore bound as an edge bound.
-/

set_option maxHeartbeats 800000

/-! ### Cycles and girth -/

/-- `G` has no cycle of length at most `m`, i.e. no cycle of length `3, …, m`. -/
def NoCyclesUpTo {W : Type*} (G : SimpleGraph W) (m : ℕ) : Prop :=
  ∀ ⦃v : W⦄ (c : G.Walk v v), c.IsCycle → m < c.length

theorem noCyclesUpTo_of_isAcyclic {W : Type*} {G : SimpleGraph W} (h : G.IsAcyclic) (m : ℕ) :
    NoCyclesUpTo G m :=
  fun _ c hc => (h c hc).elim

theorem NoCyclesUpTo.mono {W : Type*} {G : SimpleGraph W} {m m' : ℕ} (h : NoCyclesUpTo G m)
    (hmm : m' ≤ m) : NoCyclesUpTo G m' :=
  fun _ c hc => lt_of_le_of_lt hmm (h c hc)

/-- A cycle has at most as many edges as the graph has vertices. -/
theorem length_le_card_of_isCycle {W : Type*} [Fintype W] {G : SimpleGraph W} {v : W}
    {c : G.Walk v v} (h : c.IsCycle) : c.length ≤ Fintype.card W := by
  have hp : c.dropLast.IsPath :=
    (SimpleGraph.Walk.isCycle_iff_isPath_dropLast_and_le_length.mp h).1
  have hlt : c.dropLast.length < Fintype.card W := SimpleGraph.Walk.IsPath.length_lt hp
  have hlen : c.dropLast.length = c.length - 1 := SimpleGraph.Walk.length_dropLast c
  omega

/-- A graph all of whose cycles are longer than the number of its vertices is acyclic. -/
theorem isAcyclic_of_noCyclesUpTo {W : Type*} [Fintype W] {G : SimpleGraph W} {m : ℕ}
    (h : NoCyclesUpTo G m) (hm : Fintype.card W ≤ m) : G.IsAcyclic := by
  intro v c hc
  have h1 : c.length ≤ Fintype.card W := length_le_card_of_isCycle hc
  have h2 : m < c.length := h c hc
  omega

/-- A graph that is not a forest contains a cycle. -/
theorem exists_isCycle_of_not_isAcyclic {W : Type*} {G : SimpleGraph W} (h : ¬ G.IsAcyclic) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle :=
  SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp h

/-- A graph has no cycle of length at most `g - 1` — that is, no cycle of length
`3, …, g - 1` — if and only if its girth is at least `g`, or it is acyclic. -/
theorem noCyclesUpTo_iff_le_girth {W : Type*} (G : SimpleGraph W) (g : ℕ) :
    NoCyclesUpTo G (g - 1) ↔ G.IsAcyclic ∨ g ≤ G.girth := by
  constructor
  · intro h
    by_cases hA : G.IsAcyclic
    · exact Or.inl hA
    · right
      by_contra hcon
      push Not at hcon
      obtain ⟨v, c, hc, hgl⟩ := SimpleGraph.exists_girth_eq_length.mpr hA
      have h1 : g - 1 < c.length := h c hc
      have h2 : G.girth ≤ g - 1 := Nat.le_sub_one_of_lt hcon
      exact absurd (hgl ▸ h2) (not_le_of_gt h1)
  · rintro (hA | hg)
    · intro v c hc
      exact (hA c hc).elim
    · intro v c hc
      have h2 : G.girth ≤ c.length := SimpleGraph.Walk.IsCycle.girth_le_length hc
      have h3 : g ≤ c.length := le_trans hg h2
      rcases Nat.eq_zero_or_pos g with h0 | hpos
      · subst h0
        have h4 : 3 ≤ c.length := hc.isCircuit.three_le_length
        omega
      · exact lt_of_lt_of_le (Nat.sub_lt hpos (by decide)) h3

/-! ### Counting edges -/

omit [DecidableEq V] in
theorem nDart_eq_two_mul_ncard (G : SimpleGraph V) [DecidableRel G.Adj] :
    nDart G = 2 * G.edgeSet.ncard := by
  rw [nDart, SimpleGraph.dart_card_eq_twice_card_edges, ← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard]

/-- A graph on a finite vertex set with no cycle of length `3, ..., 2k` and at
most `2k` vertices has at most `card V - 1` edges. -/
theorem ncard_edgeSet_le_pred_of_noCycles {W : Type*} [Fintype W]
    {G : SimpleGraph W} {k : ℕ} (h : NoCyclesUpTo G (2 * k)) (hm : Fintype.card W ≤ 2 * k) :
    G.edgeSet.ncard ≤ Fintype.card W - 1 := by
  have hA := isAcyclic_of_noCyclesUpTo h hm
  have h1 := hA.ncard_edgeSet_add_card_connectedComponent (V := W)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
  rcases isEmpty_or_nonempty W with hW | hW
  · haveI := hW
    have h0 : Fintype.card W = 0 := Fintype.card_eq_zero_iff.mpr hW
    omega
  · haveI := hW
    have hc : 0 < Nat.card G.ConnectedComponent := Nat.card_pos
    rw [Nat.card_eq_fintype_card] at hc
    omega

/-- For `g ≥ 2k+1` the Moore bound `n₀(d, g)` is at least `1 + d ∑_{i<k} (d-1)^i`,
the number of vertices of the odd-degree model graph. -/
theorem n0_ge_odd_form {d : ℝ} (hd : 1 ≤ d) {k g : ℕ} (hg : 2 * k + 1 ≤ g) :
    1 + d * ∑ i ∈ Finset.range k, (d - 1) ^ i ≤ n0 d g := by
  have hd0 : (0 : ℝ) ≤ d := le_trans zero_le_one hd
  have hx0 : (0 : ℝ) ≤ d - 1 := by linarith
  set S : ℝ := ∑ i ∈ Finset.range k, (d - 1) ^ i with hS
  set Sg : ℝ := ∑ i ∈ Finset.range (g / 2), (d - 1) ^ i with hSg
  have hSk : S ≤ Sg := by
    rw [hS, hSg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hx0 i)
    intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  by_cases hpar : g % 2 = 1
  · rw [n0_odd_form d hpar, ← hSg]
    nlinarith
  · rw [n0_even_form d hpar, ← hSg]
    have hge : k + 1 ≤ g / 2 := by omega
    have hS1 : ∑ i ∈ Finset.range (k + 1), (d - 1) ^ i ≤ Sg := by
      rw [hSg]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => pow_nonneg hx0 i)
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hSsucc : ∑ i ∈ Finset.range (k + 1), (d - 1) ^ i = S + (d - 1) ^ k := by
      rw [hS, Finset.sum_range_succ]
    have hid : S * (d - 2) + 1 = (d - 1) ^ k := by
      have h := geom_sum_mul_add (d - 2) k
      have h2 : ((d - 2) + 1) = d - 1 := by ring
      rw [h2] at h
      rw [hS]
      exact h
    have hpow : (0 : ℝ) ≤ (d - 1) ^ k := pow_nonneg hx0 k
    nlinarith [hS1, hSsucc, hid, hpow]

/-- **The Moore bound as a bound on the number of edges.**  A graph on `n`
vertices with no cycle of length at most `2k`, where `k ≥ 2` and `n ≥ 2k+1`, has
at most `½(n^{1+1/k} + n)` edges. -/
theorem ncard_edgeSet_le_rpow {k : ℕ} (hk : 2 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : NoCyclesUpTo G (2 * k)) (hn : 2 * k + 1 ≤ Fintype.card V) :
    (G.edgeSet.ncard : ℝ) ≤
      ((Fintype.card V : ℝ) ^ ((1 : ℝ) + ((k : ℝ))⁻¹) + (Fintype.card V : ℝ)) / 2 := by
  classical
  have hk2 : (0 : ℝ) < (k : ℝ) := by
    have : (0 : ℕ) < k := by omega
    exact_mod_cast this
  have hcardpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  set m : ℝ := (G.edgeSet.ncard : ℝ) with hm_def
  set x : ℝ := n ^ ((k : ℝ))⁻¹ with hx_def
  have hn1 : (1 : ℝ) ≤ n := by
    rw [hn_def]
    exact_mod_cast (by omega : 1 ≤ Fintype.card V)
  have hnpos : (0 : ℝ) < n := by linarith
  have hle : n ≤ n ^ ((1 : ℝ) + ((k : ℝ))⁻¹) := by
    have hexp : (1 : ℝ) ≤ 1 + ((k : ℝ))⁻¹ := by
      have : (0 : ℝ) ≤ ((k : ℝ))⁻¹ := by positivity
      linarith
    calc n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
      _ ≤ n ^ ((1 : ℝ) + ((k : ℝ))⁻¹) := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  by_cases hbig : 2 * n ≤ 2 * m
  · by_cases hA : G.IsAcyclic
    · haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      have hb := hA.ncard_edgeSet_add_one_le_card (V := V)
      rw [Nat.card_eq_fintype_card] at hb
      have hb' : m + 1 ≤ n := by
        rw [hm_def, hn_def]
        exact_mod_cast hb
      linarith
    · have hg : 2 * k < G.girth := by
        have h1 : G.IsAcyclic ∨ 2 * k + 1 ≤ G.girth :=
          (noCyclesUpTo_iff_le_girth G (2 * k + 1)).mp (by simpa using h)
        rcases h1 with h1 | h1
        · exact absurd h1 hA
        · omega
      set d : ℝ := 2 * m / n with hd_def
      have hd2 : 2 ≤ d := by
        rw [hd_def, le_div_iff₀ hnpos]
        linarith
      have hdn : d * n = 2 * m := by
        rw [hd_def]
        exact div_mul_cancel₀ _ (ne_of_gt hnpos)
      have havg : n * d = (nDart G : ℝ) := by
        rw [mul_comm n d, hdn, nDart_eq_two_mul_ncard, hm_def]
        push_cast
        ring
      have hmoore : n0 d G.girth ≤ n := by
        have h1 : (Fintype.card V : ℝ) * d ≤ (nDart G : ℝ) := by
          rw [← hn_def]
          exact le_of_eq havg
        have h2 := moore_bound G hd2 h1
        rwa [← hn_def] at h2
      have hlow : 1 + d * ∑ i ∈ Finset.range k, (d - 1) ^ i ≤ n0 d G.girth :=
        n0_ge_odd_form (by linarith : (1 : ℝ) ≤ d) hg
      have hlt : d < 1 + x := by
        by_contra hcon
        push Not at hcon
        have hx0 : (0 : ℝ) ≤ x := Real.rpow_nonneg (le_of_lt hnpos) _
        set Sx : ℝ := ∑ i ∈ Finset.range k, x ^ i with hSx
        have hSx0 : 0 ≤ Sx := by
          rw [hSx]
          exact Finset.sum_nonneg (fun i _ => pow_nonneg hx0 i)
        have hSmono : Sx ≤ ∑ i ∈ Finset.range k, (d - 1) ^ i := by
          rw [hSx]
          exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hx0 (by linarith) i)
        have hstep : 1 + (1 + x) * Sx ≤ 1 + d * ∑ i ∈ Finset.range k, (d - 1) ^ i := by
          have h1 : (1 + x) * Sx ≤ d * ∑ i ∈ Finset.range k, (d - 1) ^ i :=
            mul_le_mul hcon hSmono hSx0 (by linarith)
          linarith
        have hS1 : (1 : ℝ) ≤ Sx := by
          rw [hSx]
          have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
          have := Finset.single_le_sum (f := fun i => x ^ i)
            (fun i _ => pow_nonneg hx0 i) h0
          simpa using this
        have hgeo : Sx * (x - 1) + 1 = x ^ k := by
          have h := geom_sum_mul_add (x - 1) k
          have h2 : ((x - 1) + 1) = x := by ring
          rw [h2] at h
          rw [hSx]
          exact h
        have hxk : x ^ k = n := by
          rw [hx_def, ← Real.rpow_natCast]
          have h1 : ((k : ℝ))⁻¹ * (k : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hk2)
          calc (n ^ ((k : ℝ))⁻¹) ^ (k : ℝ) = n ^ (((k : ℝ))⁻¹ * (k : ℝ)) :=
                (Real.rpow_mul (le_of_lt hnpos) _ _).symm
            _ = n ^ (1 : ℝ) := by rw [h1]
            _ = n := Real.rpow_one n
        rw [hxk] at hgeo
        nlinarith
      have h2 : 2 * m < n + n * x := by
        rw [hd_def] at hlt
        rw [div_lt_iff₀ hnpos] at hlt
        nlinarith
      have hnx : n * x = n ^ ((1 : ℝ) + ((k : ℝ))⁻¹) := by
        rw [hx_def, Real.rpow_add hnpos, Real.rpow_one]
      rw [hnx] at h2
      linarith
  · push Not at hbig
    linarith

/-!
## Part 12. The independence index, Minkowski sums and Lemma 4 (Section 4 of [16])

The *independence index* `ind B` of a finite set `B` of vectors over `GF(2)` is
the largest `k ≤ |B|` such that every `k` elements of `B` are linearly
independent (`Indep`, `AllIndep`, `ind`).  The *Minkowski sum* of two finite
sets is `B + C = {b + c | b ∈ B, c ∈ C}`, and `msum k B` is the `k`-fold sum,
with the convention `msum 0 B = ∅` (`minkowski`, `msum`).

**Lemma 4** of [16]: if `D ⊂ GF(2)^m`, `B ⊆ D + D` and `ind B ≥ 2k ≥ 4`, then
`|B| ≤ |D| - 1` when `|D| ≤ 2k`, and `|B| ≤ |D|^{1+1/k}` when `|D| ≥ 2k + 1`.

The proof builds a graph `G_B` on the vertex set `D`: for every `b ∈ B` choose a
pair `a, a' ∈ D` with `a + a' = b` and add the edge `{a, a'}` (`GBgraph`).
The choice is injective on `B`, so `G_B` has `|B|` edges.  A cycle of length `r`
would give `r` distinct elements of `B` summing to zero, which contradicts the
independence of the `r`-element subsets of `B` when `r ≤ 2k`; hence `G_B` has no
short cycles, and `ncard_edgeSet_le_rpow` bounds its number of edges.

## Main results

* `MooreBound.Indep`, `MooreBound.AllIndep`, `MooreBound.ind` : the
  independence index;
* `MooreBound.minkowski`, `MooreBound.msum` : Minkowski sums;
* `MooreBound.symSum` : the sum of the endpoints of an unordered pair;
* `MooreBound.GBgraph` : the graph `G_B` associated with `B ⊆ D + D`;
* `MooreBound.lemma4` : Lemma 4 of [16].
-/

set_option maxHeartbeats 2000000

/-! ### Independence index and Minkowski sums -/

variable {m : ℕ}

/-- The sum of the two entries of an unordered pair of vectors. -/
def symSum {A : Type*} [AddCommMagma A] : Sym2 A → A :=
  Sym2.lift ⟨(· + ·), fun a b => add_comm a b⟩

@[simp] theorem symSum_mk {A : Type*} [AddCommMagma A] (a b : A) :
    symSum s(a, b) = a + b := rfl

theorem add_self_fun (x : Fin m → ZMod 2) : x + x = 0 := by
  funext i
  have h : (2 : ZMod 2) = 0 := by decide
  calc x i + x i = 2 * x i := (two_mul (x i)).symm
    _ = 0 := by rw [h, zero_mul]

theorem add_add_add_cancel {A : Type*} [AddCommGroup A] (hA : ∀ x : A, x + x = 0) (a b c : A) :
    (a + b) + (b + c) = a + c := by
  rw [add_assoc a b (b + c), ← add_assoc b b c, hA b, zero_add]

/-- The sum of the endpoint sums along a walk is the sum of its endpoints. -/
theorem walk_edges_sum {A : Type*} [AddCommGroup A] (hA : ∀ x : A, x + x = 0)
    {G : SimpleGraph A} {u v : A} (c : G.Walk u v) :
    (c.edges.map (symSum (A := A))).sum = u + v := by
  induction c with
  | nil => exact (hA _).symm
  | cons hd p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih]
    simp only [symSum_mk]
    exact add_add_add_cancel hA _ _ _

/-- Minkowski sum of two finite sets of vectors over `GF(2)`. -/
def minkowski (B C : Finset (Fin m → ZMod 2)) : Finset (Fin m → ZMod 2) :=
  B.biUnion fun b => C.image fun c => b + c

@[simp] theorem mem_minkowski {B C : Finset (Fin m → ZMod 2)} {x : Fin m → ZMod 2} :
    x ∈ minkowski B C ↔ ∃ b ∈ B, ∃ c ∈ C, b + c = x := by
  simp only [minkowski, Finset.mem_biUnion, Finset.mem_image]

/-- The `k`-fold Minkowski sum, with the convention `0 • B = ∅` of the paper. -/
def msum : ℕ → Finset (Fin m → ZMod 2) → Finset (Fin m → ZMod 2)
  | 0, _ => ∅
  | 1, B => B
  | k + 2, B => minkowski (msum (k + 1) B) B

@[simp] theorem msum_zero (B : Finset (Fin m → ZMod 2)) : msum 0 B = ∅ := rfl

@[simp] theorem msum_one (B : Finset (Fin m → ZMod 2)) : msum 1 B = B := rfl

theorem msum_add_two (k : ℕ) (B : Finset (Fin m → ZMod 2)) :
    msum (k + 2) B = minkowski (msum (k + 1) B) B := rfl

@[simp] theorem msum_two (B : Finset (Fin m → ZMod 2)) : msum 2 B = minkowski B B := by
  simpa using msum_add_two 0 B

/-- A finite set of vectors over `GF(2)` is linearly independent. -/
def Indep (S : Finset (Fin m → ZMod 2)) : Prop :=
  LinearIndependent (ZMod 2) (fun x : S => (x : Fin m → ZMod 2))

theorem indep_empty : Indep (∅ : Finset (Fin m → ZMod 2)) :=
  linearIndependent_empty_type

theorem Indep.mono {S T : Finset (Fin m → ZMod 2)} (h : Indep T) (hST : S ⊆ T) : Indep S := by
  have h' := h.comp (fun x : S => (⟨x.1, hST x.2⟩ : T)) (fun x y hxy => by
    have := congrArg Subtype.val hxy
    simpa using this)
  simpa [Indep, Function.comp_def] using h'

/-- `AllIndep B k`: every `k`-element subset of `B` is linearly independent. -/
def AllIndep (B : Finset (Fin m → ZMod 2)) (k : ℕ) : Prop :=
  ∀ S : Finset (Fin m → ZMod 2), S ⊆ B → S.card = k → Indep S

/-- The independence index of a finite set of vectors over `GF(2)`: the largest
`k ≤ |B|` such that every `k` elements of `B` are linearly independent. -/
noncomputable def ind (B : Finset (Fin m → ZMod 2)) : ℕ := by
  classical
  exact Nat.findGreatest (AllIndep B) B.card

theorem ind_le_card (B : Finset (Fin m → ZMod 2)) : ind B ≤ B.card := by
  classical
  unfold ind
  exact Nat.findGreatest_le _

theorem allIndep_zero (B : Finset (Fin m → ZMod 2)) : AllIndep B 0 := by
  intro S _ hc
  rw [Finset.card_eq_zero.mp hc]
  exact indep_empty

theorem ind_spec (B : Finset (Fin m → ZMod 2)) : AllIndep B (ind B) := by
  classical
  unfold ind
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (allIndep_zero B)

theorem ind_elim {B S : Finset (Fin m → ZMod 2)} {r : ℕ} (hr : r ≤ ind B) (hSB : S ⊆ B)
    (hcard : S.card = r) : Indep S := by
  classical
  obtain ⟨T, hST, hTB, hTc⟩ := Finset.exists_subsuperset_card_eq hSB (hcard ▸ hr) (ind_le_card B)
  exact (ind_spec B T hTB hTc).mono hST

theorem le_ind {B : Finset (Fin m → ZMod 2)} {r : ℕ} (h : AllIndep B r) (hr : r ≤ B.card) :
    r ≤ ind B := by
  classical
  unfold ind
  exact Nat.le_findGreatest hr h

/-- A dependent subset of `B` of size at most `M` forces `ind B < M`. -/
theorem ind_lt_of_dependent {B S : Finset (Fin m → ZMod 2)} {M : ℕ} (hSB : S ⊆ B)
    (hdep : ¬ Indep S) (hSM : S.card ≤ M) (hMB : M ≤ B.card) : ind B < M := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hST, hTB, hTc⟩ := Finset.exists_subsuperset_card_eq hSB hSM hMB
  exact hdep ((ind_elim (hTc ▸ hcon) hTB rfl).mono hST)

/-- The sum of a nonempty set of distinct vectors is not a linear dependence. -/
theorem not_indep_of_sum_eq_zero {S : Finset (Fin m → ZMod 2)} (hne : S.Nonempty)
    (hsum : ∑ x ∈ S, x = 0) : ¬ Indep S := by
  intro hLI
  obtain ⟨x, hx⟩ := hne
  have h := (linearIndependent_iff'.mp hLI) (Finset.univ : Finset ↥S) (fun _ => (1 : ZMod 2))
  have hsum' : ∑ i : ↥S, (1 : ZMod 2) • (i : Fin m → ZMod 2) = 0 := by
    rw [Finset.sum_coe_sort]
    simpa using hsum
  exact one_ne_zero (h hsum' ⟨x, hx⟩ (Finset.mem_univ _))


/-! ### Lemma 4: graphs from sets with large independence index -/

/-- If `ind B ≥ 1` then `B` does not contain the zero vector. -/
theorem zero_not_mem_of_ind_pos {B : Finset (Fin m → ZMod 2)} (h : 1 ≤ ind B) :
    (0 : Fin m → ZMod 2) ∉ B := by
  intro h0
  have h1 : ({0} : Finset (Fin m → ZMod 2)) ⊆ B := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact h0
  have hdep : ¬ Indep ({0} : Finset (Fin m → ZMod 2)) := by
    refine not_indep_of_sum_eq_zero (Finset.singleton_nonempty 0) ?_
    simp
  have := ind_lt_of_dependent h1 hdep (M := 1) (by simp) (Finset.card_pos.mpr ⟨0, h0⟩)
  omega

/-- First summand of a chosen representation `b = a + a'` with `a, a' ∈ D`. -/
noncomputable def pick₁ (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (b : {x // x ∈ B}) :
    {x // x ∈ D} :=
  ⟨Classical.choose (hBD b.1 b.2), (Classical.choose_spec (hBD b.1 b.2)).1⟩

/-- Second summand of a chosen representation `b = a + a'` with `a, a' ∈ D`. -/
noncomputable def pick₂ (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (b : {x // x ∈ B}) :
    {x // x ∈ D} :=
  ⟨Classical.choose (Classical.choose_spec (hBD b.1 b.2)).2,
    (Classical.choose_spec (Classical.choose_spec (hBD b.1 b.2)).2).1⟩

theorem pick_sum (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (b : {x // x ∈ B}) :
    (pick₁ D B hBD b : Fin m → ZMod 2) + (pick₂ D B hBD b : Fin m → ZMod 2) = b.1 :=
  (Classical.choose_spec (Classical.choose_spec (hBD b.1 b.2)).2).2

theorem pick_ne (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b)
    (h0 : (0 : Fin m → ZMod 2) ∉ B) (b : {x // x ∈ B}) :
    pick₁ D B hBD b ≠ pick₂ D B hBD b := by
  intro h
  have hv : (pick₁ D B hBD b : Fin m → ZMod 2) = pick₂ D B hBD b := congrArg Subtype.val h
  have hsum := pick_sum D B hBD b
  rw [hv, add_self_fun] at hsum
  exact h0 (hsum.symm ▸ b.2)

/-- The chosen edge of `G_B` representing `b ∈ B`. -/
noncomputable def GBedge (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (b : {x // x ∈ B}) :
    Sym2 {x // x ∈ D} :=
  s(pick₁ D B hBD b, pick₂ D B hBD b)

/-- Sum of the two endpoints of an edge of the graph on `D`. -/
def symSumD {m : ℕ} {D : Finset (Fin m → ZMod 2)} (e : Sym2 {x // x ∈ D}) :
    Fin m → ZMod 2 :=
  symSum (e.map Subtype.val)

@[simp] theorem symSumD_mk {m : ℕ} {D : Finset (Fin m → ZMod 2)} (a a' : {x // x ∈ D}) :
    symSumD (s(a, a') : Sym2 {x // x ∈ D}) = (a : Fin m → ZMod 2) + a' := by
  simp only [symSumD, Sym2.map_mk, symSum_mk]

theorem symSumD_GBedge (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (b : {x // x ∈ B}) :
    symSumD (D := D) (GBedge D B hBD b) = b.1 := by
  simp only [GBedge, symSumD_mk]
  exact pick_sum D B hBD b

theorem GBedge_injective (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) :
    Function.Injective (GBedge D B hBD) := by
  intro b₁ b₂ h
  have h2 : b₁.1 = b₂.1 := by
    simpa only [symSumD_GBedge] using congrArg (symSumD (D := D)) h
  exact Subtype.ext h2

/-- The edge set of the graph `G_B` of Lemma 4. -/
noncomputable def edgeSet (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) :
    Finset (Sym2 {x // x ∈ D}) :=
  Finset.univ.image (GBedge D B hBD)

theorem edgeSet_card (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) :
    (edgeSet D B hBD).card = B.card := by
  rw [edgeSet, Finset.card_image_of_injective _ (GBedge_injective D B hBD), Finset.card_univ,
    Fintype.card_coe]

theorem mem_edgeSet {D B : Finset (Fin m → ZMod 2)}
    {hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b} {e : Sym2 {x // x ∈ D}} :
    e ∈ edgeSet D B hBD ↔ ∃ b : {x // x ∈ B}, GBedge D B hBD b = e := by
  simp [edgeSet, eq_comm]

theorem edgeSet_not_diag (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b)
    (h0 : (0 : Fin m → ZMod 2) ∉ B) {e : Sym2 {x // x ∈ D}}
    (he : e ∈ edgeSet D B hBD) : ¬ e.IsDiag := by
  obtain ⟨b, hb⟩ := (mem_edgeSet (hBD := hBD)).mp he
  rw [← hb, GBedge, Sym2.mk_isDiag_iff]
  exact pick_ne D B hBD h0 b

/-- The graph `G_B` of Lemma 4: vertices `D`, and one edge for every `b ∈ B`
chosen among the pairs of `D` whose sum is `b`. -/
noncomputable def GBgraph (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) : SimpleGraph {x // x ∈ D} :=
  SimpleGraph.fromEdgeSet ((edgeSet D B hBD : Finset (Sym2 {x // x ∈ D})) : Set _)

theorem GBgraph_edgeSet (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b)
    (h0 : (0 : Fin m → ZMod 2) ∉ B) :
    (GBgraph D B hBD).edgeSet = ((edgeSet D B hBD : Finset (Sym2 {x // x ∈ D})) : Set _) := by
  rw [GBgraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
  exact ⟨fun h => h.1, fun h => ⟨h, edgeSet_not_diag D B hBD h0 h⟩⟩

theorem GBgraph_ncard (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b)
    (h0 : (0 : Fin m → ZMod 2) ∉ B) :
    (GBgraph D B hBD).edgeSet.ncard = B.card := by
  rw [GBgraph_edgeSet D B hBD h0, Set.ncard_coe_finset, edgeSet_card]

/-- The label of an edge of `G_B`: the unique `b ∈ B` it represents. -/
noncomputable def lab (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) (e : Sym2 {x // x ∈ D}) :
    Fin m → ZMod 2 :=
  if h : e ∈ edgeSet D B hBD then (Classical.choose ((mem_edgeSet (hBD := hBD)).mp h)).1 else 0

theorem lab_mem (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) {e : Sym2 {x // x ∈ D}}
    (he : e ∈ edgeSet D B hBD) : lab D B hBD e ∈ B := by
  rw [lab, dite_eq_left he]
  exact (Classical.choose ((mem_edgeSet (hBD := hBD)).mp he)).2

theorem lab_edge (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) {e : Sym2 {x // x ∈ D}}
    (he : e ∈ edgeSet D B hBD) :
    GBedge D B hBD ⟨lab D B hBD e, lab_mem D B hBD he⟩ = e := by
  have := Classical.choose_spec ((mem_edgeSet (hBD := hBD)).mp he)
  simpa only [lab, dite_eq_left he] using this

theorem lab_injOn (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) {e₁ e₂ : Sym2 {x // x ∈ D}}
    (h₁ : e₁ ∈ edgeSet D B hBD) (h₂ : e₂ ∈ edgeSet D B hBD)
    (h : lab D B hBD e₁ = lab D B hBD e₂) : e₁ = e₂ := by
  rw [← lab_edge D B hBD h₁, ← lab_edge D B hBD h₂]
  congr 1
  exact Subtype.ext h

theorem lab_eq_symSumD (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b) {e : Sym2 {x // x ∈ D}}
    (he : e ∈ edgeSet D B hBD) : lab D B hBD e = symSumD e := by
  have h := lab_edge D B hBD he
  calc lab D B hBD e = symSumD (GBedge D B hBD ⟨lab D B hBD e, lab_mem D B hBD he⟩) :=
        by simp only [symSumD_GBedge]
    _ = symSumD e := by rw [h]

/-- The sum of the endpoint sums along a walk in the graph on `D` is the sum of
its endpoints. -/
theorem walk_edges_sumD {m : ℕ} {D : Finset (Fin m → ZMod 2)}
    {G : SimpleGraph {x // x ∈ D}} {u v : {x // x ∈ D}} (c : G.Walk u v) :
    (c.edges.map symSumD).sum = (u : Fin m → ZMod 2) + v := by
  induction c with
  | nil => exact (add_self_fun _).symm
  | cons hd p ih =>
    rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih, symSumD_mk]
    exact add_add_add_cancel add_self_fun _ _ _

/-- The graph `G_B` has no cycle of length at most `2k` when `ind B ≥ 2k`. -/
theorem GBgraph_noCycles (D B : Finset (Fin m → ZMod 2))
    (hBD : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b)
    (h0 : (0 : Fin m → ZMod 2) ∉ B) (k : ℕ) (hk : 2 * k ≤ ind B) :
    NoCyclesUpTo (GBgraph D B hBD) (2 * k) := by
  intro v c hc
  by_contra hle
  push Not at hle
  have hnd : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
  have hsub : ∀ e ∈ c.edges, e ∈ edgeSet D B hBD := by
    intro e he
    have h1 : e ∈ (GBgraph D B hBD).edgeSet := SimpleGraph.Walk.edges_subset_edgeSet c he
    rwa [GBgraph_edgeSet D B hBD h0] at h1
  have hes : (c.edges.toFinset).card = c.length := by
    rw [List.toFinset_card_of_nodup hnd, SimpleGraph.Walk.length_edges]
  have hinj : Set.InjOn (lab D B hBD) ↑(c.edges.toFinset) := by
    intro e₁ h₁ e₂ h₂ h
    exact lab_injOn D B hBD (hsub e₁ (List.mem_toFinset.mp h₁))
      (hsub e₂ (List.mem_toFinset.mp h₂)) h
  set T : Finset (Fin m → ZMod 2) := (c.edges.toFinset).image (lab D B hBD) with hT
  have hTcard : T.card = c.length := by
    rw [hT, Finset.card_image_of_injOn hinj, hes]
  have hTsub : T ⊆ B := by
    intro x hx
    rw [hT] at hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact lab_mem D B hBD (hsub e (List.mem_toFinset.mp he))
  have hTsum : ∑ x ∈ T, x = 0 := by
    have h1 : ∑ e ∈ c.edges.toFinset, lab D B hBD e = ∑ e ∈ c.edges.toFinset, symSumD e :=
      Finset.sum_congr rfl fun e he => lab_eq_symSumD D B hBD (hsub e (List.mem_toFinset.mp he))
    rw [hT, Finset.sum_image hinj, h1, List.sum_toFinset symSumD hnd, walk_edges_sumD c,
      add_self_fun]
  have hne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    have := hc.isCircuit.three_le_length
    omega
  exact not_indep_of_sum_eq_zero hne hTsum (ind_elim (le_trans hle hk) hTsub hTcard)

/-- **Lemma 4** of [16]: if `B ⊆ D + D` and `ind B ≥ 2k ≥ 4`, then `|B| ≤ |D| - 1`
when `|D| ≤ 2k` and `|B| ≤ |D|^{1+1/k}` when `|D| ≥ 2k + 1`. -/
theorem lemma4 (D B : Finset (Fin m → ZMod 2)) (k : ℕ) (hk : 2 ≤ k)
    (hBD : B ⊆ msum 2 D) (hind : 2 * k ≤ ind B) :
    (D.card ≤ 2 * k → B.card ≤ D.card - 1) ∧
      (2 * k + 1 ≤ D.card → (B.card : ℝ) ≤ (D.card : ℝ) ^ (1 + (k : ℝ)⁻¹)) := by
  classical
  rw [msum_two] at hBD
  have hBD' : ∀ b ∈ B, ∃ a ∈ D, ∃ a' ∈ D, a + a' = b :=
    fun b hb => mem_minkowski.mp (hBD hb)
  have h0 : (0 : Fin m → ZMod 2) ∉ B := zero_not_mem_of_ind_pos (by omega)
  have hno := GBgraph_noCycles D B hBD' h0 k hind
  have hnc := GBgraph_ncard D B hBD' h0
  have hW : Fintype.card {x // x ∈ D} = D.card := Fintype.card_coe D
  constructor
  · intro hD
    have h1 := ncard_edgeSet_le_pred_of_noCycles (W := {x // x ∈ D}) hno (by rw [hW]; exact hD)
    rwa [hnc, hW] at h1
  · intro hD
    have h1 := ncard_edgeSet_le_rpow (V := {x // x ∈ D}) hk (GBgraph D B hBD') hno (by rw [hW]; exact hD)
    rw [hnc, hW] at h1
    have hD1 : (1 : ℝ) ≤ (D.card : ℝ) := by
      have : 1 ≤ D.card := by omega
      exact_mod_cast this
    have hexp : (1 : ℝ) ≤ 1 + (k : ℝ)⁻¹ := by
      have : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
      linarith
    have hle : (D.card : ℝ) ≤ (D.card : ℝ) ^ (1 + (k : ℝ)⁻¹) := by
      calc (D.card : ℝ) = (D.card : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (D.card : ℝ) ^ (1 + (k : ℝ)⁻¹) := Real.rpow_le_rpow_of_exponent_le hD1 hexp
    linarith
end MooreBound

namespace AchainsComplexityGF2
open MooreBound
open scoped BigOperators

variable {m : ℕ}

/-! ### The unit vectors and the set `C₀ = B ∪ γI_m` -/

/-- The set of unit vectors of `GF(2)^m`. -/
def unitVecs (m : ℕ) : Finset (Vec m) := Finset.univ.image basisVec

@[simp] theorem mem_unitVecs {v : Vec m} :
    v ∈ unitVecs m ↔ ∃ i : Fin m, basisVec i = v := by
  simp [unitVecs]

theorem basisVec_injective : Function.Injective (basisVec (n := m)) := by
  intro i j h
  by_cases hij : i = j
  · exact hij
  · exfalso
    have h' := congrFun h i
    simp [basisVec, hij] at h'

theorem basisVec_ne_zero (i : Fin m) : (basisVec i : Vec m) ≠ 0 := by
  intro h
  have h' := congrFun h i
  simp [basisVec] at h'


theorem unitVecs_card : (unitVecs m).card = m := by
  have h := Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin m)))
    (f := basisVec) basisVec_injective
  simpa [unitVecs] using h


/-- The unit vectors that are available as inputs of an extended scheme with inessential
variables `aux`, i.e. the basis vectors of the essential coordinates `auxᶜ`. -/
def freeVecs (aux : Finset (Fin m)) : Finset (Vec m) :=
  (unitVecs m).filter (fun v => proj aux v = 0)

@[simp] theorem mem_freeVecs {aux : Finset (Fin m)} {v : Vec m} :
    v ∈ freeVecs aux ↔ ∃ i : Fin m, i ∉ aux ∧ basisVec i = v := by
  rw [freeVecs, Finset.mem_filter, mem_unitVecs]
  constructor
  · rintro ⟨⟨i, rfl⟩, hi⟩
    rw [proj_basisVec] at hi
    by_cases hmem : i ∈ aux
    · rw [if_pos hmem] at hi
      exact absurd hi (basisVec_ne_zero i)
    · exact ⟨i, hmem, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, rfl⟩, by rw [proj_basisVec, if_neg hi]⟩

theorem freeVecs_subset_unitVecs (aux : Finset (Fin m)) : freeVecs aux ⊆ unitVecs m :=
  Finset.filter_subset _ _

theorem freeVecs_card_le (aux : Finset (Fin m)) : (freeVecs aux).card ≤ m := by
  calc (freeVecs aux).card ≤ (unitVecs m).card :=
        Finset.card_le_card (freeVecs_subset_unitVecs aux)
    _ = m := unitVecs_card

/-- The number of unit vectors that the counting bound has to give away.  The elements of the work
set of weight `1` are exactly the unit vectors that are not computed by a step of the chain.  When
`γ = 1` every unit vector of an essential coordinate lies in `C₀`, so only the `|aux|` unit
vectors of the inessential coordinates are left; when `γ = 0` there are at most `m` of them.  For
`aux = ∅` this is the constant `(1-γ)m` of the paper. -/
def inputSlack (aux : Finset (Fin m)) (γ : Bool) : ℕ := if γ then aux.card else m

/-- The set `C₀ = B ∪ γI_m` of Theorem 2; `γ = 1` is represented by `γ = true`.

The matrix `I_m` is the identity on the *essential* coordinates of the scheme: its rows are
single input variables, hence vectors of type `0`.  The basis vectors of the inessential
coordinates `aux` are not inputs of the scheme and are therefore excluded. -/
def C0 (aux : Finset (Fin m)) (γ : Bool) (B : Finset (Vec m)) : Finset (Vec m) :=
  B ∪ if γ then freeVecs aux else ∅

theorem mem_C0 {aux : Finset (Fin m)} {γ : Bool} {B : Finset (Vec m)} {v : Vec m} :
    v ∈ C0 aux γ B ↔ v ∈ B ∨ γ = true ∧ v ∈ freeVecs aux := by
  unfold C0
  by_cases hγ : γ = true <;> simp [hγ]

theorem subset_C0_left {aux : Finset (Fin m)} {γ : Bool} {B : Finset (Vec m)} :
    B ⊆ C0 aux γ B :=
  fun _ h => Finset.mem_union_left _ h


/-- Every vector of `C₀ = B ∪ γI_m` has type `0` as soon as every row of `B` does: the rows of
`B` are circuit outputs, and the rows of `I_m` are single essential input variables. -/
theorem proj_eq_zero_of_mem_C0 {aux : Finset (Fin m)} {γ : Bool} {B : Finset (Vec m)}
    (hB : ∀ b ∈ B, proj aux b = 0) : ∀ x ∈ C0 aux γ B, proj aux x = 0 := by
  intro x hx
  rw [mem_C0] at hx
  rcases hx with hx | ⟨-, hx⟩
  · exact hB x hx
  · obtain ⟨i, hi, rfl⟩ := mem_freeVecs.mp hx
    rw [proj_basisVec, if_neg hi]

theorem C0_card_le (aux : Finset (Fin m)) (γ : Bool) (B : Finset (Vec m)) :
    (C0 aux γ B).card ≤ B.card + m := by
  calc (C0 aux γ B).card ≤ B.card + (if γ then freeVecs aux else ∅).card :=
        Finset.card_union_le _ _
    _ ≤ B.card + m := by
        have h : (if γ then freeVecs aux else ∅).card ≤ m := by
          by_cases hγ : γ = true
          · simp only [hγ, ite_true]; exact freeVecs_card_le aux
          · simp [hγ]
        omega

/-! ### Weights of vectors with respect to all coordinates -/

theorem proj_univ_eq (v : Vec m) : proj (Finset.univ : Finset (Fin m)) v = v := by
  funext i
  simp [proj]


theorem weight_univ_basisVec (i : Fin m) :
    weight (Finset.univ : Finset (Fin m)) (basisVec i) = 1 := by
  unfold weight
  have h : (Finset.univ.filter (fun j : Fin m => basisVec i j ≠ 0)) = {i} := by
    ext j
    simp [basisVec, eq_comm]
  rw [h, Finset.card_singleton]

theorem eq_basisVec_of_weight_univ_eq_one {v : Vec m}
    (h : weight (Finset.univ : Finset (Fin m)) v = 1) : ∃ i : Fin m, v = basisVec i := by
  obtain ⟨i, hi⟩ := proj_eq_basisVec_of_weight_eq_one (Finset.univ : Finset (Fin m)) v h
  exact ⟨i, by rwa [proj_univ_eq] at hi⟩


/-! ### The independence toolkit -/

/-- A linearly independent set has no nonempty subsum equal to zero. -/
theorem Indep.sum_eq_zero {S : Finset (Vec m)} (h : Indep S) (hsum : (∑ x ∈ S, x) = 0) :
    S = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  exact not_indep_of_sum_eq_zero ⟨x, hx⟩ hsum h


/-- A subset of `C` with at most `r` elements is linearly independent when `r ≤ ind C`. -/
theorem Indep_of_subset_of_card_le {C T : Finset (Vec m)} {r : ℕ} (hT : T ⊆ C)
    (hcard : T.card ≤ r) (hr : r ≤ ind C) : Indep T := by
  obtain ⟨T', hTT', hCT', hT'card⟩ :=
    Finset.exists_subsuperset_card_eq hT hcard (le_trans hr (ind_le_card C))
  exact (ind_elim (S := T') (r := r) (hT'card ▸ hr) hCT' hT'card).mono hTT'

/-- **The key independence lemma.**  If `A, B ⊆ C`, `(A ∪ B).card ≤ r ≤ ind C` and the sums of
the elements of `A` and of `B` coincide, then `A = B`. -/
theorem eq_of_sum_eq_of_subset {C A B : Finset (Vec m)} {r : ℕ} (hA : A ⊆ C) (hB : B ⊆ C)
    (hcard : (A ∪ B).card ≤ r) (hr : r ≤ ind C) (hsum : (∑ x ∈ A, x) = ∑ x ∈ B, x) :
    A = B := by
  have hUA : (A ∪ B) \ A = B \ A := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hUB : (A ∪ B) \ B = A \ B := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  have e1 := Finset.sum_sdiff (s₁ := A) (s₂ := A ∪ B) (f := fun x : Vec m => x)
    (Finset.subset_union_left)
  have e2 := Finset.sum_sdiff (s₁ := B) (s₂ := A ∪ B) (f := fun x : Vec m => x)
    (Finset.subset_union_right)
  rw [hUA] at e1
  rw [hUB] at e2
  have hkey : (∑ x ∈ B \ A, x) + (∑ x ∈ A, x) = (∑ x ∈ A \ B, x) + (∑ x ∈ B, x) :=
    e1.trans e2.symm
  rw [hsum] at hkey
  have hcancel : (∑ x ∈ B \ A, x) = (∑ x ∈ A \ B, x) := add_right_cancel hkey
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hzero : (∑ x ∈ A \ B ∪ B \ A, x) = 0 := by
    rw [Finset.sum_union hdisj, hcancel, add_self_fun]
  have hcard' : (A \ B ∪ B \ A).card ≤ r := by
    refine le_trans (Finset.card_le_card ?_) hcard
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp h).1
  have hDsub : A \ B ∪ B \ A ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hA (Finset.mem_sdiff.mp h).1
    · exact hB (Finset.mem_sdiff.mp h).1
  have hempty : A \ B ∪ B \ A = ∅ :=
    Indep.sum_eq_zero (Indep_of_subset_of_card_le hDsub hcard' hr) hzero
  ext x
  constructor
  · intro hx
    by_contra hxB
    have hmem : x ∈ A \ B ∪ B \ A :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxB⟩))
    rw [hempty] at hmem
    simp at hmem
  · intro hx
    by_contra hxA
    have hmem : x ∈ A \ B ∪ B \ A :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxA⟩))
    rw [hempty] at hmem
    simp at hmem

/-! ### Parity of multiplicities: the "the equality must be an identity" step -/

theorem nsmul_eq_ite (a : Vec m) (n : ℕ) : n • a = if n % 2 = 1 then a else 0 := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [add_nsmul, mul_nsmul, two_nsmul, add_self_fun, smul_zero, add_zero]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- The sum of a multiset equals the sum of the elements occurring an odd number of times,
expressed through `nsmul`. -/
theorem sum_count_nsmul {s : Multiset (Vec m)} :
    (∑ a ∈ s.toFinset, s.count a • a) = s.sum := by
  simpa using (Finset.sum_multiset_map_count (s := s) (f := fun x : Vec m => x)).symm

/-- **The parity lemma.**  If the entries of a multiset `s` all lie in a set `C` with
`ind C ≥ s.card` and the sum of the entries is zero, then every element occurs an even
number of times.  This is the formal counterpart of the paper's observation that a vanishing
sum of at most `ind C` elements of `C` "must be an identity". -/
theorem even_count_of_sum_eq_zero {C : Finset (Vec m)} {s : Multiset (Vec m)}
    (hsub : ∀ x ∈ s, x ∈ C) (hsum : s.sum = 0) (hlen : s.card ≤ ind C) :
    ∀ x, s.count x % 2 = 0 := by
  classical
  intro x
  by_contra hx
  have hx1 : s.count x % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (s.count x) with h | h
    · exact absurd h hx
    · exact h
  have hite : (∑ a ∈ s.toFinset, (if s.count a % 2 = 1 then a else 0)) = s.sum := by
    rw [← sum_count_nsmul]
    refine Finset.sum_congr rfl ?_
    intro a _
    exact (nsmul_eq_ite a (s.count a)).symm
  set S := s.toFinset.filter (fun a => s.count a % 2 = 1) with hS
  have hSsum : (∑ a ∈ S, a) = 0 := by
    rw [hS, Finset.sum_filter, hite, hsum]
  have hSsub : S ⊆ C := by
    intro a ha
    rw [hS, Finset.mem_filter] at ha
    exact hsub a (Multiset.mem_toFinset.mp ha.1)
  have hScard : S.card ≤ ind C := by
    rw [hS]
    calc (s.toFinset.filter (fun a => s.count a % 2 = 1)).card ≤ s.toFinset.card :=
          Finset.card_filter_le _ _
      _ ≤ s.card := Multiset.toFinset_card_le s
      _ ≤ ind C := hlen
  have hxmem : x ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by omega)), hx1⟩
  have hempty : S = ∅ := Indep.sum_eq_zero (Indep_of_subset_of_card_le hSsub hScard le_rfl) hSsum
  rw [hempty] at hxmem
  simp at hxmem

/-! ### Point 1 of the proof of Theorem 2 -/

/-- **Point 1 of the proof of Theorem 2.**  If `ind(B ∪ γI_m) ≥ 3`, then no row `b ∈ B` is the
sum `b' + b''` of two elements of `C₀ = B ∪ γI_m`. -/
theorem no_row_eq_sum_of_C0 {aux : Finset (Fin m)} {γ : Bool} {B : Finset (Vec m)}
    {b b' b'' : Vec m} (hb : b ∈ B) (hb' : b' ∈ C0 aux γ B) (hb'' : b'' ∈ C0 aux γ B)
    (hsum : b' + b'' = b) (hind : 3 ≤ ind (C0 aux γ B)) : False := by
  have h0C : (0 : Vec m) ∉ C0 aux γ B := zero_not_mem_of_ind_pos (by omega)
  have hbC : b ∈ C0 aux γ B := subset_C0_left hb
  rcases eq_or_ne b' b'' with heq | hne
  · rw [heq, add_self_fun] at hsum
    exact h0C (hsum.symm ▸ hbC)
  · have hcard : (({b} : Finset (Vec m)) ∪ {b', b''}).card ≤ 3 := by
      have h := Finset.card_union_le ({b} : Finset (Vec m)) {b', b''}
      have h2 : ({b', b''} : Finset (Vec m)).card ≤ 2 := by
        rw [Finset.card_pair hne]
      simp only [Finset.card_singleton] at h
      omega
    have hsum' : (∑ x ∈ ({b} : Finset (Vec m)), x) = ∑ x ∈ ({b', b''} : Finset (Vec m)), x := by
      simp only [Finset.sum_singleton, Finset.sum_pair hne]
      exact hsum.symm
    have heq := eq_of_sum_eq_of_subset (A := {b}) (B := {b', b''}) (C := C0 aux γ B) (r := 3)
      (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hbC)
      (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb'
        · exact hb'')
      hcard hind hsum'
    have h1 : ({b} : Finset (Vec m)).card = 1 := Finset.card_singleton b
    rw [heq, Finset.card_pair hne] at h1
    omega

/-! ### Point 1 of the proof of Theorem 2: the hierarchy `Bᵢ`, `Cᵢ`

The paper fixes a minimal extended scheme for `B` and builds the sets `B₀ = ∅`, `C₀ = B ∪ γI_m`
and, for `j ≥ 1`, the set `B_j` of rows `b ∈ B \ ⋃_{i<j} B_i` that the scheme computes as
`b = b' + c` with `b' ∈ C_{j-1}`, together with the set `C_j` of the vectors `c` occurring in
these expressions.

To formalize this we fix a chain `c` and, for every row `b ∈ B`, a step `rowStep b` of `c`
computing it.  If one summand of that step lies in `C`, the summand lying in `C` is `oldV C b`
and the other summand is `newV C b`; the row belongs to the next `B`-set when such a summand
exists at all.  The sets `B (i+1)` and `C (i+1)` are then defined by recursion, the union of the
earlier `B`-sets being carried along in the first component of `hier`. -/

/-- The rows of a finite set `B` of vectors, as a subtype. -/
abbrev Row {m : ℕ} (B : Finset (Vec m)) := {b : Vec m // b ∈ B}

variable (c : ExtChain m) (B : Finset (Vec m)) (γ : Bool)

/-- The first summand of the step `k` of the chain. -/
noncomputable def smd1 (k : Fin c.L) : Vec m :=
  chainPool c.y k.1 (le_of_lt k.2) (Classical.choose (c.valid k))

/-- The second summand of the step `k` of the chain. -/
noncomputable def smd2 (k : Fin c.L) : Vec m :=
  chainPool c.y k.1 (le_of_lt k.2) (Classical.choose (Classical.choose_spec (c.valid k)))

theorem smd_add (k : Fin c.L) : smd1 c k + smd2 c k = c.y k :=
  (Classical.choose_spec (Classical.choose_spec (c.valid k))).symm

/-- A summand of a step of the chain that equals a row of `B` must itself be computed by an
earlier step: it cannot be a basis vector, since no row of `B` has weight `1`. -/
theorem exists_lt_of_smd_eq (hweight : ∀ b : Row B,
      weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1) {k : Fin c.L} {b' : Row B}
    (h : smd1 c k = b'.1 ∨ smd2 c k = b'.1) :
    ∃ j : Fin k.1, c.y ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩ = b'.1 := by
  have key : ∀ a : Fin m ⊕ Fin k.1, chainPool c.y k.1 (le_of_lt k.2) a = b'.1 →
      ∃ j : Fin k.1, c.y ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩ = b'.1 := by
    rintro (i | j) h
    · exfalso
      refine hweight b' ?_
      rw [← h]
      simpa [chainPool] using weight_univ_basisVec i
    · exact ⟨j, h⟩
  rcases h with h | h
  · exact key _ h
  · exact key _ h

/-- The first step of the chain computing the row `b`.  Taking the *least* such step (rather
than an arbitrary one) is what makes the hierarchy compatible with the order in which the chain
computes its elements. -/
noncomputable def rowStep (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) : Fin c.L :=
  (Finset.univ.filter (fun k : Fin c.L => c.y k = b.1)).min' (by
    obtain ⟨k, hk⟩ := hrow b
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩)

theorem rowStep_y (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) :
    c.y (rowStep c B hrow b) = b.1 := by
  have hmem := Finset.min'_mem (Finset.univ.filter (fun k : Fin c.L => c.y k = b.1))
    (by obtain ⟨k, hk⟩ := hrow b
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩)
  exact (Finset.mem_filter.mp hmem).2

theorem rowStep_le (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {b : Row B} {k : Fin c.L}
    (hk : c.y k = b.1) : rowStep c B hrow b ≤ k :=
  Finset.min'_le (Finset.univ.filter (fun k : Fin c.L => c.y k = b.1)) k
    (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

theorem rowStep_lt_of_smd_eq (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1) {b b' : Row B}
    (h : smd1 c (rowStep c B hrow b) = b'.1 ∨ smd2 c (rowStep c B hrow b) = b'.1) :
    rowStep c B hrow b' < rowStep c B hrow b := by
  obtain ⟨j, hj⟩ := exists_lt_of_smd_eq c B hweight h
  have h1 : rowStep c B hrow b' ≤ ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt (rowStep c B hrow b).2)⟩ :=
    rowStep_le c B hrow hj
  exact lt_of_le_of_lt h1 j.2


/-- The two summands of the step computing the row `b`. -/
noncomputable def rowS1 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) : Vec m :=
  smd1 c (rowStep c B hrow b)

noncomputable def rowS2 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) : Vec m :=
  smd2 c (rowStep c B hrow b)

theorem rowS_add (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) :
    rowS1 c B hrow b + rowS2 c B hrow b = b.1 := by
  rw [rowS1, rowS2, smd_add, rowStep_y]

/-- One of the summands of the step computing `b` belongs to `C`. -/
noncomputable def hasComp (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m))
    (b : Row B) : Prop :=
  rowS1 c B hrow b ∈ C ∨ rowS2 c B hrow b ∈ C

/-- The summand of the step computing `b` that lies in `C`. -/
noncomputable def oldV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m))
    (b : Row B) : Vec m :=
  if rowS1 c B hrow b ∈ C then rowS1 c B hrow b else rowS2 c B hrow b

/-- The other summand of the step computing `b`. -/
noncomputable def newV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m))
    (b : Row B) : Vec m :=
  if rowS1 c B hrow b ∈ C then rowS2 c B hrow b else rowS1 c B hrow b

theorem oldV_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {C : Finset (Vec m)} {b : Row B}
    (h : hasComp c B hrow C b) : oldV c B hrow C b ∈ C := by
  by_cases h1 : rowS1 c B hrow b ∈ C
  · simp [oldV, h1]
  · simpa [oldV, h1] using h.resolve_left h1

theorem oldV_add_newV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m))
    (b : Row B) : oldV c B hrow C b + newV c B hrow C b = b.1 := by
  by_cases h1 : rowS1 c B hrow b ∈ C
  · simpa [oldV, newV, h1] using rowS_add c B hrow b
  · rw [add_comm]
    simpa [oldV, newV, h1] using rowS_add c B hrow b

theorem newV_eq (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m)) (b : Row B) :
    newV c B hrow C b = b.1 + oldV c B hrow C b := by
  have h := oldV_add_newV c B hrow C b
  calc newV c B hrow C b
      = (oldV c B hrow C b + oldV c B hrow C b) + newV c B hrow C b := by
        rw [add_self_fun, zero_add]
    _ = oldV c B hrow C b + (oldV c B hrow C b + newV c B hrow C b) := by rw [add_assoc]
    _ = oldV c B hrow C b + b.1 := by rw [h]
    _ = b.1 + oldV c B hrow C b := add_comm _ _

theorem rowStep_lt_of_oldV_eq (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    (C : Finset (Vec m)) {b b' : Row B} (h : oldV c B hrow C b = b'.1) :
    rowStep c B hrow b' < rowStep c B hrow b := by
  have h' : rowS1 c B hrow b = b'.1 ∨ rowS2 c B hrow b = b'.1 := by
    by_cases h1 : rowS1 c B hrow b ∈ C
    · exact Or.inl (by simpa [oldV, h1] using h)
    · exact Or.inr (by simpa [oldV, h1] using h)
  exact rowStep_lt_of_smd_eq c B hrow hweight (by simpa only [rowS1, rowS2] using h')

/-- The new `B`-set at a successor step, computed from the previous state. -/
noncomputable def nextBs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (p : Finset (Row B) × Finset (Row B) × Finset (Vec m)) : Finset (Row B) := by
  classical
  exact B.attach.filter (fun r => r ∉ p.1 ∧ hasComp c B hrow p.2.2 r)

/-- The hierarchy of `B`-sets and `C`-sets, carrying the union of the earlier `B`-sets. -/
noncomputable def hier (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    ℕ → Finset (Row B) × Finset (Row B) × Finset (Vec m)
  | 0 => (∅, ∅, C0 c.aux γ B)
  | i + 1 =>
      let p := hier hrow i
      let Bn := nextBs c B hrow p
      let Cn : Finset (Vec m) := Bn.image (fun r => newV c B hrow p.2.2 r)
      (p.1 ∪ Bn, Bn, Cn)

/-- The union of `B₀, …, Bᵢ`. -/
noncomputable def acc (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) : Finset (Row B) :=
  (hier c B γ hrow i).1

/-- The set `Bᵢ` of the paper. -/
noncomputable def Bs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) : Finset (Row B) :=
  (hier c B γ hrow i).2.1

/-- The set `Cᵢ` of the paper. -/
noncomputable def Cs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) : Finset (Vec m) :=
  (hier c B γ hrow i).2.2

/-- The vectors of the rows in `Bᵢ`. -/
noncomputable def BsV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) : Finset (Vec m) :=
  (Bs c B γ hrow i).image Subtype.val

@[simp] theorem acc_zero (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    acc c B γ hrow 0 = ∅ := rfl

@[simp] theorem Bs_zero (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    Bs c B γ hrow 0 = ∅ := rfl

@[simp] theorem Cs_zero (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    Cs c B γ hrow 0 = C0 c.aux γ B := rfl

theorem acc_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) :
    acc c B γ hrow (i + 1) = acc c B γ hrow i ∪ Bs c B γ hrow (i + 1) := rfl

theorem Bs_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) :
    Bs c B γ hrow (i + 1) = nextBs c B hrow (hier c B γ hrow i) :=
  rfl

theorem Cs_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) :
    Cs c B γ hrow (i + 1) =
      (Bs c B γ hrow (i + 1)).image (fun r => newV c B hrow (Cs c B γ hrow i) r) := rfl

theorem mem_Bs_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i : ℕ} {b : Row B} :
    b ∈ Bs c B γ hrow (i + 1) ↔
      b ∉ acc c B γ hrow i ∧ hasComp c B hrow (Cs c B γ hrow i) b := by
  rw [Bs_succ]
  simp [nextBs, acc, Cs]


theorem mem_acc (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i : ℕ} {b : Row B} :
    b ∈ acc c B γ hrow i ↔ ∃ l, l ≤ i ∧ b ∈ Bs c B γ hrow l := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [acc_succ, Finset.mem_union, ih]
    constructor
    · rintro (⟨l, hl, hbl⟩ | hb)
      · exact ⟨l, by omega, hbl⟩
      · exact ⟨i + 1, le_rfl, hb⟩
    · rintro ⟨l, hl, hbl⟩
      rcases Nat.lt_or_eq_of_le hl with h | h
      · exact Or.inl ⟨l, by omega, hbl⟩
      · exact Or.inr (h ▸ hbl)

theorem acc_mono (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i j : ℕ} (h : i ≤ j) :
    acc c B γ hrow i ⊆ acc c B γ hrow j := by
  intro b hb
  obtain ⟨l, hl, hbl⟩ := (mem_acc c B γ hrow).mp hb
  exact (mem_acc c B γ hrow).mpr ⟨l, le_trans hl h, hbl⟩

theorem Bs_not_mem_acc (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i : ℕ} {b : Row B}
    (hb : b ∈ Bs c B γ hrow (i + 1)) : b ∉ acc c B γ hrow i :=
  ((mem_Bs_succ c B γ hrow).mp hb).1

/-- **Point 1, first property.**  The sets `Bᵢ` are pairwise disjoint. -/
theorem Bs_disjoint (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Bs c B γ hrow i) (Bs c B γ hrow j) := by
  rw [Finset.disjoint_left]
  intro b hbi hbj
  rcases lt_or_gt_of_ne hij with h | h
  · have hj : j = (j - 1) + 1 := by omega
    rw [hj] at hbj
    exact Bs_not_mem_acc c B γ hrow hbj
      (acc_mono c B γ hrow (by omega) ((mem_acc c B γ hrow).mpr ⟨i, le_rfl, hbi⟩))
  · have hi : i = (i - 1) + 1 := by omega
    rw [hi] at hbi
    exact Bs_not_mem_acc c B γ hrow hbi
      (acc_mono c B γ hrow (by omega) ((mem_acc c B γ hrow).mpr ⟨j, le_rfl, hbj⟩))


/-- **Point 1, third property.**  If all the vectors of `C₀` have type `0`, then all the vectors
of the sets `Cᵢ` have type `0` as well. -/
theorem Cs_type_zero (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) :
    ∀ i, ∀ x ∈ Cs c B γ hrow i, proj c.aux x = 0
  | 0 => by rw [Cs_zero]; exact proj_eq_zero_of_mem_C0 (fun b hb => hB ⟨b, hb⟩)
  | i + 1 => by
      intro x hx
      rw [Cs_succ] at hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      have hcomp : hasComp c B hrow (Cs c B γ hrow i) b := (mem_Bs_succ c B γ hrow).mp hb |>.2
      have hold : oldV c B hrow (Cs c B γ hrow i) b ∈ Cs c B γ hrow i :=
        oldV_mem c B hrow hcomp
      rw [newV_eq, proj_add, hB b,
        Cs_type_zero hrow hB i _ hold]
      simp

/-- **Point 1, third property (basis form).**  A vector of `Cᵢ` with `i ≥ 1` that happens to be a
basis vector is a basis vector of an essential coordinate: all vectors of `Cᵢ`, `i ≥ 1`, have
type `0`, whereas `proj aux (basisVec l) = basisVec l ≠ 0` for an inessential `l`. -/
theorem basisVec_notMem_aux_of_mem_Cs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) {i : ℕ} (hi : 1 ≤ i) {v : Vec m}
    (hv : v ∈ Cs c B γ hrow i) {l : Fin m} (hl : v = basisVec l) : l ∉ c.aux := by
  intro hlmem
  have htype := Cs_type_zero c B γ hrow hB i v hv
  rw [hl, proj_basisVec, if_pos hlmem] at htype
  exact basisVec_ne_zero l htype


/-! ### Elementary multiset facts for the rows of a decomposition -/

theorem multiset_sum_map_univ {n : ℕ} (f : Fin n → Vec m) :
    ((Finset.univ : Finset (Fin n)).val.map f).sum = ∑ l, f l := by
  rw [Finset.sum]

theorem count_map_univ_eq_zero {n : ℕ} {f : Fin n → Vec m} {a : Vec m}
    (h : ∀ l, f l ≠ a) :
    ((Finset.univ : Finset (Fin n)).val.map f).count a = 0 := by
  rw [Multiset.count_eq_zero]
  intro ha
  obtain ⟨l, -, hl⟩ := Multiset.mem_map.mp ha
  exact h l hl

theorem count_map_univ_eq_one {n : ℕ} {f : Fin n → Vec m} (hinj : Function.Injective f)
    {a : Vec m} {l : Fin n} (hl : f l = a) :
    ((Finset.univ : Finset (Fin n)).val.map f).count a = 1 := by
  have hnodup : ((Finset.univ : Finset (Fin n)).val.map f).Nodup :=
    Multiset.Nodup.map hinj (Finset.univ : Finset (Fin n)).nodup
  have hle : ((Finset.univ : Finset (Fin n)).val.map f).count a ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hnodup) a
  have hpos : 0 < ((Finset.univ : Finset (Fin n)).val.map f).count a :=
    Multiset.count_pos.mpr (Multiset.mem_map.mpr ⟨l, Finset.mem_univ l, hl⟩)
  omega

theorem count_map_univ_eq_ite {n : ℕ} {f : Fin n → Vec m} (hinj : Function.Injective f)
    {a : Vec m} {l : Fin n} (huniq : ∀ l', f l' = a → l' = l) :
    ((Finset.univ : Finset (Fin n)).val.map f).count a = if f l = a then 1 else 0 := by
  by_cases h : f l = a
  · rw [ite_eq_left h]
    exact count_map_univ_eq_one hinj h
  · rw [ite_eq_right h]
    refine count_map_univ_eq_zero ?_
    intro l' hl'
    exact h (huniq l' hl' ▸ hl')

/-! ### Point 2 of the proof of Theorem 2: the canonical decomposition -/

variable (c : ExtChain m) (B : Finset (Vec m)) (γ : Bool)
variable (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)

theorem mem_Cs_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) {x : Vec m} :
    x ∈ Cs c B γ hrow (i + 1) ↔
      ∃ b : Row B, b ∈ Bs c B γ hrow (i + 1) ∧
        newV c B hrow (Cs c B γ hrow i) b = x := by
  rw [Cs_succ, Finset.mem_image]

/-- The row of `Bᵢ₊₁` whose `newV` is a given element `x` of `Cᵢ₊₁`. -/
noncomputable def decRow (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) : Row B :=
  Classical.choose ((mem_Cs_succ c B γ hrow i).mp hx)

theorem decRow_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) :
    decRow c B γ hrow i x hx ∈ Bs c B γ hrow (i + 1) :=
  (Classical.choose_spec ((mem_Cs_succ c B γ hrow i).mp hx)).1

theorem decRow_newV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) :
    newV c B hrow (Cs c B γ hrow i) (decRow c B γ hrow i x hx) = x :=
  (Classical.choose_spec ((mem_Cs_succ c B γ hrow i).mp hx)).2

/-- The `oldV` of the row witnessing `x ∈ Cᵢ₊₁`: the previous element of the canonical
decomposition. -/
noncomputable def decPred (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) : Vec m :=
  oldV c B hrow (Cs c B γ hrow i) (decRow c B γ hrow i x hx)

theorem decPred_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) : decPred c B γ hrow i x hx ∈ Cs c B γ hrow i :=
  oldV_mem c B hrow ((mem_Bs_succ c B γ hrow).mp (decRow_mem c B γ hrow i x hx)).2

theorem decPred_add_decRow (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) :
    decPred c B γ hrow i x hx + x = (decRow c B γ hrow i x hx).1 := by
  have h := oldV_add_newV c B hrow (Cs c B γ hrow i) (decRow c B γ hrow i x hx)
  rw [decRow_newV c B γ hrow i x hx] at h
  exact h

/-- The level-`0` element of the canonical decomposition of `x ∈ Cᵢ`. -/
noncomputable def decV0 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    (i : ℕ) → (x : Vec m) → (hx : x ∈ Cs c B γ hrow i) → Vec m
  | 0, x, _ => x
  | i + 1, x, hx =>
      decV0 hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx)

/-- The rows at levels `1, …, i` of the canonical decomposition of `x ∈ Cᵢ`. -/
noncomputable def decRows (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    (i : ℕ) → (x : Vec m) → (hx : x ∈ Cs c B γ hrow i) → Fin i → Row B
  | 0, _, _, j => j.elim0
  | i + 1, x, hx, j =>
      Fin.snoc (α := fun _ => Row B)
        (fun j' : Fin i =>
          decRows hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx) j')
        (decRow c B γ hrow i x hx) j

@[simp] theorem decV0_zero (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow 0) : decV0 c B γ hrow 0 x hx = x := rfl

theorem decV0_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) :
    decV0 c B γ hrow (i + 1) x hx =
      decV0 c B γ hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx) := rfl

theorem decRows_succ (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) (j : Fin (i + 1)) :
    decRows c B γ hrow (i + 1) x hx j =
      Fin.snoc (α := fun _ => Row B)
        (fun j' : Fin i =>
          decRows c B γ hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx) j')
        (decRow c B γ hrow i x hx) j := rfl

theorem decRows_castSucc (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) (j : Fin i) :
    decRows c B γ hrow (i + 1) x hx j.castSucc =
      decRows c B γ hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx) j := by
  rw [decRows_succ, Fin.snoc_castSucc]

theorem decRows_last (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow (i + 1)) :
    decRows c B γ hrow (i + 1) x hx (Fin.last i) = decRow c B γ hrow i x hx := by
  rw [decRows_succ, Fin.snoc_last]

theorem decV0_one (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow 1) :
    decV0 c B γ hrow 1 x hx = decPred c B γ hrow 0 x hx := by
  have := decV0_succ c B γ hrow 0 x hx
  simpa using this

theorem decRows_one (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow 1) (j : Fin 1) :
    decRows c B γ hrow 1 x hx j = decRow c B γ hrow 0 x hx := by
  have hj : j = Fin.last 0 := Fin.ext (by omega)
  subst hj
  rw [decRows_succ, Fin.snoc_last]

theorem decV0_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    ∀ (i : ℕ) (x : Vec m) (hx : x ∈ Cs c B γ hrow i), decV0 c B γ hrow i x hx ∈ C0 c.aux γ B
  | 0, x, hx => hx
  | i + 1, x, hx => decV0_mem hrow i _ _

theorem decRows_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    ∀ (i : ℕ) (x : Vec m) (hx : x ∈ Cs c B γ hrow i) (j : Fin i),
      decRows c B γ hrow i x hx j ∈ Bs c B γ hrow (j.1 + 1)
  | 0, x, hx, j => j.elim0
  | i + 1, x, hx, j => by
      rw [decRows_succ]
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [Fin.snoc_last]
        exact decRow_mem c B γ hrow i x hx
      · rw [Fin.snoc_castSucc]
        exact decRows_mem hrow i _ _ j'

theorem dec_sum (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) :
    ∀ (i : ℕ) (x : Vec m) (hx : x ∈ Cs c B γ hrow i),
      decV0 c B γ hrow i x hx + (∑ j : Fin i, (decRows c B γ hrow i x hx j).1) = x
  | 0, x, hx => by
      rw [decV0_zero]
      simp
  | i + 1, x, hx => by
      rw [show decV0 c B γ hrow (i + 1) x hx =
        decV0 c B γ hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx)
        from decV0_succ c B γ hrow i x hx]
      rw [Fin.sum_univ_castSucc]
      simp only [decRows_castSucc, decRows_last]
      rw [← add_assoc,
        dec_sum hrow i (decPred c B γ hrow i x hx) (decPred_mem c B γ hrow i x hx)]
      rw [← decPred_add_decRow c B γ hrow i x hx, ← add_assoc, add_self_fun, zero_add]


/-! ### Point 2 of the proof of Theorem 2: `Cᵢ` does not meet `C₀` for `i ≥ 1` -/

/-- **Point 2, preliminary.**  For `i ≥ 1`, no element of `Cᵢ` belongs to `C₀`.

For `i = 1` this is the observation that otherwise a row of `B` would be the sum of two
elements of `C₀`, which is impossible by point 1.  For `i ≥ 2`, the row whose `newV` produces
the element would then belong both to `B₁` and to `Bᵢ`, contradicting the disjointness of the
`Bᵢ`. -/
theorem Cs_notMem_C0 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hind : 3 ≤ ind (C0 c.aux γ B)) {i : ℕ} (hi : 1 ≤ i) {x : Vec m}
    (hx : x ∈ Cs c B γ hrow i) : x ∉ C0 c.aux γ B := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  cases j with
  | zero =>
      intro hxC
      have hpred : decPred c B γ hrow 0 x hx ∈ C0 c.aux γ B := by
        have h := decPred_mem c B γ hrow 0 x hx
        rwa [Cs_zero] at h
      exact no_row_eq_sum_of_C0 (decRow c B γ hrow 0 x hx).2 hpred hxC
        (decPred_add_decRow c B γ hrow 0 x hx) hind
  | succ j =>
      intro hxC
      have hr : decRow c B γ hrow (j + 1) x hx ∈ Bs c B γ hrow (j + 2) :=
        decRow_mem c B γ hrow (j + 1) x hx
      have hnew : newV c B hrow (Cs c B γ hrow (j + 1)) (decRow c B γ hrow (j + 1) x hx) = x :=
        decRow_newV c B γ hrow (j + 1) x hx
      have hcomp : hasComp c B hrow (Cs c B γ hrow 0) (decRow c B γ hrow (j + 1) x hx) := by
        by_cases h1 : rowS1 c B hrow (decRow c B γ hrow (j + 1) x hx) ∈ Cs c B γ hrow (j + 1)
        · refine Or.inr ?_
          have hnv : newV c B hrow (Cs c B γ hrow (j + 1)) (decRow c B γ hrow (j + 1) x hx) =
              rowS2 c B hrow (decRow c B γ hrow (j + 1) x hx) := by simp [newV, h1]
          rw [Cs_zero, ← hnv, hnew]
          exact hxC
        · refine Or.inl ?_
          have hnv : newV c B hrow (Cs c B γ hrow (j + 1)) (decRow c B γ hrow (j + 1) x hx) =
              rowS1 c B hrow (decRow c B γ hrow (j + 1) x hx) := by simp [newV, h1]
          rw [Cs_zero, ← hnv, hnew]
          exact hxC
      have hr1 : decRow c B γ hrow (j + 1) x hx ∈ Bs c B γ hrow 1 := by
        rw [mem_Bs_succ]
        exact ⟨by rw [acc_zero]; simp, hcomp⟩
      exact Finset.disjoint_left.mp (Bs_disjoint c B γ hrow (i := 1) (j := j + 2) (by omega)) hr1 hr


/-! ### Point 2 of the proof of Theorem 2: the canonical decomposition as a multiset -/

/-- The multiset of the canonical decomposition of `x ∈ Cᵢ`: the level-`0` vector together with
the values of the `i` rows of levels `1, …, i`.  Formally this is the right-hand side
`b'₀ + b'₁ + … + b'ᵢ` of equation (cij) in the paper. -/
noncomputable def decMultiset (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) : Multiset (Vec m) :=
  {decV0 c B γ hrow i x hx} +
    ((Finset.univ : Finset (Fin i)).val.map (fun j => (decRows c B γ hrow i x hx j).1))

theorem decMultiset_sum (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) : (decMultiset c B γ hrow i x hx).sum = x := by
  rw [decMultiset, Multiset.sum_add, Multiset.sum_singleton, multiset_sum_map_univ]
  exact dec_sum c B γ hrow i x hx

theorem decMultiset_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) : (decMultiset c B γ hrow i x hx).card = i + 1 := by
  simp [decMultiset]

theorem decMultiset_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) {y : Vec m} :
    y ∈ decMultiset c B γ hrow i x hx ↔
      y = decV0 c B γ hrow i x hx ∨ ∃ j : Fin i, (decRows c B γ hrow i x hx j).1 = y := by
  simp [decMultiset, eq_comm]

theorem BsV_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) {y : Vec m} :
    y ∈ BsV c B γ hrow i ↔ ∃ r ∈ Bs c B γ hrow i, r.1 = y :=
  Finset.mem_image

theorem Bs_val_mem (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) {b : Row B}
    (hb : b ∈ Bs c B γ hrow i) : b.1 ∈ B := by
  classical
  cases i with
  | zero => rw [Bs_zero] at hb; exact absurd hb (by simp)
  | succ _ =>
    exact b.2

theorem decMultiset_sub (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) {y : Vec m} (hy : y ∈ decMultiset c B γ hrow i x hx) :
    y ∈ C0 c.aux γ B := by
  rw [decMultiset_mem] at hy
  rcases hy with h | ⟨j, rfl⟩
  · exact h ▸ decV0_mem c B γ hrow i x hx
  · exact subset_C0_left
      (Bs_val_mem c B γ hrow (j.1 + 1) (decRows_mem c B γ hrow i x hx j))

/-- Values of rows of different levels are different vectors. -/
theorem BsV_disjoint (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (BsV c B γ hrow i) (BsV c B γ hrow j) := by
  rw [Finset.disjoint_left]
  intro y hyi hyj
  rw [BsV_mem c B γ hrow i] at hyi
  rw [BsV_mem c B γ hrow j] at hyj
  obtain ⟨r, hr, hry⟩ := hyi
  obtain ⟨r', hr', hr'y⟩ := hyj
  have hrr : r = r' := Subtype.ext (hry.trans hr'y.symm)
  exact Finset.disjoint_left.mp (Bs_disjoint c B γ hrow hij) hr (hrr ▸ hr')

/-- At a fixed level, the rows of the canonical decomposition have pairwise different values. -/
theorem decRows_injective (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (i : ℕ) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) :
    Function.Injective (fun j : Fin i => (decRows c B γ hrow i x hx j).1) := by
  intro j j' hjj'
  have hsub : decRows c B γ hrow i x hx j = decRows c B γ hrow i x hx j' := Subtype.ext hjj'
  have hmem : decRows c B γ hrow i x hx j ∈ Bs c B γ hrow (j.1 + 1) :=
    decRows_mem c B γ hrow i x hx j
  have hmem' : decRows c B γ hrow i x hx j ∈ Bs c B γ hrow (j'.1 + 1) := by
    rw [hsub]; exact decRows_mem c B γ hrow i x hx j'
  have hlev : j.1 + 1 = j'.1 + 1 := by
    by_contra h
    exact Finset.disjoint_left.mp (Bs_disjoint c B γ hrow h) hmem hmem'
  exact Fin.ext (by omega)

/-! ### Counting in a canonical decomposition -/

theorem decMultiset_count_eq {i : ℕ} (x : Vec m) (hx : x ∈ Cs c B γ hrow i) (y : Vec m) :
    (decMultiset c B γ hrow i x hx).count y =
      (if decV0 c B γ hrow i x hx = y then 1 else 0) +
        ((Finset.univ : Finset (Fin i)).val.map
          (fun k => (decRows c B γ hrow i x hx k).1)).count y := by
  rw [decMultiset, Multiset.count_add, Multiset.count_singleton]
  congr 1
  by_cases h : decV0 c B γ hrow i x hx = y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The level-`0` vector of the decomposition of `x ∈ Cᵢ` (`i ≥ 1`) is the `oldV` of its level-`1`
row. -/
theorem decV0_eq_oldV_decRows (i : ℕ) (x : Vec m) (hx : x ∈ Cs c B γ hrow i) (hi : 1 ≤ i) :
    decV0 c B γ hrow i x hx =
      oldV c B hrow (Cs c B γ hrow 0) (decRows c B γ hrow i x hx ⟨0, hi⟩) := by
  induction i using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    rcases n with _ | _ | n
    · omega
    · rw [decV0_one, decRows_one]
      rfl
    · have hy : decPred c B γ hrow (n + 1) x hx ∈ Cs c B γ hrow (n + 1) :=
        decPred_mem c B γ hrow (n + 1) x hx
      rw [decV0_succ c B γ hrow (n + 1) x hx]
      rw [ih (n + 1) (by omega) (decPred c B γ hrow (n + 1) x hx) hy (by omega)]
      have hrows :
          decRows c B γ hrow (n + 1) (decPred c B γ hrow (n + 1) x hx) hy ⟨0, by omega⟩
            = decRows c B γ hrow (n + 2) x hx ⟨0, hi⟩ := by
        simpa using
          (decRows_castSucc c B γ hrow (n + 1) x hx (⟨0, by omega⟩ : Fin (n + 1))).symm
      rw [hrows]

/-- A decomposition of level `i` contains no row value of a level `l > i`, except possibly as its
level-`0` vector. -/
theorem decMultiset_count_of_mem_BsV_gt {i : ℕ} (x : Vec m) (hx : x ∈ Cs c B γ hrow i)
    {l : ℕ} (hl : i < l) {y : Vec m} (hy : y ∈ BsV c B γ hrow l) :
    (decMultiset c B γ hrow i x hx).count y =
      if decV0 c B γ hrow i x hx = y then 1 else 0 := by
  rw [decMultiset_count_eq]
  have hmap : ((Finset.univ : Finset (Fin i)).val.map
      (fun k => (decRows c B γ hrow i x hx k).1)).count y = 0 := by
    refine count_map_univ_eq_zero ?_
    intro k hk
    have hmem : (decRows c B γ hrow i x hx k).1 ∈ BsV c B γ hrow (k.1 + 1) :=
      (BsV_mem c B γ hrow (k.1 + 1)).mpr ⟨_, decRows_mem c B γ hrow i x hx k, rfl⟩
    exact (Finset.disjoint_left.mp
      (BsV_disjoint c B γ hrow (i := k.1 + 1) (j := l) (by omega)) hmem) (hk ▸ hy)
  rw [hmap, add_zero]

/-- In a decomposition of level `i ≥ 1`, a value of a level-`1` row occurs only as the level-`1`
row of the decomposition, plus possibly once as the level-`0` vector. -/
theorem decMultiset_count_of_mem_BsV_one {i : ℕ} (hi : 1 ≤ i) (x : Vec m)
    (hx : x ∈ Cs c B γ hrow i) {f : Vec m} (hf : f ∈ BsV c B γ hrow 1) :
    (decMultiset c B γ hrow i x hx).count f =
      (if decV0 c B γ hrow i x hx = f then 1 else 0) +
        (if (decRows c B γ hrow i x hx ⟨0, hi⟩).1 = f then 1 else 0) := by
  rw [decMultiset_count_eq]
  congr 1
  have huniq : ∀ k : Fin i, (decRows c B γ hrow i x hx k).1 = f → k = ⟨0, hi⟩ := by
    intro k hk
    have hmem : (decRows c B γ hrow i x hx k).1 ∈ BsV c B γ hrow (k.1 + 1) :=
      (BsV_mem c B γ hrow (k.1 + 1)).mpr ⟨_, decRows_mem c B γ hrow i x hx k, rfl⟩
    have hlev : k.1 + 1 = 1 := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := k.1 + 1) (j := 1) hne) hmem) (hk.symm ▸ hf)
    have hk0 : k.1 = 0 := by omega
    exact Fin.ext (by simpa using hk0)
  simpa using count_map_univ_eq_ite (decRows_injective c B γ hrow i x hx)
    (l := (⟨0, hi⟩ : Fin i)) huniq

/-- In a decomposition of level `j`, the value of the row of index `m` occurs exactly once among
the rows of positive level, plus possibly once as the level-`0` vector. -/
theorem decMultiset_count_decRows {j : ℕ} (x : Vec m) (hx : x ∈ Cs c B γ hrow j) (mm : Fin j) :
    (decMultiset c B γ hrow j x hx).count ((decRows c B γ hrow j x hx mm).1) =
      (if decV0 c B γ hrow j x hx = (decRows c B γ hrow j x hx mm).1 then 1 else 0) + 1 := by
  rw [decMultiset_count_eq]
  have hmap : ((Finset.univ : Finset (Fin j)).val.map
      (fun k => (decRows c B γ hrow j x hx k).1)).count
      ((decRows c B γ hrow j x hx mm).1) = 1 :=
    count_map_univ_eq_one (decRows_injective c B γ hrow j x hx) (l := mm) rfl
  rw [hmap]

/-! ### Parity of two decompositions -/

theorem decMultiset_pair_even {i j : ℕ} (hind : i + j + 2 ≤ ind (C0 c.aux γ B))
    {x : Vec m} (hxi : x ∈ Cs c B γ hrow i) (hxj : x ∈ Cs c B γ hrow j) :
    (∀ y, (decMultiset c B γ hrow i x hxi +
        decMultiset c B γ hrow j x hxj).count y % 2 = 0) ∧ (i + j + 2) % 2 = 0 := by
  classical
  set M : Multiset (Vec m) :=
    decMultiset c B γ hrow i x hxi + decMultiset c B γ hrow j x hxj with hM
  have hsum : M.sum = 0 := by
    rw [hM, Multiset.sum_add, decMultiset_sum, decMultiset_sum, add_self_fun]
  have hcard : M.card = i + j + 2 := by
    rw [hM, Multiset.card_add, decMultiset_card, decMultiset_card]
    ring
  have hsub : ∀ y ∈ M, y ∈ C0 c.aux γ B := by
    intro y hy
    rw [hM, Multiset.mem_add] at hy
    rcases hy with hy | hy
    · exact decMultiset_sub c B γ hrow i x hxi hy
    · exact decMultiset_sub c B γ hrow j x hxj hy
  have heven : ∀ y, M.count y % 2 = 0 :=
    even_count_of_sum_eq_zero hsub hsum (by rw [hcard]; exact hind)
  refine ⟨fun y => heven y, ?_⟩
  rw [← hcard]
  have hsum2 : M.card = ∑ a ∈ M.toFinset, M.count a :=
    (Multiset.toFinset_sum_count_eq M).symm
  rw [hsum2]
  have h2 : ∀ a ∈ M.toFinset, M.count a = (M.count a / 2) * 2 := by
    intro a _
    have := heven a
    omega
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul]
  exact Nat.mul_mod_left _ _

/-! ### The matching step -/

theorem count_match {i j : ℕ} (_hi : 1 ≤ i) (_hij : i < j)
    {x : Vec m} (hxi : x ∈ Cs c B γ hrow i) (hxj : x ∈ Cs c B γ hrow j)
    (heven : ∀ y, (decMultiset c B γ hrow i x hxi +
      decMultiset c B γ hrow j x hxj).count y % 2 = 0)
    {mm : Fin j} (hm : i ≤ mm.1) :
    decV0 c B γ hrow i x hxi = (decRows c B γ hrow j x hxj mm).1 ∨
      decV0 c B γ hrow j x hxj = (decRows c B γ hrow j x hxj mm).1 := by
  classical
  have hyB : (decRows c B γ hrow j x hxj mm).1 ∈ BsV c B γ hrow (mm.1 + 1) :=
    (BsV_mem c B γ hrow (mm.1 + 1)).mpr ⟨_, decRows_mem c B γ hrow j x hxj mm, rfl⟩
  have hA : (decMultiset c B γ hrow i x hxi).count
      ((decRows c B γ hrow j x hxj mm).1) =
      if decV0 c B γ hrow i x hxi = (decRows c B γ hrow j x hxj mm).1 then 1 else 0 :=
    decMultiset_count_of_mem_BsV_gt c B γ hrow x hxi (l := mm.1 + 1) (by omega) hyB
  have hD : (decMultiset c B γ hrow j x hxj).count
      ((decRows c B γ hrow j x hxj mm).1) =
      (if decV0 c B γ hrow j x hxj = (decRows c B γ hrow j x hxj mm).1 then 1 else 0) + 1 :=
    decMultiset_count_decRows c B γ hrow x hxj mm
  have hev := heven ((decRows c B γ hrow j x hxj mm).1)
  rw [Multiset.count_add, hA, hD] at hev
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [if_neg h1, if_neg h2] at hev
  norm_num at hev

/-! ### Three consecutive levels are impossible -/

theorem diff_le_two {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    {x : Vec m} (hxi : x ∈ Cs c B γ hrow i) (hxj : x ∈ Cs c B γ hrow j)
    (heven : ∀ y, (decMultiset c B γ hrow i x hxi +
      decMultiset c B γ hrow j x hxj).count y % 2 = 0) :
    j ≤ i + 2 := by
  classical
  by_contra h
  push Not at h
  set g : Fin j → Vec m := fun k => (decRows c B γ hrow j x hxj k).1 with hg
  have hginj : Function.Injective g := decRows_injective c B γ hrow j x hxj
  have key : ∀ a b : Fin j, (a : ℕ) ≠ (b : ℕ) → g a = g b → False := by
    intro a b hne hab
    exact hne (congrArg Fin.val (hginj hab))
  have hne13 : ((⟨i, by omega⟩ : Fin j) : ℕ) ≠ ((⟨i + 1, by omega⟩ : Fin j) : ℕ) := by
    show i ≠ i + 1
    omega
  have hne24 : ((⟨i + 1, by omega⟩ : Fin j) : ℕ) ≠ ((⟨i + 2, by omega⟩ : Fin j) : ℕ) := by
    show i + 1 ≠ i + 2
    omega
  have hne14 : ((⟨i, by omega⟩ : Fin j) : ℕ) ≠ ((⟨i + 2, by omega⟩ : Fin j) : ℕ) := by
    show i ≠ i + 2
    omega
  have e1 := count_match c B γ hrow hi hij hxi hxj heven
    (mm := (⟨i, by omega⟩ : Fin j)) (by simp)
  have e2 := count_match c B γ hrow hi hij hxi hxj heven
    (mm := (⟨i + 1, by omega⟩ : Fin j)) (by simp)
  have e3 := count_match c B γ hrow hi hij hxi hxj heven
    (mm := (⟨i + 2, by omega⟩ : Fin j)) (by simp)
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3
  · exact key _ _ hne13 (e1.symm.trans e2)
  · exact key _ _ hne13 (e1.symm.trans e2)
  · exact key _ _ hne14 (e1.symm.trans e3)
  · exact key _ _ hne24 (e2.symm.trans e3)
  · exact key _ _ hne24 (e2.symm.trans e3)
  · exact key _ _ hne14 (e1.symm.trans e3)
  · exact key _ _ hne13 (e1.symm.trans e2)
  · exact key _ _ hne13 (e1.symm.trans e2)

/-! ### The two level-`0` vectors are distinct -/

theorem decV0_ne {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hdist : j = i + 2)
    {x : Vec m} (hxi : x ∈ Cs c B γ hrow i) (hxj : x ∈ Cs c B γ hrow j)
    (heven : ∀ y, (decMultiset c B γ hrow i x hxi +
      decMultiset c B γ hrow j x hxj).count y % 2 = 0) :
    decV0 c B γ hrow i x hxi ≠ decV0 c B γ hrow j x hxj := by
  classical
  intro hbc
  set g : Fin j → Vec m := fun k => (decRows c B γ hrow j x hxj k).1 with hg
  have hginj : Function.Injective g := decRows_injective c B γ hrow j x hxj
  have e1 : decV0 c B γ hrow i x hxi = g (⟨i, by omega⟩ : Fin j) ∨
      decV0 c B γ hrow j x hxj = g (⟨i, by omega⟩ : Fin j) :=
    count_match c B γ hrow hi hij hxi hxj heven (mm := (⟨i, by omega⟩ : Fin j)) (by simp)
  have e2 : decV0 c B γ hrow i x hxi = g (⟨i + 1, by omega⟩ : Fin j) ∨
      decV0 c B γ hrow j x hxj = g (⟨i + 1, by omega⟩ : Fin j) :=
    count_match c B γ hrow hi hij hxi hxj heven (mm := (⟨i + 1, by omega⟩ : Fin j)) (by simp)
  have h1 : decV0 c B γ hrow j x hxj = g (⟨i, by omega⟩ : Fin j) := by
    rcases e1 with e1 | e1
    · exact hbc.symm.trans e1
    · exact e1
  have h2 : decV0 c B γ hrow j x hxj = g (⟨i + 1, by omega⟩ : Fin j) := by
    rcases e2 with e2 | e2
    · exact hbc.symm.trans e2
    · exact e2
  have hfin : (⟨i, by omega⟩ : Fin j) = ⟨i + 1, by omega⟩ := hginj (h1.symm.trans h2)
  have hval : i = i + 1 := congrArg Fin.val hfin
  omega

/-! ### The level-`1` rows coincide -/

theorem decRows_zero_eq {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hdist : j = i + 2)
    {x : Vec m} (hxi : x ∈ Cs c B γ hrow i) (hxj : x ∈ Cs c B γ hrow j)
    (heven : ∀ y, (decMultiset c B γ hrow i x hxi +
      decMultiset c B γ hrow j x hxj).count y % 2 = 0)
    (_hbase_ne : decV0 c B γ hrow i x hxi ≠ decV0 c B γ hrow j x hxj) :
    (decRows c B γ hrow i x hxi ⟨0, hi⟩).1 =
      (decRows c B γ hrow j x hxj ⟨0, by omega⟩).1 := by
  classical
  set b0 : Vec m := decV0 c B γ hrow i x hxi with hb0
  set c0 : Vec m := decV0 c B γ hrow j x hxj with hc0
  set g : Fin j → Vec m := fun k => (decRows c B γ hrow j x hxj k).1 with hg
  have hginj : Function.Injective g := decRows_injective c B γ hrow j x hxj
  set f0 : Vec m := (decRows c B γ hrow i x hxi ⟨0, hi⟩).1 with hf0
  have hf0_mem : f0 ∈ BsV c B γ hrow 1 := by
    rw [hf0]
    exact (BsV_mem c B γ hrow 1).mpr ⟨_, decRows_mem c B γ hrow i x hxi ⟨0, hi⟩, rfl⟩
  have hmem_left : g ⟨i, by omega⟩ ∈ BsV c B γ hrow (i + 1) :=
    (BsV_mem c B γ hrow (i + 1)).mpr
      ⟨_, decRows_mem c B γ hrow j x hxj (⟨i, by omega⟩ : Fin j), rfl⟩
  have hmem_right : g ⟨i + 1, by omega⟩ ∈ BsV c B γ hrow j := by
    have h := (BsV_mem c B γ hrow ((i + 1) + 1)).mpr
      ⟨_, decRows_mem c B γ hrow j x hxj (⟨i + 1, by omega⟩ : Fin j), rfl⟩
    rw [show (i + 1) + 1 = j by omega] at h
    simpa using h
  have hne : ((⟨i, by omega⟩ : Fin j) : ℕ) ≠ ((⟨i + 1, by omega⟩ : Fin j) : ℕ) := by
    show i ≠ i + 1
    omega
  have hmem_of : ∀ z : Vec m, z = b0 ∨ z = c0 →
      z ∈ BsV c B γ hrow (i + 1) ∨ z ∈ BsV c B γ hrow j := by
    intro z hz
    have e1 : b0 = g ⟨i, by omega⟩ ∨ c0 = g ⟨i, by omega⟩ := by
      have h := count_match c B γ hrow hi hij hxi hxj heven
        (mm := (⟨i, by omega⟩ : Fin j)) (by simp)
      rwa [← hb0, ← hc0] at h
    have e2 : b0 = g ⟨i + 1, by omega⟩ ∨ c0 = g ⟨i + 1, by omega⟩ := by
      have h := count_match c B γ hrow hi hij hxi hxj heven
        (mm := (⟨i + 1, by omega⟩ : Fin j)) (by simp)
      rwa [← hb0, ← hc0] at h
    rcases hz with rfl | rfl
    · rcases e1 with e | e
      · exact Or.inl (e ▸ hmem_left)
      · rcases e2 with e2 | e2
        · exact Or.inr (e2 ▸ hmem_right)
        · exact absurd (congrArg Fin.val (hginj (e.symm.trans e2))) hne
    · rcases e1 with e | e
      · rcases e2 with e2 | e2
        · exact absurd (congrArg Fin.val (hginj (e.symm.trans e2))) hne
        · exact Or.inr (e2 ▸ hmem_right)
      · exact Or.inl (e ▸ hmem_left)
  have hb0_ne_f0 : b0 ≠ f0 := by
    intro hEq
    rcases hmem_of b0 (Or.inl rfl) with hm | hm
    · exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := 1) (by omega)) hm) (hEq.symm ▸ hf0_mem)
    · exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := j) (j := 1) (by omega)) hm) (hEq.symm ▸ hf0_mem)
  have hc0_ne_f0 : c0 ≠ f0 := by
    intro hEq
    rcases hmem_of c0 (Or.inr rfl) with hm | hm
    · exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := 1) (by omega)) hm) (hEq.symm ▸ hf0_mem)
    · exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := j) (j := 1) (by omega)) hm) (hEq.symm ▸ hf0_mem)
  have hrow0 : (decRows c B γ hrow i x hxi ⟨0, hi⟩).1 = f0 := rfl
  have hA : (decMultiset c B γ hrow i x hxi).count f0 = (if b0 = f0 then 1 else 0) + 1 := by
    have h := decMultiset_count_of_mem_BsV_one c B γ hrow hi x hxi (f := f0) hf0_mem
    rw [h, ← hb0, hrow0, if_pos rfl]
  have hD : (decMultiset c B γ hrow j x hxj).count f0 =
      (if c0 = f0 then 1 else 0) + (if g ⟨0, by omega⟩ = f0 then 1 else 0) := by
    have h := decMultiset_count_of_mem_BsV_one c B γ hrow (by omega) x hxj (f := f0) hf0_mem
    rw [h, ← hc0]
  have hMc : (decMultiset c B γ hrow i x hxi + decMultiset c B γ hrow j x hxj).count f0 =
      (if b0 = f0 then 1 else 0) + (if c0 = f0 then 1 else 0) +
        (if g ⟨0, by omega⟩ = f0 then 1 else 0) + 1 := by
    rw [Multiset.count_add, hA, hD]
    ring
  have hev := heven f0
  rw [hMc] at hev
  rw [if_neg hb0_ne_f0, if_neg hc0_ne_f0] at hev
  by_cases h : g ⟨0, by omega⟩ = f0
  · exact h.symm
  · rw [if_neg h] at hev
    norm_num at hev

/-! ### Point 2, first assertion -/

theorem Cs_disjoint {i j : ℕ} (hij : i < j) (hind : i + j + 2 ≤ ind (C0 c.aux γ B)) :
    Disjoint (Cs c B γ hrow i) (Cs c B γ hrow j) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases Nat.eq_zero_or_pos i with h0 | hi
  · subst h0
    exact Cs_notMem_C0 c B γ hrow (by omega) (by omega) hxj hxi
  · obtain ⟨heven, hpar⟩ := decMultiset_pair_even c B γ hrow hind hxi hxj
    have hle := diff_le_two c B γ hrow hi hij hxi hxj heven
    have hdist : j = i + 2 := by omega
    have hbase := decV0_ne c B γ hrow hi hij hdist hxi hxj heven
    have hlev := decRows_zero_eq c B γ hrow hi hij hdist hxi hxj heven hbase
    have hrow_eq : decRows c B γ hrow i x hxi ⟨0, hi⟩ =
        decRows c B γ hrow j x hxj ⟨0, by omega⟩ := Subtype.ext hlev
    have h1 := decV0_eq_oldV_decRows c B γ hrow i x hxi hi
    have h2 := decV0_eq_oldV_decRows c B γ hrow j x hxj (by omega)
    have h3 : oldV c B hrow (Cs c B γ hrow 0) (decRows c B γ hrow i x hxi ⟨0, hi⟩) =
        decV0 c B γ hrow j x hxj := by
      rw [hrow_eq]
      exact h2.symm
    exact hbase (h1.trans h3)


/-! ### Point 2, second assertion: `|Bᵢ| = |Cᵢ|`

The paper's argument: if `|Bⱼ| > |Cⱼ|`, two different rows `b', b'' ∈ Bⱼ` produce the same `c ∈ Cⱼ`,
so `c = b'₀ + … + b'ⱼ = b''₀ + … + b''ⱼ` with `b'ⱼ = b'`, `b''ⱼ = b''`.  Both sides have `j+1`
terms, so the total is `2j+2 ≤ 2k` terms of `C₀ ∪ B₁ ∪ … ∪ Bⱼ`; by the independence bound the
equality must be an identity, i.e. all multiplicities are even.  Hence `{b'ⱼ, b''ⱼ} = {b'₀, b''₀}`
and `b'ₗ = b''ₗ` for `1 ≤ l < j`.  Since `b'₀` (resp. `b''₀`) is the `oldV` of the level-`1` row
`b'₁` (resp. `b''₁`), the coincidence `b'₁ = b''₁` forces `b'₀ = b''₀`, and then `b'ⱼ = b''ⱼ`. -/

/-- In the decomposition of a level-`i` element, a value of a level-`l` row with `1 ≤ l ≤ i`
occurs once as that row, plus possibly once as the level-`0` vector. -/
theorem decMultiset_count_of_mem_BsV_le {i l : ℕ} (hl : 1 ≤ l) (hli : l ≤ i)
    (x : Vec m) (hx : x ∈ Cs c B γ hrow i) {y : Vec m} (hy : y ∈ BsV c B γ hrow l) :
    (decMultiset c B γ hrow i x hx).count y =
      (if decV0 c B γ hrow i x hx = y then 1 else 0) +
        (if (decRows c B γ hrow i x hx ⟨l - 1, by omega⟩).1 = y then 1 else 0) := by
  rw [decMultiset, Multiset.count_add, Multiset.count_singleton]
  have h1 : (if y = decV0 c B γ hrow i x hx then 1 else 0) =
      (if decV0 c B γ hrow i x hx = y then 1 else 0) := by
    by_cases h : decV0 c B γ hrow i x hx = y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [h1]
  congr 1
  have huniq : ∀ k : Fin i, (decRows c B γ hrow i x hx k).1 = y → k = ⟨l - 1, by omega⟩ := by
    intro k hk
    have hmem : (decRows c B γ hrow i x hx k).1 ∈ BsV c B γ hrow (k.1 + 1) :=
      (BsV_mem c B γ hrow (k.1 + 1)).mpr ⟨_, decRows_mem c B γ hrow i x hx k, rfl⟩
    have hlev : k.1 + 1 = l := by
      by_contra hne
      exact (Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := k.1 + 1) (j := l) hne) hmem) (hk.symm ▸ hy)
    exact Fin.ext (Nat.eq_sub_of_add_eq hlev)
  simpa using count_map_univ_eq_ite (decRows_injective c B γ hrow i x hx)
    (l := (⟨l - 1, by omega⟩ : Fin i)) huniq


/-- **Point 2, second assertion, injectivity.**  The map `newV` is injective on `Bᵢ₊₁`. -/
theorem newV_injOn (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    (i : ℕ) (hind : 2 * (i + 2) ≤ ind (C0 c.aux γ B)) :
    Set.InjOn (fun b : Row B => newV c B hrow (Cs c B γ hrow i) b)
      (↑(Bs c B γ hrow (i + 1)) : Set (Row B)) := by
  classical
  intro b hb b' hb' hbb'
  by_contra hne
  have hne' : b.1 ≠ b'.1 := fun h => hne (Subtype.ext h)
  have hcomp : hasComp c B hrow (Cs c B γ hrow i) b := (mem_Bs_succ c B γ hrow).mp hb |>.2
  have hcomp' : hasComp c B hrow (Cs c B γ hrow i) b' := (mem_Bs_succ c B γ hrow).mp hb' |>.2
  have hold : oldV c B hrow (Cs c B γ hrow i) b ∈ Cs c B γ hrow i := oldV_mem c B hrow hcomp
  have hold' : oldV c B hrow (Cs c B γ hrow i) b' ∈ Cs c B γ hrow i := oldV_mem c B hrow hcomp'
  set M : Multiset (Vec m) := ({b.1} : Multiset (Vec m))
      + decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold
      + ({b'.1} : Multiset (Vec m))
      + decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold' with hM
  have hbb2 : newV c B hrow (Cs c B γ hrow i) b = newV c B hrow (Cs c B γ hrow i) b' := hbb'
  have hsum : M.sum = 0 := by
    have h1 : b.1 + oldV c B hrow (Cs c B γ hrow i) b = newV c B hrow (Cs c B γ hrow i) b :=
      (newV_eq c B hrow (Cs c B γ hrow i) b).symm
    have h2 : b'.1 + oldV c B hrow (Cs c B γ hrow i) b' = newV c B hrow (Cs c B γ hrow i) b' :=
      (newV_eq c B hrow (Cs c B γ hrow i) b').symm
    rw [hM, Multiset.sum_add, Multiset.sum_add, Multiset.sum_add, Multiset.sum_singleton,
      Multiset.sum_singleton, decMultiset_sum, decMultiset_sum, h1, add_assoc, h2, hbb2,
      add_self_fun]
  have hcard : M.card = 2 * (i + 2) := by
    rw [hM, Multiset.card_add, Multiset.card_add, Multiset.card_add, Multiset.card_singleton,
      Multiset.card_singleton, decMultiset_card, decMultiset_card]
    ring
  have hsub : ∀ y ∈ M, y ∈ C0 c.aux γ B := by
    intro y hy
    rw [hM, Multiset.mem_add] at hy
    rcases hy with hy | hy
    · rw [Multiset.mem_add] at hy
      rcases hy with hy | hy
      · rw [Multiset.mem_add] at hy
        rcases hy with hy | hy
        · rw [Multiset.mem_singleton] at hy
          exact hy ▸ subset_C0_left b.2
        · exact decMultiset_sub c B γ hrow i _ hold hy
      · rw [Multiset.mem_singleton] at hy
        exact hy ▸ subset_C0_left b'.2
    · exact decMultiset_sub c B γ hrow i _ hold' hy
  have heven : ∀ y, M.count y % 2 = 0 :=
    even_count_of_sum_eq_zero hsub hsum (by rw [hcard]; exact hind)
  have hbV : b.1 ∈ BsV c B γ hrow (i + 1) :=
    (BsV_mem c B γ hrow (i + 1)).mpr ⟨b, hb, rfl⟩
  have hbV' : b'.1 ∈ BsV c B γ hrow (i + 1) :=
    (BsV_mem c B γ hrow (i + 1)).mpr ⟨b', hb', rfl⟩
  set A : Vec m := decV0 c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold with hA
  set A' : Vec m := decV0 c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold' with hA'
  have hgt1 : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold).count b.1 =
      (if A = b.1 then 1 else 0) := by
    rw [hA]
    exact decMultiset_count_of_mem_BsV_gt c B γ hrow _ hold (l := i + 1) (by omega) hbV
  have hgt2 : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold').count b.1 =
      (if A' = b.1 then 1 else 0) := by
    rw [hA']
    exact decMultiset_count_of_mem_BsV_gt c B γ hrow _ hold' (l := i + 1) (by omega) hbV
  have htop : M.count b.1 = (1 + (if A = b.1 then 1 else 0)) + (if A' = b.1 then 1 else 0) := by
    rw [hM, Multiset.count_add, Multiset.count_add, Multiset.count_add, hgt1, hgt2,
      Multiset.count_singleton_self, Multiset.count_singleton, if_neg hne', add_zero]
  have hcase1 : (A = b.1 ∧ A' ≠ b.1) ∨ (A ≠ b.1 ∧ A' = b.1) := by
    have hev := heven b.1
    rw [htop] at hev
    by_cases h1 : A = b.1 <;> by_cases h2 : A' = b.1
    · exfalso
      rw [if_pos h1, if_pos h2] at hev
      norm_num at hev
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      rw [if_neg h1, if_neg h2] at hev
      norm_num at hev
  have hgt1' : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold).count b'.1 =
      (if A = b'.1 then 1 else 0) := by
    rw [hA]
    exact decMultiset_count_of_mem_BsV_gt c B γ hrow _ hold (l := i + 1) (by omega) hbV'
  have hgt2' : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold').count b'.1 =
      (if A' = b'.1 then 1 else 0) := by
    rw [hA']
    exact decMultiset_count_of_mem_BsV_gt c B γ hrow _ hold' (l := i + 1) (by omega) hbV'
  have htop' : M.count b'.1 = (1 + (if A = b'.1 then 1 else 0)) + (if A' = b'.1 then 1 else 0) := by
    rw [hM, Multiset.count_add, Multiset.count_add, Multiset.count_add, hgt1', hgt2',
      Multiset.count_singleton, if_neg (Ne.symm hne'), Multiset.count_singleton_self]
    omega
  have hcase1' : (A = b'.1 ∧ A' ≠ b'.1) ∨ (A ≠ b'.1 ∧ A' = b'.1) := by
    have hev := heven b'.1
    rw [htop'] at hev
    by_cases h1 : A = b'.1 <;> by_cases h2 : A' = b'.1
    · exfalso
      rw [if_pos h1, if_pos h2] at hev
      norm_num at hev
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      rw [if_neg h1, if_neg h2] at hev
      norm_num at hev
  have hAcases : (A = b.1 ∧ A' = b'.1) ∨ (A = b'.1 ∧ A' = b.1) := by
    rcases hcase1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rcases hcase1' with ⟨e2', -⟩ | ⟨-, e2'⟩
      · exact absurd (e1.symm.trans e2') hne'
      · exact Or.inl ⟨e1, e2'⟩
    · rcases hcase1' with ⟨e2', -⟩ | ⟨-, e2'⟩
      · exact Or.inr ⟨e2', e2⟩
      · exact absurd (e2.symm.trans e2') hne'
  have hA_ne : A ≠ A' := by
    intro h
    rcases hAcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hne' (e1.symm.trans (h.trans e2))
    · exact hne' (e2.symm.trans (h.symm.trans e1))
  have hA_mem : A ∈ BsV c B γ hrow (i + 1) := by
    rcases hAcases with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]; exact hbV
    · rw [e]; exact hbV'
  have hA'_mem : A' ∈ BsV c B γ hrow (i + 1) := by
    rcases hAcases with ⟨-, e⟩ | ⟨-, e⟩
    · rw [e]; exact hbV'
    · rw [e]; exact hbV
  have hmatch : ∀ (l : ℕ) (hl : 1 ≤ l) (hli : l ≤ i),
      decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold ⟨l - 1, by omega⟩ =
        decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold' ⟨l - 1, by omega⟩ := by
    intro l hl hli
    set r : Row B := decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold
      ⟨l - 1, by omega⟩ with hr
    set r' : Row B := decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold'
      ⟨l - 1, by omega⟩ with hr'
    have hyV : r.1 ∈ BsV c B γ hrow l :=
      (BsV_mem c B γ hrow l).mpr ⟨r, by
        rw [hr]
        simpa [Nat.sub_add_cancel hl] using
          decRows_mem c B γ hrow i _ hold ⟨l - 1, by omega⟩, rfl⟩
    have hle1 : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold).count r.1 =
        (if A = r.1 then 1 else 0) + (if r.1 = r.1 then 1 else 0) := by
      have h := decMultiset_count_of_mem_BsV_le c B γ hrow hl hli
        (oldV c B hrow (Cs c B γ hrow i) b) hold (y := r.1) hyV
      rw [← hA, ← hr] at h
      exact h
    have hle2 : (decMultiset c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold').count r.1 =
        (if A' = r.1 then 1 else 0) + (if r'.1 = r.1 then 1 else 0) := by
      have h := decMultiset_count_of_mem_BsV_le c B γ hrow hl hli
        (oldV c B hrow (Cs c B γ hrow i) b') hold' (y := r.1) hyV
      rw [← hA', ← hr'] at h
      exact h
    have hby : b.1 ≠ r.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := l) (by omega)) hbV (by rw [h]; exact hyV)
    have hby' : b'.1 ≠ r.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := l) (by omega)) hbV' (by rw [h]; exact hyV)
    have hAy : A ≠ r.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := l) (by omega)) hA_mem (by rw [h]; exact hyV)
    have hA'y : A' ≠ r.1 := by
      intro h
      exact Finset.disjoint_left.mp
        (BsV_disjoint c B γ hrow (i := i + 1) (j := l) (by omega)) hA'_mem (by rw [h]; exact hyV)
    have hev := heven r.1
    rw [hM, Multiset.count_add, Multiset.count_add, Multiset.count_add, hle1, hle2] at hev
    simp only [Multiset.count_singleton] at hev
    rw [if_neg (Ne.symm hby), if_neg (Ne.symm hby'), if_neg hAy, if_neg hA'y] at hev
    simp only [if_true] at hev
    by_cases hrr : r'.1 = r.1
    · exact Subtype.ext hrr.symm
    · rw [if_neg hrr] at hev
      norm_num at hev
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · subst hi0
    have hA0 : A = oldV c B hrow (Cs c B γ hrow 0) b := by rw [hA]; rfl
    have hA0' : A' = oldV c B hrow (Cs c B γ hrow 0) b' := by rw [hA']; rfl
    rcases hcase1 with ⟨e, -⟩ | ⟨-, e⟩
    · have hlt := rowStep_lt_of_oldV_eq c B hrow hweight (Cs c B γ hrow 0) (b := b) (b' := b)
        (by rw [← hA0]; exact e)
      exact absurd hlt (lt_irrefl _)
    · rcases hcase1' with ⟨e2, -⟩ | ⟨-, e2⟩
      · have hlt1 := rowStep_lt_of_oldV_eq c B hrow hweight (Cs c B γ hrow 0) (b := b) (b' := b')
          (by rw [← hA0]; exact e2)
        have hlt2 := rowStep_lt_of_oldV_eq c B hrow hweight (Cs c B γ hrow 0) (b := b') (b' := b)
          (by rw [← hA0']; exact e)
        exact absurd hlt1 (not_lt.mpr (le_of_lt hlt2))
      · exact hne' (e.symm.trans e2)
  · have h0 : decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold ⟨0, hi⟩ =
        decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold' ⟨0, hi⟩ := by
      have h := hmatch 1 le_rfl hi
      have e : ((⟨1 - 1, by omega⟩ : Fin i)) = ⟨0, hi⟩ := Fin.ext rfl
      rwa [e] at h
    have hAA' : A = A' := by
      rw [hA, hA', decV0_eq_oldV_decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b) hold hi,
        decV0_eq_oldV_decRows c B γ hrow i (oldV c B hrow (Cs c B γ hrow i) b') hold' hi, h0]
    exact hA_ne hAA'

/-- **Point 2, second assertion.** Each level satisfies `|Bᵢ| = |Cᵢ|`. -/
theorem Bs_card_eq_Cs_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    (i : ℕ) (hind : 2 * (i + 2) ≤ ind (C0 c.aux γ B)) :
    (Bs c B γ hrow (i + 1)).card = (Cs c B γ hrow (i + 1)).card := by
  rw [Cs_succ, Finset.card_image_of_injOn (newV_injOn c B γ hrow hweight i hind)]


/-! ### Point 2, conclusion: cardinalities of `Bᵢ` and of `⋃ Cᵢ` -/

/-- The vector `newV` of a row is one of the two summands of the step computing that row. -/
theorem newV_smd_or (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (C : Finset (Vec m))
    (b : Row B) :
    newV c B hrow C b = smd1 c (rowStep c B hrow b) ∨
      newV c B hrow C b = smd2 c (rowStep c B hrow b) := by
  unfold newV
  split_ifs with hc
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A summand of a step is either computed by an earlier step or is a unit vector. -/
theorem step_or_basis_of_smd {k : Fin c.L} {x : Vec m}
    (h : smd1 c k = x ∨ smd2 c k = x) :
    (∃ k' : Fin c.L, c.y k' = x) ∨ ∃ i : Fin m, basisVec i = x := by
  have key : ∀ a : Fin m ⊕ Fin k.1, chainPool c.y k.1 (le_of_lt k.2) a = x →
      (∃ k' : Fin c.L, c.y k' = x) ∨ ∃ i : Fin m, basisVec i = x := by
    rintro (i | j) h
    · exact Or.inr ⟨i, by simpa [chainPool] using h⟩
    · exact Or.inl ⟨⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩, h⟩
  rcases h with h | h
  · exact key _ (by simpa [smd1] using h)
  · exact key _ (by simpa [smd2] using h)


/-- Pairwise disjointness of the sets `Cᵢ` for `i < j ≤ k`, assuming `2k + 2 ≤ ind(C₀)`. -/
theorem Cs_disjoint_le (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    {k : ℕ} (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) {i j : ℕ} (hij : i < j) (hj : j ≤ k) :
    Disjoint (Cs c B γ hrow i) (Cs c B γ hrow j) :=
  Cs_disjoint c B γ hrow hij (by omega)

/-- **Point 2, union cardinality.**  `|⋃_{i=1}^{j} Cᵢ| = Σ_{i=1}^{j} |Cᵢ|`. -/
theorem sum_Cs_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    {k : ℕ} (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) {j : ℕ} (hj : j ≤ k) :
    ((Finset.Icc 1 j).biUnion (fun i => Cs c B γ hrow i)).card =
      ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card := by
  refine Finset.card_biUnion ?_
  intro a ha b hb hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact Cs_disjoint_le c B γ hrow hind h (le_trans (Finset.mem_Icc.mp hb).2 hj)
  · exact disjoint_comm.mp
      (Cs_disjoint_le c B γ hrow hind h (le_trans (Finset.mem_Icc.mp ha).2 hj))


/-- **Point 2, union cardinality.**  The vectors of the levels `1, …, j` are the disjoint union of
the levels, so their number is `∑ |Bᵢ|`. -/
theorem sum_Bs_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) :
    ((Finset.Icc 1 j).biUnion (fun i => BsV c B γ hrow i)).card =
      ∑ i ∈ Finset.Icc 1 j, (Bs c B γ hrow i).card := by
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro i _
    exact Finset.card_image_of_injective _ Subtype.val_injective
  · intro a _ b _ hab
    exact BsV_disjoint c B γ hrow hab

theorem BsV_biUnion_subset (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) :
    (Finset.Icc 1 j).biUnion (fun i => BsV c B γ hrow i) ⊆ B := by
  intro v hv
  rw [Finset.mem_biUnion] at hv
  obtain ⟨i, -, hi⟩ := hv
  rw [BsV_mem c B γ hrow i] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  exact Bs_val_mem c B γ hrow i hr


/-- **Point 2, conclusion.**  `B` is disjoint from `⋃_{i=1}^{j} Cᵢ`, since `B ⊆ C₀` and no `Cᵢ`
with `i ≥ 1` meets `C₀`. -/
theorem disjoint_B_biUnion_Cs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {k : ℕ}
    (_hk : 2 ≤ k) (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) {j : ℕ} (_hj : j ≤ k) :
    Disjoint B ((Finset.Icc 1 j).biUnion (fun i => Cs c B γ hrow i)) := by
  rw [Finset.disjoint_left]
  intro v hvB hvC
  rw [Finset.mem_biUnion] at hvC
  obtain ⟨i, hi, hvi⟩ := hvC
  exact Cs_notMem_C0 c B γ hrow (by omega) (Finset.mem_Icc.mp hi).1 hvi (subset_C0_left hvB)

theorem card_sub_image_card_eq_sum_fiber {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card - (s.image f).card = ∑ a ∈ s.image f, ((s.filter (fun x => f x = a)).card - 1) := by
  classical
  have h1 : s.card = ∑ a ∈ s.image f, (s.filter (fun x => f x = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image_of_mem f hx)
  have h2 : (s.image f).card = ∑ _a ∈ s.image f, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  have h3 : ∀ a ∈ s.image f, 1 ≤ (s.filter (fun x => f x = a)).card := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  rw [h1, h2]
  exact (Finset.sum_tsub_distrib (s.image f) (fun a ha => h3 a ha)).symm

theorem min_ind_le_ind_of_subset {S T : Finset (Vec m)} (hST : S ⊆ T) :
    min (ind T) S.card ≤ ind S := by
  classical
  refine le_ind ?_ (min_le_right (ind T) S.card)
  intro R hRS hRc
  refine ind_elim (B := T) ?_ (fun x hx => hST (hRS hx)) rfl
  rw [hRc]
  exact min_le_left (ind T) S.card

theorem card_le_card_sub_one_of_subset_msum_two {D B : Finset (Vec m)}
    (hD : D.Nonempty) (hBD : B ⊆ msum 2 D) (hI : Indep B) : B.card ≤ D.card - 1 := by
  classical
  obtain ⟨d₀, hd₀⟩ := hD
  set T : Finset (Vec m) := (D.erase d₀).image (fun d => d + d₀) with hT
  have hTcard : T.card = D.card - 1 := by
    rw [hT, Finset.card_image_of_injective _ (fun x y h => add_right_cancel h),
      Finset.card_erase_of_mem hd₀]
  have hTmem : ∀ d ∈ D, d ≠ d₀ → d + d₀ ∈ T := by
    intro d hd hne
    exact Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨hne, hd⟩, rfl⟩
  have hsub : ∀ b ∈ B, b ∈ Submodule.span (ZMod 2) (T : Set (Vec m)) := by
    intro b hb
    have hb' := hBD hb
    rw [msum_two, mem_minkowski] at hb'
    obtain ⟨d1, hd1, d2, hd2, hsum⟩ := hb'
    have h1 : d1 + d₀ ∈ Submodule.span (ZMod 2) (T : Set (Vec m)) := by
      by_cases h : d1 = d₀
      · rw [h, add_self_fun]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span (hTmem d1 hd1 h)
    have h2 : d2 + d₀ ∈ Submodule.span (ZMod 2) (T : Set (Vec m)) := by
      by_cases h : d2 = d₀
      · rw [h, add_self_fun]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span (hTmem d2 hd2 h)
    have hsum' : (d1 + d₀) + (d2 + d₀) = b := by
      rw [add_add_add_comm, add_self_fun, add_zero, hsum]
    rw [← hsum']
    exact Submodule.add_mem _ h1 h2
  have hLI : LinearIndependent (ZMod 2)
      (fun x : B => (⟨x.1, hsub x.1 x.2⟩ : Submodule.span (ZMod 2) (T : Set (Vec m)))) :=
    hI.codRestrict (Submodule.span (ZMod 2) (T : Set (Vec m))) (fun x : B => hsub x.1 x.2)
  have h1 : B.card ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (T : Set (Vec m))) := by
    have h := LinearIndependent.fintype_card_le_finrank
      (M := Submodule.span (ZMod 2) (T : Set (Vec m))) hLI
    rwa [Fintype.card_coe] at h
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (T : Set (Vec m))) ≤ T.card :=
    finrank_span_finset_le_card T
  omega

theorem point31_arith {k : ℕ} (hk : 2 ≤ k) {D A : Finset (Vec m)} (n : ℝ) (hn : 1 ≤ n)
    (hD : 1 ≤ D.card) (hAn : (A.card : ℝ) ≤ n)
    (hsmall : D.card ≤ 2 * (k + 1) → A.card ≤ D.card - 1)
    (hlarge : 2 * (k + 1) + 1 ≤ D.card →
      (A.card : ℝ) ≤ (D.card : ℝ) ^ (1 + ((k : ℝ) + 1)⁻¹)) :
    ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * n ^ (-(1 / ((k : ℝ) + 1))) * (A.card : ℝ) ≤
      (D.card : ℝ) - 1 := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn
  by_cases hd : D.card ≤ 2 * (k + 1)
  · have hAc : (A.card : ℝ) ≤ (D.card : ℝ) - 1 := by
      have hcast : ((D.card - 1 : ℕ) : ℝ) = (D.card : ℝ) - 1 := by
        rw [Nat.cast_sub hD]; norm_num
      exact hcast ▸ (Nat.cast_le.mpr (hsmall hd))
    have hc1 : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 3)]
      linarith
    have hnneg : n ^ (-(1 / ((k : ℝ) + 1))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hn ?_
      have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hmul : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * n ^ (-(1 / ((k : ℝ) + 1))) ≤ 1 := by
      calc (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * n ^ (-(1 / ((k : ℝ) + 1)))
          ≤ 1 * 1 := mul_le_mul hc1 hnneg (by positivity) (by norm_num)
        _ = 1 := by norm_num
    have hAn0 : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    calc (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * n ^ (-(1 / ((k : ℝ) + 1))) * (A.card : ℝ)
        ≤ 1 * (A.card : ℝ) := mul_le_mul_of_nonneg_right hmul hAn0
      _ = (A.card : ℝ) := one_mul _
      _ ≤ (D.card : ℝ) - 1 := hAc
  · have hd2 : 2 * (k + 1) + 1 ≤ D.card := by omega
    have hAlarge : (A.card : ℝ) ≤ (D.card : ℝ) ^ (1 + ((k : ℝ) + 1)⁻¹) := hlarge hd2
    set d : ℝ := (D.card : ℝ) with hddef
    set mm : ℝ := (A.card : ℝ) with hmdef
    have hd1 : 1 ≤ d := by
      rw [hddef]; exact_mod_cast hD
    have hdpos : 0 < d := by linarith
    have hm0 : 0 ≤ mm := by rw [hmdef]; exact Nat.cast_nonneg _
    have hdle : (2 * (k : ℝ) + 3) ≤ d := by
      rw [hddef]; exact_mod_cast hd2
    have hpow : (1 : ℝ) + ((k : ℝ) + 1)⁻¹ = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      field_simp
      ring
    have h1 : mm ^ (((k : ℝ) + 1) / ((k : ℝ) + 2)) ≤ d := by
      have hmexp : mm ≤ d ^ (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
        rw [← hpow]; exact hAlarge
      have hstep := Real.rpow_le_rpow hm0 hmexp
        (by positivity : (0 : ℝ) ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2))
      have hdpow : (d ^ (((k : ℝ) + 2) / ((k : ℝ) + 1))) ^
          (((k : ℝ) + 1) / ((k : ℝ) + 2)) = d := by
        rw [← Real.rpow_mul (le_of_lt hdpos)]
        have hone : (((k : ℝ) + 2) / ((k : ℝ) + 1)) * (((k : ℝ) + 1) / ((k : ℝ) + 2)) = 1 := by
          field_simp
        rw [hone, Real.rpow_one]
      rw [hdpow] at hstep
      exact hstep
    have h2 : mm ^ (1 / ((k : ℝ) + 2)) ≤ n ^ (1 / ((k : ℝ) + 1)) := by
      have h2a : mm ^ (1 / ((k : ℝ) + 2)) ≤ n ^ (1 / ((k : ℝ) + 2)) :=
        Real.rpow_le_rpow hm0 hAn (by positivity)
      have h2b : n ^ (1 / ((k : ℝ) + 2)) ≤ n ^ (1 / ((k : ℝ) + 1)) := by
        refine Real.rpow_le_rpow_of_exponent_le hn ?_
        rw [one_div, one_div, inv_le_inv₀ (by positivity) (by positivity)]
        nlinarith
      linarith
    have h3 : mm ^ (1 / ((k : ℝ) + 2)) * mm ^ (((k : ℝ) + 1) / ((k : ℝ) + 2)) = mm := by
      rcases eq_or_lt_of_le hm0 with hzero | hpos
      · rw [← hzero]
        rw [Real.zero_rpow (by positivity), Real.zero_rpow (by positivity), mul_zero]
      · rw [← Real.rpow_add hpos]
        have hone : 1 / ((k : ℝ) + 2) + ((k : ℝ) + 1) / ((k : ℝ) + 2) = 1 := by
          field_simp
          ring
        rw [hone, Real.rpow_one]
    have h4 : mm ≤ n ^ (1 / ((k : ℝ) + 1)) * d := by
      calc mm = mm ^ (1 / ((k : ℝ) + 2)) * mm ^ (((k : ℝ) + 1) / ((k : ℝ) + 2)) := h3.symm
        _ ≤ n ^ (1 / ((k : ℝ) + 1)) * d :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
    have h5 : ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * mm ≤
        (d - 1) * n ^ (1 / ((k : ℝ) + 1)) := by
      have hcoef : ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * d ≤ d - 1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 3)]
        nlinarith
      have hfac : 0 ≤ (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) := by positivity
      calc ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * mm
          ≤ ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (n ^ (1 / ((k : ℝ) + 1)) * d) :=
              mul_le_mul_of_nonneg_left h4 hfac
        _ = (((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * d) * n ^ (1 / ((k : ℝ) + 1)) := by
              ring
        _ ≤ (d - 1) * n ^ (1 / ((k : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hcoef (by positivity)
    have hc : ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * n ^ (-(1 / ((k : ℝ) + 1))) =
        ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) / n ^ (1 / ((k : ℝ) + 1)) := by
      rw [Real.rpow_neg (le_of_lt hn0)]
      simp only [div_eq_mul_inv]
    have hNpos : 0 < n ^ (1 / ((k : ℝ) + 1)) := Real.rpow_pos_of_pos hn0 _
    have h5' : ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * mm / n ^ (1 / ((k : ℝ) + 1)) ≤
        d - 1 := by
      rw [div_le_iff₀ hNpos]
      exact h5
    rw [hc]
    rw [div_eq_mul_inv] at h5'
    exact le_of_eq_of_le (by simp only [div_eq_mul_inv]; ac_rfl) h5'

/-! ### Point 3: the counting step -/

/-- The values whose computation must be accounted for in the chain: the rows of `B` together
with the elements of `C₁, …, Cⱼ`. -/
noncomputable def workSet (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) : Finset (Vec m) :=
  B ∪ (Finset.Icc 1 j).biUnion (fun i => Cs c B γ hrow i)

theorem mem_workSet {hrow : ∀ b : Row B, b.1 ∈ Set.range c.y} {j : ℕ} {v : Vec m} :
    v ∈ workSet c B γ hrow j ↔
      v ∈ B ∨ ∃ i, 1 ≤ i ∧ i ≤ j ∧ v ∈ Cs c B γ hrow i := by
  rw [workSet, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨i, hi, hvi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2, hvi⟩
  · rintro (h | ⟨i, h1, h2, hvi⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, Finset.mem_Icc.mpr ⟨h1, h2⟩, hvi⟩

/-- **Point 3, counting step (existence).**  Every vector of the work set whose weight is not `1`
is the value of a step of the chain whose type is `0`.

The row itself is not a sum of two elements of `C₀` by point 1, and an element of `Cᵢ` is a
summand of the step computing a row: it is either a previous value of the chain or a unit
vector, and a unit vector has weight `1`. -/
theorem exists_step_of_mem_workSet (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) {j : ℕ} {v : Vec m}
    (hv : v ∈ workSet c B γ hrow j) (hv1 : weight (Finset.univ : Finset (Fin m)) v ≠ 1) :
    ∃ k : Fin c.L, c.y k = v ∧ c.typeWeight k = 0 := by
  rw [mem_workSet] at hv
  rcases hv with hvB | ⟨i, hi1, -, hvi⟩
  · obtain ⟨k, hk⟩ := hrow ⟨v, hvB⟩
    refine ⟨k, hk, ?_⟩
    rw [typeWeight_eq_weight_y, hk, weight_eq_zero_iff]
    exact hB ⟨v, hvB⟩
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Cs_succ] at hvi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hvi
    have hproj : proj c.aux (newV c B hrow (Cs c B γ hrow i') b) = 0 :=
      Cs_type_zero c B γ hrow hB (i' + 1) _ (Finset.mem_image_of_mem _ hb)
    have hdisj := newV_smd_or c B hrow (Cs c B γ hrow i') b
    rcases step_or_basis_of_smd c (k := rowStep c B hrow b) (by
        rcases hdisj with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm) with ⟨k', hk'⟩ | ⟨l, hl⟩
    · refine ⟨k', hk', ?_⟩
      rw [typeWeight_eq_weight_y, hk', weight_eq_zero_iff]
      exact hproj
    · exact absurd (by rw [← hl]; exact weight_univ_basisVec l) hv1

/-- **Point 3, counting step (main).**  Different vectors of the work set are computed by
different steps, and all these steps have type `0`, hence are not heavy.  Therefore the reduced
complexity is at least the number of non-input vectors of the work set. -/
theorem card_workSet_sub_reducedComplexity (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    (hind : 3 ≤ ind (C0 c.aux γ B)) (j : ℕ) :
    (workSet c B γ hrow j).card - inputSlack c.aux γ ≤ c.reducedComplexity := by
  classical
  set W := workSet c B γ hrow j with hW
  set W₀ := W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1) with hW₀
  have hW₀mem : ∀ v : W₀, (v : Vec m) ∈ workSet c B γ hrow j ∧
      weight (Finset.univ : Finset (Fin m)) (v : Vec m) ≠ 1 := by
    intro v
    have hv : (v : Vec m) ∈
        W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1) := by
      rw [← hW₀]; exact v.2
    rw [Finset.mem_filter] at hv
    exact ⟨hW ▸ hv.1, hv.2⟩
  set f : W₀ → Fin c.L := fun v =>
    Classical.choose (exists_step_of_mem_workSet c B γ hrow hB
      (hW₀mem v).1 (hW₀mem v).2) with hf
  have hf_spec : ∀ v : W₀, c.y (f v) = v.1 ∧ c.typeWeight (f v) = 0 := fun v =>
    Classical.choose_spec (exists_step_of_mem_workSet c B γ hrow hB
      (hW₀mem v).1 (hW₀mem v).2)
  have hf_inj : Function.Injective f := by
    intro v v' hvv'
    have : (v : Vec m) = v' := by rw [← (hf_spec v).1, ← (hf_spec v').1, hvv']
    exact Subtype.ext this
  have hS_card : (W₀.attach.image f).card = W₀.card := by
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_attach]
  have hS_light : ∀ k ∈ W₀.attach.image f, k ∉ c.heavySteps := by
    intro k hk
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hk
    rw [ExtChain.mem_heavySteps]
    have := (hf_spec v).2
    omega
  have hL : (W₀.attach.image f).card + c.heavySteps.card ≤ c.L := by
    have hcompl : c.heavySteps ⊆ Finset.univ \ (W₀.attach.image f) := by
      intro k hk
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, fun hmem => hS_light k hmem hk⟩
    have hle := Finset.card_le_card hcompl
    have hdisj : Disjoint (W₀.attach.image f) (Finset.univ \ (W₀.attach.image f)) :=
      Finset.disjoint_sdiff
    have hunion : (W₀.attach.image f) ∪ (Finset.univ \ (W₀.attach.image f)) = Finset.univ :=
      Finset.union_sdiff_of_subset (Finset.subset_univ _)
    calc (W₀.attach.image f).card + c.heavySteps.card
        ≤ (W₀.attach.image f).card + (Finset.univ \ (W₀.attach.image f)).card := by omega
      _ = ((W₀.attach.image f) ∪ (Finset.univ \ (W₀.attach.image f))).card := by
          rw [Finset.card_union_of_disjoint hdisj]
      _ = c.L := by rw [hunion, Finset.card_univ, Fintype.card_fin]
  have htype : c.typeSet.card ≤ c.heavySteps.card := Finset.card_image_le
  have hW0 : W₀.card ≤ c.reducedComplexity := by
    rw [ExtChain.reducedComplexity, ← hS_card]
    omega
  have hsplit : W.card = W₀.card +
      (W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1)).card := by
    have hsum := Finset.card_filter_add_card_filter_not (s := W)
      (p := fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1)
    have hnot : W.filter (fun v => ¬ weight (Finset.univ : Finset (Fin m)) v ≠ 1) =
        W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) := by
      refine Finset.filter_congr ?_
      intro v _
      exact not_not
    rw [← hW₀, hnot] at hsum
    exact hsum.symm
  have hEc : (W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1)).card ≤
      inputSlack c.aux γ := by
    have hsub : W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) ⊆ W :=
      Finset.filter_subset _ _
    by_cases hγ : γ = true
    · have hzero :
          (W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1)).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr ?_)
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvW, hv1⟩ := hv
        obtain ⟨l, hl⟩ := eq_basisVec_of_weight_univ_eq_one hv1
        rw [hW, mem_workSet] at hvW
        rcases hvW with hvB | ⟨i, hi1, -, hvi⟩
        · exact hweight ⟨v, hvB⟩ hv1
        · have hlnot : l ∉ c.aux :=
            basisVec_notMem_aux_of_mem_Cs c B γ hrow hB hi1 hvi hl
          refine Cs_notMem_C0 c B γ hrow hind hi1 hvi ?_
          rw [mem_C0]
          exact Or.inr ⟨hγ, by rw [mem_freeVecs]; exact ⟨l, hlnot, hl.symm⟩⟩
      subst hγ
      simp [inputSlack]
      omega
    · have hγf : γ = false := by cases γ <;> simp_all
      rw [hγf]
      simp [inputSlack]
      set E := W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) with hE
      have hEmem : ∀ v : ↥E, weight (Finset.univ : Finset (Fin m)) (v : Vec m) = 1 := by
        intro v
        have hv : (v : Vec m) ∈
            W.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) := by
          rw [← hE]; exact v.2
        exact (Finset.mem_filter.mp hv).2
      let g : ↥E → Fin m := fun v =>
        Classical.choose (eq_basisVec_of_weight_univ_eq_one (hEmem v))
      have hg : ∀ v : ↥E, (v : Vec m) = basisVec (g v) := fun v =>
        Classical.choose_spec (eq_basisVec_of_weight_univ_eq_one (hEmem v))
      have hg_inj : Function.Injective g := by
        intro v v' hvv
        have hcoe : (v : Vec m) = (v' : Vec m) := by rw [hg v, hg v', hvv]
        exact Subtype.ext hcoe
      have hle := Fintype.card_le_of_injective g hg_inj
      rw [Fintype.card_coe, Fintype.card_fin] at hle
      exact hle
  omega

/-- **Point 3, the counting bound.**  `L*(B) ≥ |B| + ∑_{i=1}^{j} |Cᵢ| - (1-γ)m`. -/
theorem count_bound (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    {k : ℕ} (hk : 2 ≤ k) (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B))
    {j : ℕ} (hj : j ≤ k) :
    B.card + ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card - inputSlack c.aux γ ≤
      c.reducedComplexity := by
  have h1 := card_workSet_sub_reducedComplexity c B γ hrow hB hweight (by omega) j
  have h2 : (workSet c B γ hrow j).card =
      B.card + ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card := by
    rw [workSet,
      Finset.card_union_of_disjoint
        (disjoint_B_biUnion_Cs c B γ hrow hk hind hj),
      sum_Cs_card c B γ hrow hind hj]
  omega


/-- **Counting lemma for point 3.1.**  If every vector of `X` is the value of a step of the
chain, no two of them by the same step, and every vector of `X` outside `D` has type `0`, then
the reduced complexity is at least `|X|` minus the number of types occurring in `D`. -/
theorem reducedComplexity_ge_card_sub_image_proj (c : ExtChain m) (X D : Finset (Vec m))
    (φ : ↥X → Fin c.L) (hφ : ∀ v : ↥X, c.y (φ v) = v.1)
    (hinj : Function.Injective φ)
    (hX : ∀ v ∈ X, v ∉ D → proj c.aux v = 0) :
    X.card - (D.image (proj c.aux)).card ≤ c.reducedComplexity := by
  classical
  set I : Finset (Fin c.L) := X.attach.image φ with hI
  have hI_mem : ∀ k ∈ I, ∃ v : ↥X, φ v = k := by
    intro k hk
    rw [hI, Finset.mem_image] at hk
    obtain ⟨v, -, hv⟩ := hk
    exact ⟨v, hv⟩
  have hIcard : I.card = X.card := by
    rw [hI, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  set J : Finset (Fin c.L) := I.filter (fun k => 2 ≤ c.typeWeight k) with hJ
  have hJ_sub : J ⊆ I := by
    intro k hk
    rw [hJ] at hk
    exact (Finset.mem_filter.mp hk).1
  have hJ_type : J.image c.stepType ⊆ D.image (proj c.aux) := by
    intro y hy
    obtain ⟨k, hk, hky⟩ := Finset.mem_image.mp hy
    have hkI : k ∈ I := hJ_sub hk
    have hheavy : 2 ≤ c.typeWeight k := by
      rw [hJ] at hk
      exact (Finset.mem_filter.mp hk).2
    obtain ⟨v, hvk⟩ := hI_mem k hkI
    have hvD : v.1 ∈ D := by
      by_contra hv
      have hz : proj c.aux v.1 = 0 := hX v.1 v.2 hv
      have hw : c.typeWeight k = 0 := by
        rw [ExtChain.typeWeight, ← hvk, hφ v]
        exact (weight_eq_zero_iff c.aux v.1).mpr hz
      omega
    refine Finset.mem_image.mpr ⟨v.1, hvD, ?_⟩
    rw [← hky, ExtChain.stepType, ← hvk, hφ v]
  have htypeSet_sub : c.typeSet ⊆
      J.image c.stepType ∪ (c.heavySteps \ I).image c.stepType := by
    intro y hy
    rw [ExtChain.typeSet] at hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    by_cases hkI : k ∈ I
    · have hkJ : k ∈ J := by
        rw [hJ]
        exact Finset.mem_filter.mpr ⟨hkI, (ExtChain.mem_heavySteps).mp hk⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hkJ, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hk, hkI⟩, rfl⟩)
  have huniv : (Finset.univ \ I).card = c.L - I.card := by
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
  have hcard : c.typeSet.card ≤ (D.image (proj c.aux)).card + (c.L - I.card) := by
    calc c.typeSet.card
        ≤ (J.image c.stepType ∪ (c.heavySteps \ I).image c.stepType).card :=
          Finset.card_le_card htypeSet_sub
      _ ≤ (J.image c.stepType).card + ((c.heavySteps \ I).image c.stepType).card :=
          Finset.card_union_le _ _
      _ ≤ (D.image (proj c.aux)).card + (c.heavySteps \ I).card :=
          add_le_add (Finset.card_le_card hJ_type) Finset.card_image_le
      _ ≤ (D.image (proj c.aux)).card + (c.L - I.card) := by
          have h1 : (c.heavySteps \ I).card ≤ (Finset.univ \ I).card :=
            Finset.card_le_card (by
              intro k hk
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
                (Finset.mem_sdiff.mp hk).2⟩)
          omega
  have hXle : X.card ≤ c.L := by
    rw [← hIcard]
    calc I.card ≤ (Finset.univ : Finset (Fin c.L)).card :=
          Finset.card_le_card (Finset.subset_univ I)
      _ = c.L := by rw [Finset.card_univ, Fintype.card_fin]
  have h3 : c.typeSet.card + X.card ≤ (D.image (proj c.aux)).card + c.L := by
    omega
  rw [ExtChain.reducedComplexity]
  omega


/-! ### Point 3.1: some level `Cⱼ` is small

We follow the paper: `B' = B ∖ ⋃_{i≤j} Bᵢ`, and `D` is the set of both summands of the steps
computing the rows of `B'`.  Every vector of `W ∪ D` of weight different from `1` is computed by
a step, and the only vectors of `W ∪ D` whose type may be nonzero lie in `D`; hence the reduced
complexity is at least `|W| + |D| - |Cⱼ| - |types(D)| - (1-γ)m`, and the per-type estimate for
`|Dᵃ|` bounds `|D| - |types(D)|` from below by `c·|B'|`. -/

/-- The union of the values of the rows of `B₁, …, Bⱼ`. -/
noncomputable def accV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) : Finset (Vec m) :=
  (Finset.Icc 1 j).biUnion (fun i => BsV c B γ hrow i)

theorem mem_accV (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {v : Vec m} :
    v ∈ accV c B γ hrow j ↔ ∃ i, 1 ≤ i ∧ i ≤ j ∧ v ∈ BsV c B γ hrow i := by
  rw [accV, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, hi, hvi⟩
    exact ⟨i, (Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2, hvi⟩
  · rintro ⟨i, h1, h2, hvi⟩
    exact ⟨i, Finset.mem_Icc.mpr ⟨h1, h2⟩, hvi⟩

theorem mem_accV_iff_mem_acc (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ}
    {b : Row B} : b.1 ∈ accV c B γ hrow j ↔ b ∈ acc c B γ hrow j := by
  rw [mem_accV]
  constructor
  · rintro ⟨i, -, h2, hi⟩
    rw [BsV_mem c B γ hrow i] at hi
    obtain ⟨r, hr, hrb⟩ := hi
    have hrb' : r = b := Subtype.ext hrb
    exact (mem_acc c B γ hrow).mpr ⟨i, h2, hrb' ▸ hr⟩
  · intro hb
    obtain ⟨l, hl, hbl⟩ := (mem_acc c B γ hrow).mp hb
    have hl1 : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with h0 | hpos
      · rw [h0, Bs_zero] at hbl
        exact absurd hbl (by simp)
      · exact hpos
    exact ⟨l, hl1, hl, (BsV_mem c B γ hrow l).mpr ⟨b, hbl, rfl⟩⟩

/-- The rows of `B' = B ∖ ⋃_{i≤j} Bᵢ`, as a finite set of rows. -/
noncomputable def B'R (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) : Finset (Row B) :=
  B.attach.filter (fun r => r.1 ∈ B \ accV c B γ hrow j)

theorem mem_B'R (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {b : Row B} :
    b ∈ B'R c B γ hrow j ↔ b.1 ∈ B \ accV c B γ hrow j := by
  rw [B'R, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_attach _ _, h⟩⟩

theorem not_mem_acc_of_mem_B'R (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ}
    {b : Row B} (hb : b ∈ B'R c B γ hrow j) : b ∉ acc c B γ hrow j := by
  intro h
  exact (Finset.mem_sdiff.mp ((mem_B'R c B γ hrow).mp hb)).2
    ((mem_accV_iff_mem_acc c B γ hrow).mpr h)

/-- **Key avoidance.**  If a row lies outside `B₁, …, Bⱼ`, neither summand of the step computing
it lies in `Cᵢ` for any `i < j`.  Otherwise the row would itself belong to `Bᵢ₊₁`. -/
theorem rowS_notMem_Cs_of_mem_B'R (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ}
    {b : Row B} (hb : b ∈ B'R c B γ hrow j) {i : ℕ} (hi : i < j) :
    rowS1 c B hrow b ∉ Cs c B γ hrow i ∧ rowS2 c B hrow b ∉ Cs c B γ hrow i := by
  have hbacc : b ∉ acc c B γ hrow j := not_mem_acc_of_mem_B'R c B γ hrow hb
  have key : ∀ s : Vec m, (s = rowS1 c B hrow b ∨ s = rowS2 c B hrow b) →
      s ∉ Cs c B γ hrow i := by
    intro s hs hmem
    have hcomp : hasComp c B hrow (Cs c B γ hrow i) b := by
      rcases hs with h | h
      · exact Or.inl (h ▸ hmem)
      · exact Or.inr (h ▸ hmem)
    by_cases hbi : b ∈ acc c B γ hrow i
    · exact hbacc (acc_mono c B γ hrow (by omega) hbi)
    · have hbs : b ∈ Bs c B γ hrow (i + 1) := (mem_Bs_succ c B γ hrow).mpr ⟨hbi, hcomp⟩
      exact hbacc (acc_mono c B γ hrow (by omega)
        ((mem_acc c B γ hrow).mpr ⟨i + 1, le_rfl, hbs⟩))
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

/-- The set `D` of point 3.1: the two summands of the steps computing the rows of `B'`. -/
noncomputable def Dset (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) : Finset (Vec m) :=
  (B'R c B γ hrow j).image (fun r => rowS1 c B hrow r) ∪
    (B'R c B γ hrow j).image (fun r => rowS2 c B hrow r)

theorem mem_Dset (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {d : Vec m} :
    d ∈ Dset c B γ hrow j ↔
      (∃ b ∈ B'R c B γ hrow j, rowS1 c B hrow b = d) ∨
        ∃ b ∈ B'R c B γ hrow j, rowS2 c B hrow b = d := by
  rw [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_image]

/-- No element of `D` belongs to `C₀`; in particular `D` is disjoint from `B` and contains no
vector of weight `1`. -/
theorem Dset_notMem_C0 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} (hj1 : 1 ≤ j)
    {d : Vec m} (hd : d ∈ Dset c B γ hrow j) : d ∉ C0 c.aux γ B := by
  rcases (mem_Dset c B γ hrow).mp hd with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · have h := (rowS_notMem_Cs_of_mem_B'R c B γ hrow hb (i := 0) (by omega)).1
    rwa [Cs_zero] at h
  · have h := (rowS_notMem_Cs_of_mem_B'R c B γ hrow hb (i := 0) (by omega)).2
    rwa [Cs_zero] at h

theorem Dset_notMem_Cs (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ}
    {d : Vec m} (hd : d ∈ Dset c B γ hrow j) {i : ℕ} (hij : i < j) :
    d ∉ Cs c B γ hrow i := by
  rcases (mem_Dset c B γ hrow).mp hd with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · exact (rowS_notMem_Cs_of_mem_B'R c B γ hrow hb hij).1
  · exact (rowS_notMem_Cs_of_mem_B'R c B γ hrow hb hij).2

/-- The type assigned to a row in point 3.1: the common type of the two summands of the step
computing it. -/
noncomputable def lab (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (b : Row B) : Vec m :=
  proj c.aux (rowS1 c B hrow b)

/-- The two summands of the step computing a row of `B'` have the same type, since the row
itself has type `0`. -/
theorem lab_eq_s2 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) (b : Row B) :
    proj c.aux (rowS2 c B hrow b) = lab c B hrow b := by
  have h := proj_add c.aux (rowS1 c B hrow b) (rowS2 c B hrow b)
  rw [rowS_add, hB b] at h
  have h' : proj c.aux (rowS1 c B hrow b) + proj c.aux (rowS1 c B hrow b) = 0 :=
    add_self_fun _
  calc proj c.aux (rowS2 c B hrow b)
      = 0 + proj c.aux (rowS2 c B hrow b) := (zero_add _).symm
    _ = (proj c.aux (rowS1 c B hrow b) + proj c.aux (rowS1 c B hrow b)) +
          proj c.aux (rowS2 c B hrow b) := by rw [h']
    _ = proj c.aux (rowS1 c B hrow b) +
          (proj c.aux (rowS1 c B hrow b) + proj c.aux (rowS2 c B hrow b)) := by rw [add_assoc]
    _ = proj c.aux (rowS1 c B hrow b) + 0 := by rw [h]
    _ = proj c.aux (rowS1 c B hrow b) := add_zero _

/-- The rows of `B'` whose type is `a`. -/
noncomputable def Ba (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) (a : Vec m) :
    Finset (Row B) :=
  (B'R c B γ hrow j).filter (fun b => lab c B hrow b = a)

/-- The elements of `D` whose type is `a`. -/
noncomputable def Da (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) (a : Vec m) :
    Finset (Vec m) :=
  (Dset c B γ hrow j).filter (fun d => proj c.aux d = a)

theorem mem_Ba (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {a : Vec m}
    {b : Row B} :
    b ∈ Ba c B γ hrow j a ↔ b ∈ B'R c B γ hrow j ∧ lab c B hrow b = a := by
  rw [Ba, Finset.mem_filter]

theorem mem_Da (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {a : Vec m} {d : Vec m} :
    d ∈ Da c B γ hrow j a ↔ d ∈ Dset c B γ hrow j ∧ proj c.aux d = a := by
  rw [Da, Finset.mem_filter]

theorem BaV_subset_C0 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) (a : Vec m) :
    (Ba c B γ hrow j a).image Subtype.val ⊆ C0 c.aux γ B := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  exact subset_C0_left (Finset.mem_sdiff.mp ((mem_B'R c B γ hrow).mp
    ((mem_Ba c B γ hrow).mp hb).1)).1

/-- **Point 3.1, per-type inclusion.**  `Bᵃ ⊆ Dᵃ + Dᵃ`. -/
theorem BaV_subset_msum (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) (j : ℕ) (a : Vec m) :
    (Ba c B γ hrow j a).image Subtype.val ⊆ msum 2 (Da c B γ hrow j a) := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  have hbR : b ∈ B'R c B γ hrow j := ((mem_Ba c B γ hrow).mp hb).1
  have hlab : lab c B hrow b = a := ((mem_Ba c B γ hrow).mp hb).2
  have h1 : rowS1 c B hrow b ∈ Da c B γ hrow j a := by
    rw [mem_Da]
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hbR, rfl⟩), hlab⟩
  have h2 : rowS2 c B hrow b ∈ Da c B γ hrow j a := by
    rw [mem_Da]
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hbR, rfl⟩),
      by rw [lab_eq_s2 c B hrow hB b]; exact hlab⟩
  rw [msum_two, mem_minkowski]
  exact ⟨rowS1 c B hrow b, h1, rowS2 c B hrow b, h2, rowS_add c B hrow b⟩

/-- **Point 3.1, independence.**  `ind Bᵃ ≥ min{2k+2, |Bᵃ|}`. -/
theorem BaV_ind (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {k : ℕ}
    (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) (j : ℕ) (a : Vec m) :
    min (2 * k + 2) ((Ba c B γ hrow j a).image Subtype.val).card ≤
      ind ((Ba c B γ hrow j a).image Subtype.val) :=
  le_trans (min_le_min hind (le_refl _))
    (min_ind_le_ind_of_subset (BaV_subset_C0 c B γ hrow j a))

theorem Da_nonempty_of_mem_image (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ}
    {a : Vec m} (ha : a ∈ (Dset c B γ hrow j).image (proj c.aux)) :
    (Da c B γ hrow j a).Nonempty := by
  obtain ⟨d, hd, hda⟩ := Finset.mem_image.mp ha
  exact ⟨d, (mem_Da c B γ hrow).mpr ⟨hd, hda⟩⟩

/-- **Point 3.1, the per-type estimate.**  `|Dᵃ| - 1 ≥ c·|Bᵃ|` with
`c = (2k+2)/(2k+3) · n^{-1/(k+1)}`. -/
theorem per_type_bound (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) {k : ℕ} (hk : 2 ≤ k)
    (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) {j : ℕ} {a : Vec m}
    (ha : a ∈ (Dset c B γ hrow j).image (proj c.aux)) :
    ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) *
        (((Ba c B γ hrow j a).image Subtype.val).card : ℝ) ≤
      ((Da c B γ hrow j a).card : ℝ) - 1 := by
  classical
  set A := (Ba c B γ hrow j a).image Subtype.val with hA
  set D := Da c B γ hrow j a with hDdef
  have hDne : D.Nonempty := hDdef ▸ Da_nonempty_of_mem_image c B γ hrow ha
  have hDcard : 1 ≤ D.card := Finset.card_pos.mpr hDne
  have hmsum : A ⊆ msum 2 D := hA ▸ BaV_subset_msum c B γ hrow hB j a
  have hindA : min (2 * k + 2) A.card ≤ ind A := hA ▸ BaV_ind c B γ hrow hind j a
  have hAcard : A.card ≤ B.card := by
    rw [hA]
    refine le_trans Finset.card_image_le ?_
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    calc (B'R c B γ hrow j).card ≤ B.attach.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = B.card := Finset.card_attach
  by_cases hBa : (Ba c B γ hrow j a) = ∅
  · rw [hA, hBa]
    simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero, mul_zero]
    have h1 : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hDcard
    linarith
  · have hne : A.Nonempty := by
      rw [hA]
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hBa
      exact ⟨b.1, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    have hn : (1 : ℝ) ≤ (B.card : ℝ) := by
      have h1 : 0 < A.card := Finset.card_pos.mpr hne
      have h2 : 0 < B.card := lt_of_lt_of_le h1 hAcard
      exact_mod_cast h2
    refine point31_arith (D := D) (A := A) (n := (B.card : ℝ)) hk hn hDcard
      ?_ ?_ ?_
    · exact_mod_cast hAcard
    · intro hdk
      by_cases hAc : A.card ≤ 2 * (k + 1)
      · refine card_le_card_sub_one_of_subset_msum_two hDne hmsum ?_
        have hmin : A.card ≤ min (2 * k + 2) A.card := le_min (by omega) le_rfl
        exact ind_elim (le_trans hmin hindA) (Finset.Subset.refl _) rfl
      · have hmin : 2 * (k + 1) ≤ min (2 * k + 2) A.card :=
          le_min (by omega) (by omega)
        exact (lemma4 D A (k + 1) (by omega) hmsum (le_trans hmin hindA)).1 hdk
    · intro hd
      by_cases hAc : 2 * (k + 1) ≤ A.card
      · have hmin : 2 * (k + 1) ≤ min (2 * k + 2) A.card := le_min (by omega) hAc
        simpa only [Nat.cast_add, Nat.cast_one] using
          (lemma4 D A (k + 1) (by omega) hmsum (le_trans hmin hindA)).2 hd
      · have h1 : A.card ≤ D.card := by omega
        have h1' : (A.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h1
        have hD1 : (1 : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast hDcard
        have hexp : (1 : ℝ) ≤ 1 + ((k : ℝ) + 1)⁻¹ := by
          have hp : (0 : ℝ) ≤ ((k : ℝ) + 1)⁻¹ := by positivity
          linarith
        have h2 : (D.card : ℝ) ≤ (D.card : ℝ) ^ (1 + ((k : ℝ) + 1)⁻¹) := by
          calc (D.card : ℝ) = (D.card : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hD1 hexp
        linarith

/-- The number of vectors of `D` of each type: `|D| - |types(D)| = Σ_a (|Dᵃ| - 1)`. -/
theorem Dset_card_sub_image_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) :
    (Dset c B γ hrow j).card - ((Dset c B γ hrow j).image (proj c.aux)).card =
      ∑ a ∈ (Dset c B γ hrow j).image (proj c.aux), ((Da c B γ hrow j a).card - 1) := by
  rw [card_sub_image_card_eq_sum_fiber]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Da]

/-- The type of a row of `B'` is the common type of the two summands of its step, and it occurs
among the types of `D`. -/
theorem lab_mem_image_proj (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {b : Row B}
    (hb : b ∈ B'R c B γ hrow j) :
    lab c B hrow b ∈ (Dset c B γ hrow j).image (proj c.aux) :=
  Finset.mem_image.mpr ⟨rowS1 c B hrow b,
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩), rfl⟩

/-- Rows whose type is not the type of any row of `B'` do not exist. -/
theorem Ba_empty_of_not_mem_lab (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) {j : ℕ} {a : Vec m}
    (ha : a ∉ (B'R c B γ hrow j).image (lab c B hrow)) : Ba c B γ hrow j a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro b hb
  have h := (mem_Ba c B γ hrow).mp hb
  exact ha (Finset.mem_image.mpr ⟨b, h.1, h.2⟩)

/-- Passing from rows to their value is injective. -/
theorem Ba_card_eq_image_card (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) (a : Vec m) :
    (Ba c B γ hrow j a).card = ((Ba c B γ hrow j a).image Subtype.val).card :=
  (Finset.card_image_of_injective _ Subtype.val_injective).symm

/-- The rows of `B'` split by type. -/
theorem B'R_card_eq_sum_Ba (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y) (j : ℕ) :
    (B'R c B γ hrow j).card =
      ∑ a ∈ (B'R c B γ hrow j).image (lab c B hrow), (Ba c B γ hrow j a).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := B'R c B γ hrow j) (f := lab c B hrow)
    (t := (B'R c B γ hrow j).image (lab c B hrow)) (fun x hx => Finset.mem_image_of_mem _ hx)
  rw [h]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Ba]

/-- **Point 3.1, the per-type estimate summed over the types.**  `|D| - |types(D)|` is at least
`c·|B'|` with `c = (2k+2)/(2k+3)·n^{-1/(k+1)}`. -/
theorem Dset_sum_per_type (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0) {k : ℕ} (hk : 2 ≤ k)
    (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) (j : ℕ) :
    ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) *
        ((B'R c B γ hrow j).card : ℝ) ≤
      (((Dset c B γ hrow j).card - ((Dset c B γ hrow j).image (proj c.aux)).card : ℕ) : ℝ) := by
  classical
  set T := (Dset c B γ hrow j).image (proj c.aux) with hT
  set S := (B'R c B γ hrow j).image (lab c B hrow) with hS
  have hsub : S ⊆ T := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact lab_mem_image_proj c B γ hrow hb
  have hzero : ∀ a ∈ T, a ∉ S → (Ba c B γ hrow j a).card = 0 := by
    intro a ha hna
    rw [Ba_empty_of_not_mem_lab c B γ hrow (by rw [← hS]; exact hna)]
    simp
  have hsum_nat : ∑ a ∈ T, (Ba c B γ hrow j a).card = (B'R c B γ hrow j).card := by
    rw [B'R_card_eq_sum_Ba c B γ hrow j]
    exact (Finset.sum_subset hsub (fun a ha hna => hzero a ha hna)).symm
  have hsum_eq : ∑ a ∈ T, ((Ba c B γ hrow j a).card : ℝ) = ((B'R c B γ hrow j).card : ℝ) := by
    rw [← Nat.cast_sum, hsum_nat]
  have h2 : ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) *
        (∑ a ∈ T, ((Ba c B γ hrow j a).card : ℝ)) ≤
      ∑ a ∈ T, (((Da c B γ hrow j a).card : ℝ) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a ha => ?_)
    rw [Ba_card_eq_image_card c B γ hrow j a]
    exact per_type_bound c B γ hrow hB hk hind (hT ▸ ha)
  have hDa1 : ∀ a ∈ T, (((Da c B γ hrow j a).card - 1 : ℕ) : ℝ) =
      ((Da c B γ hrow j a).card : ℝ) - 1 := by
    intro a ha
    have hpos : 1 ≤ (Da c B γ hrow j a).card :=
      Finset.card_pos.mpr (Da_nonempty_of_mem_image c B γ hrow (hT ▸ ha))
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  rw [Dset_card_sub_image_card c B γ hrow j, Nat.cast_sum]
  rw [show ∑ a ∈ T, (((Da c B γ hrow j a).card - 1 : ℕ) : ℝ) =
      ∑ a ∈ T, (((Da c B γ hrow j a).card : ℝ) - 1) from Finset.sum_congr rfl hDa1]
  calc ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) *
        ((B'R c B γ hrow j).card : ℝ)
      = ((2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3)) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) *
          (∑ a ∈ T, ((Ba c B γ hrow j a).card : ℝ)) := by rw [hsum_eq]
    _ ≤ _ := h2

/-- **Point 3.1, the cardinality of `B`.**  `|B| = |B'| + Σ_{i≤j} |Cᵢ|`, since the rows split
into those that are reached within `j` levels and the remaining ones. -/
theorem card_B_eq_B'R_add (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1) {k : ℕ} (_hk : 2 ≤ k) (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B))
    {j : ℕ} (hj : j ≤ k) :
    B.card = (B'R c B γ hrow j).card +
      ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card := by
  classical
  have hacc : accV c B γ hrow j ⊆ B := BsV_biUnion_subset c B γ hrow j
  have hB'Req : B'R c B γ hrow j = B.attach.filter (fun r => r.1 ∉ accV c B γ hrow j) := by
    rw [B'R]
    refine Finset.filter_congr ?_
    intro r _
    rw [Finset.mem_sdiff]
    exact ⟨fun h => h.2, fun h => ⟨r.2, h⟩⟩
  have hunion : B'R c B γ hrow j ∪ B.attach.filter (fun r => r.1 ∈ accV c B γ hrow j) =
      B.attach := by
    rw [hB'Req]
    ext r
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_attach, true_and]
    tauto
  have hdisj : Disjoint (B'R c B γ hrow j)
      (B.attach.filter (fun r => r.1 ∈ accV c B γ hrow j)) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [hB'Req, Finset.mem_filter] at hr
    exact hr.2 (Finset.mem_filter.mp hr').2
  have hsplit : (B.attach.filter (fun r => r.1 ∈ accV c B γ hrow j)).card =
      (accV c B γ hrow j).card := by
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hr).2
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v, hacc hv⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hv⟩, rfl⟩
  have hacc_card : (accV c B γ hrow j).card =
      ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card := by
    rw [accV, sum_Bs_card c B γ hrow j]
    refine Finset.sum_congr rfl ?_
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact Bs_card_eq_Cs_card c B γ hrow hweight i' (by omega)
  rw [← Finset.card_attach (s := B), ← hunion, Finset.card_union_of_disjoint hdisj,
    hsplit, hacc_card]

/-- At most `inputSlack aux γ` vectors of a set `S` disjoint from `C₀` (when `γ = true`) have
weight `1`: every such vector is a unit vector, and a unit vector that is missing from `C₀` is a
unit vector of an inessential coordinate. -/
theorem card_filter_weight_one_le {S : Finset (Vec m)}
    (hS : γ = true → ∀ v ∈ S, weight (Finset.univ : Finset (Fin m)) v = 1 → v ∉ C0 c.aux γ B) :
    (S.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1)).card ≤
      inputSlack c.aux γ := by
  classical
  set E := S.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) with hE
  have hEmem : ∀ v : ↥E, weight (Finset.univ : Finset (Fin m)) (v : Vec m) = 1 := by
    intro v
    have hv : (v : Vec m) ∈ S.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) := by
      rw [← hE]; exact v.2
    exact (Finset.mem_filter.mp hv).2
  have hSE : ∀ v : ↥E, (v : Vec m) ∈ S := by
    intro v
    have hv : (v : Vec m) ∈ S.filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) := by
      rw [← hE]; exact v.2
    exact (Finset.mem_filter.mp hv).1
  let g : ↥E → Fin m := fun v =>
    Classical.choose (eq_basisVec_of_weight_univ_eq_one (hEmem v))
  have hg : ∀ v : ↥E, (v : Vec m) = basisVec (g v) := fun v =>
    Classical.choose_spec (eq_basisVec_of_weight_univ_eq_one (hEmem v))
  have hg_inj : Function.Injective g := by
    intro v v' hvv
    have hcoe : (v : Vec m) = (v' : Vec m) := by rw [hg v, hg v', hvv]
    exact Subtype.ext hcoe
  by_cases hγ : γ = true
  · have hgaux : ∀ v : ↥E, g v ∈ c.aux := by
      intro v
      by_contra hnot
      refine hS hγ _ (hSE v) (hEmem v) ?_
      rw [mem_C0]
      exact Or.inr ⟨hγ, by rw [mem_freeVecs]; exact ⟨g v, hnot, (hg v).symm⟩⟩
    let g' : ↥E → c.aux := fun v => ⟨g v, hgaux v⟩
    have hg'_inj : Function.Injective g' := by
      intro v v' hvv
      exact hg_inj (congrArg Subtype.val hvv)
    have hle : E.card ≤ c.aux.card := by
      have h := Fintype.card_le_of_injective g' hg'_inj
      rwa [Fintype.card_coe, Fintype.card_coe] at h
    have hval : inputSlack c.aux γ = c.aux.card := by
      unfold inputSlack; rw [if_pos hγ]
    rw [hval]
    exact hle
  · have hval : inputSlack c.aux γ = m := by
      unfold inputSlack
      rw [if_neg hγ]
    rw [hval]
    have hle := Fintype.card_le_of_injective g hg_inj
    rw [Fintype.card_coe, Fintype.card_fin] at hle
    exact hle

/-- The cardinality of the work set: `|W| = |B| + ∑_{i≤j} |Cᵢ|`. -/
theorem card_workSet (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    {k : ℕ} (hk : 2 ≤ k) (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) {j : ℕ} (hj : j ≤ k) :
    (workSet c B γ hrow j).card = B.card + ∑ i ∈ Finset.Icc 1 j, (Cs c B γ hrow i).card := by
  rw [workSet, Finset.card_union_of_disjoint (disjoint_B_biUnion_Cs c B γ hrow hk hind hj),
    sum_Cs_card c B γ hrow hind hj]

/-- **Point 3.1 of the proof of Theorem 2.**  If some level `Cⱼ`, `1 ≤ j ≤ k-1`, has at most
`(2/(2k+1))·n^{k/(k+1)}` elements, the counting bound gives the estimate of Theorem 2. -/
theorem case31 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    {k : ℕ} (hk : 2 ≤ k)
    (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) (hm : m ≤ B.card)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ k - 1)
    (hCj : ((Cs c B γ hrow j).card : ℝ) ≤
      (2 : ℝ) / (2 * (k : ℝ) + 1) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1))) :
    (B.card : ℝ) + ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) *
        (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) -
        (((inputSlack c.aux γ : ℕ)) : ℝ) ≤ (c.reducedComplexity : ℝ) := by
  classical
  have hjle : j ≤ k := by omega
  set N : ℝ := (B.card : ℝ) with hNdef
  set e : ℝ := (k : ℝ) / ((k : ℝ) + 1) with hedef
  set Ssum : ℝ := ∑ i ∈ Finset.Icc 1 j, ((Cs c B γ hrow i).card : ℝ) with hSsum
  set NB' : ℝ := ((B'R c B γ hrow j).card : ℝ) with hNB'def
  set Dj : ℝ := ((Cs c B γ hrow j).card : ℝ) with hDjdef
  set Em : ℝ := (((inputSlack c.aux γ : ℕ)) : ℝ) with hEmdef
  set cst : ℝ := (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) *
    (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) with hcstdef
  set D := Dset c B γ hrow j with hD
  set W := workSet c B γ hrow j with hW
  set T : ℕ := (D.image (proj c.aux)).card with hTdef
  have hNpos : (0 : ℝ) < N := by
    have h1 : 2 * k + 2 ≤ (C0 c.aux γ B).card := le_trans hind (ind_le_card _)
    have h2 : (C0 c.aux γ B).card ≤ B.card + m := C0_card_le c.aux γ B
    have h3 : 1 ≤ B.card := by omega
    rw [hNdef]
    exact_mod_cast h3
  have hWcard : (W.card : ℝ) = N + Ssum := by
    rw [hW, card_workSet c B γ hrow hk hind hjle, hNdef, hSsum]
    push_cast
    ring
  have hcap_sub : W ∩ D ⊆ Cs c B γ hrow j := by
    intro v hv
    rw [Finset.mem_inter] at hv
    obtain ⟨hvW, hvD⟩ := hv
    have hvD' : v ∈ Dset c B γ hrow j := hD ▸ hvD
    rw [hW, mem_workSet] at hvW
    rcases hvW with hvB | ⟨i, hi1, hij, hvi⟩
    · exact absurd (subset_C0_left hvB) (Dset_notMem_C0 c B γ hrow hj1 hvD')
    · by_cases hji : j = i
      · rw [hji]; exact hvi
      · exact absurd hvi (Dset_notMem_Cs c B γ hrow hvD' (by omega))
  have hs_inter : ((W ∩ D).card : ℝ) ≤ Dj := by
    rw [hDjdef]
    exact_mod_cast Finset.card_le_card hcap_sub
  have hUW : N + Ssum + (D.card : ℝ) - Dj ≤ ((W ∪ D).card : ℝ) := by
    have hcard : (W ∪ D).card + (W ∩ D).card = W.card + D.card :=
      Finset.card_union_add_card_inter W D
    have h1 : ((W ∪ D).card : ℝ) =
        (W.card : ℝ) + (D.card : ℝ) - ((W ∩ D).card : ℝ) := by
      have hcast : (((W ∪ D).card + (W ∩ D).card : ℕ) : ℝ) =
          ((W.card + D.card : ℕ) : ℝ) := by rw [hcard]
      push_cast at hcast ⊢
      linarith
    linarith
  have hEbound : (((W ∪ D).filter
      (fun v => weight (Finset.univ : Finset (Fin m)) v = 1)).card : ℝ) ≤ Em := by
    have h := card_filter_weight_one_le (c := c) (B := B) (γ := γ) (S := W ∪ D) (by
      intro hγ v hvS hv1
      rw [Finset.mem_union] at hvS
      rcases hvS with hvS | hvS
      · rw [hW, mem_workSet] at hvS
        rcases hvS with hvB | ⟨i, hi1, -, hvi⟩
        · exact absurd hv1 (hweight ⟨v, hvB⟩)
        · exact Cs_notMem_C0 c B γ hrow (by omega) hi1 hvi
      · exact Dset_notMem_C0 c B γ hrow hj1 (hD ▸ hvS))
    rw [hEmdef]
    exact_mod_cast h
  set X := (W ∪ D).filter (fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1) with hXdef
  set E := (W ∪ D).filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) with hEdef
  have hsplit : X.card + E.card = (W ∪ D).card := by
    rw [hXdef, hEdef]
    have hsum := Finset.card_filter_add_card_filter_not (s := W ∪ D)
      (p := fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1)
    have hnot : (W ∪ D).filter (fun v => ¬ weight (Finset.univ : Finset (Fin m)) v ≠ 1) =
        (W ∪ D).filter (fun v => weight (Finset.univ : Finset (Fin m)) v = 1) := by
      refine Finset.filter_congr ?_
      intro v _
      exact not_not
    rw [hnot] at hsum
    exact hsum
  have hEbound' : (E.card : ℝ) ≤ Em := by
    rw [hEdef]
    exact hEbound
  have hXge : N + Ssum + (D.card : ℝ) - Dj - Em ≤ (X.card : ℝ) := by
    have hcast : (X.card : ℝ) + (E.card : ℝ) = ((W ∪ D).card : ℝ) := by
      rw [← Nat.cast_add, hsplit]
    linarith
  have hstep : ∀ v : ↥X, ∃ kk : Fin c.L, c.y kk = v.1 := by
    intro v
    have hvX : (v : Vec m) ∈ (W ∪ D).filter
        (fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1) := by
      rw [← hXdef]; exact v.2
    rw [Finset.mem_filter, Finset.mem_union] at hvX
    obtain ⟨hvs, hv1⟩ := hvX
    rcases hvs with hvs | hvs
    · obtain ⟨kk, hk, -⟩ :=
        exists_step_of_mem_workSet c B γ hrow hB hvs hv1
      exact ⟨kk, hk⟩
    · have hvs' : (v : Vec m) ∈ Dset c B γ hrow j := hD ▸ hvs
      rcases (mem_Dset c B γ hrow).mp hvs' with ⟨b, hb, hb1⟩ | ⟨b, hb, hb2⟩
      · rcases step_or_basis_of_smd c (k := rowStep c B hrow b)
          (Or.inl (rfl : smd1 c (rowStep c B hrow b) = rowS1 c B hrow b)) with ⟨kk, hk⟩ | ⟨i, hi⟩
        · exact ⟨kk, hk.trans hb1⟩
        · refine absurd ?_ hv1
          rw [← hi.trans hb1]
          exact weight_univ_basisVec i
      · rcases step_or_basis_of_smd c (k := rowStep c B hrow b)
          (Or.inr (rfl : smd2 c (rowStep c B hrow b) = rowS2 c B hrow b)) with ⟨kk, hk⟩ | ⟨i, hi⟩
        · exact ⟨kk, hk.trans hb2⟩
        · refine absurd ?_ hv1
          rw [← hi.trans hb2]
          exact weight_univ_basisVec i
  let φ : ↥X → Fin c.L := fun v => Classical.choose (hstep v)
  have hφ : ∀ v : ↥X, c.y (φ v) = v.1 := fun v => Classical.choose_spec (hstep v)
  have hinj : Function.Injective φ := by
    intro v v' hvv
    refine Subtype.ext ?_
    rw [← hφ v, ← hφ v', hvv]
  have hXtype : ∀ v ∈ X, v ∉ D → proj c.aux v = 0 := by
    intro v hvX hvD
    have hvX' : v ∈ (W ∪ D).filter
        (fun v => weight (Finset.univ : Finset (Fin m)) v ≠ 1) := by
      rw [← hXdef]; exact hvX
    rw [Finset.mem_filter, Finset.mem_union] at hvX'
    obtain ⟨hvs, hv1⟩ := hvX'
    have hvw : v ∈ W := by
      rcases hvs with h | h
      · exact h
      · exact absurd h hvD
    obtain ⟨kk, hk, htw⟩ :=
      exists_step_of_mem_workSet c B γ hrow hB hvw hv1
    have hw : weight c.aux (c.y kk) = 0 := by
      rw [← typeWeight_eq_weight_y]
      exact htw
    rw [← hk]
    exact (weight_eq_zero_iff c.aux (c.y kk)).mp hw
  have hrc := reducedComplexity_ge_card_sub_image_proj c X D φ hφ hinj hXtype
  have hr : ((X.card : ℝ) - (T : ℝ)) ≤ (c.reducedComplexity : ℝ) := by
    have hsub : (D.image (proj c.aux)).card = T := hTdef.symm
    by_cases hle : (D.image (proj c.aux)).card ≤ X.card
    · rw [← hsub]
      have h1 : ((X.card - (D.image (proj c.aux)).card : ℕ) : ℝ) =
          (X.card : ℝ) - ((D.image (proj c.aux)).card : ℝ) := by
        rw [Nat.cast_sub hle]
      rw [← h1]
      exact_mod_cast hrc
    · have hlt : X.card < (D.image (proj c.aux)).card := Nat.lt_of_not_le hle
      rw [← hsub]
      have h2 : (X.card : ℝ) < ((D.image (proj c.aux)).card : ℝ) := by exact_mod_cast hlt
      have h3 : (0 : ℝ) ≤ (c.reducedComplexity : ℝ) := Nat.cast_nonneg _
      linarith
  have hDT : cst * NB' ≤ (D.card : ℝ) - (T : ℝ) := by
    have h := Dset_sum_per_type c B γ hrow hB hk hind j
    rw [← hD, ← hcstdef, ← hNB'def] at h
    have hTle : (D.image (proj c.aux)).card ≤ D.card := Finset.card_image_le
    rw [Nat.cast_sub hTle, ← hTdef] at h
    exact h
  have hNB'le : NB' ≤ N := by
    have h : (B'R c B γ hrow j).card ≤ B.card := by
      rw [B'R, ← Finset.card_attach (s := B)]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [hNB'def, hNdef]
    exact_mod_cast h
  have hcstle : cst ≤ 1 := by
    have h1 : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 3)]
      linarith
    have hB1 : (1 : ℝ) ≤ (B.card : ℝ) := by
      have h1 : 2 * k + 2 ≤ (C0 c.aux γ B).card := le_trans hind (ind_le_card _)
      have h2 : (C0 c.aux γ B).card ≤ B.card + m := C0_card_le c.aux γ B
      have h3 : 1 ≤ B.card := by omega
      exact_mod_cast h3
    have h2 : (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hB1 ?_
      have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    rw [hcstdef]
    calc (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1)))
        ≤ 1 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num)
      _ = 1 := by norm_num
  have hcstN : cst * N = (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * N ^ e := by
    have hpow : (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) * (B.card : ℝ) = (B.card : ℝ) ^ e := by
      have h1 : (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1)) + 1) =
          (B.card : ℝ) ^ (-(1 / ((k : ℝ) + 1))) * (B.card : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hNpos _ _
      rw [Real.rpow_one] at h1
      rw [← h1, hedef]
      congr 1
      field_simp
      ring
    rw [hcstdef, hNdef, mul_assoc, hpow]
  have hDjle : Dj ≤ 2 / (2 * (k : ℝ) + 1) * N ^ e := by
    rw [hDjdef, hNdef, hedef]
    exact hCj
  have hcoef : (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) ≤
      (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) - 2 / (2 * (k : ℝ) + 1) := by
    have hd : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) - 2 / (2 * (k : ℝ) + 1) -
        (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) =
        2 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 1)) := by
      field_simp
      ring
    have hpos : 0 < 2 / ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 1)) := by positivity
    linarith
  have hNe : 0 ≤ N ^ e := Real.rpow_nonneg (le_of_lt hNpos) _
  have hNsplit : N = NB' + Ssum := by
    have h := card_B_eq_B'R_add c B γ hrow hweight hk hind (j := j) hjle
    rw [hNdef, hNB'def, hSsum, h]
    push_cast
    ring
  have step4 : N + (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) * N ^ e - Em ≤
      2 * N - NB' + cst * NB' - Dj - Em := by
    have hNsub : 0 ≤ N - NB' := by linarith
    have h1 : cst * (N - NB') ≤ 1 * (N - NB') := mul_le_mul_of_nonneg_right hcstle hNsub
    have h1' : cst * N ≤ N - NB' + cst * NB' := by nlinarith [h1]
    have h2 : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * N ^ e ≤ N - NB' + cst * NB' := by
      rw [← hcstN]; exact h1'
    have h4 : (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) * N ^ e ≤
        (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) * N ^ e - 2 / (2 * (k : ℝ) + 1) * N ^ e := by
      have h := mul_le_mul_of_nonneg_right hcoef hNe
      nlinarith [h]
    linarith
  have step3 : 2 * N - NB' + cst * NB' - Dj - Em ≤ N + Ssum + cst * NB' - Dj - Em := by
    linarith
  have step2 : N + Ssum + cst * NB' - Dj - Em ≤ N + Ssum + (D.card : ℝ) - Dj - Em - (T : ℝ) := by
    linarith
  have step1 : N + Ssum + (D.card : ℝ) - Dj - Em - (T : ℝ) ≤ (X.card : ℝ) - (T : ℝ) := by
    linarith
  have hmain : N + (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) * N ^ e - Em ≤
      (c.reducedComplexity : ℝ) := by
    calc N + (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) * N ^ e - Em
        ≤ 2 * N - NB' + cst * NB' - Dj - Em := step4
      _ ≤ N + Ssum + cst * NB' - Dj - Em := step3
      _ ≤ N + Ssum + (D.card : ℝ) - Dj - Em - (T : ℝ) := step2
      _ ≤ (X.card : ℝ) - (T : ℝ) := step1
      _ ≤ (c.reducedComplexity : ℝ) := hr
  simpa [hNdef, hedef, hEmdef] using hmain

/-! ### Point 3.2: all levels `C₁, …, C_{k-1}` are large -/

/-- **Point 3.2 of the proof of Theorem 2.**  If every level `Cᵢ`, `1 ≤ i ≤ k-1`, has at least
`(2/(2k+1))·n^{k/(k+1)}` elements, the counting bound gives the estimate of Theorem 2. -/
theorem case32 (hrow : ∀ b : Row B, b.1 ∈ Set.range c.y)
    (hB : ∀ b : Row B, proj c.aux b.1 = 0)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    {k : ℕ} (hk : 2 ≤ k) (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B))
    (hm : m ≤ B.card)
    (hCi : ∀ i ∈ Finset.Icc 1 (k - 1),
      (2 : ℝ) / (2 * (k : ℝ) + 1) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤
        ((Cs c B γ hrow i).card : ℝ)) :
    (B.card : ℝ) + ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) *
        (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) -
        (((inputSlack c.aux γ : ℕ)) : ℝ) ≤ (c.reducedComplexity : ℝ) := by
  classical
  have hcount := count_bound c B γ hrow hB hweight hk hind (j := k - 1) (by omega)
  set N : ℝ := (B.card : ℝ) with hN
  set e : ℝ := (k : ℝ) / ((k : ℝ) + 1) with he
  set a : ℝ := (2 : ℝ) / (2 * (k : ℝ) + 1) * N ^ e with ha
  set S : ℕ := ∑ i ∈ Finset.Icc 1 (k - 1), (Cs c B γ hrow i).card with hS
  have hcount' : B.card + S - inputSlack c.aux γ ≤ c.reducedComplexity := by
    rw [hS]; exact hcount
  have hSsum : (S : ℝ) = ∑ i ∈ Finset.Icc 1 (k - 1), ((Cs c B γ hrow i).card : ℝ) := by
    rw [hS]; push_cast; rfl
  have hcard : (Finset.Icc 1 (k - 1)).card = k - 1 := by
    rw [Nat.card_Icc]; omega
  have hSreal : ((k - 1 : ℕ) : ℝ) * a ≤ (S : ℝ) := by
    rw [hSsum]
    have hconst : ∑ i ∈ Finset.Icc 1 (k - 1), a = ((k - 1 : ℕ) : ℝ) * a := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rw [← hconst]
    refine Finset.sum_le_sum ?_
    intro i hi
    have := hCi i hi
    rwa [ha] at this
  have hcoef : ((k - 1 : ℕ) : ℝ) * (2 / (2 * (k : ℝ) + 1)) =
      (2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1) := by
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      push_cast
      ring
    rw [hk1]
    field_simp
  have hSe : ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) * N ^ e ≤ (S : ℝ) := by
    have hsplit : ((k - 1 : ℕ) : ℝ) * a =
        ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) * N ^ e := by
      calc ((k - 1 : ℕ) : ℝ) * a
          = ((k - 1 : ℕ) : ℝ) * (2 / (2 * (k : ℝ) + 1)) * N ^ e := by rw [ha]; ring
        _ = ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) * N ^ e := by rw [hcoef]
    rw [← hsplit]; exact hSreal
  have hdle : inputSlack c.aux γ ≤ B.card + S := by
    have haux : c.aux.card ≤ m := by simpa using Finset.card_le_univ c.aux
    unfold inputSlack
    split_ifs with h <;> omega
  have hcountR : (B.card : ℝ) + (S : ℝ) - (((inputSlack c.aux γ : ℕ)) : ℝ) ≤
      (c.reducedComplexity : ℝ) := by
    have h1 : ((B.card + S - inputSlack c.aux γ : ℕ) : ℝ) ≤
        (c.reducedComplexity : ℝ) := by exact_mod_cast hcount'
    have h2 : ((B.card + S - inputSlack c.aux γ : ℕ) : ℝ) =
        (B.card : ℝ) + (S : ℝ) - (((inputSlack c.aux γ : ℕ)) : ℝ) := by
      rw [Nat.cast_sub hdle]; push_cast; ring
    rwa [h2] at h1
  linarith

/-! ### The setup of Theorem 2: the chain computes the rows of `B` -/

/-- A chain computes a finite set `B` of row vectors if every row of `B` is an output of the
chain: it is the value of a step and it does not depend on the inessential variables.  In the
degenerate cases allowed by `ExtChain.Computes` a row may also be a single input variable or the
zero row.  This is the standing assumption of Theorem 2 (the paper's "consider a minimal
extended scheme for `B`"), not an additional hypothesis on the rows: the hypotheses `0 ∉ B` and
"no row of `B` has weight `1`" rule out the two degenerate cases, see
`mem_range_y_of_computesVecs`. -/
def ExtChain.ComputesVecs (c : ExtChain m) (B : Finset (Vec m)) : Prop :=
  ∀ b ∈ B, proj c.aux b = 0 ∧
    b ∈ Set.range c.y ∪ Set.range (basisVec (n := m)) ∪ ({0} : Set (Vec m))

/-- In the setting of Theorem 2 every row of `B` is the value of a step of the chain: it cannot
be the zero row (the independence index of `C₀` is positive) and it cannot be a single input
variable (no row of `B` has weight `1`). -/
theorem mem_range_y_of_computesVecs {c : ExtChain m} {B : Finset (Vec m)}
    (hcomp : c.ComputesVecs B)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    (h0 : (0 : Vec m) ∉ B) : ∀ b : Row B, b.1 ∈ Set.range c.y := by
  rintro ⟨b, hb⟩
  obtain ⟨-, hmem⟩ := hcomp b hb
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hmem
  rcases hmem with (⟨k, hk⟩ | ⟨i, hi⟩) | hzero
  · exact ⟨k, hk⟩
  · exact absurd (hi ▸ weight_univ_basisVec i) (hweight ⟨b, hb⟩)
  · exact absurd (hzero ▸ hb) h0

/-- **Theorem 2 of [16]**, at the level of an extended chain `c` and a finite set `B` of row
vectors.

This is the estimate that the proof of Theorem 2 establishes for an extended scheme `c` that
computes `B` (`hcomp`, the standing setup of the theorem: every row of `B` is an output of type
`0` of the chain).  The only remaining hypotheses are those of the paper: `γ ∈ {0,1}`; no row of
`B` has weight `1` (`hweight`); the independence index of `C₀ = B ∪ γI_m` is at least
`2k+2 ≥ 6`; and `m ≤ |B|`.  Then
`|B| + (2k-2)/(2k+1) · |B|^(k/(k+1)) - (1-γ)m ≤ L*(c)`, where `L*(c)` denotes the reduced
complexity `c.reducedComplexity` of the chain.

The two properties that the paper obtains from the setup rather than assumes —
that every row of `B` is the value of a step, and that the rows of `B` (like the rows of `I_m`)
have type `0` — are derived from `hcomp` by `mem_range_y_of_computesVecs` and from the first
conjunct of `hcomp`, respectively. -/
theorem theorem2 (c : ExtChain m) (B : Finset (Vec m)) (γ : Bool)
    (hcomp : c.ComputesVecs B)
    (hweight : ∀ b : Row B, weight (Finset.univ : Finset (Fin m)) b.1 ≠ 1)
    {k : ℕ} (hk : 2 ≤ k)
    (hind : 2 * k + 2 ≤ ind (C0 c.aux γ B)) (hm : m ≤ B.card) :
    (B.card : ℝ) + ((2 * (k : ℝ) - 2) / (2 * (k : ℝ) + 1)) *
        (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) -
        (((inputSlack c.aux γ : ℕ)) : ℝ) ≤ (c.reducedComplexity : ℝ) := by
  classical
  have h0C0 : (0 : Vec m) ∉ C0 c.aux γ B :=
    zero_not_mem_of_ind_pos (le_trans (by omega : 1 ≤ 2 * k + 2) hind)
  have h0B : (0 : Vec m) ∉ B := fun h => h0C0 (subset_C0_left h)
  have hrow : ∀ b : Row B, b.1 ∈ Set.range c.y :=
    mem_range_y_of_computesVecs hcomp hweight h0B
  have hB : ∀ b : Row B, proj c.aux b.1 = 0 := fun b => (hcomp b b.2).1
  by_cases hcase : ∀ i ∈ Finset.Icc 1 (k - 1),
      (2 : ℝ) / (2 * (k : ℝ) + 1) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤
        ((Cs c B γ hrow i).card : ℝ)
  · exact case32 c B γ hrow hB hweight hk hind hm hcase
  · push Not at hcase
    obtain ⟨j, hjIcc, hjlt⟩ := hcase
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hjIcc
    exact case31 c B γ hrow hB hweight hk hind hm hj1 hj2 (le_of_lt hjlt)

end AchainsComplexityGF2
