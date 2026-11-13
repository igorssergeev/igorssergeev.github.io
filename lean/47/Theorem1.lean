/-
Theorem 1 of Sergeev, *Economical formulae for symmetric boolean functions*
(2025), Section 7: for `0 < t ≤ k` and `k + t ≤ n`,

`D_{B_M}(Ψⁿ_{k,t}) ≤ log_{√5−1}(k/t) + log₂(n/k) + 2 log₂ log₂(C(k−t) + C(k+t)) + O(1)`,

formalized as `theorem1` at the end of this file.

This single file contains the whole proof, in dependency order.  It depends
only on Mathlib: the few primitive notions of the introduction that the proof
uses are defined in the first section.

* `Primitives` — bases `BooleanBasis`, formulae `Formula` with their
  `complexity`, `depth`, `eval` and `rename`, and the counting function
  `onesCount` with its `support`; these declarations live in the namespace
  `SymmFormulae.Thm1`, which is opened for the rest of the file, so that
  `BasicNotions` can declare the same notions without a clash;
* `Basic`, `Partial` — the monotone basis `B_M = {∨,∧}`, partial monotone
  formulae, `partialDepth`, the partial threshold function `Ψⁿ_{k,t}`, duality,
  and the reduction of correctness to the two boundary layers;
* `OrPow`, `Delta` — powers of `∨` and the distributions `Δ_d` on formulae of
  depth `⌈log₂ m⌉ + 2d`;
* `Alpha`, `Prob` — the constant `α = (3−√5)/2`, weighted counting on seeds, and
  the recurrences (23), (27) for the error probabilities `p_d`, `q_d`;
* `Initial`, `Bounds` — the initial probabilities `p₀, q₀` with `δ₀ ≤ ε₀ ≤ 8δ₀`,
  the iterations `p ↦ p²(2−p)²` and `q ↦ q²(2−q²)`, and their convergence at
  rate `4α` (Lemma 4);
* `Eps`, `EpsBounds`, `Lemma4` — the sequences `p_d, q_d`, the lower bound
  `ε₀, δ₀ ≥ t/(64k)`, and the bound `s ≤ log_{4α}(k/t) + 1`;
* `Halving`, `Union` — the doubly-exponential phase (Lemma 5) and the union
  bound `partialDepth_psi_le`;
* `Theorem1` — the logarithmic bookkeeping and the dual case.
-/
import Mathlib

open scoped BigOperators

set_option linter.unusedVariables false

namespace SymmFormulae

/-! ## Primitives: bases, formulae and the counting function

The proof of Theorem 1 uses only formulae over a basis and the counting
function `σ = x₁ + ... + xₙ`.  They are defined here, in the private namespace
`Thm1`.  The namespace is opened right after the section, so the rest of the file 
uses the unqualified names.
-/

universe u

namespace Thm1

/-! ### Formulae, complexity and depth -/

/-- A finite boolean basis.

`Op` indexes the non-constant gates, `arity op` is the arity of the gate,
`interp op` is its boolean semantics, and `consts` is the set of constants that
may be used as leaves of formulae. -/
structure BooleanBasis where
  /-- The type of non-constant gate symbols. -/
  Op : Type u
  [fintype : Fintype Op]
  /-- The arity of a gate. -/
  arity : Op → ℕ
  /-- Non-constant gates have positive arity. -/
  arity_pos : ∀ op, 0 < arity op
  /-- The boolean function computed by a gate. -/
  interp : (op : Op) → (Fin (arity op) → Bool) → Bool
  /-- Constants available as leaves of formulae. -/
  consts : Set Bool

attribute [instance] BooleanBasis.fintype

/-- Formulae over the basis `B` in `n` boolean variables. -/
inductive Formula (B : BooleanBasis.{u}) (n : ℕ) : Type u where
  /-- A variable symbol; it has complexity `1` and depth `0`. -/
  | var (i : Fin n) : Formula B n
  /-- A basis constant; it has complexity and depth `0`. -/
  | const (b : Bool) (hb : b ∈ B.consts) : Formula B n
  /-- Application of a non-constant basis gate to a tuple of formulae. -/
  | app (op : B.Op) (args : Fin (B.arity op) → Formula B n) : Formula B n

namespace Formula

variable {B : BooleanBasis.{u}} {n : ℕ}

/-- `Φ_B(F)`, the complexity of a formula: the number of variable symbols. -/
def complexity : Formula B n → ℕ
  | var _ => 1
  | const _ _ => 0
  | app _ args => ∑ i, complexity (args i)

/-- `D_B(F)`, the depth of a formula: the length of the longest path from the
root to a leaf. -/
def depth : Formula B n → ℕ
  | var _ => 0
  | const _ _ => 0
  | app _ args => (Finset.univ.sup fun i => depth (args i)) + 1

/-- The boolean function implemented by a formula. -/
def eval : Formula B n → (Fin n → Bool) → Bool
  | var i, x => x i
  | const b _, _ => b
  | app op args, x => B.interp op fun i => eval (args i) x

@[simp] theorem complexity_var (i : Fin n) : (var i : Formula B n).complexity = 1 := rfl

@[simp] theorem complexity_const (b : Bool) (hb : b ∈ B.consts) :
    (const b hb : Formula B n).complexity = 0 := rfl

@[simp] theorem complexity_app (op : B.Op) (args : Fin (B.arity op) → Formula B n) :
    (app op args).complexity = ∑ i, (args i).complexity := rfl

@[simp] theorem depth_var (i : Fin n) : (var i : Formula B n).depth = 0 := rfl

@[simp] theorem depth_const (b : Bool) (hb : b ∈ B.consts) :
    (const b hb : Formula B n).depth = 0 := rfl

@[simp] theorem depth_app (op : B.Op) (args : Fin (B.arity op) → Formula B n) :
    (app op args).depth = (Finset.univ.sup fun i => (args i).depth) + 1 := rfl

@[simp] theorem eval_var (i : Fin n) (x : Fin n → Bool) :
    (var i : Formula B n).eval x = x i := rfl

@[simp] theorem eval_const (b : Bool) (hb : b ∈ B.consts) (x : Fin n → Bool) :
    (const b hb : Formula B n).eval x = b := rfl

@[simp] theorem eval_app (op : B.Op) (args : Fin (B.arity op) → Formula B n)
    (x : Fin n → Bool) :
    (app op args).eval x = B.interp op (fun i => (args i).eval x) := rfl


/-- Rename the variables of a formula along a map of indices. -/
def rename (f : Fin n → Fin m) : Formula B n → Formula B m
  | .var i => .var (f i)
  | .const b hb => .const b hb
  | .app op args => .app op fun i => (args i).rename f

theorem eval_rename (f : Fin n → Fin m) (F : Formula B n) (x : Fin m → Bool) :
    (F.rename f).eval x = F.eval (fun i => x (f i)) := by
  induction F with
  | var i => rfl
  | const b hb => rfl
  | app op args ih =>
      simp only [Formula.rename, Formula.eval_app]
      congr 1
      funext i
      exact ih i

end Formula

/-- The arithmetic sum `σ = x₁ + ... + xₙ` of the boolean variables, i.e. the
number of ones in `x`. -/
def onesCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i, if x i then 1 else 0

/-- The set of coordinates at which `x` is true. -/
def support {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

theorem onesCount_eq_card_support {n : ℕ} (x : Fin n → Bool) :
    onesCount x = (support x).card := by
  rw [onesCount, Finset.sum_boole]
  simp [support]

theorem onesCount_le {n : ℕ} (x : Fin n → Bool) : onesCount x ≤ n := by
  rw [onesCount_eq_card_support]
  simpa [support] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i = true)

end Thm1

open Thm1

/-! ## Module `Basic` -/

section

/-
The monotone basis `B_M = {∨, ∧}`, partial boolean functions, and the partial
threshold function `Ψⁿ_{k,t}` of Sergeev, *Economical formulae for symmetric
boolean functions* (2025), Section 3.

Theorem 1 bounds the formula depth `D_{B_M}(Ψⁿ_{k,t})`, i.e. the minimal depth of
a monotone formula that computes `Ψⁿ_{k,t}` on its domain of definition.
-/



/-! ### The monotone basis -/

/-- The two monotone connectives. -/
inductive MonOp : Type
  | or
  | and
  deriving DecidableEq, Repr

instance MonOp.instFintype : Fintype MonOp :=
  ⟨{MonOp.or, MonOp.and}, by intro x; cases x <;> simp⟩

namespace MonOp

/-- Both connectives are binary. -/
def arity : MonOp → ℕ
  | _ => 2

/-- Semantics of the monotone connectives. -/
def interp : (op : MonOp) → (Fin (arity op) → Bool) → Bool
  | or, v => v ⟨0, by decide⟩ || v ⟨1, by decide⟩
  | and, v => v ⟨0, by decide⟩ && v ⟨1, by decide⟩

end MonOp

/-- The monotone basis `B_M = {∨, ∧}`.  As in the proof of Theorem 1 the
constant `0` is available as a leaf: the distributions `Δ_d` use it to tune the
initial error probability.  Symmetrically the constant `1` is available, which
makes the dual reduction to `k > n/2` available as well. -/
def BM : BooleanBasis where
  Op := MonOp
  arity := MonOp.arity
  arity_pos := by intro op; cases op <;> decide
  interp := MonOp.interp
  consts := Set.univ

/-- Formulae over the monotone basis. -/
abbrev MFormula (n : ℕ) := Formula BM n

/-! ### The pointwise order on booleans -/

/-- The order `false < true` on booleans, stated as a proposition. -/
def ble (a b : Bool) : Prop := a = false ∨ b = true

theorem ble_of_imp {a b : Bool} (h : a = true → b = true) : ble a b := by
  cases a with
  | false => exact Or.inl rfl
  | true => exact Or.inr (h rfl)

theorem imp_of_ble {a b : Bool} (h : ble a b) : a = true → b = true := by
  rintro rfl
  rcases h with h | h
  · exact Bool.noConfusion h
  · exact h

theorem ble_refl (a : Bool) : ble a a := ble_of_imp id

theorem ble_trans {a b c : Bool} (hab : ble a b) (hbc : ble b c) : ble a c :=
  ble_of_imp fun h => imp_of_ble hbc (imp_of_ble hab h)

theorem ble_or {a a' b b' : Bool} (ha : ble a a') (hb : ble b b') :
    ble (a || b) (a' || b') := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [ble]

theorem ble_and {a a' b b' : Bool} (ha : ble a a') (hb : ble b b') :
    ble (a && b) (a' && b') := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [ble]

/-! ### Monotonicity of formula evaluation -/

theorem eval_mono {n : ℕ} (F : MFormula n) :
    ∀ {x y : Fin n → Bool}, (∀ i, ble (x i) (y i)) → ble (F.eval x) (F.eval y) := by
  induction F with
  | var i => intro x y h; exact h i
  | const b hb => intro x y h; exact ble_refl b
  | app op args ih =>
      intro x y h
      cases op with
      | or => exact ble_or (ih ⟨0, by decide⟩ h) (ih ⟨1, by decide⟩ h)
      | and => exact ble_and (ih ⟨0, by decide⟩ h) (ih ⟨1, by decide⟩ h)

/-- Monotonicity in the usable form. -/
theorem eval_mono_imp {n : ℕ} (F : MFormula n) {x y : Fin n → Bool}
    (h : ∀ i, x i = true → y i = true) (hx : F.eval x = true) : F.eval y = true :=
  imp_of_ble (eval_mono F (fun i => ble_of_imp (h i))) hx

theorem onesCount_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    onesCount x ≤ onesCount y := by
  rw [onesCount_eq_card_support, onesCount_eq_card_support]
  apply Finset.card_le_card
  intro i hi
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-! ### Partial boolean functions and partial depth -/

/-- A partial boolean function of `n` variables: a domain of definition and the
values taken on it. -/
structure PartialBool (n : ℕ) where
  /-- The domain of definition. -/
  dom : (Fin n → Bool) → Prop
  /-- The values taken on the domain. -/
  val : (Fin n → Bool) → Bool

/-- A formula computes a partial function on its domain. -/
def ComputesOn {n : ℕ} (F : MFormula n) (Ψ : PartialBool n) : Prop :=
  ∀ x, Ψ.dom x → F.eval x = Ψ.val x

/-- `D_{B_M}(Ψ)`, the minimal depth of a monotone formula computing `Ψ` on its
domain. -/
noncomputable def partialDepth {n : ℕ} (Ψ : PartialBool n) : ℕ :=
  sInf {d : ℕ | ∃ F : MFormula n, F.depth = d ∧ ComputesOn F Ψ}

theorem partialDepth_le {n : ℕ} {Ψ : PartialBool n} {F : MFormula n}
    (h : ComputesOn F Ψ) : partialDepth Ψ ≤ F.depth :=
  Nat.sInf_le ⟨F, rfl, h⟩

/-! ### The partial threshold function -/

/-- `Ψⁿ_{k,t}`: the partial threshold function with threshold `k` and
uncertainty radius `t`.  It takes the value `1` where `σ ≥ k + t` and `0` where
`σ ≤ k - t`, and is undefined in between. -/
def psi (n k t : ℕ) : PartialBool n where
  dom x := k + t ≤ onesCount x ∨ onesCount x + t ≤ k
  val x := decide (k + t ≤ onesCount x)

theorem psi_dom_one {n k t : ℕ} {x : Fin n → Bool} (h : k + t ≤ onesCount x) :
    (psi n k t).dom x := Or.inl h

theorem psi_dom_zero {n k t : ℕ} {x : Fin n → Bool} (h : onesCount x + t ≤ k) :
    (psi n k t).dom x := Or.inr h

theorem psi_val_one {n k t : ℕ} {x : Fin n → Bool} (h : k + t ≤ onesCount x) :
    (psi n k t).val x = true := by
  simp [psi, h]

theorem psi_val_zero {n k t : ℕ} (ht : 0 < t) {x : Fin n → Bool}
    (h : onesCount x + t ≤ k) : (psi n k t).val x = false := by
  have h' : ¬ (k + t ≤ onesCount x) := by omega
  simp [psi, h']



end

/-! ## Module `Partial` -/

section

/-
Duality of monotone formulae, duality of the partial threshold function, and the
reduction of correctness on the whole domain of `Ψⁿ_{k,t}` to correctness on the
two boundary layers (used in the proof of Theorem 1, Section 7).
-/



/-! ### Duality -/

/-- Swap the two monotone connectives. -/
def dualOp : MonOp → MonOp
  | MonOp.or => MonOp.and
  | MonOp.and => MonOp.or

/-- The dual of a monotone formula: swap `∨` and `∧`, negate constants. -/
def dual {n : ℕ} : MFormula n → MFormula n
  | Formula.var i => Formula.var i
  | Formula.const b _ => Formula.const (!b) (Set.mem_univ _)
  | Formula.app op args => Formula.app (dualOp op) fun i => dual (args i)

theorem interp_congr {op : MonOp} {v w : Fin (MonOp.arity op) → Bool}
    (h : ∀ i, v i = w i) : MonOp.interp op v = MonOp.interp op w := by
  cases op <;> simp only [MonOp.interp] <;> congr 1 <;> exact h _

theorem interp_dual (op : MonOp) (v : Fin (MonOp.arity op) → Bool) :
    MonOp.interp (dualOp op) v = !(MonOp.interp op fun i => !(v i)) := by
  cases op <;>
    simp only [MonOp.interp, dualOp, Bool.not_or, Bool.not_and, Bool.not_not] <;>
    congr 1

/-- Evaluation of a dual formula: `dual` commutes with complementing inputs. -/
theorem eval_dual {n : ℕ} (F : MFormula n) (x : Fin n → Bool) :
    (dual F).eval x = !(F.eval fun i => !(x i)) := by
  induction F with
  | var i => simp [dual]
  | const b hb => rfl
  | app op args ih =>
      cases op with
      | or =>
          simp only [dual, dualOp, Formula.eval, BM, MonOp.interp, Bool.not_or]
          congr 1 <;> exact ih _
      | and =>
          simp only [dual, dualOp, Formula.eval, BM, MonOp.interp, Bool.not_and]
          congr 1 <;> exact ih _

theorem depth_dual {n : ℕ} (F : MFormula n) : (dual F).depth = F.depth := by
  induction F with
  | var i => simp [dual]
  | const b hb => rfl
  | app op args ih =>
      cases op with
      | or =>
          simp only [dual, dualOp, Formula.depth]
          congr 1
          exact Finset.sup_congr rfl fun i _ => ih i
      | and =>
          simp only [dual, dualOp, Formula.depth]
          congr 1
          exact Finset.sup_congr rfl fun i _ => ih i

theorem complexity_dual {n : ℕ} (F : MFormula n) : (dual F).complexity = F.complexity := by
  induction F with
  | var i => simp [dual]
  | const b hb => rfl
  | app op args ih =>
      cases op with
      | or =>
          simp only [dual, dualOp, Formula.complexity]
          exact Finset.sum_congr rfl fun i _ => ih i
      | and =>
          simp only [dual, dualOp, Formula.complexity]
          exact Finset.sum_congr rfl fun i _ => ih i

/-! ### Complements of boolean vectors -/

theorem support_not {n : ℕ} (x : Fin n → Bool) :
    support (fun i => !(x i)) = (support x)ᶜ := by
  ext i
  simp [support]

theorem onesCount_not {n : ℕ} (x : Fin n → Bool) :
    onesCount (fun i => !(x i)) = n - onesCount x := by
  rw [onesCount_eq_card_support, onesCount_eq_card_support, support_not, Finset.card_compl]
  simp

/-- `Ψⁿ_{k,t}` is the dual of `Ψⁿ_{n-k,t}`: negating all variables exchanges the
two boundary layers. -/
theorem computes_dual {n k t : ℕ} (ht : 0 < t) (hkn : k + t ≤ n)
    {F : MFormula n} (h : ComputesOn F (psi n (n - k) t)) :
    ComputesOn (dual F) (psi n k t) := by
  intro x hx
  rw [eval_dual F x]
  have hz : onesCount (fun i => !(x i)) = n - onesCount x := onesCount_not x
  rcases hx with hx | hx
  · have hval : (psi n (n - k) t).val (fun i => !(x i)) = false := by
      have hlt : ¬ ((n - k) + t ≤ onesCount fun i => !(x i)) := by
        rw [hz]; omega
      simp [psi, hlt]
    rw [h _ (psi_dom_zero (by rw [hz]; omega)), hval]
    simp [psi_val_one hx]
  · have hval : (psi n (n - k) t).val (fun i => !(x i)) = true := by
      have hle : (n - k) + t ≤ onesCount fun i => !(x i) := by
        rw [hz]; omega
      simp [psi, hle]
    rw [h _ (psi_dom_one (by rw [hz]; omega)), hval]
    simp [psi_val_zero ht hx]

/-! ### Vectors of a prescribed weight -/

theorem exists_le_of_le_onesCount {n : ℕ} {x : Fin n → Bool} {w : ℕ}
    (h : w ≤ onesCount x) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ onesCount y = w := by
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq (s := support x) (n := w)
    (by simpa [onesCount_eq_card_support] using h)
  refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
  · intro i hi
    have hiS : i ∈ S := by simpa using hi
    have : i ∈ support x := hS hiS
    simpa [support] using this
  · have hs : support (fun i => decide (i ∈ S)) = S := by ext i; simp [support]
    rw [onesCount_eq_card_support, hs, hcard]

theorem exists_ge_of_le_onesCount {n : ℕ} {x : Fin n → Bool} {w : ℕ}
    (h : onesCount x ≤ w) (hw : w ≤ n) :
    ∃ y : Fin n → Bool, (∀ i, x i = true → y i = true) ∧ onesCount y = w := by
  obtain ⟨T, hT, -, hcard⟩ := Finset.exists_subsuperset_card_eq
    (s := support x) (t := Finset.univ) (Finset.subset_univ _)
    (by simpa [onesCount_eq_card_support] using h) (by simpa using hw)
  refine ⟨fun i => decide (i ∈ T), ?_, ?_⟩
  · intro i hi
    have hiS : i ∈ support x := by simpa [support] using hi
    have : i ∈ T := hT hiS
    simpa using this
  · have hs : support (fun i => decide (i ∈ T)) = T := by ext i; simp [support]
    rw [onesCount_eq_card_support, hs, hcard]

/-! ### Correctness on the boundary implies correctness on the domain -/

/-- If a monotone formula is correct on the two boundary layers `σ = k + t` and
`σ = k - t`, then it computes `Ψⁿ_{k,t}` on its whole domain. -/
theorem computes_of_boundary {n k t : ℕ} (ht : 0 < t) (_hk : t ≤ k) (hkn : k + t ≤ n)
    {F : MFormula n}
    (h₁ : ∀ y : Fin n → Bool, onesCount y = k + t → F.eval y = true)
    (h₀ : ∀ y : Fin n → Bool, onesCount y = k - t → F.eval y = false) :
    ComputesOn F (psi n k t) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨y, hyle, hy⟩ := exists_le_of_le_onesCount (x := x) (w := k + t) hx
    rw [psi_val_one hx]
    exact eval_mono_imp F hyle (h₁ y hy)
  · obtain ⟨y, hyle, hy⟩ := exists_ge_of_le_onesCount (x := x) (w := k - t)
      (by omega) (by omega)
    rw [psi_val_zero ht hx]
    by_contra hc
    have hx1 : F.eval x = true := by cases hv : F.eval x <;> simp_all
    have : F.eval y = true := eval_mono_imp F hyle hx1
    rw [h₀ y hy] at this
    exact Bool.noConfusion this

/-! ### The boundary layers -/

/-- The two boundary layers of `Ψⁿ_{k,t}` as a finite set of inputs. -/
noncomputable def boundary (n k t : ℕ) : Finset (Fin n → Bool) :=
  (Finset.univ.filter fun x => onesCount x = k + t) ∪
    (Finset.univ.filter fun x => onesCount x = k - t)

theorem mem_boundary {n k t : ℕ} {x : Fin n → Bool} :
    x ∈ boundary n k t ↔ onesCount x = k + t ∨ onesCount x = k - t := by
  simp [boundary]

theorem card_weight {n w : ℕ} (_h : w ≤ n) :
    (Finset.univ.filter fun x : Fin n → Bool => onesCount x = w).card = Nat.choose n w := by
  classical
  have h1 : (Finset.univ.filter fun x : Fin n → Bool => onesCount x = w).card
      = Fintype.card {x : Fin n → Bool // onesCount x = w} := by
    rw [Fintype.card_subtype]
  have h2 : Nat.choose n w = Fintype.card {S : Finset (Fin n) // S.card = w} := by
    rw [Fintype.card_finset_len]
    simp
  rw [h1, h2]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x => ⟨support x.val, ?_⟩
      invFun := fun S => ⟨fun i => decide (i ∈ S.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← onesCount_eq_card_support]
    exact x.2
  · have hs : support (fun i => decide (i ∈ S.val)) = S.val := by
      ext i
      simp [support]
    rw [onesCount_eq_card_support, hs]
    exact S.2
  · intro x
    apply Subtype.ext
    funext i
    simp [support]
  · intro S
    apply Subtype.ext
    ext i
    simp [support]

theorem card_boundary {n k t : ℕ} (ht : 0 < t) (hkn : k + t ≤ n) (hkt : k - t ≤ n) :
    (boundary n k t).card = Nat.choose n (k + t) + Nat.choose n (k - t) := by
  classical
  rw [boundary, Finset.card_union_of_disjoint]
  · rw [card_weight hkn, card_weight hkt]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    omega



end

/-! ## Module `OrPow` -/

section

/-
Balanced disjunctions of formulae over the monotone basis, used to realise the
distribution `Δ₀` of Section 7 of Sergeev, *Economical formulae for symmetric
boolean functions* (2025).
-/

set_option linter.unusedVariables false



/-! ### Binary connectives -/

/-- The formula `a ∨ b`. -/
def mkOr {n : ℕ} (a b : MFormula n) : MFormula n := Formula.app MonOp.or ![a, b]

/-- The formula `a ∧ b`. -/
def mkAnd {n : ℕ} (a b : MFormula n) : MFormula n := Formula.app MonOp.and ![a, b]

theorem mkOr_eval {n : ℕ} (a b : MFormula n) (x : Fin n → Bool) :
    (mkOr a b).eval x = (a.eval x || b.eval x) := rfl

theorem mkAnd_eval {n : ℕ} (a b : MFormula n) (x : Fin n → Bool) :
    (mkAnd a b).eval x = (a.eval x && b.eval x) := rfl

theorem mkOr_true {n : ℕ} {a b : MFormula n} {x : Fin n → Bool}
    (h : a.eval x = true) : (mkOr a b).eval x = true := by
  rw [mkOr_eval, h]; simp

theorem mkOr_true' {n : ℕ} {a b : MFormula n} {x : Fin n → Bool}
    (h : b.eval x = true) : (mkOr a b).eval x = true := by
  rw [mkOr_eval, h]; simp

theorem mkAnd_true {n : ℕ} {a b : MFormula n} {x : Fin n → Bool}
    (ha : a.eval x = true) (hb : b.eval x = true) : (mkAnd a b).eval x = true := by
  rw [mkAnd_eval, ha, hb]; simp

theorem mkOr_depth_le {n : ℕ} (a b : MFormula n) :
    (mkOr a b).depth ≤ max a.depth b.depth + 1 := by
  have h : (mkOr a b).depth
      = Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i)) + 1 := rfl
  rw [h]
  have hsup : Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i))
      ≤ max a.depth b.depth := by
    refine Finset.sup_le ?_
    intro i _
    fin_cases i
    · simp
    · simp
  omega

theorem mkAnd_depth_le {n : ℕ} (a b : MFormula n) :
    (mkAnd a b).depth ≤ max a.depth b.depth + 1 := by
  have h : (mkAnd a b).depth
      = Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i)) + 1 := rfl
  rw [h]
  have hsup : Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i))
      ≤ max a.depth b.depth := by
    refine Finset.sup_le ?_
    intro i _
    fin_cases i
    · simp
    · simp
  omega

/-! ### Balanced disjunctions -/

/-- The inclusion of `Fin (2 ^ k)` into the first half of `Fin (2 ^ (k + 1))`. -/
def loFin (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨i.val, by
    have h := i.isLt
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    omega⟩

/-- The inclusion of `Fin (2 ^ k)` into the second half of `Fin (2 ^ (k + 1))`. -/
def hiFin (k : ℕ) (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 ^ k + i.val, by
    have h := i.isLt
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
    omega⟩

theorem loFin_val (k : ℕ) (i : Fin (2 ^ k)) : (loFin k i).val = i.val := rfl

theorem hiFin_val (k : ℕ) (i : Fin (2 ^ k)) : (hiFin k i).val = 2 ^ k + i.val := rfl

/-- The disjunction of the `2 ^ k` formulae `f 0, ..., f (2 ^ k - 1)`, computed
by a balanced binary tree of depth `k`. -/
def orPow {n : ℕ} : (k : ℕ) → (Fin (2 ^ k) → MFormula n) → MFormula n
  | 0, f => f 0
  | k + 1, f => mkOr (orPow k fun i => f (loFin k i)) (orPow k fun i => f (hiFin k i))

theorem orPow_depth_le {n : ℕ} (k : ℕ) (f : Fin (2 ^ k) → MFormula n) :
    (orPow k f).depth ≤ k + Finset.univ.sup (fun i => (f i).depth) := by
  induction k with
  | zero =>
      show (f 0).depth ≤ 0 + Finset.univ.sup (fun i : Fin (2 ^ 0) => (f i).depth)
      have h : (f 0).depth ≤ Finset.univ.sup (fun i : Fin (2 ^ 0) => (f i).depth) :=
        Finset.le_sup (s := (Finset.univ : Finset (Fin (2 ^ 0))))
          (f := fun i : Fin (2 ^ 0) => (f i).depth) (Finset.mem_univ (0 : Fin (2 ^ 0)))
      omega
  | succ k ih =>
      have h1 := ih (fun i => f (loFin k i))
      have h2 := ih (fun i => f (hiFin k i))
      have hs1 : Finset.univ.sup (fun i : Fin (2 ^ k) => (f (loFin k i)).depth)
          ≤ Finset.univ.sup (fun i : Fin (2 ^ (k + 1)) => (f i).depth) := by
        refine Finset.sup_le ?_
        intro i _
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (2 ^ (k + 1)))))
          (f := fun i : Fin (2 ^ (k + 1)) => (f i).depth) (Finset.mem_univ (loFin k i))
      have hs2 : Finset.univ.sup (fun i : Fin (2 ^ k) => (f (hiFin k i)).depth)
          ≤ Finset.univ.sup (fun i : Fin (2 ^ (k + 1)) => (f i).depth) := by
        refine Finset.sup_le ?_
        intro i _
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (2 ^ (k + 1)))))
          (f := fun i : Fin (2 ^ (k + 1)) => (f i).depth) (Finset.mem_univ (hiFin k i))
      have h3 : (orPow (k + 1) f).depth
          = (mkOr (orPow k fun i => f (loFin k i))
              (orPow k fun i => f (hiFin k i))).depth := rfl
      rw [h3]
      have h4 := mkOr_depth_le (orPow k fun i => f (loFin k i))
        (orPow k fun i => f (hiFin k i))
      have : max (orPow k fun i => f (loFin k i)).depth
            (orPow k fun i => f (hiFin k i)).depth
          ≤ k + Finset.univ.sup (fun i : Fin (2 ^ (k + 1)) => (f i).depth) := by
        apply max_le <;> omega
      omega

theorem orPow_eval {n : ℕ} :
    ∀ (k : ℕ) (f : Fin (2 ^ k) → MFormula n) (x : Fin n → Bool),
      (orPow k f).eval x = true ↔ ∃ i : Fin (2 ^ k), (f i).eval x = true
  | 0, f, x => by
    constructor
    · intro h; exact ⟨0, h⟩
    · rintro ⟨i, hi⟩
      have : i = 0 := Fin.ext (by have := i.isLt; omega)
      rwa [this] at hi
  | k + 1, f, x => by
    show (mkOr (orPow k fun i => f (loFin k i)) (orPow k fun i => f (hiFin k i))).eval x
        = true ↔ _
    rw [mkOr_eval, Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · obtain ⟨i, hi⟩ := (orPow_eval k _ x).mp h
        exact ⟨loFin k i, hi⟩
      · obtain ⟨i, hi⟩ := (orPow_eval k _ x).mp h
        exact ⟨hiFin k i, hi⟩
    · rintro ⟨j, hj⟩
      by_cases hlt : j.val < 2 ^ k
      · left
        refine (orPow_eval k (fun i => f (loFin k i)) x).mpr ⟨⟨j.val, hlt⟩, ?_⟩
        simpa [loFin] using hj
      · right
        have hjlt := j.isLt
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
        have hge : 2 ^ k ≤ j.val := by omega
        refine (orPow_eval k (fun i => f (hiFin k i)) x).mpr ⟨⟨j.val - 2 ^ k, by omega⟩, ?_⟩
        have hval : (hiFin k ⟨j.val - 2 ^ k, by omega⟩ : Fin (2 ^ (k + 1))).val = j.val := by
          rw [hiFin_val]
          simp
          omega
        have heq : (hiFin k ⟨j.val - 2 ^ k, by omega⟩ : Fin (2 ^ (k + 1))) = j := Fin.ext hval
        rw [heq]
        exact hj

/-! ### Disjunctions of `m` formulae -/

/-- The disjunction of the formulae `f 0, ..., f (m - 1)`, computed by a
balanced tree of depth `k`, where `m ≤ 2 ^ k`.  Unused slots contribute the
constant `false`. -/
def orFin {n : ℕ} (m : ℕ) (f : Fin m → MFormula n) (k : ℕ) (hk : m ≤ 2 ^ k) :
    MFormula n :=
  orPow k fun i => if h : i.val < m then f ⟨i.val, h⟩ else Formula.const false (Set.mem_univ _)

theorem orFin_depth_le {n m : ℕ} (f : Fin m → MFormula n) {k : ℕ} (hk : m ≤ 2 ^ k) :
    (orFin m f k hk).depth ≤ k + Finset.univ.sup (fun i => (f i).depth) := by
  have h := orPow_depth_le (n := n) k (fun i : Fin (2 ^ k) =>
    if h : i.val < m then f ⟨i.val, h⟩ else Formula.const false (Set.mem_univ _))
  have hsup : Finset.univ.sup (fun i : Fin (2 ^ k) =>
        (if h : i.val < m then f ⟨i.val, h⟩ else Formula.const false (Set.mem_univ _)).depth)
      ≤ Finset.univ.sup (fun i : Fin m => (f i).depth) := by
    refine Finset.sup_le ?_
    intro i _
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      have hmem : (⟨i.val, hi⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) :=
        Finset.mem_univ _
      exact Finset.le_sup (f := fun j : Fin m => (f j).depth) hmem
    · rw [dif_neg hi]
      exact Nat.zero_le _
  exact le_trans h (by omega)

theorem orFin_eval {n m : ℕ} (f : Fin m → MFormula n) {k : ℕ} (hk : m ≤ 2 ^ k)
    (x : Fin n → Bool) :
    (orFin m f k hk).eval x = true ↔ ∃ i : Fin m, (f i).eval x = true := by
  have key : ∀ i : Fin (2 ^ k),
      (if h : i.val < m then f ⟨i.val, h⟩ else Formula.const false (Set.mem_univ _)).eval x
          = true
        ↔ ∃ h : i.val < m, (f ⟨i.val, h⟩).eval x = true := by
    intro i
    by_cases hi : i.val < m
    · rw [dif_pos hi]
      exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
    · rw [dif_neg hi]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd h.1 hi⟩
  rw [orFin, orPow_eval]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨hjm, hjt⟩ := (key j).mp hj
    exact ⟨⟨j.val, hjm⟩, hjt⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨i.val, by omega⟩, (key ⟨i.val, by omega⟩).mpr ⟨i.isLt, hi⟩⟩



end

/-! ## Module `Delta` -/

section

/-
The distributions `Δ_d` on monotone formulae of Section 7 of Sergeev,
*Economical formulae for symmetric boolean functions* (2025).

`Δ₀` consists of formulae `x_{i₁} ∨ ... ∨ x_{i_m}` (each index chosen
equiprobably from `{1,...,n}`, repetitions allowed) together with the constant
formula `0`; a `Δ_{d+1}` formula is `(G₁ ∨ G₂) ∧ (G₃ ∨ G₄)` with four
independent `Δ_d` subformulae.  Formulae of `Δ_d` have depth
`⌈log₂ m⌉ + 2d`.
-/

set_option linter.unusedVariables false



/-! ### Seeds -/

/-- A seed for `Δ₀`: `none` is the constant formula `0`, and `some f` is the
disjunction of the variables `f 0, ..., f (m-1)`. -/
abbrev Seed0 (n m : ℕ) : Type := Option (Fin m → Fin n)

/-- Seeds for `Δ_d`: a `Δ_{d+1}` formula is `(G₁ ∨ G₂) ∧ (G₃ ∨ G₄)` with four
independent `Δ_d` subformulae, grouped as two pairs. -/
def Seed (n m : ℕ) : ℕ → Type
  | 0 => Seed0 n m
  | d + 1 => (Seed n m d × Seed n m d) × (Seed n m d × Seed n m d)

instance instFintypeSeed (n m : ℕ) : ∀ d : ℕ, Fintype (Seed n m d)
  | 0 => inferInstanceAs (Fintype (Seed0 n m))
  | d + 1 =>
      haveI := instFintypeSeed n m d
      inferInstanceAs
        (Fintype ((Seed n m d × Seed n m d) × (Seed n m d × Seed n m d)))

/-! ### The formulae of `Δ_d` -/

/-- The formula of `Δ₀` determined by a seed. -/
noncomputable def delta0Form (n m : ℕ) : Seed0 n m → MFormula n
  | Option.none => Formula.const false (Set.mem_univ _)
  | Option.some f =>
      orFin m (fun i => Formula.var (f i)) (Nat.clog 2 m) (Nat.le_pow_clog (by norm_num) m)

/-- The formula of `Δ_d` determined by a seed. -/
noncomputable def deltaForm (n m : ℕ) : (d : ℕ) → Seed n m d → MFormula n
  | 0, s => delta0Form n m s
  | d + 1, s =>
      mkAnd (mkOr (deltaForm n m d s.1.1) (deltaForm n m d s.1.2))
        (mkOr (deltaForm n m d s.2.1) (deltaForm n m d s.2.2))

theorem deltaForm_succ_eval {n m d : ℕ} (s : Seed n m (d + 1)) (x : Fin n → Bool) :
    (deltaForm n m (d + 1) s).eval x
      = (((deltaForm n m d s.1.1).eval x || (deltaForm n m d s.1.2).eval x)
          && ((deltaForm n m d s.2.1).eval x || (deltaForm n m d s.2.2).eval x)) := rfl

theorem delta0Form_some_eval {n m : ℕ} (f : Fin m → Fin n) (x : Fin n → Bool) :
    (delta0Form n m (Option.some f)).eval x = true ↔ ∃ i : Fin m, x (f i) = true := by
  rw [delta0Form, orFin_eval]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩

theorem delta0Form_none_eval {n m : ℕ} (x : Fin n → Bool) :
    (delta0Form n m Option.none).eval x = false := rfl

/-! ### Depths -/

theorem delta0Form_depth_le {n m : ℕ} (s : Seed0 n m) :
    (delta0Form n m s).depth ≤ Nat.clog 2 m := by
  cases s with
  | none =>
      show (Formula.const false _).depth ≤ Nat.clog 2 m
      exact Nat.zero_le _
  | some f =>
      have h := orFin_depth_le (fun i => Formula.var (f i)) (Nat.le_pow_clog (by norm_num) m)
      have hzero : Finset.univ.sup (fun i : Fin m => (Formula.var (f i) : MFormula n).depth) = 0 := by
        refine le_antisymm ?_ (Nat.zero_le _)
        refine Finset.sup_le ?_
        intro i _
        exact Nat.zero_le _
      rw [hzero] at h
      simpa [delta0Form] using h

theorem deltaForm_depth_le {n m : ℕ} (d : ℕ) (s : Seed n m d) :
    (deltaForm n m d s).depth ≤ Nat.clog 2 m + 2 * d := by
  induction d with
  | zero =>
      simpa [deltaForm] using delta0Form_depth_le (n := n) (m := m) s
  | succ d ih =>
      show (mkAnd (mkOr (deltaForm n m d s.1.1) (deltaForm n m d s.1.2))
        (mkOr (deltaForm n m d s.2.1) (deltaForm n m d s.2.2))).depth
          ≤ Nat.clog 2 m + 2 * (d + 1)
      have h1 : (deltaForm n m d s.1.1).depth ≤ Nat.clog 2 m + 2 * d := ih s.1.1
      have h2 : (deltaForm n m d s.1.2).depth ≤ Nat.clog 2 m + 2 * d := ih s.1.2
      have h3 : (deltaForm n m d s.2.1).depth ≤ Nat.clog 2 m + 2 * d := ih s.2.1
      have h4 : (deltaForm n m d s.2.2).depth ≤ Nat.clog 2 m + 2 * d := ih s.2.2
      have hor1 := mkOr_depth_le (deltaForm n m d s.1.1) (deltaForm n m d s.1.2)
      have hor2 := mkOr_depth_le (deltaForm n m d s.2.1) (deltaForm n m d s.2.2)
      have hand := mkAnd_depth_le (mkOr (deltaForm n m d s.1.1) (deltaForm n m d s.1.2))
        (mkOr (deltaForm n m d s.2.1) (deltaForm n m d s.2.2))
      omega



end

/-! ## Module `Alpha` -/

section

/-
The constant `α = (3 - √5)/2` of Section 7 of Sergeev, *Economical formulae
for symmetric boolean functions* (2025): the fixed point of
`p ↦ (1 - (1-p)^2)^2` lying in `(0,1)`.
-/



/-- `α = (3 - √5)/2 ≈ 0.382`. -/
noncomputable def alpha : ℝ := (3 - Real.sqrt 5) / 2

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem two_lt_sqrt5 : 2 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

theorem sqrt5_lt_three : Real.sqrt 5 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem sqrt5_lt_five_halves : Real.sqrt 5 < 5 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem alpha_pos : 0 < alpha := by
  unfold alpha
  have := sqrt5_lt_three
  linarith

theorem alpha_lt_half : alpha < 1 / 2 := by
  unfold alpha
  have := two_lt_sqrt5
  linarith

theorem alpha_lt_one : alpha < 1 := by
  have := alpha_lt_half
  linarith

theorem alpha_nonneg : 0 ≤ alpha := le_of_lt alpha_pos

/-- `(1 - α)^2 = α`. -/
theorem one_sub_alpha_sq : (1 - alpha) ^ 2 = alpha := by
  unfold alpha
  have h := sqrt5_sq
  nlinarith

/-- `α^2 = 3α - 1`. -/
theorem alpha_sq : alpha ^ 2 = 3 * alpha - 1 := by
  have h := one_sub_alpha_sq
  nlinarith

/-- `4α = 6 - 2√5`. -/
theorem four_alpha : 4 * alpha = 6 - 2 * Real.sqrt 5 := by
  unfold alpha; ring

/-- `4α = (√5 - 1)^2`. -/
theorem four_alpha_eq_sq : 4 * alpha = (Real.sqrt 5 - 1) ^ 2 := by
  rw [four_alpha]; nlinarith [sqrt5_sq]

theorem one_lt_four_alpha : 1 < 4 * alpha := by
  rw [four_alpha]
  have := sqrt5_lt_five_halves
  linarith

theorem four_alpha_lt_two : 4 * alpha < 2 := by
  rw [four_alpha]
  have := two_lt_sqrt5
  linarith

theorem four_alpha_pos : 0 < 4 * alpha := by linarith [one_lt_four_alpha]

/-- `α(2 - α)^2 = 1`, so that `α` is a fixed point of `p ↦ (1-(1-p)^2)^2`. -/
theorem alpha_mul_sq : alpha * (2 - alpha) ^ 2 = 1 := by
  have h := one_sub_alpha_sq
  have h2 : (2 - alpha) = 1 + (1 - alpha) := by ring
  rw [h2]
  nlinarith [h]

/-- `α` is a fixed point of `p ↦ p^2 (2-p)^2`. -/
theorem alpha_fixed : alpha ^ 2 * (2 - alpha) ^ 2 = alpha := by
  have h := alpha_mul_sq
  nlinarith [h]

theorem one_sub_alpha_pos : 0 < 1 - alpha := by linarith [alpha_lt_one]

theorem one_sub_alpha_nonneg : 0 ≤ 1 - alpha := le_of_lt one_sub_alpha_pos

/-- `(1 - α)(2 - α) = 1`. -/
theorem one_sub_alpha_mul : (1 - alpha) * (2 - alpha) = 1 := by
  have h := one_sub_alpha_sq
  nlinarith [h]



end

/-! ## Module `Prob` -/

section

/-
The probability distributions `Δ_d` of Section 7 of Sergeev, *Economical
formulae for symmetric boolean functions* (2025), and the recurrences (23) for
the error probabilities `p_d`, `q_d`.

The distribution `Δ₀` is described by the weight `w0`: the constant formula `0`
has weight `τ` and every disjunction `x_{i₁} ∨ ... ∨ x_{i_m}` has weight
`(1 - τ)/n^m`.  The distribution `Δ_{d+1}` is the fourth power of `Δ_d`.
-/

open scoped BigOperators



/-! ### Weighted counting -/

/-- The total weight of the elements where the boolean indicator `p` is true. -/
noncomputable def bsum {A : Type*} [Fintype A] (w : A → ℝ) (p : A → Bool) : ℝ :=
  ∑ a, if p a then w a else 0

theorem bsum_congr {A : Type*} [Fintype A] {w : A → ℝ} {p q : A → Bool}
    (h : ∀ a, p a = q a) : bsum w p = bsum w q := by
  unfold bsum
  exact Finset.sum_congr rfl (fun a _ => by rw [h a])

theorem bsum_total {A : Type*} [Fintype A] (w : A → ℝ) :
    bsum w (fun _ => true) = ∑ a, w a := by
  unfold bsum
  simp

theorem bsum_not {A : Type*} [Fintype A] (w : A → ℝ) (p : A → Bool) :
    bsum w (fun a => !p a) = bsum w (fun _ => true) - bsum w p := by
  unfold bsum
  have h : (∑ a, (if !p a then w a else 0))
      = ∑ a, (w a - (if p a then w a else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    cases hpa : p a <;> simp
  rw [h, Finset.sum_sub_distrib]
  simp

/-- Independence: weights multiply on a product type. -/
theorem bsum_prod_and {A B : Type*} [Fintype A] [Fintype B]
    (w : A → ℝ) (v : B → ℝ) (p : A → Bool) (q : B → Bool) :
    bsum (fun z : A × B => w z.1 * v z.2) (fun z => p z.1 && q z.2)
      = bsum w p * bsum v q := by
  unfold bsum
  rw [Fintype.sum_prod_type]
  have h : ∀ a b, (if p a && q b then w a * v b else 0)
      = (if p a then w a else 0) * (if q b then v b else 0) := by
    intro a b
    cases p a <;> cases q b <;> simp
  simp only [h]
  rw [Finset.sum_mul_sum]

/-- Probability of a union, by inclusion–exclusion. -/
theorem bsum_prod_or {A B : Type*} [Fintype A] [Fintype B]
    (w : A → ℝ) (v : B → ℝ) (p : A → Bool) (q : B → Bool) :
    bsum (fun z : A × B => w z.1 * v z.2) (fun z => p z.1 || q z.2)
      = bsum w (fun _ => true) * bsum v (fun _ => true)
        - bsum w (fun a => !p a) * bsum v (fun b => !q b) := by
  have h1 : bsum (fun z : A × B => w z.1 * v z.2) (fun z => p z.1 || q z.2)
      = bsum (fun z : A × B => w z.1 * v z.2)
          (fun z => !(!p z.1 && !q z.2)) :=
    bsum_congr (fun z => by cases p z.1 <;> cases q z.2 <;> rfl)
  rw [h1, bsum_not]
  have h2 : bsum (fun z : A × B => w z.1 * v z.2) (fun z => !p z.1 && !q z.2)
      = bsum w (fun a => !p a) * bsum v (fun b => !q b) :=
    bsum_prod_and w v (fun a => !p a) (fun b => !q b)
  have h3 : bsum (fun z : A × B => w z.1 * v z.2) (fun _ => true)
      = bsum w (fun _ => true) * bsum v (fun _ => true) := by
    simpa using bsum_prod_and w v (fun _ => true) (fun _ => true)
  rw [h2, h3]

/-! ### The distribution `Δ₀` -/

/-- The probability `τ` of Section 7 that a `Δ₀` formula is the constant `0`:
`τ = 1 - α/(1 - (1-k/n)^m)`. -/
noncomputable def tau (n m k : ℕ) : ℝ :=
  1 - alpha / (1 - (1 - (k : ℝ) / (n : ℝ)) ^ m)

/-- The weights of the distribution `Δ₀` on its seeds. -/
noncomputable def w0 (n m k : ℕ) : Seed0 n m → ℝ
  | Option.none => tau n m k
  | Option.some _ => (1 - tau n m k) / ((n : ℝ) ^ m)

theorem sum_w0 {n m k : ℕ} (hn : 0 < n) :
    ∑ s : Seed0 n m, w0 n m k s = 1 := by
  classical
  rw [Fintype.sum_option]
  have hcard : Fintype.card (Fin m → Fin n) = n ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hsum : (∑ f : Fin m → Fin n, w0 n m k (Option.some f)) = 1 - tau n m k := by
    have hterm : ∀ f : Fin m → Fin n,
        w0 n m k (Option.some f) = (1 - tau n m k) / ((n : ℝ) ^ m) := fun f => rfl
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_pow]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [hsum]
  simp only [w0]
  ring

/-! ### The distributions `Δ_d` -/

/-- The weights of the distribution `Δ_d`: the fourth power of `Δ_{d-1}`. -/
noncomputable def wseed (n m k : ℕ) : (d : ℕ) → Seed n m d → ℝ
  | 0, s => w0 n m k s
  | d + 1, s =>
      (wseed n m k d s.1.1 * wseed n m k d s.1.2) *
        (wseed n m k d s.2.1 * wseed n m k d s.2.2)

theorem sum_pair_mul {A : Type*} [Fintype A] (W : A → ℝ) :
    ∑ p : A × A, W p.1 * W p.2 = (∑ a, W a) * (∑ b, W b) := by
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem sum_wseed {n m k : ℕ} (hn : 0 < n) (d : ℕ) :
    ∑ s : Seed n m d, wseed n m k d s = 1 := by
  induction d with
  | zero =>
      show (∑ s : Seed n m 0, w0 n m k s) = 1
      exact sum_w0 hn
  | succ d ih =>
      change (∑ z : (Seed n m d × Seed n m d) × (Seed n m d × Seed n m d),
        (wseed n m k d z.1.1 * wseed n m k d z.1.2)
          * (wseed n m k d z.2.1 * wseed n m k d z.2.2)) = 1
      rw [Fintype.sum_prod_type]
      have hfac : ∑ p : Seed n m d × Seed n m d,
            ∑ q : Seed n m d × Seed n m d,
              (wseed n m k d p.1 * wseed n m k d p.2)
                * (wseed n m k d q.1 * wseed n m k d q.2)
          = (∑ p : Seed n m d × Seed n m d, wseed n m k d p.1 * wseed n m k d p.2)
            * (∑ q : Seed n m d × Seed n m d, wseed n m k d q.1 * wseed n m k d q.2) := by
        rw [Finset.sum_mul_sum]
      rw [hfac, sum_pair_mul, ih]
      ring

/-! ### Error probabilities `p_d`, `q_d` -/

/-- The indicator of the event `G(x) = 1` for a `Δ_d` formula. -/
noncomputable def badOne (n m d : ℕ) (x : Fin n → Bool) : Seed n m d → Bool :=
  fun s => (deltaForm n m d s).eval x

/-- The indicator of the event `G(x) = 0` for a `Δ_d` formula. -/
noncomputable def badZero (n m d : ℕ) (x : Fin n → Bool) : Seed n m d → Bool :=
  fun s => !((deltaForm n m d s).eval x)

/-- `p_d = P(G(X⁰) = 1)`. -/
noncomputable def pErr (n m k d : ℕ) (x : Fin n → Bool) : ℝ :=
  bsum (wseed n m k d) (badOne n m d x)

/-- `q_d = P(G(X¹) = 0)`. -/
noncomputable def qErr (n m k d : ℕ) (x : Fin n → Bool) : ℝ :=
  bsum (wseed n m k d) (badZero n m d x)

/-- Equation (23), first identity: `p_{d+1} = (1 - (1 - p_d)^2)^2`. -/
theorem pErr_succ {n m k d : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    pErr n m k (d + 1) x = (1 - (1 - pErr n m k d x) ^ 2) ^ 2 := by
  change bsum (fun z : (Seed n m d × Seed n m d) × (Seed n m d × Seed n m d) =>
      (wseed n m k d z.1.1 * wseed n m k d z.1.2)
        * (wseed n m k d z.2.1 * wseed n m k d z.2.2))
    (fun z => ((badOne n m d x z.1.1 || badOne n m d x z.1.2)
      && (badOne n m d x z.2.1 || badOne n m d x z.2.2)))
    = (1 - (1 - pErr n m k d x) ^ 2) ^ 2
  rw [bsum_prod_and
    (fun p : Seed n m d × Seed n m d => wseed n m k d p.1 * wseed n m k d p.2)
    (fun p : Seed n m d × Seed n m d => wseed n m k d p.1 * wseed n m k d p.2)
    (fun p => badOne n m d x p.1 || badOne n m d x p.2)
    (fun p => badOne n m d x p.1 || badOne n m d x p.2)]
  have hor : bsum (fun p : Seed n m d × Seed n m d =>
        wseed n m k d p.1 * wseed n m k d p.2)
      (fun p => badOne n m d x p.1 || badOne n m d x p.2)
      = 1 - (1 - pErr n m k d x) ^ 2 := by
    rw [bsum_prod_or]
    have hT : bsum (wseed n m k d) (fun _ => true) = 1 := by
      rw [bsum_total]
      exact sum_wseed hn d
    have hN : bsum (wseed n m k d) (fun a => !badOne n m d x a) = 1 - pErr n m k d x := by
      rw [bsum_not, hT]
      rfl
    rw [hT, hN]
    ring
  rw [hor]
  ring

/-- `q_d` is the probability of the complementary event, whence
`q_d = 1 - p_d`. -/
theorem qErr_eq {n m k d : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    qErr n m k d x = 1 - pErr n m k d x := by
  have h : qErr n m k d x = bsum (wseed n m k d) (fun a => !(badOne n m d x a)) := rfl
  rw [h, bsum_not, bsum_total, sum_wseed hn d]
  rfl

/-- Equation (23), second identity: `q_{d+1} = 1 - (1 - q_d^2)^2`. -/
theorem qErr_succ {n m k d : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    qErr n m k (d + 1) x = 1 - (1 - qErr n m k d x ^ 2) ^ 2 := by
  rw [qErr_eq (d := d + 1) hn, qErr_eq (d := d) hn, pErr_succ hn]

/-- Equation (27), first identity: `p_{d+1} = p_d^2 (2 - p_d)^2`. -/
theorem pErr_succ_mul {n m k d : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    pErr n m k (d + 1) x = pErr n m k d x ^ 2 * (2 - pErr n m k d x) ^ 2 := by
  rw [pErr_succ hn]; ring

/-- Equation (27), second identity: `q_{d+1} = q_d^2 (2 - q_d^2)`. -/
theorem qErr_succ_mul {n m k d : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    qErr n m k (d + 1) x = qErr n m k d x ^ 2 * (2 - qErr n m k d x ^ 2) := by
  rw [qErr_succ hn]; ring



end

/-! ## Module `Initial` -/

section

/-
The initial error probabilities `p₀ = pErr 0` and `q₀ = qErr 0` of the
distributions `Δ₀` of Section 7 of Sergeev, *Economical formulae for symmetric
boolean functions* (2025), and the lower bounds `ε₀, δ₀ = Ω(t/k)` for the
deficits `ε₀ = α - p₀`, `δ₀ = (1-α) - q₀`.
-/

open scoped BigOperators



/-! ### Counting the seeds that hit a prescribed set -/

/-- The number of maps `Fin m → Fin n` avoiding a fixed set `S`. -/
lemma card_fun_notMem (n m : ℕ) (S : Finset (Fin n)) :
    Fintype.card {f : Fin m → Fin n // ∀ i, f i ∉ S} = (n - S.card) ^ m := by
  have e : {f : Fin m → Fin n // ∀ i, f i ∉ S} ≃ (Fin m → {x : Fin n // x ∉ S}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

/-- The number of maps avoiding `S`, as a sum of indicators. -/
lemma sum_indicator_notMem (n m : ℕ) (S : Finset (Fin n)) :
    (∑ f : Fin m → Fin n, (if ∀ i, f i ∉ S then (1:ℝ) else 0))
      = ((n - S.card : ℕ) : ℝ) ^ m := by
  have h1 : (∑ f : Fin m → Fin n, (if (∀ i, f i ∉ S) then (1:ℝ) else 0))
      = ((Finset.univ.filter fun f : Fin m → Fin n => ∀ i, f i ∉ S).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [h1, ← Fintype.card_subtype (fun f : Fin m → Fin n => ∀ i, f i ∉ S), card_fun_notMem]
  norm_cast

/-- The number of maps that hit `S`, as a sum of indicators. -/
lemma sum_indicator_exists (n m : ℕ) (S : Finset (Fin n)) :
    (∑ f : Fin m → Fin n, (if ∃ i, f i ∈ S then (1:ℝ) else 0))
      = (n : ℝ) ^ m - ((n - S.card : ℕ) : ℝ) ^ m := by
  have h2 := sum_indicator_notMem (n := n) (m := m) S
  have hsplit : ∀ f : Fin m → Fin n,
      (if ∃ i, f i ∈ S then (1:ℝ) else 0)
        = 1 - (if ∀ i, f i ∉ S then (1:ℝ) else 0) := by
    intro f
    by_cases h : ∃ i, f i ∈ S
    · have h' : ¬ ∀ i, f i ∉ S := fun hc => h.elim (fun i hi => hc i hi)
      simp [h, h']
    · have h' : ∀ i, f i ∉ S := fun i hi => h ⟨i, hi⟩
      simp [h']
  rw [Finset.sum_congr rfl fun f _ => hsplit f, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul,
    mul_one, h2, Nat.cast_pow]

/-! ### The error probabilities of `Δ₀` -/

/-- `1 - τ = α/(1 - (1-k/n)^m)`, by the definition of `τ`. -/
lemma one_sub_tau (n m k : ℕ) :
    1 - tau n m k = alpha / (1 - (1 - (k : ℝ) / (n : ℝ)) ^ m) := by
  unfold tau; ring

/-- The error probability `p₀` at a vector of weight `σ`: the disjunction of `m`
random variables is true unless all of them are non-ones. -/
lemma pErr_zero (hn : 0 < n) (m k : ℕ) (x : Fin n → Bool) :
    pErr n m k 0 x
      = (1 - tau n m k)
        * (1 - ((n - onesCount x : ℕ) : ℝ) ^ m / (n : ℝ) ^ m) := by
  have hσ : (support x).card = onesCount x := (onesCount_eq_card_support x).symm
  have hsum := sum_indicator_exists (n := n) (m := m) (support x)
  have hterm : ∀ f : Fin m → Fin n,
      (if (delta0Form n m (Option.some f)).eval x then w0 n m k (Option.some f) else 0)
        = (1 - tau n m k) / (n : ℝ) ^ m * (if ∃ i, f i ∈ support x then (1:ℝ) else 0) := by
    intro f
    have hiff : (delta0Form n m (Option.some f)).eval x = true ↔ ∃ i, f i ∈ support x := by
      rw [delta0Form_some_eval]
      exact ⟨fun ⟨i, hi⟩ => ⟨i, by simpa [support] using hi⟩,
             fun ⟨i, hi⟩ => ⟨i, by simpa [support] using hi⟩⟩
    have hc : (delta0Form n m (Option.some f)).eval x = decide (∃ i, f i ∈ support x) := by
      by_cases h : ∃ i, f i ∈ support x
      · rw [hiff.mpr h]; simp [h]
      · have hf : (delta0Form n m (Option.some f)).eval x ≠ true := fun hh => h (hiff.mp hh)
        cases hv : (delta0Form n m (Option.some f)).eval x
        · simp [h]
        · exact absurd hv hf
    rw [hc]
    by_cases h : ∃ i, f i ∈ support x <;> simp [h, w0]
  calc pErr n m k 0 x
      = (if (delta0Form n m Option.none).eval x then w0 n m k Option.none else 0)
        + ∑ f : Fin m → Fin n,
            (if (delta0Form n m (Option.some f)).eval x then w0 n m k (Option.some f) else 0) := by
        rw [pErr, bsum]
        exact Fintype.sum_option _
    _ = ∑ f : Fin m → Fin n,
            (1 - tau n m k) / (n : ℝ) ^ m * (if ∃ i, f i ∈ support x then (1:ℝ) else 0) := by
        rw [delta0Form_none_eval]
        simp only [Bool.false_eq_true, ite_false, zero_add]
        exact Finset.sum_congr rfl fun f _ => hterm f
    _ = (1 - tau n m k) / (n : ℝ) ^ m
          * ((n : ℝ) ^ m - ((n - onesCount x : ℕ) : ℝ) ^ m) := by
        rw [← Finset.mul_sum, hsum, hσ]
    _ = (1 - tau n m k)
        * (1 - ((n - onesCount x : ℕ) : ℝ) ^ m / (n : ℝ) ^ m) := by
        have hn' : (n : ℝ) ^ m ≠ 0 := by
          have : (0:ℝ) < n := by exact_mod_cast hn
          positivity
        field_simp

/-- The error probability `q₀` at a vector of weight `σ`: a `Δ₀` formula is
false only if it is the constant `0` or all its variables are non-ones. -/
lemma qErr_zero (hn : 0 < n) (m k : ℕ) (x : Fin n → Bool) :
    qErr n m k 0 x
      = tau n m k + (1 - tau n m k) * (((n - onesCount x : ℕ) : ℝ) ^ m / (n : ℝ) ^ m) := by
  have hzero := pErr_zero (n := n) hn m k x
  have h := qErr_eq (n := n) (m := m) (k := k) (d := 0) (x := x) hn
  rw [h]; rw [hzero]; ring



/-! ### The parameters `a = 1 - k/n` and `b = t/n` -/

/-- `a = 1 - k/n`. -/
noncomputable def abase (n k : ℕ) : ℝ := 1 - (k : ℝ) / (n : ℝ)

/-- `b = t/n`. -/
noncomputable def bshift (n t : ℕ) : ℝ := (t : ℝ) / (n : ℝ)

theorem abase_pos {n k : ℕ} (hn : 0 < n) (h2k : 2 * k ≤ n) : 0 < abase n k := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h2 : (2:ℝ) * (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2k
  have hkn : (k:ℝ) < (n:ℝ) := by nlinarith
  have : (k:ℝ)/(n:ℝ) < 1 := (div_lt_one hn').mpr hkn
  unfold abase; linarith

theorem abase_le_one (n k : ℕ) : abase n k ≤ 1 := by
  unfold abase
  have h2 : (0:ℝ) ≤ (k:ℝ)/(n:ℝ) := by positivity
  linarith

theorem abase_lt_one {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : abase n k < 1 := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hk' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h : 0 < (k:ℝ)/(n:ℝ) := by positivity
  unfold abase; linarith

theorem abase_half {n k : ℕ} (hn : 0 < n) (h2k : 2 * k ≤ n) : (1/2 : ℝ) ≤ abase n k := by
  unfold abase
  have h : (k:ℝ)/(n:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ (by exact_mod_cast hn)]
    have : (2:ℝ)*(k:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2k
    linarith
  linarith

theorem abase_sub_eq (n k : ℕ) : 1 - abase n k = (k:ℝ)/(n:ℝ) := by
  unfold abase; ring

theorem bshift_pos {n t : ℕ} (hn : 0 < n) (ht : 0 < t) : 0 < bshift n t := by
  unfold bshift
  apply div_pos <;> [exact_mod_cast ht; exact_mod_cast hn]

theorem bshift_le_half {n k t : ℕ} (hn : 0 < n) (htk : t ≤ k) (h2k : 2*k ≤ n) :
    bshift n t ≤ 1/2 := by
  unfold bshift
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  have h1 : (t:ℝ) ≤ (k:ℝ) := by exact_mod_cast htk
  have h2 : (2:ℝ)*(k:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2k
  linarith

theorem bshift_le_abase {n k t : ℕ} (hn : 0 < n) (hkn : k + t ≤ n) :
    bshift n t ≤ abase n k := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hkt : (k:ℝ) + (t:ℝ) ≤ (n:ℝ) := by exact_mod_cast hkn
  have h : abase n k - bshift n t = ((n:ℝ) - (k:ℝ) - (t:ℝ))/(n:ℝ) := by
    unfold abase bshift; field_simp
  rw [← sub_nonneg, h]
  exact div_nonneg (by linarith) (le_of_lt hn0)

theorem bshift_eq_sub {n k t : ℕ} (hn : 0 < n) :
    abase n k - bshift n t = 1 - ((k:ℝ) + (t:ℝ))/(n:ℝ) := by
  unfold abase bshift
  field_simp
  ring

theorem abase_add_eq_sub {n k t : ℕ} (htk : t ≤ k) :
    abase n k + bshift n t = 1 - ((k:ℝ) - (t:ℝ))/(n:ℝ) := by
  unfold abase bshift
  field_simp
  ring

/-- `log (1-k/n) ≥ -2k/n`. -/
theorem abase_log_ge {n k : ℕ} (hn : 0 < n) (h2k : 2*k ≤ n) :
    -(2 * (k:ℝ)/(n:ℝ)) ≤ Real.log (abase n k) := by
  have hy1 : (k:ℝ)/(n:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ (by exact_mod_cast hn)]
    have : (2:ℝ)*(k:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2k
    linarith
  have hy0 : (0:ℝ) ≤ (k:ℝ)/(n:ℝ) := by positivity
  have h1y : 0 < 1 - (k:ℝ)/(n:ℝ) := by linarith
  have hne : (1 - (k:ℝ)/(n:ℝ)) ≠ 0 := ne_of_gt h1y
  have hinv : Real.log ((1 - (k:ℝ)/(n:ℝ))⁻¹) ≤ (1 - (k:ℝ)/(n:ℝ))⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog : Real.log (1 - (k:ℝ)/(n:ℝ)) = -Real.log ((1 - (k:ℝ)/(n:ℝ))⁻¹) := by
    rw [Real.log_inv]; ring
  have hsub : (1 - (k:ℝ)/(n:ℝ))⁻¹ - 1 = ((k:ℝ)/(n:ℝ)) / (1 - (k:ℝ)/(n:ℝ)) := by
    rw [eq_div_iff hne, sub_mul, inv_mul_cancel₀ hne]
    ring
  have h2y : ((k:ℝ)/(n:ℝ)) / (1 - (k:ℝ)/(n:ℝ)) ≤ 2 * ((k:ℝ)/(n:ℝ)) := by
    rw [div_le_iff₀ h1y]; nlinarith
  have hmain : Real.log ((1 - (k:ℝ)/(n:ℝ))⁻¹) ≤ 2 * ((k:ℝ)/(n:ℝ)) := by
    rw [hsub] at hinv
    linarith
  have hmain' : Real.log ((1 - (k:ℝ)/(n:ℝ))⁻¹) ≤ (2 * (k:ℝ))/(n:ℝ) := by
    have h := hmain
    rw [show 2 * ((k:ℝ)/(n:ℝ)) = (2 * (k:ℝ))/(n:ℝ) by ring] at h
    exact h
  have ha : abase n k = 1 - (k:ℝ)/(n:ℝ) := rfl
  rw [ha, hlog]
  linarith

/-- `(1-k/n)^m ≥ 1/8`. -/
theorem abase_pow_ge {n k m : ℕ} (hn : 0 < n) (h2k : 2*k ≤ n) (hm : m * k ≤ n) :
    (1/8 : ℝ) ≤ abase n k ^ m := by
  have ha0 := abase_pos (n := n) (k := k) hn h2k
  have hlog := abase_log_ge (n := n) (k := k) hn h2k
  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hmk : (m:ℝ) * (k:ℝ) / (n:ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hm
  have hprod : -(2 : ℝ) ≤ (m:ℝ) * Real.log (abase n k) := by
    have h1 : (m:ℝ) * (-(2 * (k:ℝ)/(n:ℝ))) ≤ (m:ℝ) * Real.log (abase n k) :=
      mul_le_mul_of_nonneg_left hlog hm0
    have h2 : (m:ℝ) * (-(2 * (k:ℝ)/(n:ℝ))) = -(2 * ((m:ℝ)*(k:ℝ)/(n:ℝ))) := by ring
    linarith
  have hexp : abase n k ^ m = Real.exp ((m:ℝ) * Real.log (abase n k)) := by
    rw [← Real.exp_log (pow_pos ha0 m), Real.log_pow]
  have he2 : Real.exp 2 ≤ 8 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h]
    nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
  have h18 : (1/8 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (by norm_num) (Real.exp_pos 2)).mpr he2
  calc (1/8 : ℝ) ≤ Real.exp (-2) := h18
    _ ≤ Real.exp ((m:ℝ) * Real.log (abase n k)) := Real.exp_le_exp.mpr hprod
    _ = abase n k ^ m := hexp.symm

/-- `(1-k/n)^m ≤ 3/5` when `m = n/k` and `2k ≤ n`. -/
theorem abase_pow_le {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2*k ≤ n) (hm : m = n / k) :
    abase n k ^ m ≤ 3/5 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ha0 := abase_pos (n := n) (k := k) hn h2k
  have hm2 : 2 ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le (by omega : 0 < k)]
    omega
  have hlt : n < k * (m + 1) := by
    have h := Nat.div_add_mod n k
    have hmod := Nat.mod_lt n (by omega : 0 < k)
    rw [← hm] at h
    calc n = k * m + n % k := h.symm
      _ < k * m + k := by omega
      _ = k * (m + 1) := by ring
  have hmk : (2:ℝ)/3 ≤ (m:ℝ) * (k:ℝ) / (n:ℝ) := by
    have h1 : (n:ℝ) < (k:ℝ) * ((m:ℝ) + 1) := by exact_mod_cast hlt
    have h2 : (k:ℝ) * ((m:ℝ) + 1) ≤ (k:ℝ) * ((m:ℝ) * (3/2)) := by
      have : (m:ℝ) + 1 ≤ (m:ℝ) * (3/2) := by
        have : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm2
        linarith
      nlinarith [le_of_lt hk0]
    have h3 : (0:ℝ) < (k:ℝ) * (m:ℝ) := by
      have : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
      positivity
    rw [le_div_iff₀ hn0]
    nlinarith
  have hlog : Real.log (abase n k) ≤ -((k:ℝ)/(n:ℝ)) := by
    have h := Real.log_le_sub_one_of_pos ha0
    have : abase n k - 1 = -((k:ℝ)/(n:ℝ)) := by unfold abase; ring
    linarith
  have hprod : (m:ℝ) * Real.log (abase n k) ≤ -(2/3) := by
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have h1 : (m:ℝ) * Real.log (abase n k) ≤ (m:ℝ) * (-((k:ℝ)/(n:ℝ))) :=
      mul_le_mul_of_nonneg_left hlog hm0
    have h2 : (m:ℝ) * ((k:ℝ)/(n:ℝ)) = (m:ℝ)*(k:ℝ)/(n:ℝ) := by ring
    linarith
  have hexp : abase n k ^ m = Real.exp ((m:ℝ) * Real.log (abase n k)) := by
    rw [← Real.exp_log (pow_pos ha0 m), Real.log_pow]
  have h35 : Real.exp (-(2/3) : ℝ) ≤ 3/5 := by
    have he : (0:ℝ) < Real.exp (2/3 : ℝ) := Real.exp_pos _
    have h5 : (5/3 : ℝ) ≤ Real.exp (2/3 : ℝ) := by
      have := Real.add_one_le_exp (2/3 : ℝ)
      linarith
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    nlinarith
  calc abase n k ^ m = Real.exp ((m:ℝ) * Real.log (abase n k)) := hexp
    _ ≤ Real.exp (-(2/3) : ℝ) := Real.exp_le_exp.mpr hprod
    _ ≤ 3/5 := h35


/-! ### The initial error probabilities `p₀` and `q₀` -/

/-- The error probability `p₀` of `Δ₀` at a vector of weight `k - t`. -/
noncomputable def p0 (n m k t : ℕ) : ℝ :=
  alpha * (1 - (abase n k + bshift n t) ^ m) / (1 - abase n k ^ m)

/-- The error probability `q₀` of `Δ₀` at a vector of weight `k + t`. -/
noncomputable def q0 (n m k t : ℕ) : ℝ :=
  1 - alpha * (1 - (abase n k - bshift n t) ^ m) / (1 - abase n k ^ m)

lemma abase_add_bshift {n k t : ℕ} (hn : 0 < n) (htk : t ≤ k) (hkn : k + t ≤ n) :
    abase n k + bshift n t = 1 - ((k - t : ℕ) : ℝ) / (n : ℝ) := by
  have hkt : ((k - t : ℕ) : ℝ) = (k:ℝ) - (t:ℝ) := by
    rw [Nat.cast_sub htk]
  unfold abase bshift
  rw [hkt]
  ring

lemma abase_sub_bshift {n k t : ℕ} (hn : 0 < n) (hkn : k + t ≤ n) :
    abase n k - bshift n t = 1 - ((k + t : ℕ) : ℝ) / (n : ℝ) := by
  unfold abase bshift
  push_cast
  ring

lemma pErr_zero_eq_p0 {n m k t : ℕ} (hn : 0 < n) (htk : t ≤ k) (hkn : k + t ≤ n)
    (x : Fin n → Bool) (hx : onesCount x = k - t) : pErr n m k 0 x = p0 n m k t := by
  rw [pErr_zero hn m k x, hx]
  have hσn : k - t ≤ n := by omega
  have hn0 : (n : ℝ) ^ m ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hcast : ((n - (k - t) : ℕ) : ℝ) = (n:ℝ) * (abase n k + bshift n t) := by
    rw [Nat.cast_sub hσn, abase_add_bshift hn htk hkn]
    have h1 : ((k - t : ℕ) : ℝ) ≤ (n:ℝ) := by
      have : ((k - t : ℕ) : ℝ) ≤ ((n:ℕ):ℝ) := by
        exact_mod_cast (show k - t ≤ n by omega)
      simpa using this
    field_simp
  have hdiv : ((n - (k - t) : ℕ) : ℝ) ^ m / (n : ℝ) ^ m = (abase n k + bshift n t) ^ m := by
    rw [hcast, mul_pow, mul_div_cancel_left₀ _ hn0]
  rw [hdiv, one_sub_tau]
  unfold p0 abase
  ring

lemma qErr_zero_eq_q0 {n m k t : ℕ} (hn : 0 < n) (hkn : k + t ≤ n)
    (x : Fin n → Bool) (hx : onesCount x = k + t) : qErr n m k 0 x = q0 n m k t := by
  rw [qErr_zero hn m k x, hx]
  have hσn : k + t ≤ n := hkn
  have hn0 : (n : ℝ) ^ m ≠ 0 := by
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    positivity
  have hcast : ((n - (k + t) : ℕ) : ℝ) = (n:ℝ) * (abase n k - bshift n t) := by
    rw [Nat.cast_sub hσn, abase_sub_bshift hn hkn]
    field_simp
  have hdiv : ((n - (k + t) : ℕ) : ℝ) ^ m / (n : ℝ) ^ m = (abase n k - bshift n t) ^ m := by
    rw [hcast, mul_pow, mul_div_cancel_left₀ _ hn0]
  rw [hdiv, one_sub_tau]
  unfold q0 tau abase
  ring



end

/-! ## Module `Bounds` -/

section

/-
The real-analytic part of the proof of Theorem 1 (§7 of Sergeev, *Economical
formulae for symmetric boolean functions* (2025)): the error probabilities
`p_d` and `q_d` of the distributions `Δ_d` converge to the fixed points
`α = (3-√5)/2` and `1-α` of the iterations
`p ↦ p²(2-p)²` and `q ↦ q²(2-q²)` at the geometric rate `4α` (Lemma 4), and
then the iteration squares the error down to `1/2^{r+1}` (Lemma 5).
-/

open scoped BigOperators

set_option linter.unusedVariables false



/-! ### The two iterations of (23) and (27) -/

/-- The iteration `p ↦ p²(2-p)² = (1-(1-p)²)²` of the error probability `p_d`. -/
noncomputable def pstep (x : ℝ) : ℝ := x ^ 2 * (2 - x) ^ 2

/-- The iteration `q ↦ q²(2-q²) = 1-(1-q²)²` of the error probability `q_d`. -/
noncomputable def qstep (x : ℝ) : ℝ := x ^ 2 * (2 - x ^ 2)

theorem pstep_nonneg (x : ℝ) : 0 ≤ pstep x := by
  unfold pstep
  exact mul_nonneg (sq_nonneg x) (sq_nonneg (2 - x))

/-- `p_{d+1} ≤ 4 p_d²`. -/
theorem pstep_le_four_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2) : pstep x ≤ 4 * x ^ 2 := by
  unfold pstep
  nlinarith [sq_nonneg x, sq_nonneg (2 - x), mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem qstep_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ qstep x := by
  unfold qstep
  have : (0:ℝ) ≤ 2 - x ^ 2 := by nlinarith
  exact mul_nonneg (sq_nonneg x) this

/-- `q_{d+1} ≤ 2 q_d²`. -/
theorem qstep_le_two_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : qstep x ≤ 2 * x ^ 2 := by
  unfold qstep
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

/-! ### Numerical facts about `α` -/

theorem alpha_ge_third : 1 / 3 ≤ alpha := by
  unfold alpha
  have h : Real.sqrt 5 ≤ 7 / 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

theorem five_alpha_le_two : 5 * alpha ≤ 2 := by
  unfold alpha
  have h : (11 / 5 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

theorem three_le_eight_alpha : 3 ≤ 8 * alpha := by
  unfold alpha
  have h : Real.sqrt 5 ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  linarith

/-! ### The one-step estimates for `p_d = α - ε_d` and `q_d = 1 - α - δ_d` -/

theorem errE_eq (eps : ℝ) :
    alpha - pstep (alpha - eps) =
      4 * alpha * eps - (6 * alpha - 2) * eps ^ 2 - 4 * (1 - alpha) * eps ^ 3 - eps ^ 4 := by
  unfold pstep
  nlinarith [alpha_sq]

theorem qstep_one_sub (q : ℝ) : qstep q = 1 - pstep (1 - q) := by
  unfold qstep pstep; ring

theorem errD_eq (dl : ℝ) :
    (1 - alpha) - qstep (1 - alpha - dl) =
      4 * alpha * dl + (6 * alpha - 2) * dl ^ 2 - 4 * (1 - alpha) * dl ^ 3 + dl ^ 4 := by
  have hq : qstep (1 - alpha - dl) = 1 - pstep (alpha + dl) := by
    rw [qstep_one_sub]; congr 1; ring
  rw [hq]
  have hp : pstep (alpha + dl) = alpha + 4 * alpha * dl + (6 * alpha - 2) * dl ^ 2
      - 4 * (1 - alpha) * dl ^ 3 + dl ^ 4 := by
    have h := errE_eq (-dl)
    rw [show alpha - -dl = alpha + dl from by ring] at h
    linarith [h]
  rw [hp]; ring

/-- `ε_{d+1} ≤ 4α ε_d`. -/
theorem errE_le {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ alpha) :
    alpha - pstep (alpha - eps) ≤ 4 * alpha * eps := by
  have hid : 4 * alpha * eps - (alpha - pstep (alpha - eps))
      = eps ^ 2 * (6 * alpha - 2 + 4 * (1 - alpha) * eps + eps ^ 2) := by
    rw [errE_eq]; ring
  have h6 : 0 ≤ 6 * alpha - 2 := by nlinarith [alpha_ge_third]
  have h4 : 0 ≤ 4 * (1 - alpha) := by nlinarith [alpha_lt_one]
  have hpos : 0 ≤ eps ^ 2 * (6 * alpha - 2 + 4 * (1 - alpha) * eps + eps ^ 2) := by
    apply mul_nonneg (sq_nonneg eps)
    have := mul_nonneg h4 h0
    nlinarith [sq_nonneg eps]
  rw [← hid] at hpos
  linarith

theorem auxE {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ alpha) :
    0 ≤ 2 * (1 - alpha) - 4 * (1 - alpha) * eps - eps ^ 2 := by
  nlinarith [alpha_sq, alpha_ge_third, alpha_lt_one]

/-- `ε_{d+1} ≥ 4α(1-ε_d) ε_d`. -/
theorem errE_ge {eps : ℝ} (h0 : 0 ≤ eps) (h1 : eps ≤ alpha) :
    4 * alpha * (1 - eps) * eps ≤ alpha - pstep (alpha - eps) := by
  have hid : (alpha - pstep (alpha - eps)) - 4 * alpha * (1 - eps) * eps
      = eps ^ 2 * (2 * (1 - alpha) - 4 * (1 - alpha) * eps - eps ^ 2) := by
    rw [errE_eq]; ring
  have := auxE h0 h1
  have hpos : 0 ≤ eps ^ 2 * (2 * (1 - alpha) - 4 * (1 - alpha) * eps - eps ^ 2) :=
    mul_nonneg (sq_nonneg eps) this
  rw [← hid] at hpos
  linarith

/-- `δ_{d+1} ≤ 4α(1 + δ_d/4) δ_d`. -/
theorem errD_le {dl : ℝ} (h0 : 0 ≤ dl) (h1 : dl ≤ alpha / 4) :
    (1 - alpha) - qstep (1 - alpha - dl) ≤ 4 * alpha * (1 + dl / 4) * dl := by
  have hid : 4 * alpha * (1 + dl / 4) * dl - ((1 - alpha) - qstep (1 - alpha - dl))
      = dl ^ 2 * (2 - 5 * alpha + 4 * (1 - alpha) * dl - dl ^ 2) := by
    rw [errD_eq]; ring
  have h2 : 0 ≤ 2 - 5 * alpha := by nlinarith [five_alpha_le_two]
  have h3 : 0 ≤ 4 * (1 - alpha) - dl := by nlinarith [alpha_lt_one, alpha_pos, h1]
  have hpos : 0 ≤ dl ^ 2 * (2 - 5 * alpha + 4 * (1 - alpha) * dl - dl ^ 2) := by
    apply mul_nonneg (sq_nonneg dl)
    have := mul_nonneg h0 h3
    nlinarith
  rw [← hid] at hpos
  linarith

/-- `δ_{d+1} ≥ 4α δ_d` (for `δ_d ≤ α/4`). -/
theorem errD_ge {dl : ℝ} (h0 : 0 ≤ dl) (h1 : dl ≤ alpha / 4) :
    4 * alpha * dl ≤ (1 - alpha) - qstep (1 - alpha - dl) := by
  have hid : ((1 - alpha) - qstep (1 - alpha - dl)) - 4 * alpha * dl
      = dl ^ 2 * (6 * alpha - 2 - 4 * (1 - alpha) * dl + dl ^ 2) := by
    rw [errD_eq]; ring
  have h3 : 0 ≤ 6 * alpha - 2 - 4 * (1 - alpha) * dl := by
    nlinarith [three_le_eight_alpha, alpha_lt_one, alpha_pos, h0, h1, mul_nonneg h0 h0]
  have hpos : 0 ≤ dl ^ 2 * (6 * alpha - 2 - 4 * (1 - alpha) * dl + dl ^ 2) := by
    apply mul_nonneg (sq_nonneg dl)
    nlinarith [sq_nonneg dl]
  rw [← hid] at hpos
  linarith

/-! ### Lemma 4, first part: `ε_d ≤ (4α)^d ε₀` -/

/-- Along the iteration `p_{d+1} = p_d²(2-p_d)²` starting in `[0, α]` the error
`ε_d = α - p_d` stays in `[0, α]` and grows at most geometrically. -/
theorem pIter_bounds (p : ℕ → ℝ) (hp : ∀ d, p (d + 1) = pstep (p d))
    (h0 : 0 ≤ p 0) (hα : p 0 ≤ alpha) :
    ∀ d, 0 ≤ p d ∧ p d ≤ alpha ∧ alpha - p d ≤ (4 * alpha) ^ d * (alpha - p 0) := by
  intro d
  induction d with
  | zero => exact ⟨h0, hα, by simp⟩
  | succ d ih =>
      obtain ⟨h0d, hαd, hbd⟩ := ih
      have harg : alpha - (alpha - p d) = p d := by ring
      have heps0 : 0 ≤ alpha - p d := by linarith
      have heps1 : alpha - p d ≤ alpha := by linarith
      have hlow : 4 * alpha * (1 - (alpha - p d)) * (alpha - p d) ≤ alpha - p (d + 1) := by
        have h := errE_ge heps0 heps1
        rw [harg] at h
        rw [hp d]
        exact h
      have hup : alpha - p (d + 1) ≤ 4 * alpha * (alpha - p d) := by
        have h := errE_le heps0 heps1
        rw [harg] at h
        rw [hp d]
        exact h
      have hε : 0 ≤ alpha - p (d + 1) := by
        have h1 : (0:ℝ) ≤ 1 - (alpha - p d) := by linarith [alpha_lt_one]
        have h2 : (0:ℝ) ≤ 4 * alpha := le_of_lt four_alpha_pos
        nlinarith [mul_nonneg (mul_nonneg h2 h1) heps0]
      have hnon : 0 ≤ p (d + 1) := by rw [hp d]; exact pstep_nonneg _
      have hb : alpha - p (d + 1) ≤ (4 * alpha) ^ (d + 1) * (alpha - p 0) := by
        calc alpha - p (d + 1) ≤ 4 * alpha * (alpha - p d) := hup
          _ ≤ 4 * alpha * ((4 * alpha) ^ d * (alpha - p 0)) :=
              mul_le_mul_of_nonneg_left hbd (le_of_lt four_alpha_pos)
          _ = (4 * alpha) ^ (d + 1) * (alpha - p 0) := by ring
      exact ⟨hnon, by linarith, hb⟩

/-! ### Elementary product bounds -/

/-- The union bound for a product: `1 - Σ x_i ≤ ∏ (1 - x_i)`. -/
theorem prod_one_sub_ge_sum (x : ℕ → ℝ) (m : ℕ) (hx : ∀ i < m, 0 ≤ x i)
    (hx1 : ∀ i < m, x i ≤ 1) :
    1 - ∑ i ∈ Finset.range m, x i ≤ ∏ i ∈ Finset.range m, (1 - x i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      have h1 := ih (fun i hi => hx i (Nat.lt_succ_of_lt hi))
        (fun i hi => hx1 i (Nat.lt_succ_of_lt hi))
      have hx0 : 0 ≤ x m := hx m (Nat.lt_succ_self m)
      have hxle : x m ≤ 1 := hx1 m (Nat.lt_succ_self m)
      have hS : 0 ≤ ∑ i ∈ Finset.range m, x i :=
        Finset.sum_nonneg fun i hi => hx i (by have := Finset.mem_range.mp hi; omega)
      have h2 : (1 - ∑ i ∈ Finset.range m, x i) * (1 - x m)
          ≤ (∏ i ∈ Finset.range m, (1 - x i)) * (1 - x m) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      have h3 : 1 - (∑ i ∈ Finset.range m, x i + x m)
          ≤ (1 - ∑ i ∈ Finset.range m, x i) * (1 - x m) := by
        nlinarith [mul_nonneg hS hx0]
      linarith

/-- If `Σ x_i ≤ 1/2` then `∏ (1 + x_i) ≤ 2`. -/
theorem prod_one_add_le (x : ℕ → ℝ) (m : ℕ) (hx : ∀ i, 0 ≤ x i)
    (hS : ∑ i ∈ Finset.range m, x i ≤ 1 / 2) :
    ∏ i ∈ Finset.range m, (1 + x i) ≤ 2 := by
  have key : ∀ n, (∏ i ∈ Finset.range n, (1 + x i)) * (1 - ∑ i ∈ Finset.range n, x i) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ, Finset.sum_range_succ]
        have hSn : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg fun i _ => hx i
        have hP : 0 ≤ ∏ i ∈ Finset.range n, (1 + x i) :=
          Finset.prod_nonneg fun i _ => by have := hx i; linarith
        have hx0 : 0 ≤ x n := hx n
        have hle : (1 + x n) * (1 - (∑ i ∈ Finset.range n, x i + x n))
            ≤ 1 - ∑ i ∈ Finset.range n, x i := by
          nlinarith [mul_nonneg hSn hx0]
        have hstep : (∏ i ∈ Finset.range n, (1 + x i)) * (1 + x n)
              * (1 - (∑ i ∈ Finset.range n, x i + x n))
            ≤ (∏ i ∈ Finset.range n, (1 + x i)) * (1 - ∑ i ∈ Finset.range n, x i) := by
          have h := mul_le_mul_of_nonneg_left hle hP
          calc (∏ i ∈ Finset.range n, (1 + x i)) * (1 + x n)
                * (1 - (∑ i ∈ Finset.range n, x i + x n))
              = (∏ i ∈ Finset.range n, (1 + x i))
                * ((1 + x n) * (1 - (∑ i ∈ Finset.range n, x i + x n))) := by ring
            _ ≤ (∏ i ∈ Finset.range n, (1 + x i)) * (1 - ∑ i ∈ Finset.range n, x i) := h
        linarith
  have h := key m
  have hS' : 0 < 1 - ∑ i ∈ Finset.range m, x i := by linarith
  have h1 : ∏ i ∈ Finset.range m, (1 + x i) ≤ 1 / (1 - ∑ i ∈ Finset.range m, x i) :=
    (le_div_iff₀ hS').mpr h
  have h2 : 1 / (1 - ∑ i ∈ Finset.range m, x i) ≤ 2 := by
    rw [div_le_iff₀ hS']
    linarith
  linarith

/-! ### Lemma 4, second part: the lower bounds (24) -/

/-- Along `p_{d+1} = p_d²(2-p_d)²` the error `ε_d = α - p_d` decays at rate `4α`
up to a factor `1/2`: if `(4α)^s ε₀ ≤ α/8` then `ε_s ≥ (4α)^s ε₀ / 2`. -/
theorem pIter_eps_lower (p : ℕ → ℝ) (hp : ∀ d, p (d + 1) = pstep (p d))
    (h0 : 0 ≤ p 0) (hα : p 0 ≤ alpha) (s : ℕ)
    (hs : (4 * alpha) ^ s * (alpha - p 0) ≤ alpha / 8) :
    (4 * alpha) ^ s * (alpha - p 0) / 2 ≤ alpha - p s := by
  have bounds := pIter_bounds p hp h0 hα
  have hlt1 : alpha < 1 := alpha_lt_one
  have h4 : (0:ℝ) < 4 * alpha := four_alpha_pos
  have hα15 : 4 / 15 ≤ alpha := by have := alpha_ge_third; linarith
  have heps0 : 0 ≤ alpha - p 0 := by have := (bounds 0).2.1; linarith
  have key : ∀ n, (4 * alpha) ^ n * (alpha - p 0)
      * ∏ d ∈ Finset.range n, (1 - (alpha - p d)) ≤ alpha - p n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        obtain ⟨h0n, hαn, -⟩ := bounds n
        have he0 : 0 ≤ alpha - p n := by linarith
        have he1 : alpha - p n ≤ alpha := by linarith
        have h1e : 0 ≤ 1 - (alpha - p n) := by linarith
        have hge := errE_ge he0 he1
        rw [show alpha - (alpha - p n) = p n from by ring] at hge
        have hge' : 4 * alpha * (alpha - p n) * (1 - (alpha - p n)) ≤ alpha - p (n + 1) := by
          rw [hp n]
          calc 4 * alpha * (alpha - p n) * (1 - (alpha - p n))
              = 4 * alpha * (1 - (alpha - p n)) * (alpha - p n) := by ring
            _ ≤ alpha - pstep (p n) := hge
        have hB : ((4 * alpha) ^ n * (alpha - p 0)
              * ∏ d ∈ Finset.range n, (1 - (alpha - p d))) * (1 - (alpha - p n))
            ≤ (alpha - p n) * (1 - (alpha - p n)) := mul_le_mul_of_nonneg_right ih h1e
        have hC := mul_le_mul_of_nonneg_left hB (le_of_lt h4)
        have hmono : 4 * alpha * ((4 * alpha) ^ n * (alpha - p 0)
              * ∏ d ∈ Finset.range n, (1 - (alpha - p d))) * (1 - (alpha - p n))
            ≤ 4 * alpha * (alpha - p n) * (1 - (alpha - p n)) := by
          calc 4 * alpha * ((4 * alpha) ^ n * (alpha - p 0)
                * ∏ d ∈ Finset.range n, (1 - (alpha - p d))) * (1 - (alpha - p n))
              = 4 * alpha * (((4 * alpha) ^ n * (alpha - p 0)
                * ∏ d ∈ Finset.range n, (1 - (alpha - p d))) * (1 - (alpha - p n))) := by ring
            _ ≤ 4 * alpha * ((alpha - p n) * (1 - (alpha - p n))) := hC
            _ = 4 * alpha * (alpha - p n) * (1 - (alpha - p n)) := by ring
        calc (4 * alpha) ^ (n + 1) * (alpha - p 0)
              * ∏ d ∈ Finset.range (n + 1), (1 - (alpha - p d))
            = 4 * alpha * ((4 * alpha) ^ n * (alpha - p 0)
                * ∏ d ∈ Finset.range n, (1 - (alpha - p d))) * (1 - (alpha - p n)) := by
              rw [Finset.prod_range_succ]; ring
          _ ≤ 4 * alpha * (alpha - p n) * (1 - (alpha - p n)) := hmono
          _ ≤ alpha - p (n + 1) := hge'
  have hprod : 1 - ∑ d ∈ Finset.range s, (alpha - p d)
      ≤ ∏ d ∈ Finset.range s, (1 - (alpha - p d)) := by
    apply prod_one_sub_ge_sum
    · intro i _
      have := (bounds i).2.1
      linarith
    · intro i _
      have h1 := (bounds i).1
      have h2 := (bounds i).2.1
      linarith
  have hden : (0:ℝ) < 4 * alpha - 1 := by linarith [one_lt_four_alpha]
  have hsum : ∑ d ∈ Finset.range s, (alpha - p d) ≤ 1 / 2 := by
    have h1 : ∑ d ∈ Finset.range s, (alpha - p d)
        ≤ ∑ d ∈ Finset.range s, (4 * alpha) ^ d * (alpha - p 0) :=
      Finset.sum_le_sum fun d _ => (bounds d).2.2
    have h2 : ∑ d ∈ Finset.range s, (4 * alpha) ^ d * (alpha - p 0)
        = (∑ d ∈ Finset.range s, (4 * alpha) ^ d) * (alpha - p 0) := by
      rw [Finset.sum_mul]
    have h5 : (4:ℝ) * alpha ≠ 1 := by linarith [one_lt_four_alpha]
    have h3 : ∑ d ∈ Finset.range s, (4 * alpha) ^ d
        = ((4 * alpha) ^ s - 1) / (4 * alpha - 1) := geom_sum_eq h5 s
    have h6 : ((4 * alpha) ^ s - 1) / (4 * alpha - 1)
        ≤ (4 * alpha) ^ s / (4 * alpha - 1) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hden)
      linarith
    have h7 : (4 * alpha) ^ s / (4 * alpha - 1) * (alpha - p 0) ≤ 1 / 2 := by
      have hA : (4 * alpha) ^ s / (4 * alpha - 1) * (alpha - p 0)
          = ((4 * alpha) ^ s * (alpha - p 0)) / (4 * alpha - 1) := by ring
      rw [hA, div_le_iff₀ hden]
      nlinarith [hs, hα15]
    calc ∑ d ∈ Finset.range s, (alpha - p d)
        ≤ (∑ d ∈ Finset.range s, (4 * alpha) ^ d) * (alpha - p 0) := h1.trans_eq h2
      _ = ((4 * alpha) ^ s - 1) / (4 * alpha - 1) * (alpha - p 0) := by rw [h3]
      _ ≤ (4 * alpha) ^ s / (4 * alpha - 1) * (alpha - p 0) :=
          mul_le_mul_of_nonneg_right h6 heps0
      _ ≤ 1 / 2 := h7
  have hnn : 0 ≤ (4 * alpha) ^ s * (alpha - p 0) :=
    mul_nonneg (pow_nonneg (le_of_lt h4) s) heps0
  have step1 : (4 * alpha) ^ s * (alpha - p 0)
        * (1 - ∑ d ∈ Finset.range s, (alpha - p d))
      ≤ (4 * alpha) ^ s * (alpha - p 0)
        * ∏ d ∈ Finset.range s, (1 - (alpha - p d)) :=
    mul_le_mul_of_nonneg_left hprod hnn
  have step2 : (4 * alpha) ^ s * (alpha - p 0) / 2
      ≤ (4 * alpha) ^ s * (alpha - p 0)
        * (1 - ∑ d ∈ Finset.range s, (alpha - p d)) := by
    have h' : (1 / 2 : ℝ) ≤ 1 - ∑ d ∈ Finset.range s, (alpha - p d) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h' hnn
    calc (4 * alpha) ^ s * (alpha - p 0) / 2
        = (4 * alpha) ^ s * (alpha - p 0) * (1 / 2) := by ring
      _ ≤ (4 * alpha) ^ s * (alpha - p 0) * (1 - ∑ d ∈ Finset.range s, (alpha - p d)) := h2
  linarith [key s, step1, step2]

/-! ### The `q`-iteration -/

/-- The deviation `δ_d = (1-α) - q_d` of the `q`-iteration from its fixed point. -/
noncomputable def qdev (q : ℕ → ℝ) (d : ℕ) : ℝ := (1 - alpha) - q d

/-- `qstep` is increasing on `[0,1]`: `qstep x = 2x² - x⁴`. -/
theorem qstep_mono {x y : ℝ} (hxy : x ≤ y) (hx : 0 ≤ x) (hy : y ≤ 1) :
    qstep x ≤ qstep y := by
  have h1 : x ^ 2 ≤ y ^ 2 := by nlinarith
  have h2 : y ^ 2 ≤ 1 := by nlinarith
  have key : 2 * x ^ 2 - x ^ 4 ≤ 2 * y ^ 2 - y ^ 4 := by
    have :
        (y ^ 2 - x ^ 2) * (2 - y ^ 2 - x ^ 2) = (2 * y ^ 2 - y ^ 4) - (2 * x ^ 2 - x ^ 4) := by
      ring
    have hpos : 0 ≤ (y ^ 2 - x ^ 2) * (2 - y ^ 2 - x ^ 2) := by
      apply mul_nonneg (by linarith) (by nlinarith)
    linarith [this ▸ hpos]
  calc qstep x = 2 * x ^ 2 - x ^ 4 := by unfold qstep; ring
    _ ≤ 2 * y ^ 2 - y ^ 4 := key
    _ = qstep y := by unfold qstep; ring

/-- `1-α` is a fixed point of `qstep`. -/
theorem qstep_fixed : qstep (1 - alpha) = 1 - alpha := by
  unfold qstep
  nlinarith [one_sub_alpha_sq, alpha_sq]

/-- The `q`-iteration stays in `[0, 1-α]`. -/
theorem qIter_basic (q : ℕ → ℝ) (hq : ∀ d, q (d + 1) = qstep (q d))
    (h0 : 0 ≤ q 0) (h1 : q 0 ≤ 1 - alpha) :
    ∀ d, 0 ≤ q d ∧ q d ≤ 1 - alpha ∧ 0 ≤ qdev q d := by
  have hpos : (0:ℝ) ≤ 1 - alpha := one_sub_alpha_nonneg
  have hαnn : (0:ℝ) ≤ alpha := alpha_nonneg
  intro d
  have hzero : qstep 0 = 0 := by unfold qstep; norm_num
  have hm : ∀ d, 0 ≤ q d ∧ q d ≤ 1 - alpha := by
    intro e
    induction e with
    | zero => exact ⟨h0, h1⟩
    | succ e ih =>
        obtain ⟨he0, he1⟩ := ih
        rw [hq e]
        exact ⟨by
          calc (0:ℝ) = qstep 0 := hzero.symm
            _ ≤ qstep (q e) := qstep_mono he0 le_rfl (by linarith)
          , by
          calc qstep (q e) ≤ qstep (1 - alpha) :=
                qstep_mono he1 he0 (by linarith)
            _ = 1 - alpha := qstep_fixed⟩
  obtain ⟨ha, hb⟩ := hm d
  exact ⟨ha, hb, by unfold qdev; linarith⟩

/-- The sum of the geometric series `(4α)^i δ₀ / 2` is at most `1/2`. -/
theorem qsum_geom (dl0 : ℝ) (hdl0 : 0 ≤ dl0) {s n : ℕ} (hn : n ≤ s)
    (hs : (4 * alpha) ^ s * dl0 ≤ alpha / 8) :
    ∑ i ∈ Finset.range n, (4 * alpha) ^ i * dl0 / 2 ≤ 1 / 2 := by
  have hA1 : (1:ℝ) ≤ 4 * alpha := le_of_lt one_lt_four_alpha
  have hden : (0:ℝ) < 4 * alpha - 1 := by linarith [one_lt_four_alpha]
  have hα26 : 8 / 31 ≤ alpha := by have := alpha_ge_third; linarith
  have hgeom : ∑ i ∈ Finset.range n, (4 * alpha) ^ i = ((4 * alpha) ^ n - 1) / (4 * alpha - 1) :=
    geom_sum_eq (by linarith [one_lt_four_alpha] : (4 * alpha) ≠ 1) n
  have hpow : (4 * alpha) ^ n ≤ (4 * alpha) ^ s := pow_le_pow_right₀ hA1 hn
  have hnum : (4 * alpha) ^ n * dl0 ≤ alpha / 8 :=
    le_trans (mul_le_mul_of_nonneg_right hpow hdl0) hs
  have h6 : ((4 * alpha) ^ n - 1) / (4 * alpha - 1) ≤ (4 * alpha) ^ n / (4 * alpha - 1) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    linarith
  calc ∑ i ∈ Finset.range n, (4 * alpha) ^ i * dl0 / 2
      = (∑ i ∈ Finset.range n, (4 * alpha) ^ i) * dl0 / 2 := by
        rw [← Finset.sum_div, ← Finset.sum_mul]
    _ = ((4 * alpha) ^ n - 1) / (4 * alpha - 1) * dl0 / 2 := by rw [hgeom]
    _ ≤ (4 * alpha) ^ n / (4 * alpha - 1) * dl0 / 2 := by
        have := mul_le_mul_of_nonneg_right h6 hdl0
        linarith
    _ ≤ 1 / 2 := by
        have hA : (4 * alpha) ^ n / (4 * alpha - 1) * dl0 / 2
            = ((4 * alpha) ^ n * dl0) / (4 * alpha - 1) / 2 := by ring
        rw [hA, div_le_iff₀ (by norm_num : (0:ℝ) < 2), div_le_iff₀ hden]
        nlinarith [hnum, hα26]

/-- Paper, step 2.3: `δ_d < 2(4α)^d δ₀` for `d ≤ s`. -/
theorem qIter_upper (q : ℕ → ℝ) (hq : ∀ d, q (d + 1) = qstep (q d))
    (h0 : 0 ≤ q 0) (h1 : q 0 ≤ 1 - alpha) (s : ℕ)
    (hs : (4 * alpha) ^ s * qdev q 0 ≤ alpha / 8) :
    ∀ d, d ≤ s → qdev q d ≤ 2 * (4 * alpha) ^ d * qdev q 0 := by
  have hdl0 : 0 ≤ qdev q 0 := (qIter_basic q hq h0 h1 0).2.2
  have hA : (0:ℝ) < 4 * alpha := four_alpha_pos
  have hA1 : (1:ℝ) ≤ 4 * alpha := le_of_lt one_lt_four_alpha
  have hbasic := qIter_basic q hq h0 h1
  have hprod2 : ∀ d, d ≤ s → ∏ i ∈ Finset.range d, (1 + (4 * alpha) ^ i * qdev q 0 / 2) ≤ 2 := by
    intro d hd
    apply prod_one_add_le
    · intro i
      have : (0:ℝ) ≤ (4 * alpha) ^ i * qdev q 0 :=
        mul_nonneg (pow_nonneg (le_of_lt hA) i) hdl0
      linarith
    · exact qsum_geom (qdev q 0) hdl0 hd hs
  have main : ∀ d, d ≤ s → qdev q d
      ≤ (4 * alpha) ^ d * qdev q 0
        * ∏ i ∈ Finset.range d, (1 + (4 * alpha) ^ i * qdev q 0 / 2) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ n ih =>
        intro hns
        have hns' : n ≤ s := by omega
        obtain ⟨-, -, hnn⟩ := hbasic n
        have hb : qdev q n ≤ 2 * (4 * alpha) ^ n * qdev q 0 := by
          have hp := ih hns'
          have hpn : (0:ℝ) ≤ (4 * alpha) ^ n * qdev q 0 :=
            mul_nonneg (pow_nonneg (le_of_lt hA) n) hdl0
          calc qdev q n
              ≤ (4 * alpha) ^ n * qdev q 0
                * ∏ i ∈ Finset.range n, (1 + (4 * alpha) ^ i * qdev q 0 / 2) := hp
            _ ≤ (4 * alpha) ^ n * qdev q 0 * 2 :=
                mul_le_mul_of_nonneg_left (hprod2 n hns') hpn
            _ = 2 * (4 * alpha) ^ n * qdev q 0 := by ring
        have hpow : (4 * alpha) ^ n * qdev q 0 ≤ (4 * alpha) ^ s * qdev q 0 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 hns') hdl0
        have hn4 : qdev q n ≤ alpha / 4 := by linarith [hb, hpow, hs]
        have hstep := errD_le hnn hn4
        rw [show (1 - alpha) - qdev q n = q n from by unfold qdev; ring] at hstep
        rw [show qdev q (n + 1) = (1 - alpha) - qstep (q n) from by
          unfold qdev; rw [hq n]]
        have hincr : 1 + qdev q n / 4 ≤ 1 + (4 * alpha) ^ n * qdev q 0 / 2 := by linarith
        have hfac : (0:ℝ) ≤ 1 + qdev q n / 4 := by linarith
        have hfac2 : (0:ℝ) ≤ 1 + (4 * alpha) ^ n * qdev q 0 / 2 := by linarith
        have hstep2 : 4 * alpha * (1 + qdev q n / 4) * qdev q n
            ≤ 4 * alpha * (1 + (4 * alpha) ^ n * qdev q 0 / 2) * qdev q n := by
          apply mul_le_mul_of_nonneg_right _ hnn
          exact mul_le_mul_of_nonneg_left hincr (le_of_lt hA)
        have hstep3 : 4 * alpha * (1 + (4 * alpha) ^ n * qdev q 0 / 2) * qdev q n
            ≤ 4 * alpha * (1 + (4 * alpha) ^ n * qdev q 0 / 2)
              * ((4 * alpha) ^ n * qdev q 0
                * ∏ i ∈ Finset.range n, (1 + (4 * alpha) ^ i * qdev q 0 / 2)) := by
          apply mul_le_mul_of_nonneg_left (ih hns')
          exact mul_nonneg (le_of_lt hA) hfac2
        calc (1 - alpha) - qstep (q n)
            ≤ 4 * alpha * (1 + qdev q n / 4) * qdev q n := hstep
          _ ≤ 4 * alpha * (1 + (4 * alpha) ^ n * qdev q 0 / 2) * qdev q n := hstep2
          _ ≤ 4 * alpha * (1 + (4 * alpha) ^ n * qdev q 0 / 2)
              * ((4 * alpha) ^ n * qdev q 0
                * ∏ i ∈ Finset.range n, (1 + (4 * alpha) ^ i * qdev q 0 / 2)) := hstep3
          _ = (4 * alpha) ^ (n + 1) * qdev q 0
                * ∏ i ∈ Finset.range (n + 1), (1 + (4 * alpha) ^ i * qdev q 0 / 2) := by
              rw [Finset.prod_range_succ]; ring
  intro d hd
  have hp := main d hd
  have hpn : (0:ℝ) ≤ (4 * alpha) ^ d * qdev q 0 :=
    mul_nonneg (pow_nonneg (le_of_lt hA) d) hdl0
  calc qdev q d
      ≤ (4 * alpha) ^ d * qdev q 0
        * ∏ i ∈ Finset.range d, (1 + (4 * alpha) ^ i * qdev q 0 / 2) := hp
    _ ≤ (4 * alpha) ^ d * qdev q 0 * 2 := mul_le_mul_of_nonneg_left (hprod2 d hd) hpn
    _ = 2 * (4 * alpha) ^ d * qdev q 0 := by ring

/-- Eq. (24), second inequality: `δ_s ≥ (4α)^s δ₀`. -/
theorem qIter_eps_lower (q : ℕ → ℝ) (hq : ∀ d, q (d + 1) = qstep (q d))
    (h0 : 0 ≤ q 0) (h1 : q 0 ≤ 1 - alpha) (s : ℕ)
    (hs : (4 * alpha) ^ s * qdev q 0 ≤ alpha / 8) :
    (4 * alpha) ^ s * qdev q 0 ≤ qdev q s := by
  have hbasic := qIter_basic q hq h0 h1
  have hupper := qIter_upper q hq h0 h1 s hs
  have hA : (0:ℝ) < 4 * alpha := four_alpha_pos
  have key : ∀ n, n ≤ s →
      (4 * alpha) ^ n * qdev q 0 ≤ qdev q n := by
    intro n hn
    induction n with
    | zero => simp
    | succ m ih =>
        have hms : m ≤ s := by omega
        obtain ⟨-, -, hnn⟩ := hbasic m
        have hpow : (4 * alpha) ^ m * qdev q 0 ≤ (4 * alpha) ^ s * qdev q 0 :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (le_of_lt one_lt_four_alpha) hms)
            (qIter_basic q hq h0 h1 0).2.2
        have hm4 : qdev q m ≤ alpha / 4 := by linarith [hupper m hms, hpow, hs]
        have hge := errD_ge hnn hm4
        rw [show (1 - alpha) - qdev q m = q m from by unfold qdev; ring] at hge
        rw [show qdev q (m + 1) = (1 - alpha) - qstep (q m) from by
          unfold qdev; rw [hq m]]
        have hrec := ih hms
        calc (4 * alpha) ^ (m + 1) * qdev q 0
            = 4 * alpha * ((4 * alpha) ^ m * qdev q 0) := by ring
          _ ≤ 4 * alpha * qdev q m := mul_le_mul_of_nonneg_left hrec (le_of_lt hA)
          _ ≤ (1 - alpha) - qstep (q m) := hge
  exact key s (le_refl s)

/-- Eq. (24): the two bounds on `p_s` and `q_s`, which is the content of
Lemma 4 after the choice of `s`. -/
theorem pIter_qIter_bounds (p q : ℕ → ℝ) (hp : ∀ d, p (d + 1) = pstep (p d))
    (hq : ∀ d, q (d + 1) = qstep (q d))
    (hp0 : 0 ≤ p 0) (hpα : p 0 ≤ alpha) (hq0 : 0 ≤ q 0) (hq1 : q 0 ≤ 1 - alpha) (s : ℕ)
    (hε : (4 * alpha) ^ s * (alpha - p 0) ≤ alpha / 8)
    (hδ : (4 * alpha) ^ s * qdev q 0 ≤ alpha / 8) :
    p s ≤ alpha - (4 * alpha) ^ s * (alpha - p 0) / 2
      ∧ q s ≤ 1 - alpha - (4 * alpha) ^ s * qdev q 0
      ∧ (4 * alpha) ^ s * (alpha - p 0) / 2 ≤ alpha - p s
      ∧ (4 * alpha) ^ s * qdev q 0 ≤ qdev q s :=
  ⟨by linarith [pIter_eps_lower p hp hp0 hpα s hε],
   by have := qIter_eps_lower q hq hq0 hq1 s hδ; unfold qdev at *; linarith,
   pIter_eps_lower p hp hp0 hpα s hε,
   qIter_eps_lower q hq hq0 hq1 s hδ⟩



end

/-! ## Module `Eps` -/

section

/-
The initial error probabilities of Section 7 of Sergeev, *Economical formulae for
symmetric boolean functions* (2025): the sequences `p_d` and `q_d`, the deficits
`ε₀ = α - p₀` and `δ₀ = (1-α) - q₀`, the comparison `δ₀ ≤ ε₀ ≤ 8 δ₀` and the
lower bound `ε₀ = Ω(t/k)`.
-/

open scoped BigOperators



/-! ### The sequences `p_d` and `q_d` of error probabilities -/

/-- The error probability `p_d` of a `Δ_d` formula on a vector of weight `k - t`. -/
noncomputable def pSeq (n m k t : ℕ) : ℕ → ℝ
  | 0 => p0 n m k t
  | d + 1 => pstep (pSeq n m k t d)

/-- The error probability `q_d` of a `Δ_d` formula on a vector of weight `k + t`. -/
noncomputable def qSeq (n m k t : ℕ) : ℕ → ℝ
  | 0 => q0 n m k t
  | d + 1 => qstep (qSeq n m k t d)

theorem pSeq_zero (n m k t : ℕ) : pSeq n m k t 0 = p0 n m k t := rfl

theorem pSeq_succ (n m k t d : ℕ) : pSeq n m k t (d + 1) = pstep (pSeq n m k t d) := rfl

theorem qSeq_zero (n m k t : ℕ) : qSeq n m k t 0 = q0 n m k t := rfl

theorem qSeq_succ (n m k t d : ℕ) : qSeq n m k t (d + 1) = qstep (qSeq n m k t d) := rfl

/-- `p_d` evaluated on a vector of weight `k - t` is the sequence `pSeq`. -/
theorem pErr_eq_pSeq {n m k t : ℕ} (hn : 0 < n) (htk : t ≤ k) (hkn : k + t ≤ n)
    (d : ℕ) (x : Fin n → Bool) (hx : onesCount x = k - t) :
    pErr n m k d x = pSeq n m k t d := by
  induction d with
  | zero => exact pErr_zero_eq_p0 hn htk hkn x hx
  | succ d ih => rw [pErr_succ_mul hn, ih]; exact (pSeq_succ n m k t d).symm

/-- `q_d` evaluated on a vector of weight `k + t` is the sequence `qSeq`. -/
theorem qErr_eq_qSeq {n m k t : ℕ} (hn : 0 < n) (hkn : k + t ≤ n)
    (d : ℕ) (x : Fin n → Bool) (hx : onesCount x = k + t) :
    qErr n m k d x = qSeq n m k t d := by
  induction d with
  | zero => exact qErr_zero_eq_q0 hn hkn x hx
  | succ d ih => rw [qErr_succ_mul hn, ih]; exact (qSeq_succ n m k t d).symm

/-! ### The deficits `ε₀` and `δ₀` -/

/-- The deficit `ε₀ = α - p₀` of the fixed point `α`. -/
noncomputable def eps0 (n m k t : ℕ) : ℝ := alpha - p0 n m k t

/-- The deficit `δ₀ = (1-α) - q₀` of the fixed point `1-α`. -/
noncomputable def delta0 (n m k t : ℕ) : ℝ := (1 - alpha) - q0 n m k t

theorem qdev_qSeq_zero (n m k t : ℕ) : qdev (qSeq n m k t) 0 = delta0 n m k t := rfl

theorem one_sub_abase_pow_pos {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hm : m = n / k) : 0 < 1 - abase n k ^ m := by
  have h := abase_pow_le hn hk h2k hm
  linarith

theorem eps0_eq {n m k t : ℕ} (h : 1 - abase n k ^ m ≠ 0) :
    eps0 n m k t
      = alpha * ((abase n k + bshift n t) ^ m - abase n k ^ m) / (1 - abase n k ^ m) := by
  unfold eps0 p0
  field_simp
  ring

theorem delta0_eq {n m k t : ℕ} (h : 1 - abase n k ^ m ≠ 0) :
    delta0 n m k t
      = alpha * (abase n k ^ m - (abase n k - bshift n t) ^ m) / (1 - abase n k ^ m) := by
  unfold delta0 q0
  field_simp
  ring



end

/-! ## Module `EpsBounds` -/

section

/-
The estimates of Section 7 of Sergeev, *Economical formulae for symmetric boolean
functions* (2025) that feed Lemma 4: the Bernoulli-type inequalities
`(1+x)^m ≥ 1 + mx` and `(1-x)^m ≤ 1 - mx/3`, the elementary bounds `pstep x ≤ x`,
`qstep x ≤ x` on the relevant intervals, the location `0 ≤ p₀ ≤ α`,
`0 ≤ q₀ ≤ 1-α` of the initial error probabilities, the invariance of `[0,α]`
and `[0,1-α]` under `pstep` and `qstep`, and the two-sided bounds
`t/(128k) ≤ δ₀`, `t/(32k) ≤ ε₀` and `ε₀, δ₀ ≤ t/k` for the deficits
`ε₀ = α - p₀`, `δ₀ = (1-α) - q₀`.
-/

open scoped BigOperators



/-- Bernoulli-type estimate: if `m*x ≤ 2` and `0 ≤ x ≤ 1`, then
`(1-x)^m ≤ 1 - m*x/3`. -/
theorem one_sub_pow_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ m : ℕ, (m : ℝ) * x ≤ 2 → (m : ℝ) * x / 3 ≤ 1 - (1 - x) ^ m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hmx : (m : ℝ) * x ≤ 2 := by
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hm
        nlinarith [hx0]
      have ihx : (1 - x) ^ m ≤ 1 - (m : ℝ) * x / 3 := by
        have := ih hmx
        linarith
      have hx1m : 0 ≤ 1 - x := by linarith
      have hmono : (1 - x) ^ m * (1 - x) ≤ (1 - (m : ℝ) * x / 3) * (1 - x) :=
        mul_le_mul_of_nonneg_right ihx hx1m
      have hkey : (1 - (m : ℝ) * x / 3) * (1 - x) ≤ 1 - ((m : ℝ) + 1) * x / 3 := by
        have hx2 : (m : ℝ) * x ^ 2 ≤ 2 * x := by nlinarith
        nlinarith
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hstep : (1 - x) ^ (m + 1) = (1 - x) ^ m * (1 - x) := pow_succ _ _
      rw [hstep, hcast]
      linarith

/-- `pstep` is monotone on `[0,1]`. -/
theorem pstep_mono {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    pstep x ≤ pstep y := by
  have hprod : 0 ≤ (y - x) * (2 - x - y) :=
    mul_nonneg (by linarith) (by linarith)
  have hid : (1 - x) ^ 2 - (1 - y) ^ 2 = (y - x) * (2 - x - y) := by ring
  have hle : 1 - (1 - x) ^ 2 ≤ 1 - (1 - y) ^ 2 := by nlinarith
  have hidx : pstep x = (1 - (1 - x) ^ 2) ^ 2 := by unfold pstep; ring
  have hidy : pstep y = (1 - (1 - y) ^ 2) ^ 2 := by unfold pstep; ring
  rw [hidx, hidy]
  exact pow_le_pow_left₀ (by nlinarith) hle 2

/-- `x(2-x)^2` is monotone on `[0, 1/2]`. -/
theorem mul_sq_mono {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    x * (2 - x) ^ 2 ≤ y * (2 - y) ^ 2 := by
  have hfac : y * (2 - y) ^ 2 - x * (2 - x) ^ 2
      = (y - x) * (4 - 4 * (x + y) + x ^ 2 + x * y + y ^ 2) := by ring
  have hg : 0 ≤ 4 - 4 * (x + y) + x ^ 2 + x * y + y ^ 2 := by nlinarith
  nlinarith

/-- `pstep x ≤ x` on `[0, α]`. -/
theorem pstep_le_self {x : ℝ} (hx0 : 0 ≤ x) (hxα : x ≤ alpha) : pstep x ≤ x := by
  have hα : alpha ≤ 1 / 2 := le_of_lt alpha_lt_half
  have h : x * (2 - x) ^ 2 ≤ 1 := by
    have hm := mul_sq_mono hx0 hxα hα
    rw [alpha_mul_sq] at hm
    exact hm
  unfold pstep
  nlinarith [hx0, h]

/-- `qstep x ≤ x` on `[0, 1-α]`. -/
theorem qstep_le_self {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 - alpha) : qstep x ≤ x := by
  have hfac : qstep x - x = x * (1 - x) * (x ^ 2 + x - 1) := by unfold qstep; ring
  have h1 : 0 ≤ 1 - x := by linarith [alpha_pos]
  have h2 : x ^ 2 + x - 1 ≤ 0 := by
    have hsq : x ^ 2 ≤ (1 - alpha) ^ 2 := by nlinarith
    nlinarith [one_sub_alpha_sq]
  have h3 : 0 ≤ x * (1 - x) := mul_nonneg hx0 h1
  have : x * (1 - x) * (x ^ 2 + x - 1) ≤ 0 := by nlinarith
  linarith [hfac]

theorem alpha_le_two_fifths : alpha ≤ 2 / 5 := by
  unfold alpha
  have h : (11/5 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- `y^m - x^m ≤ m (y - x)` for `0 ≤ x ≤ y ≤ 1`. -/
theorem pow_sub_pow_le {m : ℕ} {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    y ^ m - x ^ m ≤ (m : ℝ) * (y - x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : y ^ (m + 1) - x ^ (m + 1) = y * (y ^ m - x ^ m) + x ^ m * (y - x) := by ring
      have hy0 : 0 ≤ y := le_trans hx0 hxy
      have h1 : y * (y ^ m - x ^ m) ≤ y * ((m : ℝ) * (y - x)) :=
        mul_le_mul_of_nonneg_left ih hy0
      have h2 : x ^ m * (y - x) ≤ 1 * (y - x) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (n := m) hx0 (le_trans hxy hy1)) (by linarith)
      have h3 : y * ((m : ℝ) * (y - x)) ≤ (m : ℝ) * (y - x) := by
        have h4 : 0 ≤ (m : ℝ) * (y - x) := mul_nonneg (Nat.cast_nonneg m) (by linarith)
        nlinarith
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hstep, hcast]
      nlinarith

/-- `1 - a^m ≤ m (1 - a)` for `0 ≤ a ≤ 1`. -/
theorem one_sub_pow_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (m : ℕ) :
    1 - a ^ m ≤ (m : ℝ) * (1 - a) := by
  have hgeom : (1 - a) * ∑ i ∈ Finset.range m, a ^ i = 1 - a ^ m := by
    have h := geom_sum_mul a m
    linear_combination -h
  have hle : ∑ i ∈ Finset.range m, a ^ i ≤ (m : ℝ) := by
    have : ∀ i ∈ Finset.range m, a ^ i ≤ (1 : ℝ) := fun i _ => pow_le_one₀ (n := i) ha0 ha1
    calc ∑ i ∈ Finset.range m, a ^ i ≤ ∑ _i ∈ Finset.range m, (1:ℝ) := Finset.sum_le_sum this
      _ = (m : ℝ) := by simp
  have h1a : 0 ≤ 1 - a := by linarith
  rw [← hgeom]
  nlinarith

/-- `(a+b)^m ≤ 1` and friends. -/
theorem abase_add_bshift_le_one {n k t : ℕ} (hn : 0 < n) (htk : t ≤ k) (hkn : k + t ≤ n) :
    abase n k + bshift n t ≤ 1 := by
  rw [abase_add_bshift hn htk hkn]
  have h : (0:ℝ) ≤ ((k - t : ℕ) : ℝ) / (n : ℝ) := by positivity
  linarith

theorem bshift_nonneg (n t : ℕ) : 0 ≤ bshift n t := by
  unfold bshift; positivity

theorem p0_nonneg {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) : 0 ≤ p0 n m k t := by
  have ha0 : 0 ≤ abase n k := le_of_lt (abase_pos hn h2k)
  have hb0 : 0 ≤ bshift n t := bshift_nonneg n t
  have hp : (abase n k + bshift n t) ^ m ≤ 1 :=
    pow_le_one₀ (n := m) (by linarith) (abase_add_bshift_le_one hn htk hkn)
  have hne : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn (by omega) h2k hm
  unfold p0
  apply div_nonneg
  · exact mul_nonneg (le_of_lt alpha_pos) (by linarith)
  · linarith

theorem p0_le_alpha {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (_hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) : p0 n m k t ≤ alpha := by
  have ha0 : 0 ≤ abase n k := le_of_lt (abase_pos hn h2k)
  have hb0 : 0 ≤ bshift n t := bshift_nonneg n t
  have hne : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn (by omega) h2k hm
  have hle : abase n k ^ m ≤ (abase n k + bshift n t) ^ m :=
    pow_le_pow_left₀ ha0 (by linarith) m
  unfold p0
  rw [div_le_iff₀ hne]
  nlinarith [alpha_pos]

theorem q0_le {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) : q0 n m k t ≤ 1 - alpha := by
  have ha0 : 0 ≤ abase n k := le_of_lt (abase_pos hn h2k)
  have hsub : 0 ≤ abase n k - bshift n t := by
    have := bshift_le_abase hn hkn; linarith
  have hne : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn (by omega) h2k hm
  have hle : (abase n k - bshift n t) ^ m ≤ abase n k ^ m :=
    pow_le_pow_left₀ hsub (by linarith [bshift_nonneg n t]) m
  have hA : alpha ≤ alpha * (1 - (abase n k - bshift n t) ^ m) / (1 - abase n k ^ m) := by
    rw [le_div_iff₀ hne]
    nlinarith [alpha_pos]
  unfold q0
  linarith

theorem q0_nonneg {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) : 0 ≤ q0 n m k t := by
  have ha0 : 0 ≤ abase n k := le_of_lt (abase_pos hn h2k)
  have hsub : 0 ≤ abase n k - bshift n t := by
    have := bshift_le_abase hn hkn; linarith
  have hpm : (abase n k - bshift n t) ^ m ≤ 1 :=
    pow_le_one₀ (n := m) hsub (by linarith [abase_le_one n k, bshift_nonneg n t])
  have hne : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn (by omega) h2k hm
  have hden : (2/5 : ℝ) ≤ 1 - abase n k ^ m := by
    have := abase_pow_le hn (by omega) h2k hm; linarith
  unfold q0
  have h1 : alpha * (1 - (abase n k - bshift n t) ^ m) ≤ 1 - abase n k ^ m := by
    have h2 : alpha * (1 - (abase n k - bshift n t) ^ m) ≤ alpha := by
      have hx : 1 - (abase n k - bshift n t) ^ m ≤ 1 := by
        linarith [pow_nonneg hsub m]
      nlinarith [alpha_pos]
    linarith [alpha_le_two_fifths]
  have := div_le_one_of_le₀ h1 (le_of_lt hne)
  linarith [this]

/-! ### The ranges of the sequences `p_d` and `q_d` -/

theorem pSeq_nonneg {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) (d : ℕ) :
    0 ≤ pSeq n m k t d := by
  induction d with
  | zero => simpa [pSeq_zero] using p0_nonneg hn ht htk hkn h2k hm
  | succ d ih => rw [pSeq_succ]; exact pstep_nonneg _

theorem pSeq_le_alpha {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) (d : ℕ) :
    pSeq n m k t d ≤ alpha := by
  induction d with
  | zero => simpa [pSeq_zero] using p0_le_alpha hn ht htk hkn h2k hm
  | succ d ih =>
      rw [pSeq_succ, ← alpha_fixed]
      exact pstep_mono (pSeq_nonneg hn ht htk hkn h2k hm d) ih alpha_lt_one.le

theorem qSeq_range {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) (d : ℕ) :
    0 ≤ qSeq n m k t d ∧ qSeq n m k t d ≤ 1 - alpha := by
  induction d with
  | zero =>
      exact ⟨by simpa [qSeq_zero] using q0_nonneg hn ht htk hkn h2k hm,
        by simpa [qSeq_zero] using q0_le hn ht htk hkn h2k hm⟩
  | succ d ih =>
      obtain ⟨h0, h1⟩ := ih
      rw [qSeq_succ]
      have h1' : qSeq n m k t d ≤ 1 := by linarith [alpha_pos]
      refine ⟨qstep_nonneg h0 h1', ?_⟩
      rw [← qstep_fixed]
      exact qstep_mono h1 h0 (by linarith [alpha_pos])

theorem qSeq_le {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) (d : ℕ) :
    qSeq n m k t d ≤ 1 - alpha :=
  (qSeq_range hn ht htk hkn h2k hm d).2

theorem qSeq_nonneg {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) (d : ℕ) :
    0 ≤ qSeq n m k t d :=
  (qSeq_range hn ht htk hkn h2k hm d).1

/-! ### Two-sided bounds for the deficits `ε₀` and `δ₀` -/

theorem m_pos {n m k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hm : m = n / k) : 0 < m := by
  rw [hm]
  exact Nat.div_pos hkn hk

theorem eps0_upper {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    eps0 n m k t ≤ (t : ℝ) / k := by
  have hk : 0 < k := by omega
  have ha0 : 0 ≤ abase n k := le_of_lt (abase_pos hn h2k)
  have hden : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn hk h2k hm
  have hden45 : (2 / 5 : ℝ) ≤ 1 - abase n k ^ m := by
    have := abase_pow_le hn hk h2k hm
    linarith
  have hX : (abase n k + bshift n t) ^ m - abase n k ^ m ≤ (m : ℝ) * bshift n t := by
    have h := pow_sub_pow_le (m := m) (x := abase n k) (y := abase n k + bshift n t)
      ha0 (by linarith [bshift_nonneg n t]) (abase_add_bshift_le_one hn htk hkn)
    rwa [show abase n k + bshift n t - abase n k = bshift n t by ring] at h
  have hmb : (m : ℝ) * bshift n t ≤ (t : ℝ) / k := by
    have hle : (m : ℝ) ≤ (n : ℝ) / k := by
      rw [hm]
      exact Nat.cast_div_le
    have h1 : (m : ℝ) * ((t : ℝ) / n) ≤ ((n : ℝ) / k) * ((t : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    have h2 : ((n : ℝ) / k) * ((t : ℝ) / n) = (t : ℝ) / k := by
      have hn' : (n : ℝ) ≠ 0 := by positivity
      have hk' : (k : ℝ) ≠ 0 := by positivity
      field_simp
    unfold bshift
    linarith [h1, h2.symm]
  rw [eps0_eq (ne_of_gt hden), div_le_iff₀ hden]
  have h1 : alpha * ((abase n k + bshift n t) ^ m - abase n k ^ m) ≤ alpha * ((t : ℝ) / k) :=
    mul_le_mul_of_nonneg_left (le_trans hX hmb) (le_of_lt alpha_pos)
  have h2 : alpha * ((t : ℝ) / k) ≤ ((t : ℝ) / k) * (1 - abase n k ^ m) := by
    have htk0 : 0 ≤ (t : ℝ) / k := by positivity
    nlinarith [five_alpha_le_two, hden45, htk0]
  linarith

theorem delta0_upper {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    delta0 n m k t ≤ (t : ℝ) / k := by
  have hk : 0 < k := by omega
  have hsub : 0 ≤ abase n k - bshift n t := by
    have := bshift_le_abase hn hkn; linarith
  have hden : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn hk h2k hm
  have hX : abase n k ^ m - (abase n k - bshift n t) ^ m ≤ (m : ℝ) * bshift n t := by
    have h := pow_sub_pow_le (m := m) (x := abase n k - bshift n t) (y := abase n k)
      hsub (by linarith [bshift_nonneg n t]) (abase_le_one n k)
    rwa [show abase n k - (abase n k - bshift n t) = bshift n t by ring] at h
  have hmb : (m : ℝ) * bshift n t ≤ (t : ℝ) / k := by
    have hle : (m : ℝ) ≤ (n : ℝ) / k := by
      rw [hm]
      exact Nat.cast_div_le
    have h1 : (m : ℝ) * ((t : ℝ) / n) ≤ ((n : ℝ) / k) * ((t : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    have h2 : ((n : ℝ) / k) * ((t : ℝ) / n) = (t : ℝ) / k := by
      have hn' : (n : ℝ) ≠ 0 := by positivity
      have hk' : (k : ℝ) ≠ 0 := by positivity
      field_simp
    unfold bshift
    linarith [h1, h2.symm]
  have hden45 : (2 / 5 : ℝ) ≤ 1 - abase n k ^ m := by
    have := abase_pow_le hn hk h2k hm
    linarith
  rw [delta0_eq (ne_of_gt hden), div_le_iff₀ hden]
  have h1 : alpha * (abase n k ^ m - (abase n k - bshift n t) ^ m) ≤ alpha * ((t : ℝ) / k) :=
    mul_le_mul_of_nonneg_left (le_trans hX hmb) (le_of_lt alpha_pos)
  have h2 : alpha * ((t : ℝ) / k) ≤ ((t : ℝ) / k) * (1 - abase n k ^ m) := by
    have htk0 : 0 ≤ (t : ℝ) / k := by positivity
    nlinarith [five_alpha_le_two, hden45, htk0]
  linarith

theorem eps0_lower {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (_hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    (t : ℝ) / (32 * k) ≤ eps0 n m k t := by
  have hk : 0 < k := by omega
  have ha0 : 0 < abase n k := abase_pos hn h2k
  have ha1 : abase n k ≤ 1 := abase_le_one n k
  have hb0 : 0 < bshift n t := bshift_pos hn ht
  have hden : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn hk h2k hm
  have ham : (1 / 8 : ℝ) ≤ abase n k ^ m :=
    abase_pow_ge (n := n) (k := k) (m := m) hn h2k (by rw [hm]; exact Nat.div_mul_le_self n k)
  have h24 : (1 / 24 : ℝ) ≤ alpha * abase n k ^ m := by
    have h1 := mul_le_mul alpha_ge_third ham (by norm_num) (le_trans (by norm_num) alpha_ge_third)
    linarith
  have hbdiv : bshift n t ≤ bshift n t / abase n k := by
    rw [le_div_iff₀ ha0]
    nlinarith
  have hX : abase n k ^ m * ((m : ℝ) * bshift n t)
      ≤ (abase n k + bshift n t) ^ m - abase n k ^ m := by
    have hbern : 1 + (m : ℝ) * (bshift n t / abase n k)
        ≤ (1 + bshift n t / abase n k) ^ m :=
      one_add_mul_le_pow (by
        have hr : 0 ≤ bshift n t / abase n k := le_of_lt (div_pos hb0 ha0)
        linarith) m
    have hfac : abase n k * (1 + bshift n t / abase n k) = abase n k + bshift n t := by
      field_simp
    have h1 : abase n k ^ m * (1 + (m : ℝ) * (bshift n t / abase n k))
        ≤ (abase n k + bshift n t) ^ m := by
      calc abase n k ^ m * (1 + (m : ℝ) * (bshift n t / abase n k))
          ≤ abase n k ^ m * (1 + bshift n t / abase n k) ^ m :=
            mul_le_mul_of_nonneg_left hbern (pow_nonneg ha0.le m)
        _ = (abase n k * (1 + bshift n t / abase n k)) ^ m := by rw [mul_pow]
        _ = (abase n k + bshift n t) ^ m := by rw [hfac]
    have h2 : abase n k ^ m * ((m : ℝ) * bshift n t)
        ≤ abase n k ^ m * ((m : ℝ) * (bshift n t / abase n k)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha0.le m)
      nlinarith [hbdiv]
    nlinarith [h1, h2, pow_nonneg ha0.le m]
  have hone : 1 - abase n k ^ m ≤ (m : ℝ) * (k : ℝ) / n := by
    have h := one_sub_pow_le (abase n k) ha0.le ha1 m
    have h1 : (m : ℝ) * (1 - abase n k) = (m : ℝ) * (k : ℝ) / n := by
      rw [abase_sub_eq]
      field_simp
    linarith [h, h1.symm]
  have hmain : (t : ℝ) / (32 * k) * ((m : ℝ) * (k : ℝ) / n)
      ≤ alpha * (abase n k ^ m * ((m : ℝ) * bshift n t)) := by
    have h1 : alpha * (abase n k ^ m * ((m : ℝ) * bshift n t))
        = (alpha * abase n k ^ m) * ((m : ℝ) * (t : ℝ) / n) := by
      unfold bshift
      field_simp
    have h2 : (t : ℝ) / (32 * k) * ((m : ℝ) * (k : ℝ) / n)
        = (1 / 32 : ℝ) * ((m : ℝ) * (t : ℝ) / n) := by
      field_simp
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (le_trans (by norm_num) h24) (by positivity)
  have hstep : (t : ℝ) / (32 * k) * (1 - abase n k ^ m)
      ≤ (t : ℝ) / (32 * k) * ((m : ℝ) * (k : ℝ) / n) :=
    mul_le_mul_of_nonneg_left hone (by positivity)
  have hXα : alpha * (abase n k ^ m * ((m : ℝ) * bshift n t))
      ≤ alpha * ((abase n k + bshift n t) ^ m - abase n k ^ m) :=
    mul_le_mul_of_nonneg_left hX alpha_nonneg
  rw [eps0_eq (ne_of_gt hden), le_div_iff₀ hden]
  linarith [hstep, hmain, hXα]

theorem delta0_lower {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    (t : ℝ) / (128 * k) ≤ delta0 n m k t := by
  have hk : 0 < k := by omega
  have ha0 : 0 < abase n k := abase_pos hn h2k
  have ha1 : abase n k ≤ 1 := abase_le_one n k
  have hb0 : 0 < bshift n t := bshift_pos hn ht
  have hden : 0 < 1 - abase n k ^ m := one_sub_abase_pow_pos hn hk h2k hm
  have ham : (1 / 8 : ℝ) ≤ abase n k ^ m :=
    abase_pow_ge (n := n) (k := k) (m := m) hn h2k (by rw [hm]; exact Nat.div_mul_le_self n k)
  have hbdiv : bshift n t ≤ bshift n t / abase n k := by
    rw [le_div_iff₀ ha0]
    nlinarith
  have hdiv1 : bshift n t / abase n k ≤ 1 := by
    rw [div_le_one ha0]
    exact bshift_le_abase hn hkn
  have hmdiv : (m : ℝ) * (bshift n t / abase n k) ≤ 2 := by
    have hle : (m : ℝ) ≤ (n : ℝ) / k := by
      rw [hm]
      exact Nat.cast_div_le
    have hz0 : 0 ≤ bshift n t / abase n k := le_of_lt (div_pos hb0 ha0)
    have step1 := mul_le_mul_of_nonneg_right hle hz0
    have heq : ((n : ℝ) / k) * (bshift n t / abase n k) = (t : ℝ) / ((k : ℝ) * abase n k) := by
      unfold bshift
      field_simp
    have hta : (t : ℝ) / ((k : ℝ) * abase n k) ≤ 2 := by
      have hka : (0 : ℝ) < (k : ℝ) * abase n k := by positivity
      rw [div_le_iff₀ hka]
      have htk' : (t : ℝ) ≤ (k : ℝ) := by exact_mod_cast htk
      have h2a : (1 : ℝ) ≤ 2 * abase n k := by nlinarith [abase_half hn h2k]
      nlinarith
    linarith [step1, heq.symm, hta]
  have hbern : (m : ℝ) * (bshift n t / abase n k) / 3
      ≤ 1 - (1 - bshift n t / abase n k) ^ m :=
    one_sub_pow_ge (le_of_lt (div_pos hb0 ha0)) hdiv1 m hmdiv
  have hfac : abase n k - bshift n t = abase n k * (1 - bshift n t / abase n k) := by
    field_simp
  have hpow : (abase n k - bshift n t) ^ m
      = abase n k ^ m * (1 - bshift n t / abase n k) ^ m := by
    rw [hfac, mul_pow]
  have hlow : abase n k ^ m * ((m : ℝ) * bshift n t / 3)
      ≤ abase n k ^ m - (abase n k - bshift n t) ^ m := by
    have hkey : (m : ℝ) * bshift n t / 3
        ≤ 1 - (1 - bshift n t / abase n k) ^ m := by
      have h2 : (m : ℝ) * bshift n t / 3
          ≤ (m : ℝ) * (bshift n t / abase n k) / 3 := by
        have := mul_le_mul_of_nonneg_left hbdiv (Nat.cast_nonneg m)
        linarith
      linarith
    rw [hpow]
    have heq : abase n k ^ m - abase n k ^ m * (1 - bshift n t / abase n k) ^ m
        = abase n k ^ m * (1 - (1 - bshift n t / abase n k) ^ m) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hkey (pow_nonneg ha0.le m)
  have hone : 1 - abase n k ^ m ≤ (m : ℝ) * (k : ℝ) / n := by
    have h := one_sub_pow_le (abase n k) ha0.le ha1 m
    have h1 : (m : ℝ) * (1 - abase n k) = (m : ℝ) * (k : ℝ) / n := by
      rw [abase_sub_eq]
      field_simp
    linarith [h, h1.symm]
  have hmain : (t : ℝ) / (128 * k) * ((m : ℝ) * (k : ℝ) / n)
      ≤ alpha * (abase n k ^ m * ((m : ℝ) * bshift n t / 3)) := by
    have h1 : alpha * (abase n k ^ m * ((m : ℝ) * bshift n t / 3))
        = (alpha * abase n k ^ m / 3) * ((m : ℝ) * (t : ℝ) / n) := by
      unfold bshift
      field_simp
    have h2 : (t : ℝ) / (128 * k) * ((m : ℝ) * (k : ℝ) / n)
        = (1 / 128 : ℝ) * ((m : ℝ) * (t : ℝ) / n) := by
      field_simp
    rw [h1, h2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h3 := mul_le_mul alpha_ge_third ham (by norm_num) (le_trans (by norm_num) alpha_ge_third)
    linarith
  have hstep : (t : ℝ) / (128 * k) * (1 - abase n k ^ m)
      ≤ (t : ℝ) / (128 * k) * ((m : ℝ) * (k : ℝ) / n) :=
    mul_le_mul_of_nonneg_left hone (by positivity)
  have hXα : alpha * (abase n k ^ m * ((m : ℝ) * bshift n t / 3))
      ≤ alpha * (abase n k ^ m - (abase n k - bshift n t) ^ m) :=
    mul_le_mul_of_nonneg_left hlow alpha_nonneg
  rw [delta0_eq (ne_of_gt hden), le_div_iff₀ hden]
  linarith [hstep, hmain, hXα]



end

/-! ## Module `Lemma4` -/

section

/-
Lemma 4 of Section 7 of Sergeev, *Economical formulae for symmetric boolean
functions* (2025): for some `s ≤ log_{4α}(k/t) + 1` the error probabilities
satisfy `p_s < α - γ` and `q_s < 1 - α - γ` for a positive constant `γ`
(here an explicit `γ = 1/64` together with the rounding of `s`).
-/



noncomputable def sLem4 (k t : ℕ) : ℕ :=
  Nat.floor (Real.logb (4 * alpha) ((alpha * (k : ℝ)) / (8 * (t : ℝ))))

theorem sLem4_arg_pos {k t : ℕ} (hk : 0 < k) (ht : 0 < t) :
    0 < (alpha * (k : ℝ)) / (8 * (t : ℝ)) := by
  have hk' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ht' : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  exact div_pos (mul_pos alpha_pos hk') (by positivity)

theorem four_alpha_pow_sLem4_le {k t : ℕ} (hk : 0 < k) (ht : 0 < t)
    (hX : 1 ≤ (alpha * (k : ℝ)) / (8 * (t : ℝ))) :
    (4 * alpha) ^ (sLem4 k t) ≤ (alpha * (k : ℝ)) / (8 * (t : ℝ)) := by
  have hb : 1 < 4 * alpha := one_lt_four_alpha
  have hXpos : 0 < (alpha * (k : ℝ)) / (8 * (t : ℝ)) := sLem4_arg_pos hk ht
  have h := (Real.le_logb_iff_rpow_le hb hXpos).mp
    (Nat.floor_le (Real.logb_nonneg hb hX))
  rwa [Real.rpow_natCast] at h

theorem four_alpha_pow_sLem4_gt {k t : ℕ} (hk : 0 < k) (ht : 0 < t) :
    (alpha * (k : ℝ)) / (8 * (t : ℝ)) / (4 * alpha) < (4 * alpha) ^ (sLem4 k t) := by
  have hb : 1 < 4 * alpha := one_lt_four_alpha
  have hXpos : 0 < (alpha * (k : ℝ)) / (8 * (t : ℝ)) := sLem4_arg_pos hk ht
  have hstep := Nat.lt_floor_add_one
    (Real.logb (4 * alpha) ((alpha * (k : ℝ)) / (8 * (t : ℝ))))
  have hlt : (alpha * (k : ℝ)) / (8 * (t : ℝ)) < (4 * alpha) ^ ((sLem4 k t : ℝ) + 1) :=
    (Real.logb_lt_iff_lt_rpow hb hXpos).mp hstep
  rw [Real.rpow_add (by positivity : (0:ℝ) < 4 * alpha), Real.rpow_one,
    Real.rpow_natCast] at hlt
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < 4 * alpha)]
  linarith

theorem sLem4_eq_zero {k t : ℕ} (hk : 0 < k) (ht : 0 < t)
    (hX : (alpha * (k : ℝ)) / (8 * (t : ℝ)) < 1) : sLem4 k t = 0 := by
  have hb : 1 < 4 * alpha := one_lt_four_alpha
  rw [sLem4, Nat.floor_eq_zero]
  refine (Real.logb_lt_iff_lt_rpow hb (sLem4_arg_pos hk ht)).mpr ?_
  rw [Real.rpow_one]
  linarith

theorem sLem4_le_log {k t : ℕ} (hk : 0 < k) (ht : 0 < t) (htk : t ≤ k) :
    (sLem4 k t : ℝ) ≤ Real.logb (4 * alpha) ((k : ℝ) / t) + 1 := by
  have hb : 1 < 4 * alpha := one_lt_four_alpha
  have ht' : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hk' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hquot : (1:ℝ) ≤ (k:ℝ) / t := by
    rw [le_div_iff₀ ht']
    rw [one_mul]
    exact_mod_cast htk
  by_cases hX : 1 ≤ (alpha * (k : ℝ)) / (8 * (t : ℝ))
  · have hle : (sLem4 k t : ℝ)
        ≤ Real.logb (4 * alpha) ((alpha * (k : ℝ)) / (8 * (t : ℝ))) :=
      Nat.floor_le (Real.logb_nonneg hb hX)
    have hsplit : Real.logb (4 * alpha) ((alpha * (k : ℝ)) / (8 * (t : ℝ)))
        = Real.logb (4 * alpha) ((k :ℝ) / t) + Real.logb (4 * alpha) (alpha / 8) := by
      have heq : (alpha * (k : ℝ)) / (8 * (t : ℝ)) = ((k :ℝ) / t) * (alpha / 8) := by
        field_simp
      have h1 : ((k : ℝ) / t) ≠ 0 := div_ne_zero (ne_of_gt hk') (by exact_mod_cast ht.ne')
      have h2 : alpha / 8 ≠ 0 := ne_of_gt (by linarith [alpha_pos])
      rw [heq]
      exact Real.logb_mul (b := 4 * alpha) (x := (k : ℝ) / t) (y := alpha / 8) h1 h2
    have hneg : Real.logb (4 * alpha) (alpha / 8) ≤ 0 :=
      Real.logb_nonpos (b := 4 * alpha) (x := alpha / 8) one_lt_four_alpha
        (by linarith [alpha_pos]) (by linarith [alpha_lt_one])
    calc (sLem4 k t : ℝ)
        ≤ Real.logb (4 * alpha) ((alpha * (k : ℝ)) / (8 * (t : ℝ))) := hle
      _ = Real.logb (4 * alpha) ((k :ℝ) / t) + Real.logb (4 * alpha) (alpha / 8) := hsplit
      _ ≤ Real.logb (4 * alpha) ((k : ℝ) / t) + 1 := by linarith
  · rw [sLem4_eq_zero hk ht (by linarith [hX])]
    push_cast
    have hquot' : (0:ℝ) ≤ Real.logb (4 * alpha) ((k : ℝ) / t) :=
      Real.logb_nonneg hb hquot
    linarith

theorem lemma4 {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    pSeq n m k t (sLem4 k t) ≤ alpha - 1 / 2048 ∧
    qSeq n m k t (sLem4 k t) ≤ 1 - alpha - 1 / 4096 := by
  have hk : 0 < k := by omega
  have hk' : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ht' : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  by_cases hX : 1 ≤ (alpha * (k : ℝ)) / (8 * (t : ℝ))
  · have hpow := four_alpha_pow_sLem4_le hk ht hX
    have hXnn : (0:ℝ) ≤ (alpha * (k : ℝ)) / (8 * (t : ℝ)) := le_of_lt (sLem4_arg_pos hk ht)
    have hε0nn : 0 ≤ eps0 n m k t := by
      unfold eps0; linarith [p0_le_alpha hn ht htk hkn h2k hm]
    have hδ0nn : 0 ≤ delta0 n m k t := by
      unfold delta0; linarith [q0_le hn ht htk hkn h2k hm]
    have heq : (alpha * (k : ℝ)) / (8 * (t : ℝ)) * ((t : ℝ) / k) = alpha / 8 := by
      field_simp
    have hε : (4 * alpha) ^ (sLem4 k t) * (alpha - pSeq n m k t 0) ≤ alpha / 8 := by
      have hsame : alpha - pSeq n m k t 0 = eps0 n m k t := rfl
      rw [hsame]
      have hmul := mul_le_mul hpow (eps0_upper hn ht htk hkn h2k hm) hε0nn hXnn
      linarith [hmul, heq]
    have hδ : (4 * alpha) ^ (sLem4 k t) * qdev (qSeq n m k t) 0 ≤ alpha / 8 := by
      have hsame : qdev (qSeq n m k t) 0 = delta0 n m k t := rfl
      rw [hsame]
      have hmul := mul_le_mul hpow (delta0_upper hn ht htk hkn h2k hm) hδ0nn hXnn
      linarith [hmul, heq]
    have hb := pIter_qIter_bounds (pSeq n m k t) (qSeq n m k t)
      (fun d => pSeq_succ n m k t d) (fun d => qSeq_succ n m k t d)
      (pSeq_nonneg hn ht htk hkn h2k hm 0) (pSeq_le_alpha hn ht htk hkn h2k hm 0)
      (qSeq_nonneg hn ht htk hkn h2k hm 0) (qSeq_le hn ht htk hkn h2k hm 0)
      (sLem4 k t) hε hδ
    have hgt := four_alpha_pow_sLem4_gt hk ht
    have ha : alpha ≠ 0 := ne_of_gt alpha_pos
    have hge : (alpha * (k : ℝ)) / (8 * (t : ℝ)) / (4 * alpha) = (k:ℝ)/(32*(t:ℝ)) := by
      field_simp
      ring
    have hp2 : (k:ℝ)/(32*(t:ℝ)) ≤ (4 * alpha) ^ (sLem4 k t) := by
      rw [← hge]; exact le_of_lt hgt
    have hlowp : (1:ℝ)/1024 ≤ (4 * alpha) ^ (sLem4 k t) * (alpha - pSeq n m k t 0) := by
      have hsame : alpha - pSeq n m k t 0 = eps0 n m k t := rfl
      rw [hsame]
      have h1 : (t:ℝ)/(32*k) ≤ eps0 n m k t := eps0_lower hn ht htk hkn h2k hm
      have ht32 : (0:ℝ) ≤ (t:ℝ)/(32*(k:ℝ)) :=
        div_nonneg ht'.le (mul_nonneg (by norm_num) hk'.le)
      have hpownn : (0:ℝ) ≤ (4 * alpha) ^ (sLem4 k t) :=
        pow_nonneg (le_of_lt four_alpha_pos) _
      have hmul : (k:ℝ)/(32*(t:ℝ)) * ((t:ℝ)/(32*k)) ≤ (4 * alpha) ^ (sLem4 k t) * eps0 n m k t :=
        mul_le_mul hp2 h1 ht32 hpownn
      have hval : (k:ℝ)/(32*(t:ℝ)) * ((t:ℝ)/(32*k)) = (1:ℝ)/1024 := by
        field_simp
        ring
      linarith [hmul, hval]
    have hlowq : (1:ℝ)/4096 ≤ (4 * alpha) ^ (sLem4 k t) * qdev (qSeq n m k t) 0 := by
      have hsame : qdev (qSeq n m k t) 0 = delta0 n m k t := rfl
      rw [hsame]
      have h1 : (t:ℝ)/(128*k) ≤ delta0 n m k t := delta0_lower hn ht htk hkn h2k hm
      have ht32 : (0:ℝ) ≤ (t:ℝ)/(128*(k:ℝ)) :=
        div_nonneg ht'.le (mul_nonneg (by norm_num) hk'.le)
      have hpownn : (0:ℝ) ≤ (4 * alpha) ^ (sLem4 k t) :=
        pow_nonneg (le_of_lt four_alpha_pos) _
      have hmul : (k:ℝ)/(32*(t:ℝ)) * ((t:ℝ)/(128*k)) ≤ (4 * alpha) ^ (sLem4 k t) * delta0 n m k t :=
        mul_le_mul hp2 h1 ht32 hpownn
      have hval : (k:ℝ)/(32*(t:ℝ)) * ((t:ℝ)/(128*k)) = (1:ℝ)/4096 := by
        field_simp
        ring
      linarith [hmul, hval]
    exact ⟨by linarith [hb.1, hlowp], by linarith [hb.2.1, hlowq]⟩
  · have hXlt : (alpha * (k : ℝ)) / (8 * (t : ℝ)) < 1 := by linarith
    have hs0 : sLem4 k t = 0 := sLem4_eq_zero hk ht hXlt
    have h8t : alpha * (k:ℝ) < 8 * (t:ℝ) := by
      have h := hXlt
      rw [div_lt_one (by positivity : (0:ℝ) < 8 * (t:ℝ))] at h
      exact h
    have hε0 : alpha/256 ≤ eps0 n m k t := by
      have h1 := eps0_lower hn ht htk hkn h2k hm
      have h2 : alpha/256 < (t:ℝ)/(32*(k:ℝ)) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity : (0:ℝ) < 32 * (k:ℝ))]
        nlinarith [h8t]
      linarith
    have hδ0 : alpha/1024 ≤ delta0 n m k t := by
      have h1 := delta0_lower hn ht htk hkn h2k hm
      have h2 : alpha/1024 < (t:ℝ)/(128*(k:ℝ)) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity : (0:ℝ) < 128 * (k:ℝ))]
        nlinarith [h8t]
      linarith
    constructor
    · rw [hs0]
      have hp : pSeq n m k t 0 = alpha - eps0 n m k t := by
        simp only [pSeq_zero]; unfold eps0; ring
      rw [hp]
      have : (1:ℝ)/2048 ≤ alpha/256 := by linarith [alpha_ge_third]
      linarith
    · rw [hs0]
      have hq : qSeq n m k t 0 = (1 - alpha) - delta0 n m k t := by
        simp only [qSeq_zero]; unfold delta0; ring
      rw [hq]
      have : (1:ℝ)/4096 ≤ alpha/1024 := by linarith [alpha_ge_third]
      linarith



end

/-! ## Module `Halving` -/

section

/-
Lemma 5 of Section 7 of Sergeev, *Economical formulae for symmetric boolean
functions* (2025).

Lemma 4 separates the error probabilities `p_s` and `q_s` from the fixed points
`α` and `1 - α` of the iterations `pstep` and `qstep`.  Lemma 5 states that a
constant number `u` of further steps brings them below `1/8`, after which they
decrease doubly exponentially: `p_{s+u+i}, q_{s+u+i} ≤ 2^{-(2^i+2)}`.

The key one-step estimate is the factorisation
`x - pstep x = x (1-x) (α-x) (3-α-x)`: near the fixed point the decrease is
proportional to the deficit `α - x`, so the deficits grow geometrically.
-/



/-! ### The one-step decrease -/

theorem pstep_sub_eq (x : ℝ) :
    x - pstep x = x * (1 - x) * (alpha - x) * (3 - alpha - x) := by
  have h1 : (alpha - x) * (3 - alpha - x) = 1 - 3 * x + x ^ 2 := by
    have h := alpha_sq
    nlinarith
  unfold pstep
  rw [show x * (1 - x) * (alpha - x) * (3 - alpha - x)
      = x * (1 - x) * ((alpha - x) * (3 - alpha - x)) by ring, h1]
  ring

theorem qstep_sub_eq (x : ℝ) :
    x - qstep x = x * (1 - x) * ((1 - alpha) - x) * (2 - alpha + x) := by
  have h1 : ((1 - alpha) - x) * (2 - alpha + x) = 1 - x - x ^ 2 := by
    have h := one_sub_alpha_mul
    nlinarith
  unfold qstep
  rw [show x * (1 - x) * ((1 - alpha) - x) * (2 - alpha + x)
      = x * (1 - x) * (((1 - alpha) - x) * (2 - alpha + x)) by ring, h1]
  ring

/-- On the range where the iteration is active the product `x (1-x)` is at
least `1/10`. -/
theorem mul_one_sub_ge {x : ℝ} (h0 : 1 / 8 ≤ x) (h1 : x ≤ 5 / 8) :
    (1 : ℝ) / 10 ≤ x * (1 - x) := by
  have hprod : 0 ≤ (x - 1 / 8) * (5 / 8 - x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The decrease of `p` is at least a tenth of the deficit `α - x`. -/
theorem pstep_decrease {x : ℝ} (h0 : 1 / 8 ≤ x) (h1 : x ≤ alpha) :
    (alpha - x) / 10 ≤ x - pstep x := by
  have hxx := mul_one_sub_ge h0 (by linarith [alpha_lt_half])
  have hfac : (1 : ℝ) ≤ 3 - alpha - x := by linarith [alpha_lt_half]
  have hA : (0 : ℝ) ≤ x * (1 - x) := by linarith [h0, alpha_lt_half]
  have hprod : (1 : ℝ) / 10 ≤ x * (1 - x) * (3 - alpha - x) := by
    have hm := mul_le_mul hxx hfac (by norm_num) hA
    linarith
  have hK : (0 : ℝ) ≤ alpha - x := by linarith
  rw [pstep_sub_eq]
  calc (alpha - x) / 10 = (alpha - x) * (1 / 10) := by ring
    _ ≤ (alpha - x) * (x * (1 - x) * (3 - alpha - x)) :=
        mul_le_mul_of_nonneg_left hprod hK
    _ = x * (1 - x) * (alpha - x) * (3 - alpha - x) := by ring

/-- The decrease of `q` is at least a tenth of the deficit `(1-α) - x`. -/
theorem qstep_decrease {x : ℝ} (h0 : 1 / 8 ≤ x) (h1 : x ≤ 1 - alpha) :
    ((1 - alpha) - x) / 10 ≤ x - qstep x := by
  have h58 : x ≤ 5 / 8 := by linarith [three_le_eight_alpha]
  have hxx := mul_one_sub_ge h0 h58
  have hfac : (1 : ℝ) ≤ 2 - alpha + x := by linarith [alpha_lt_one]
  have hA : (0 : ℝ) ≤ x * (1 - x) := by linarith [h0, h58]
  have hprod : (1 : ℝ) / 10 ≤ x * (1 - x) * (2 - alpha + x) := by
    have hm := mul_le_mul hxx hfac (by norm_num) hA
    linarith
  have hK : (0 : ℝ) ≤ (1 - alpha) - x := by linarith
  rw [qstep_sub_eq]
  calc ((1 - alpha) - x) / 10 = ((1 - alpha) - x) * (1 / 10) := by ring
    _ ≤ ((1 - alpha) - x) * (x * (1 - x) * (2 - alpha + x)) :=
        mul_le_mul_of_nonneg_left hprod hK
    _ = x * (1 - x) * ((1 - alpha) - x) * (2 - alpha + x) := by ring

/-! ### The descent of `p_d` and `q_d` -/

theorem pSeq_descent {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : pSeq n m k t N ≤ alpha - 1 / 4096) (i : ℕ) :
    pSeq n m k t (N + i) ≤ max (1 / 8 : ℝ) (alpha - (1 / 4096 + (i : ℝ) / 40960)) := by
  induction i with
  | zero =>
      have h0 : alpha - (1 / 4096 + ((0 : ℕ) : ℝ) / 40960) = alpha - 1 / 4096 := by
        norm_num
      rw [Nat.add_zero, h0]
      exact le_trans hN (le_max_right _ _)
  | succ j ih =>
      have hidx : N + (j + 1) = N + j + 1 := by omega
      rw [hidx, pSeq_succ]
      have hpos : (0 : ℝ) ≤ pSeq n m k t (N + j) := pSeq_nonneg hn ht htk hkn h2k hm (N + j)
      have hα : pSeq n m k t (N + j) ≤ alpha := pSeq_le_alpha hn ht htk hkn h2k hm (N + j)
      rcases lt_or_ge (pSeq n m k t (N + j)) (1 / 8) with hlt | hge
      · exact le_trans (pstep_le_self hpos hα)
          (le_trans (le_of_lt hlt) (le_max_left _ _))
      · rcases le_total (1 / 8 : ℝ) (alpha - (1 / 4096 + (j : ℝ) / 40960)) with hc | hc
        · rw [max_eq_right hc] at ih
          have hdec := pstep_decrease hge hα
          have hj0 : (0 : ℝ) ≤ (j : ℝ) / 40960 := by positivity
          have hgap : (1 : ℝ) / 4096 ≤ alpha - pSeq n m k t (N + j) := by linarith
          have hstep : pstep (pSeq n m k t (N + j))
              ≤ alpha - (1 / 4096 + ((j + 1 : ℕ) : ℝ) / 40960) := by
            have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
            rw [hcast]
            have hcast2 : ((j : ℝ) + 1) / 40960 = (j : ℝ) / 40960 + 1 / 40960 := by ring
            rw [hcast2]
            linarith
          exact le_trans hstep (le_max_right _ _)
        · rw [max_eq_left hc] at ih
          have hp8 : pSeq n m k t (N + j) = 1 / 8 := le_antisymm ih hge
          have hstep : pstep (pSeq n m k t (N + j)) ≤ 1 / 8 := by
            rw [hp8]
            exact pstep_le_self (by norm_num) (by linarith [alpha_ge_third])
          exact le_trans hstep (le_max_left _ _)

theorem qSeq_descent {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : qSeq n m k t N ≤ 1 - alpha - 1 / 4096) (i : ℕ) :
    qSeq n m k t (N + i)
      ≤ max (1 / 8 : ℝ) ((1 - alpha) - (1 / 4096 + (i : ℝ) / 40960)) := by
  induction i with
  | zero =>
      have h0 : (1 - alpha) - (1 / 4096 + ((0 : ℕ) : ℝ) / 40960) = 1 - alpha - 1 / 4096 := by
        norm_num
      rw [Nat.add_zero, h0]
      exact le_trans hN (le_max_right _ _)
  | succ j ih =>
      have hidx : N + (j + 1) = N + j + 1 := by omega
      rw [hidx, qSeq_succ]
      have hpos : (0 : ℝ) ≤ qSeq n m k t (N + j) := qSeq_nonneg hn ht htk hkn h2k hm (N + j)
      have hα : qSeq n m k t (N + j) ≤ 1 - alpha := qSeq_le hn ht htk hkn h2k hm (N + j)
      rcases lt_or_ge (qSeq n m k t (N + j)) (1 / 8) with hlt | hge
      · exact le_trans (qstep_le_self hpos hα)
          (le_trans (le_of_lt hlt) (le_max_left _ _))
      · rcases le_total (1 / 8 : ℝ) ((1 - alpha) - (1 / 4096 + (j : ℝ) / 40960)) with hc | hc
        · rw [max_eq_right hc] at ih
          have hdec := qstep_decrease hge hα
          have hj0 : (0 : ℝ) ≤ (j : ℝ) / 40960 := by positivity
          have hgap : (1 : ℝ) / 4096 ≤ (1 - alpha) - qSeq n m k t (N + j) := by linarith
          have hstep : qstep (qSeq n m k t (N + j))
              ≤ (1 - alpha) - (1 / 4096 + ((j + 1 : ℕ) : ℝ) / 40960) := by
            have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
            rw [hcast]
            have hcast2 : ((j : ℝ) + 1) / 40960 = (j : ℝ) / 40960 + 1 / 40960 := by ring
            rw [hcast2]
            linarith
          exact le_trans hstep (le_max_right _ _)
        · rw [max_eq_left hc] at ih
          have hq8 : qSeq n m k t (N + j) = 1 / 8 := le_antisymm ih hge
          have hstep : qstep (qSeq n m k t (N + j)) ≤ 1 / 8 := by
            rw [hq8]
            exact qstep_le_self (by norm_num) (by linarith [alpha_lt_one])
          exact le_trans hstep (le_max_left _ _)

/-- A constant number of steps brings `p_d` below `1/8`. -/
theorem pSeq_half {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : pSeq n m k t N ≤ alpha - 1 / 4096) :
    pSeq n m k t (N + 23000) ≤ 1 / 8 := by
  have h := pSeq_descent hn ht htk hkn h2k hm hN 23000
  have hle : alpha - (1 / 4096 + ((23000 : ℕ) : ℝ) / 40960) ≤ 1 / 8 := by
    push_cast
    linarith [alpha_lt_half]
  exact le_trans h (max_le (le_refl _) hle)

/-- A constant number of steps brings `q_d` below `1/8`. -/
theorem qSeq_half {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : qSeq n m k t N ≤ 1 - alpha - 1 / 4096) :
    qSeq n m k t (N + 23000) ≤ 1 / 8 := by
  have h := qSeq_descent hn ht htk hkn h2k hm hN 23000
  have hle : (1 - alpha) - (1 / 4096 + ((23000 : ℕ) : ℝ) / 40960) ≤ 1 / 8 := by
    push_cast
    linarith [alpha_ge_third]
  exact le_trans h (max_le (le_refl _) hle)

/-! ### The doubly exponential tail -/

theorem pow_half_le_one (m : ℕ) : ((1 / 2 : ℝ) ^ m) ≤ 1 := by
  have h : (1 / 2 : ℝ) ^ m ≤ 1 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
  simpa using h

theorem four_mul_pow_half_sq (m : ℕ) (hm : 1 ≤ m) :
    4 * ((1 / 2 : ℝ) ^ m) ^ 2 = (1 / 2) ^ (2 * m - 2) := by
  have h1 : ((1 / 2 : ℝ) ^ m) ^ 2 = (1 / 2) ^ (2 * m) := by
    rw [← pow_mul]
    congr 1
    ring
  have h2 : (1 / 2 : ℝ) ^ (2 * m) = (1 / 2) ^ (2 * m - 2) * (1 / 2) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1, h2]
  norm_num
  ring

theorem two_mul_pow_half_sq_le (m : ℕ) (hm : 1 ≤ m) :
    2 * ((1 / 2 : ℝ) ^ m) ^ 2 ≤ (1 / 2) ^ (2 * m - 2) := by
  have h := four_mul_pow_half_sq m hm
  have hpos : (0 : ℝ) < (1 / 2) ^ (2 * m - 2) := by positivity
  linarith

theorem pSeq_iter {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : pSeq n m k t N ≤ 1 / 8) (i : ℕ) :
    pSeq n m k t (N + i) ≤ (1 / 2 : ℝ) ^ (2 ^ i + 2) := by
  induction i with
  | zero =>
      have h3 : (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 0 + 2) = 1 / 8 := by norm_num
      rw [Nat.add_zero, h3]
      exact hN
  | succ j ih =>
      have hidx : N + (j + 1) = N + j + 1 := by omega
      rw [hidx, pSeq_succ]
      have hpos : (0 : ℝ) ≤ pSeq n m k t (N + j) := pSeq_nonneg hn ht htk hkn h2k hm (N + j)
      have h1 : pSeq n m k t (N + j) ≤ 1 := le_trans ih (pow_half_le_one (2 ^ j + 2))
      have h2 := pstep_le_four_sq hpos (by linarith)
      have h3 : (pSeq n m k t (N + j)) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ j + 2)) ^ 2 :=
        pow_le_pow_left₀ hpos ih 2
      have h4 := four_mul_pow_half_sq (2 ^ j + 2)
        (by have hp : 0 < 2 ^ j := pow_pos (by norm_num) j; omega)
      have hexp : 2 * (2 ^ j + 2) - 2 = 2 ^ (j + 1) + 2 := by
        have hp : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
        omega
      rw [hexp] at h4
      nlinarith

theorem qSeq_iter {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) {N : ℕ}
    (hN : qSeq n m k t N ≤ 1 / 8) (i : ℕ) :
    qSeq n m k t (N + i) ≤ (1 / 2 : ℝ) ^ (2 ^ i + 2) := by
  induction i with
  | zero =>
      have h3 : (1 / 2 : ℝ) ^ ((2 : ℕ) ^ 0 + 2) = 1 / 8 := by norm_num
      rw [Nat.add_zero, h3]
      exact hN
  | succ j ih =>
      have hidx : N + (j + 1) = N + j + 1 := by omega
      rw [hidx, qSeq_succ]
      have hpos : (0 : ℝ) ≤ qSeq n m k t (N + j) := qSeq_nonneg hn ht htk hkn h2k hm (N + j)
      have h1 : qSeq n m k t (N + j) ≤ 1 := le_trans ih (pow_half_le_one (2 ^ j + 2))
      have h2 := qstep_le_two_sq hpos h1
      have h3 : (qSeq n m k t (N + j)) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ j + 2)) ^ 2 :=
        pow_le_pow_left₀ hpos ih 2
      have h4 := two_mul_pow_half_sq_le (2 ^ j + 2)
        (by have hp : 0 < 2 ^ j := pow_pos (by norm_num) j; omega)
      have hexp : 2 * (2 ^ j + 2) - 2 = 2 ^ (j + 1) + 2 := by
        have hp : (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
        omega
      rw [hexp] at h4
      nlinarith

/-! ### Lemma 5 -/

/-- Lemma 5 of Section 7: for any `r` the error probabilities at index
`s + 23000 + ⌈log₂ r⌉` are smaller than `2^{-(r+1)}`. -/
theorem lemma5 {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k) (hkn : k + t ≤ n)
    (h2k : 2 * k ≤ n) (hm : m = n / k) (r : ℕ) :
    pSeq n m k t (sLem4 k t + 23000 + Nat.clog 2 r) < (1 / 2 : ℝ) ^ (r + 1) ∧
    qSeq n m k t (sLem4 k t + 23000 + Nat.clog 2 r) < (1 / 2 : ℝ) ^ (r + 1) := by
  have h4 := lemma4 hn ht htk hkn h2k hm
  have hpN : pSeq n m k t (sLem4 k t) ≤ alpha - 1 / 4096 := by linarith [h4.1]
  have hqN : qSeq n m k t (sLem4 k t) ≤ 1 - alpha - 1 / 4096 := h4.2
  have hp1 := pSeq_half hn ht htk hkn h2k hm hpN
  have hq1 := qSeq_half hn ht htk hkn h2k hm hqN
  have hlt : r + 1 < 2 ^ (Nat.clog 2 r) + 2 := by
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) r
    omega
  have hpow : (1 / 2 : ℝ) ^ (2 ^ (Nat.clog 2 r) + 2) < (1 / 2 : ℝ) ^ (r + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt
  constructor
  · exact lt_of_le_of_lt (pSeq_iter hn ht htk hkn h2k hm hp1 (Nat.clog 2 r)) hpow
  · exact lt_of_le_of_lt (qSeq_iter hn ht htk hkn h2k hm hq1 (Nat.clog 2 r)) hpow



end

/-! ## Module `Union` -/

section

/-
The final step of the proof of Theorem 1 of Sergeev, *Economical formulae for
symmetric boolean functions* (2025), Section 7: the union bound over the two
boundary layers of `Ψⁿ_{k,t}`.

Lemma 5 bounds the probability that a formula of `Δ_d` errs at one prescribed
input.  There are `C(k-t) + C(k+t)` inputs on the boundary, so the probability
that a formula of `Δ_d` errs somewhere on the boundary is at most
`(C(k-t) + C(k+t)) · 2^{-(r+1)}`, where `r = ⌈log₂ (C(k-t) + C(k+t))⌉`.  This is
`< 1`, so some formula of `Δ_d` is correct on the whole boundary and hence, by
monotonicity, on the whole domain of definition.
-/

open scoped BigOperators



/-! ### Nonnegativity of the weights -/

theorem abase_pow_nonneg {n k : ℕ} (hn : 0 < n) (h2k : 2 * k ≤ n) (m : ℕ) :
    0 ≤ abase n k ^ m :=
  pow_nonneg (le_trans (by norm_num) (abase_half hn h2k)) m

/-- The probability `τ` of the constant formula is nonnegative. -/
theorem tau_nonneg {n m k : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hm : m = n / k) : 0 ≤ tau n m k := by
  have hpos := one_sub_abase_pow_pos hn hk h2k hm
  have hpw := abase_pow_le hn hk h2k hm
  have hα := alpha_le_two_fifths
  have hpos' : (0:ℝ) < 1 - (1 - (k : ℝ) / (n : ℝ)) ^ m := by simpa [abase] using hpos
  have hpw' : (1 - (k : ℝ) / (n : ℝ)) ^ m ≤ 3 / 5 := by simpa [abase] using hpw
  unfold tau
  rw [sub_nonneg, div_le_iff₀ hpos']
  linarith

/-- The probability `τ` of the constant formula is at most one. -/
theorem tau_le_one {n m k : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hm : m = n / k) : tau n m k ≤ 1 := by
  have hpos := one_sub_abase_pow_pos hn hk h2k hm
  have hnn : 0 ≤ alpha / (1 - (1 - (k : ℝ) / (n : ℝ)) ^ m) :=
    div_nonneg (le_of_lt alpha_pos) (by simpa [abase] using le_of_lt hpos)
  unfold tau
  linarith

theorem w0_nonneg {n m k : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hm : m = n / k) (s : Seed0 n m) : 0 ≤ w0 n m k s := by
  cases s with
  | none => exact tau_nonneg hn hk h2k hm
  | some f =>
      have h1 : 0 ≤ 1 - tau n m k := by linarith [tau_le_one hn hk h2k hm]
      have h2 : (0:ℝ) < (n : ℝ) ^ m := by
        have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
        positivity
      exact div_nonneg h1 (le_of_lt h2)

theorem wseed_nonneg {n m k : ℕ} (hn : 0 < n) (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hm : m = n / k) (d : ℕ) : ∀ s : Seed n m d, 0 ≤ wseed n m k d s := by
  induction d with
  | zero => intro s; exact w0_nonneg hn hk h2k hm s
  | succ d ih =>
      intro s
      exact mul_nonneg (mul_nonneg (ih s.1.1) (ih s.1.2)) (mul_nonneg (ih s.2.1) (ih s.2.2))

/-! ### The union bound -/

/-- Union bound: the weight of the seeds satisfying one of the events `E i`,
`i ∈ S`, is at most the sum of the weights of the events. -/
theorem bsum_exists_le {A ι : Type*} [Fintype A] (S : Finset ι)
    {w : A → ℝ} (hw : ∀ a, 0 ≤ w a) (E : ι → A → Bool) :
    bsum w (fun a => decide (∃ i ∈ S, E i a = true)) ≤ ∑ i ∈ S, bsum w (E i) := by
  unfold bsum
  have hstep : ∀ a : A, (if decide (∃ i ∈ S, E i a = true) then w a else 0)
      ≤ ∑ i ∈ S, (if E i a then w a else 0) := by
    intro a
    by_cases h : ∃ i ∈ S, E i a = true
    · have hc : decide (∃ i ∈ S, E i a = true) = true := by simp [h]
      rw [if_pos hc]
      obtain ⟨i₀, hi₀S, hi₀⟩ := h
      have hterm : (if E i₀ a then w a else 0) = w a := by rw [hi₀]; simp
      have hsingle : (if E i₀ a then w a else 0)
          ≤ ∑ i ∈ S, (if E i a then w a else 0) :=
        Finset.single_le_sum (f := fun i => if E i a then w a else 0)
          (fun i _ => by split <;> simp [hw a]) hi₀S
      linarith
    · have hc : ¬ (decide (∃ i ∈ S, E i a = true) = true) := by simp [h]
      rw [if_neg hc]
      exact Finset.sum_nonneg fun i _ => by split <;> simp [hw a]
  calc (∑ a, if decide (∃ i ∈ S, E i a = true) then w a else 0)
      ≤ ∑ a, ∑ i ∈ S, (if E i a then w a else 0) := Finset.sum_le_sum fun a _ => hstep a
    _ = ∑ i ∈ S, ∑ a, (if E i a then w a else 0) := Finset.sum_comm

/-- If the weight of an event is smaller than the total weight, then some
element avoids the event. -/
theorem exists_false_of_bsum_lt {A : Type*} [Fintype A] (w : A → ℝ) (p : A → Bool)
    (h : bsum w p < ∑ a, w a) : ∃ a, p a = false := by
  by_contra hc
  push Not at hc
  have hsum : bsum w p = ∑ a, w a := by
    unfold bsum
    refine Finset.sum_congr rfl fun a _ => ?_
    cases hpa : p a with
    | false => exact absurd hpa (hc a)
    | true => simp
  linarith

/-! ### The error probability at a prescribed input -/

/-- At a vector of weight `k - t` the probability that a `Δ_d` formula errs is
`p_d`. -/
theorem errOne_eq_pSeq {n m k t d : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (x : Fin n → Bool) (hx : onesCount x = k - t) :
    bsum (wseed n m k d) (fun s => decide ((deltaForm n m d s).eval x ≠ (psi n k t).val x))
      = pSeq n m k t d := by
  have hv : (psi n k t).val x = false := by
    apply psi_val_zero ht
    omega
  rw [hv]
  refine Eq.trans (bsum_congr (fun s => ?_)) (pErr_eq_pSeq hn htk hkn d x hx)
  unfold badOne
  cases h : (deltaForm n m d s).eval x <;> rfl

/-- At a vector of weight `k + t` the probability that a `Δ_d` formula errs is
`q_d`. -/
theorem errZero_eq_qSeq {n m k t d : ℕ} (hn : 0 < n) (hkn : k + t ≤ n)
    (x : Fin n → Bool) (hx : onesCount x = k + t) :
    bsum (wseed n m k d) (fun s => decide ((deltaForm n m d s).eval x ≠ (psi n k t).val x))
      = qSeq n m k t d := by
  have hv : (psi n k t).val x = true := psi_val_one (by omega)
  rw [hv]
  refine Eq.trans (bsum_congr (fun s => ?_)) (qErr_eq_qSeq hn hkn d x hx)
  unfold badZero
  cases h : (deltaForm n m d s).eval x <;> rfl

/-! ### The number of levels -/

/-- The number of levels `d` of the distributions `Δ_d` used in the proof of
Theorem 1: `s + u + ⌈log₂⌈log₂ N⌉⌉`, where `N = C(k-t) + C(k+t)` is the
number of inputs on the boundary. -/
noncomputable def proofLevel (n k t : ℕ) : ℕ :=
  sLem4 k t + 23000 + Nat.clog 2 (Nat.clog 2 (boundary n k t).card)

theorem proofLevel_eq (n k t : ℕ) :
    proofLevel n k t = sLem4 k t + 23000 + Nat.clog 2 (Nat.clog 2 (boundary n k t).card) :=
  rfl

/-! ### The union bound over the boundary -/

/-- The probability that a `Δ_d` formula errs at some input of the boundary is
smaller than one. -/
theorem badBoundary_lt_one {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    bsum (wseed n m k (proofLevel n k t))
      (fun s => decide (∃ x ∈ boundary n k t,
        (deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x)) < 1 := by
  have hk : 0 < k := by omega
  set r := Nat.clog 2 (boundary n k t).card with hr
  have hd : proofLevel n k t = sLem4 k t + 23000 + Nat.clog 2 r := rfl
  have h5 := lemma5 hn ht htk hkn h2k hm r
  have hevent : ∀ s, (decide (∃ x ∈ boundary n k t,
        (deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x))
      = decide (∃ x ∈ boundary n k t,
          decide ((deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x) = true) := by
    intro s
    congr 1
    simp
  rw [bsum_congr hevent]
  refine lt_of_le_of_lt (bsum_exists_le (boundary n k t)
    (wseed_nonneg hn hk h2k hm (proofLevel n k t))
    (fun x s => decide ((deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x))) ?_
  have hterm : ∀ x ∈ boundary n k t, bsum (wseed n m k (proofLevel n k t))
      (fun s => decide ((deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x))
        ≤ (1 / 2 : ℝ) ^ (r + 1) := by
    intro x hx
    rcases mem_boundary.mp hx with h | h
    · rw [errZero_eq_qSeq hn hkn x h, hd]
      exact le_of_lt h5.2
    · rw [errOne_eq_pSeq hn ht htk hkn x h, hd]
      exact le_of_lt h5.1
  have hsum : ∑ x ∈ boundary n k t, bsum (wseed n m k (proofLevel n k t))
      (fun s => decide ((deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x))
        ≤ ((boundary n k t).card : ℝ) * (1 / 2 : ℝ) ^ (r + 1) := by
    calc ∑ x ∈ boundary n k t, bsum (wseed n m k (proofLevel n k t))
          (fun s => decide ((deltaForm n m (proofLevel n k t) s).eval x ≠ (psi n k t).val x))
        ≤ ∑ _x ∈ boundary n k t, (1 / 2 : ℝ) ^ (r + 1) := Finset.sum_le_sum hterm
      _ = ((boundary n k t).card : ℝ) * (1 / 2 : ℝ) ^ (r + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((boundary n k t).card : ℝ) ≤ (2 : ℝ) ^ r := by
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (boundary n k t).card
    rw [hr]
    exact_mod_cast h
  have hhalf : ((boundary n k t).card : ℝ) * (1 / 2 : ℝ) ^ (r + 1) ≤ 1 / 2 := by
    have hpos : (0:ℝ) < (1 / 2 : ℝ) ^ (r + 1) := by positivity
    calc ((boundary n k t).card : ℝ) * (1 / 2 : ℝ) ^ (r + 1)
        ≤ (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (r + 1) :=
          mul_le_mul_of_nonneg_right hcard (le_of_lt hpos)
      _ = 1 / 2 := by
          rw [pow_succ, ← mul_assoc, ← mul_pow]
          norm_num
  linarith

/-- Some formula of `Δ_d` is correct on the whole domain of `Ψⁿ_{k,t}`. -/
theorem exists_good_seed {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    ∃ s : Seed n m (proofLevel n k t),
      ComputesOn (deltaForm n m (proofLevel n k t) s) (psi n k t) := by
  have hlt := badBoundary_lt_one hn ht htk hkn h2k hm
  obtain ⟨s, hs⟩ := exists_false_of_bsum_lt (wseed n m k (proofLevel n k t)) _
    (by rw [sum_wseed hn]; exact hlt)
  have hgood : ∀ x ∈ boundary n k t,
      (deltaForm n m (proofLevel n k t) s).eval x = (psi n k t).val x := by
    intro x hx
    by_contra hne
    exact (of_decide_eq_false hs) ⟨x, hx, hne⟩
  refine ⟨s, computes_of_boundary ht htk hkn ?_ ?_⟩
  · intro y hy
    have hb := hgood y (mem_boundary.mpr (Or.inl hy))
    rw [psi_val_one (by omega)] at hb
    exact hb
  · intro y hy
    have hb := hgood y (mem_boundary.mpr (Or.inr hy))
    rw [psi_val_zero ht (by omega)] at hb
    exact hb

/-- Theorem 1, without the logarithmic estimates: the depth of `Ψⁿ_{k,t}` over
the monotone basis is at most `⌈log₂ m⌉ + 2 (s + u + ⌈log₂⌈log₂ N⌉⌉)`. -/
theorem partialDepth_psi_le {n m k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) (hm : m = n / k) :
    partialDepth (psi n k t) ≤ Nat.clog 2 m + 2 * proofLevel n k t := by
  obtain ⟨s, hs⟩ := exists_good_seed hn ht htk hkn h2k hm
  calc partialDepth (psi n k t) ≤ (deltaForm n m (proofLevel n k t) s).depth :=
        partialDepth_le hs
    _ ≤ Nat.clog 2 m + 2 * proofLevel n k t := deltaForm_depth_le _ _



end

/-! ## Module `Theorem1` -/

section

/-
Theorem 1 of Sergeev, *Economical formulae for symmetric boolean functions*
(2025), Section 7:

`D_{B_M}(Ψⁿ_{k,t}) ≤ log_{√5−1}(k/t) + log₂(n/k) + 2 log₂ log₂(C(k−t) + C(k+t)) + O(1)`.

The probabilistic construction (`partialDepth_psi_le`) gives the depth bound
`⌈log₂ (n/k)⌉ + 2 (s + u)` with `s ≤ log_{4α}(k/t) + 1` (Lemma 4) and
`u = 23000 + ⌈log₂ ⌈log₂ N⌉⌉` (Lemma 5), where `N = C(k−t) + C(k+t)` is the
size of the boundary.  It remains to pass from the binary logarithms and the
bases `2`, `4α` to the single base `√5 − 1` and to the three terms of the
statement; the additive constants accumulate to `46007`.
-/

open scoped BigOperators



/-! ### The base `√5 − 1` -/

/-- `√5 − 1 > 1`, so it is a legitimate base of a logarithm. -/
theorem sqrt5_sub_one_gt_one : (1 : ℝ) < Real.sqrt 5 - 1 := by
  have : (2 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  linarith

/-- `√5 − 1 > 0`. -/
theorem sqrt5_sub_one_pos : (0 : ℝ) < Real.sqrt 5 - 1 := lt_trans one_pos sqrt5_sub_one_gt_one

/-- `√5 − 1 < 2`. -/
theorem sqrt5_sub_one_lt_two : Real.sqrt 5 - 1 < 2 := by
  have : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- The base `4α = (√5 − 1)²` of Lemma 4 is the square of the base of
Theorem 1. -/
theorem logb_four_alpha (x : ℝ) :
    Real.logb (4 * alpha) x = Real.logb (Real.sqrt 5 - 1) x / 2 := by
  have hb : Real.log (Real.sqrt 5 - 1) ≠ 0 := (Real.log_pos sqrt5_sub_one_gt_one).ne'
  rw [four_alpha_eq_sq]
  unfold Real.logb
  rw [Real.log_pow]
  push_cast
  field_simp

/-- Changing the base of a logarithm from `2` to the smaller base `√5 − 1 ≥ 2`
only increases it on `[1, ∞)`. -/
theorem logb_two_le_logb_sqrt5 {u : ℝ} (h : 1 ≤ u) :
    Real.logb 2 u ≤ Real.logb (Real.sqrt 5 - 1) u := by
  have hb := sqrt5_sub_one_gt_one
  have h1 : (1 : ℝ) ≤ Real.logb (Real.sqrt 5 - 1) 2 := by
    by_contra hc
    push Not at hc
    have hstep := (Real.logb_lt_iff_lt_rpow hb (by norm_num : (0 : ℝ) < 2)).mp hc
    rw [Real.rpow_one] at hstep
    linarith [sqrt5_sub_one_lt_two]
  have h2 : 0 ≤ Real.logb 2 u := Real.logb_nonneg (by norm_num) h
  calc Real.logb 2 u = 1 * Real.logb 2 u := (one_mul _).symm
    _ ≤ Real.logb (Real.sqrt 5 - 1) 2 * Real.logb 2 u :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = Real.logb (Real.sqrt 5 - 1) u :=
        Real.mul_logb (a := Real.sqrt 5 - 1) (b := 2) (c := u)
          (by norm_num) (by norm_num) (by norm_num)

/-! ### Binary logarithms -/

/-- `⌈log₂ m⌉ ≤ log₂ m + 1`: the ceiling of a binary logarithm exceeds it by
less than one. -/
theorem clog_le_logb_add_one {m : ℕ} (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ Real.logb 2 (m : ℝ) + 1 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hb : (1 : ℝ) < 2 := by norm_num
  have hle : Real.logb 2 (m : ℝ) ≤ (⌈Real.logb 2 (m : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (m : ℝ) ≤ (2 : ℝ) ^ ⌈Real.logb 2 (m : ℝ)⌉₊ := by
    have := (Real.logb_le_iff_le_rpow hb hm0).mp hle
    simpa using this
  have hnat : m ≤ 2 ^ ⌈Real.logb 2 (m : ℝ)⌉₊ := by exact_mod_cast hpow
  have hclog : Nat.clog 2 m ≤ ⌈Real.logb 2 (m : ℝ)⌉₊ :=
    (Nat.clog_le_iff_le_pow (by norm_num : (1 : ℕ) < 2)).mpr hnat
  have hnonneg : (0 : ℝ) ≤ Real.logb 2 (m : ℝ) := Real.logb_nonneg hb (by exact_mod_cast hm)
  calc (Nat.clog 2 m : ℝ) ≤ (⌈Real.logb 2 (m : ℝ)⌉₊ : ℝ) := by exact_mod_cast hclog
    _ ≤ Real.logb 2 (m : ℝ) + 1 := le_of_lt (Nat.ceil_lt_add_one hnonneg)

/-! ### Duality for `partialDepth` -/

/-- A formula computing `Ψⁿ_{k,t}` has a dual formula of the same depth
computing `Ψⁿ_{n-k,t}`. -/
theorem computes_dual' {n k t : ℕ} (ht : 0 < t) (hkn : k + t ≤ n) {F : MFormula n}
    (h : ComputesOn F (psi n k t)) : ComputesOn (dual F) (psi n (n - k) t) := by
  intro x hx
  rw [eval_dual F x]
  have hz : onesCount (fun i => !(x i)) = n - onesCount x := onesCount_not x
  have hkc : k ≤ n := by omega
  have hcle : onesCount x ≤ n := onesCount_le x
  rcases hx with hx | hx
  · have hval : (psi n k t).val (fun i => !(x i)) = false := by
      have hlt : ¬ (k + t ≤ onesCount fun i => !(x i)) := by
        rw [hz]; omega
      simp [psi, hlt]
    rw [h _ (psi_dom_zero (by rw [hz]; omega)), hval]
    simp [psi_val_one hx]
  · have hval : (psi n k t).val (fun i => !(x i)) = true := by
      have hle : k + t ≤ onesCount fun i => !(x i) := by
        rw [hz]; omega
      simp [psi, hle]
    rw [h _ (psi_dom_one (by rw [hz]; omega)), hval]
    simp [psi_val_zero ht hx]

/-- `D_{B_M}(Ψⁿ_{k,t})` is invariant under the substitution `k ↦ n − k`. -/
theorem partialDepth_dual {n k t : ℕ} (ht : 0 < t) (_htk : t ≤ k) (hkn : k + t ≤ n) :
    partialDepth (psi n k t) = partialDepth (psi n (n - k) t) := by
  have hk : k ≤ n := by omega
  unfold partialDepth
  congr 1
  ext d
  constructor
  · rintro ⟨F, hFd, hF⟩
    exact ⟨dual F, by rw [depth_dual, hFd],
      computes_dual' (n := n) (k := k) (t := t) ht (by omega) hF⟩
  · rintro ⟨F, hFd, hF⟩
    exact ⟨dual F, by rw [depth_dual, hFd], computes_dual ht hkn hF⟩

/-! ### The case `2k ≤ n` -/

/-- Theorem 1 under the assumption `2k ≤ n`. -/
theorem theorem1_low {n k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : 2 * k ≤ n) :
    (partialDepth (psi n k t) : ℝ) ≤
      Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t) + Real.logb 2 ((n : ℝ) / k)
        + 2 * Real.logb 2 (Real.logb 2
            ((Nat.choose n (k + t) + Nat.choose n (k - t) : ℕ) : ℝ))
        + 46007 := by
  have hk : 0 < k := by omega
  have hkm : k ≤ n := by omega
  set N : ℕ := Nat.choose n (k + t) + Nat.choose n (k - t) with hN
  set L : ℕ := Nat.clog 2 N with hL
  have hcard : (boundary n k t).card = N := by
    rw [card_boundary ht hkn (by omega), hN]
  have hpl : proofLevel n k t = sLem4 k t + 23000 + Nat.clog 2 L := by
    rw [proofLevel, hcard]
  set m : ℕ := n / k with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_div_iff hk]
    omega
  have hbase := partialDepth_psi_le hn ht htk hkn h2k hm.symm
  have hD : (partialDepth (psi n k t) : ℝ)
      ≤ (Nat.clog 2 m : ℝ) + 2 * ((sLem4 k t : ℝ) + 23000 + (Nat.clog 2 L : ℝ)) := by
    calc (partialDepth (psi n k t) : ℝ)
        ≤ ((Nat.clog 2 m + 2 * proofLevel n k t : ℕ) : ℝ) := by exact_mod_cast hbase
      _ = (Nat.clog 2 m : ℝ) + 2 * ((sLem4 k t : ℝ) + 23000 + (Nat.clog 2 L : ℝ)) := by
          rw [hpl]; push_cast; ring
  have hN2 : 2 ≤ N := by
    have h1 : 1 ≤ Nat.choose n (k + t) := Nat.choose_pos (by omega)
    have h2 : 1 ≤ Nat.choose n (k - t) := Nat.choose_pos (by omega)
    rw [hN]; omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN1 : (1 : ℝ) ≤ Real.logb 2 (N : ℝ) :=
    (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hNpos).mpr (by
      rw [Real.rpow_one]; exact hNge2)
  have hL1 : 1 ≤ L := by
    rw [hL]
    have := Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < N)
    omega
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : (Nat.clog 2 m : ℝ) ≤ Real.logb 2 ((n : ℝ) / k) + 1 := by
    have hcl := clog_le_logb_add_one hm1
    have hcast : (m : ℝ) ≤ (n : ℝ) / k := by
      simpa [← hm] using (Nat.cast_div_le (α := ℝ) (m := n) (n := k))
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hmpos hcast
    linarith
  have hc : 2 * (sLem4 k t : ℝ) ≤ Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t) + 2 := by
    have h := sLem4_le_log hk ht htk
    have hlog : 2 * Real.logb (4 * alpha) ((k : ℝ) / t)
        = Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t) := by
      rw [logb_four_alpha]; ring
    linarith
  have hd1 : (L : ℝ) ≤ Real.logb 2 (N : ℝ) + 1 := by
    rw [hL]
    exact clog_le_logb_add_one (by omega : 1 ≤ N)
  have hd2 : Real.logb 2 (L : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) + 1 := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hstep : (L : ℝ) ≤ 2 * Real.logb 2 (N : ℝ) := by linarith
    have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hLpos hstep
    have hsplit : Real.logb 2 (2 * Real.logb 2 (N : ℝ))
        = 1 + Real.logb 2 (Real.logb 2 (N : ℝ)) := by
      rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
        (show Real.logb 2 (N : ℝ) ≠ 0 by linarith)]
      rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    linarith
  have hd : 2 * (Nat.clog 2 L : ℝ) ≤ 2 * Real.logb 2 (Real.logb 2 (N : ℝ)) + 4 := by
    have hcl := clog_le_logb_add_one hL1
    linarith
  linarith

/-! ### The case `2k > n` -/

/-- Theorem 1 under the assumption `n < 2k`, by duality. -/
theorem theorem1_high {n k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) (h2k : n < 2 * k) :
    (partialDepth (psi n k t) : ℝ) ≤
      Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t) + Real.logb 2 ((n : ℝ) / k)
        + 2 * Real.logb 2 (Real.logb 2
            ((Nat.choose n (k + t) + Nat.choose n (k - t) : ℕ) : ℝ))
        + 46007 := by
  have hkm : k < n := by omega
  have htk' : t ≤ n - k := by omega
  have hkn' : (n - k) + t ≤ n := by omega
  have h2k' : 2 * (n - k) ≤ n := by omega
  have hlow := theorem1_low (n := n) (k := n - k) (t := t) hn ht htk' hkn' h2k'
  have hN' : (Nat.choose n ((n - k) + t) + Nat.choose n ((n - k) - t) : ℕ)
      = Nat.choose n (k + t) + Nat.choose n (k - t) := by
    have e1 : Nat.choose n ((n - k) + t) = Nat.choose n (k - t) := by
      rw [← Nat.choose_symm (by omega : (n - k) + t ≤ n)]
      have h : n - ((n - k) + t) = k - t := by omega
      rw [h]
    have e2 : Nat.choose n ((n - k) - t) = Nat.choose n (k + t) := by
      rw [← Nat.choose_symm (by omega : (n - k) - t ≤ n)]
      have h : n - ((n - k) - t) = k + t := by omega
      rw [h]
    rw [e1, e2]
    omega
  rw [hN'] at hlow
  rw [partialDepth_dual ht htk hkn]
  refine le_trans hlow ?_
  have hnc : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub (le_of_lt hkm)
  rw [hnc] at hlow ⊢
  have hNpos : (0 : ℝ) < ((Nat.choose n (k + t) + Nat.choose n (k - t) : ℕ) : ℝ) := by
    have h1 : 1 ≤ Nat.choose n (k + t) := Nat.choose_pos (by omega)
    exact_mod_cast (by omega : 0 < Nat.choose n (k + t) + Nat.choose n (k - t))
  have hnkpos : (0 : ℝ) < (n : ℝ) - k := by
    have h : (k : ℝ) < n := by exact_mod_cast hkm
    linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hc1 : (1 : ℝ) ≤ (k : ℝ) / ((n : ℝ) - k) := by
    rw [le_div_iff₀ hnkpos]
    have h : (n : ℝ) < 2 * k := by exact_mod_cast h2k
    linarith
  have hsplit1 : Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t)
      = Real.logb (Real.sqrt 5 - 1) (((n : ℝ) - k) / t)
        + Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / ((n : ℝ) - k)) := by
    rw [← Real.logb_mul (div_ne_zero hnkpos.ne' htpos.ne')
      (div_ne_zero hkpos.ne' hnkpos.ne')]
    congr 1
    field_simp
  have hsplit2 : Real.logb 2 ((n : ℝ) / k)
      = Real.logb 2 ((n : ℝ) / ((n : ℝ) - k))
        - Real.logb 2 ((k : ℝ) / ((n : ℝ) - k)) := by
    have h2a : Real.logb 2 ((n : ℝ) / k) = Real.logb 2 (n : ℝ) - Real.logb 2 (k : ℝ) :=
      Real.logb_div (by positivity : (n : ℝ) ≠ 0) (by positivity : (k : ℝ) ≠ 0)
    have h2b : Real.logb 2 ((n : ℝ) / ((n : ℝ) - k))
        = Real.logb 2 (n : ℝ) - Real.logb 2 ((n : ℝ) - k) :=
      Real.logb_div (by positivity : (n : ℝ) ≠ 0) hnkpos.ne'
    have h2c : Real.logb 2 ((k : ℝ) / ((n : ℝ) - k))
        = Real.logb 2 (k : ℝ) - Real.logb 2 ((n : ℝ) - k) :=
      Real.logb_div (by positivity : (k : ℝ) ≠ 0) hnkpos.ne'
    linarith
  have hmono := logb_two_le_logb_sqrt5 hc1
  linarith

/-! ### Theorem 1 -/

/-- **Theorem 1.** The depth of the partial threshold function `Ψⁿ_{k,t}` over
the monotone basis `B_M = {∨, ∧}` is at most
`log_{√5−1}(k/t) + log₂(n/k) + 2 log₂ log₂(C(k−t) + C(k+t)) + 46007`. -/
theorem theorem1 {n k t : ℕ} (hn : 0 < n) (ht : 0 < t) (htk : t ≤ k)
    (hkn : k + t ≤ n) :
    (partialDepth (psi n k t) : ℝ) ≤
      Real.logb (Real.sqrt 5 - 1) ((k : ℝ) / t) + Real.logb 2 ((n : ℝ) / k)
        + 2 * Real.logb 2 (Real.logb 2
            ((Nat.choose n (k + t) + Nat.choose n (k - t) : ℕ) : ℝ))
        + 46007 := by
  by_cases h2k : 2 * k ≤ n
  · exact theorem1_low hn ht htk hkn h2k
  · exact theorem1_high hn ht htk hkn (by omega)



end

end SymmFormulae
