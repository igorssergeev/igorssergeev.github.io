/-
Section 3 of Sergeev, *Economical formulae for symmetric boolean functions*
(2025): approximate summation.

* the basis `B₀`, declared locally so that this file only depends on
  `Theorem1.lean`, and the combinators `b0Or`, `b0And`, `b0Not`,
  `orPow0`;
* the explicit monotone threshold formula `thr n m` and its evaluation;
* embedding of monotone formulae into `B₀` at the cost of at most two depth
  levels, and the induced `B₀` formula `psiForm n k t` for `Ψⁿ_{k,t}`;
* the partial threshold functions `X_j` covering `I_j = [jt, (j+1)t)`;
* the first-one operator `J′` of equation (3) and Corollary 1 on its depth;
* the block encoding `(B, H)` with correction rule (4) and Lemma 1.
-/
import SymmFormulae.Theorem1

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SymmFormulae

open Thm1


/-! ### The basis `B₀`

The definitions are scoped in the namespace `Section3` so that this file can be
imported together with `BasicNotions.lean`, which declares the same
basis under the plain name `B₀`. -/

namespace Section3

/-- The three operation symbols of the standard basis `B₀ = {∧, ∨, ¬}`. -/
inductive B0Op where
  | and | or | not
  deriving DecidableEq

instance : Fintype B0Op where
  elems := {B0Op.and, B0Op.or, B0Op.not}
  complete := by intro x; cases x <;> simp

namespace B0Op

/-- The arities of the gates of `B₀`. -/
def arity : B0Op → ℕ
  | and => 2
  | or => 2
  | not => 1

/-- The semantics of the gates of `B₀`. -/
def interp : (op : B0Op) → (Fin (arity op) → Bool) → Bool
  | and, v => v ⟨0, by decide⟩ && v ⟨1, by decide⟩
  | or, v => v ⟨0, by decide⟩ || v ⟨1, by decide⟩
  | not, v => !v ⟨0, by decide⟩

end B0Op

/-- The standard basis `B₀ = {∧, ∨, ¬}` (without constants). -/
def B0 : BooleanBasis where
  Op := B0Op
  arity := B0Op.arity
  arity_pos := by intro op; cases op <;> decide
  interp := B0Op.interp
  consts := ∅

end Section3

open Section3


/-! ### B₀ combinators -/

def b0Or {n : ℕ} (a b : Formula B0 n) : Formula B0 n := Formula.app B0Op.or ![a, b]
def b0And {n : ℕ} (a b : Formula B0 n) : Formula B0 n := Formula.app B0Op.and ![a, b]
def b0Not {n : ℕ} (a : Formula B0 n) : Formula B0 n := Formula.app B0Op.not ![a]

@[simp] theorem b0Or_eval {n : ℕ} (a b : Formula B0 n) (x : Fin n → Bool) :
    (b0Or a b).eval x = (a.eval x || b.eval x) := rfl

@[simp] theorem b0And_eval {n : ℕ} (a b : Formula B0 n) (x : Fin n → Bool) :
    (b0And a b).eval x = (a.eval x && b.eval x) := rfl

@[simp] theorem b0Not_eval {n : ℕ} (a : Formula B0 n) (x : Fin n → Bool) :
    (b0Not a).eval x = !(a.eval x) := rfl

theorem b0Or_depth_le {n : ℕ} (a b : Formula B0 n) :
    (b0Or a b).depth ≤ max a.depth b.depth + 1 := by
  have h : (b0Or a b).depth
      = Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i)) + 1 := rfl
  rw [h]
  have hsup : Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i))
      ≤ max a.depth b.depth := by
    refine Finset.sup_le ?_
    intro i _
    fin_cases i <;> simp
  omega

theorem b0And_depth_le {n : ℕ} (a b : Formula B0 n) :
    (b0And a b).depth ≤ max a.depth b.depth + 1 := by
  have h : (b0And a b).depth
      = Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i)) + 1 := rfl
  rw [h]
  have hsup : Finset.univ.sup (fun i : Fin 2 => Formula.depth (![a, b] i))
      ≤ max a.depth b.depth := by
    refine Finset.sup_le ?_
    intro i _
    fin_cases i <;> simp
  omega

theorem b0Not_depth_eq {n : ℕ} (a : Formula B0 n) : (b0Not a).depth = a.depth + 1 := by
  have h : (b0Not a).depth
      = Finset.univ.sup (fun i : Fin 1 => Formula.depth (![a] i)) + 1 := rfl
  rw [h]
  congr 1
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro i _
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst hi
    simp
  · have h0 : (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1)) := Finset.mem_univ _
    have hle := Finset.le_sup (s := (Finset.univ : Finset (Fin 1)))
      (f := fun i : Fin 1 => Formula.depth (![a] i)) h0
    exact hle

/-- Balanced disjunction of `2 ^ k` formulae over `B₀`. -/
def orPow0 {n : ℕ} : (k : ℕ) → (Fin (2 ^ k) → Formula B0 n) → Formula B0 n
  | 0, f => f 0
  | k + 1, f => b0Or (orPow0 k fun i => f (loFin k i)) (orPow0 k fun i => f (hiFin k i))

theorem orPow0_depth_le {n : ℕ} (k : ℕ) (f : Fin (2 ^ k) → Formula B0 n) :
    (orPow0 k f).depth ≤ k + Finset.univ.sup (fun i => (f i).depth) := by
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
      have h3 : (orPow0 (k + 1) f).depth
          = (b0Or (orPow0 k fun i => f (loFin k i))
              (orPow0 k fun i => f (hiFin k i))).depth := rfl
      rw [h3]
      have h4 := b0Or_depth_le (orPow0 k fun i => f (loFin k i))
        (orPow0 k fun i => f (hiFin k i))
      have : max (orPow0 k fun i => f (loFin k i)).depth
            (orPow0 k fun i => f (hiFin k i)).depth
          ≤ k + Finset.univ.sup (fun i : Fin (2 ^ (k + 1)) => (f i).depth) := by
        apply max_le <;> omega
      omega

theorem orPow0_eval {n : ℕ} :
    ∀ (k : ℕ) (f : Fin (2 ^ k) → Formula B0 n) (x : Fin n → Bool),
      (orPow0 k f).eval x = true ↔ ∃ i : Fin (2 ^ k), (f i).eval x = true
  | 0, f, x => by
    constructor
    · intro h; exact ⟨0, h⟩
    · rintro ⟨i, hi⟩
      have : i = 0 := Fin.ext (by have := i.isLt; omega)
      rwa [this] at hi
  | k + 1, f, x => by
    show (b0Or (orPow0 k fun i => f (loFin k i)) (orPow0 k fun i => f (hiFin k i))).eval x
        = true ↔ _
    rw [b0Or_eval, Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · obtain ⟨i, hi⟩ := (orPow0_eval k _ x).mp h
        exact ⟨loFin k i, hi⟩
      · obtain ⟨i, hi⟩ := (orPow0_eval k _ x).mp h
        exact ⟨hiFin k i, hi⟩
    · rintro ⟨j, hj⟩
      by_cases hlt : j.val < 2 ^ k
      · left
        refine (orPow0_eval k (fun i => f (loFin k i)) x).mpr ⟨⟨j.val, hlt⟩, ?_⟩
        simpa [loFin] using hj
      · right
        have hjlt := j.isLt
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
        have hge : 2 ^ k ≤ j.val := by omega
        refine (orPow0_eval k (fun i => f (hiFin k i)) x).mpr ⟨⟨j.val - 2 ^ k, by omega⟩, ?_⟩
        have hval : (hiFin k ⟨j.val - 2 ^ k, by omega⟩ : Fin (2 ^ (k + 1))).val = j.val := by
          rw [hiFin_val]; simp; omega
        have heq : (hiFin k ⟨j.val - 2 ^ k, by omega⟩ : Fin (2 ^ (k + 1))) = j := Fin.ext hval
        rw [heq]
        exact hj

/-- Splitting off the first coordinate of the arithmetic sum. -/
theorem onesCount_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    onesCount x = (if x 0 then 1 else 0) + onesCount (fun i : Fin n => x i.succ) := by
  rw [onesCount, onesCount, Fin.sum_univ_succ]

/-- The arithmetic core of the first step of the threshold recursion. -/
theorem bool_and_decide_or_decide (m s : ℕ) (p : Bool) :
    ((p && decide (m ≤ s)) || decide (m + 1 ≤ s))
      = decide (m + 1 ≤ (if p then 1 else 0) + s) := by
  cases p with
  | false => simp
  | true =>
      by_cases h : m ≤ s
      · have h2 : m + 1 ≤ 1 + s := by omega
        simp [h, h2]
      · have h3 : ¬ (m + 1 ≤ s) := by omega
        have h4 : ¬ (m + 1 ≤ 1 + s) := by omega
        simp [h, h3, h4]

/-! ### The explicit threshold formula -/

/-- `thr n m`: a monotone formula for the threshold function `σ ≥ m` on `n`
variables.  It is the standard recursion splitting off one variable. -/
def thr : (n m : ℕ) → MFormula n
  | 0, 0 => Thm1.Formula.const true (Set.mem_univ _)
  | 0, _ + 1 => Thm1.Formula.const false (Set.mem_univ _)
  | n + 1, 0 => Thm1.Formula.const true (Set.mem_univ _)
  | n + 1, m + 1 =>
      mkOr (mkAnd (Thm1.Formula.var (0 : Fin (n + 1))) ((thr n m).rename Fin.succ))
        ((thr n (m + 1)).rename Fin.succ)

theorem thr_eval : ∀ (n m : ℕ) (x : Fin n → Bool),
    (thr n m).eval x = decide (m ≤ onesCount x)
  | 0, 0, x => by
      have h : decide (0 ≤ onesCount x) = true := decide_eq_true (Nat.zero_le _)
      rw [h]
      rfl
  | 0, m + 1, x => by
      have h0 : onesCount x = 0 := by simp [onesCount]
      have h1 : ¬ (m + 1 ≤ onesCount x) := by omega
      have h : decide (m + 1 ≤ onesCount x) = false := decide_eq_false h1
      rw [h]
      rfl
  | n + 1, 0, x => by
      have h : decide (0 ≤ onesCount x) = true := decide_eq_true (Nat.zero_le _)
      rw [h]
      rfl
  | n + 1, m + 1, x => by
      show (mkOr (mkAnd (Thm1.Formula.var (0 : Fin (n + 1))) ((thr n m).rename Fin.succ))
        ((thr n (m + 1)).rename Fin.succ)).eval x = decide (m + 1 ≤ onesCount x)
      rw [mkOr_eval, mkAnd_eval, Thm1.Formula.eval_rename, Thm1.Formula.eval_rename,
        thr_eval n m, thr_eval n (m + 1), onesCount_succ x]
      exact bool_and_decide_or_decide m (onesCount (fun i : Fin n => x i.succ)) (x 0)

/-! ### Embedding the monotone basis into `B₀` -/

/-- Every monotone formula is a formula over `B₀`: `∨` and `∧` are gates of
`B₀`, and the constants are replaced by `x ∨ ¬x` and `x ∧ ¬x`. -/
def toB0 {n : ℕ} (hn : 0 < n) : MFormula n → Formula B0 n
  | .var i => .var i
  | .const true _ => b0Or (.var ⟨0, hn⟩) (b0Not (.var ⟨0, hn⟩))
  | .const false _ => b0And (.var ⟨0, hn⟩) (b0Not (.var ⟨0, hn⟩))
  | .app MonOp.or args => b0Or (toB0 hn (args ⟨0, by decide⟩)) (toB0 hn (args ⟨1, by decide⟩))
  | .app MonOp.and args => b0And (toB0 hn (args ⟨0, by decide⟩)) (toB0 hn (args ⟨1, by decide⟩))

theorem toB0_eval {n : ℕ} (hn : 0 < n) (F : MFormula n) (x : Fin n → Bool) :
    (toB0 hn F).eval x = F.eval x := by
  induction F with
  | var i => rfl
  | const b hb => cases b <;> simp [toB0]
  | app op args ih =>
      cases op with
      | or =>
          simp only [toB0, b0Or_eval, Thm1.Formula.eval_app, MonOp.interp]
          rw [ih ⟨0, by decide⟩, ih ⟨1, by decide⟩]
          rfl
      | and =>
          simp only [toB0, b0And_eval, Thm1.Formula.eval_app, MonOp.interp]
          rw [ih ⟨0, by decide⟩, ih ⟨1, by decide⟩]
          rfl

theorem toB0_depth_le {n : ℕ} (hn : 0 < n) (F : MFormula n) :
    (toB0 hn F).depth ≤ F.depth + 2 := by
  induction F with
  | var i => simp only [toB0, Thm1.Formula.depth_var, Formula.depth_var]; omega
  | const b hb =>
      have hF : (Thm1.Formula.const b hb : MFormula n).depth = 0 := rfl
      rw [hF]
      cases b with
      | false =>
          have h2 : (toB0 hn (Thm1.Formula.const false hb)).depth
              = (b0And (Formula.var (B := B0) ⟨0, hn⟩)
                  (b0Not (Formula.var (B := B0) ⟨0, hn⟩))).depth := rfl
          rw [h2]
          have h3 := b0And_depth_le (Formula.var (B := B0) ⟨0, hn⟩)
            (b0Not (Formula.var (B := B0) ⟨0, hn⟩))
          rw [b0Not_depth_eq, Formula.depth_var] at h3
          omega
      | true =>
          have h2 : (toB0 hn (Thm1.Formula.const true hb)).depth
              = (b0Or (Formula.var (B := B0) ⟨0, hn⟩)
                  (b0Not (Formula.var (B := B0) ⟨0, hn⟩))).depth := rfl
          rw [h2]
          have h3 := b0Or_depth_le (Formula.var (B := B0) ⟨0, hn⟩)
            (b0Not (Formula.var (B := B0) ⟨0, hn⟩))
          rw [b0Not_depth_eq, Formula.depth_var] at h3
          omega
  | app op args ih =>
      cases op with
      | or =>
          have hF : (Thm1.Formula.app MonOp.or args : MFormula n).depth
              = Finset.univ.sup (fun i : Fin 2 => (args i).depth) + 1 := rfl
          rw [hF]
          have hs0 : (args ⟨0, by decide⟩).depth
              ≤ Finset.univ.sup (fun i : Fin 2 => (args i).depth) :=
            Finset.le_sup (s := Finset.univ) (f := fun i : Fin 2 => (args i).depth)
              (Finset.mem_univ _)
          have hs1 : (args ⟨1, by decide⟩).depth
              ≤ Finset.univ.sup (fun i : Fin 2 => (args i).depth) :=
            Finset.le_sup (s := Finset.univ) (f := fun i : Fin 2 => (args i).depth)
              (Finset.mem_univ _)
          have h2 : (toB0 hn (Thm1.Formula.app MonOp.or args)).depth
              = (b0Or (toB0 hn (args ⟨0, by decide⟩)) (toB0 hn (args ⟨1, by decide⟩))).depth :=
            rfl
          rw [h2]
          have h3 := b0Or_depth_le (toB0 hn (args ⟨0, by decide⟩))
            (toB0 hn (args ⟨1, by decide⟩))
          have i0 := ih ⟨0, by decide⟩
          have i1 := ih ⟨1, by decide⟩
          omega
      | and =>
          have hF : (Thm1.Formula.app MonOp.and args : MFormula n).depth
              = Finset.univ.sup (fun i : Fin 2 => (args i).depth) + 1 := rfl
          rw [hF]
          have hs0 : (args ⟨0, by decide⟩).depth
              ≤ Finset.univ.sup (fun i : Fin 2 => (args i).depth) :=
            Finset.le_sup (s := Finset.univ) (f := fun i : Fin 2 => (args i).depth)
              (Finset.mem_univ _)
          have hs1 : (args ⟨1, by decide⟩).depth
              ≤ Finset.univ.sup (fun i : Fin 2 => (args i).depth) :=
            Finset.le_sup (s := Finset.univ) (f := fun i : Fin 2 => (args i).depth)
              (Finset.mem_univ _)
          have h2 : (toB0 hn (Thm1.Formula.app MonOp.and args)).depth
              = (b0And (toB0 hn (args ⟨0, by decide⟩)) (toB0 hn (args ⟨1, by decide⟩))).depth :=
            rfl
          rw [h2]
          have h3 := b0And_depth_le (toB0 hn (args ⟨0, by decide⟩))
            (toB0 hn (args ⟨1, by decide⟩))
          have i0 := ih ⟨0, by decide⟩
          have i1 := ih ⟨1, by decide⟩
          omega

/-! ### Partial depth over `B₀` -/

/-- A formula over `B₀` computes a partial function on its domain. -/
def ComputesOnB0 {n : ℕ} (F : Formula B0 n) (Ψ : PartialBool n) : Prop :=
  ∀ x, Ψ.dom x → F.eval x = Ψ.val x

/-- `D_{B₀}(Ψ)`, the minimal depth of a formula over `B₀` computing `Ψ` on its
domain. -/
noncomputable def partialDepthB0 {n : ℕ} (Ψ : PartialBool n) : ℕ :=
  sInf {d : ℕ | ∃ F : Formula B0 n, F.depth = d ∧ ComputesOnB0 F Ψ}

theorem partialDepthB0_le {n : ℕ} {Ψ : PartialBool n} {F : Formula B0 n}
    (h : ComputesOnB0 F Ψ) : partialDepthB0 Ψ ≤ F.depth :=
  Nat.sInf_le ⟨F, rfl, h⟩

/-- The monotone threshold formula computes `Ψⁿ_{k,t}` on its domain. -/
theorem psi_computes_thr {n k t : ℕ} : ComputesOn (thr n (k + t)) (psi n k t) := by
  intro x _
  rw [thr_eval]
  rfl

theorem exists_computes_psi {n k t : ℕ} : ∃ F : MFormula n, ComputesOn F (psi n k t) :=
  ⟨thr n (k + t), psi_computes_thr⟩

/-- A formula of minimal depth computing a partial function, whenever one
exists. -/
theorem exists_depth_eq_partialDepth {n : ℕ} {Ψ : PartialBool n}
    (hne : ∃ F : MFormula n, ComputesOn F Ψ) :
    ∃ F : MFormula n, F.depth = partialDepth Ψ ∧ ComputesOn F Ψ := by
  have h : {d : ℕ | ∃ F : MFormula n, F.depth = d ∧ ComputesOn F Ψ}.Nonempty := by
    obtain ⟨F, hF⟩ := hne
    exact ⟨F.depth, F, rfl, hF⟩
  exact Nat.sInf_mem h

/-- Turning a monotone formula into a `B₀` formula costs at most two levels of
depth. -/
theorem partialDepthB0_le_partialDepth {n : ℕ} (hn : 0 < n) {Ψ : PartialBool n}
    (hne : ∃ F : MFormula n, ComputesOn F Ψ) :
    partialDepthB0 Ψ ≤ partialDepth Ψ + 2 := by
  obtain ⟨F, hFd, hF⟩ := exists_depth_eq_partialDepth hne
  calc partialDepthB0 Ψ ≤ (toB0 hn F).depth :=
        partialDepthB0_le fun x hx => by rw [toB0_eval]; exact hF x hx
    _ ≤ F.depth + 2 := toB0_depth_le hn F
    _ = partialDepth Ψ + 2 := by rw [hFd]

/-! ### A concrete `B₀` formula for the threshold function -/

/-- A monotone formula of minimal depth for `Ψⁿ_{k,t}`. -/
noncomputable def psiMForm (n k t : ℕ) : MFormula n :=
  Classical.choose (exists_depth_eq_partialDepth (exists_computes_psi (n := n) (k := k) (t := t)))

theorem psiMForm_depth (n k t : ℕ) : (psiMForm n k t).depth = partialDepth (psi n k t) :=
  (Classical.choose_spec
    (exists_depth_eq_partialDepth (exists_computes_psi (n := n) (k := k) (t := t)))).1

theorem psiMForm_computes (n k t : ℕ) : ComputesOn (psiMForm n k t) (psi n k t) :=
  (Classical.choose_spec
    (exists_depth_eq_partialDepth (exists_computes_psi (n := n) (k := k) (t := t)))).2

/-- The corresponding `B₀` formula for `Ψⁿ_{k,t}`. -/
noncomputable def psiForm (n k t : ℕ) (hn : 0 < n) : Formula B0 n :=
  toB0 hn (psiMForm n k t)

theorem psiForm_depth_le (n k t : ℕ) (hn : 0 < n) :
    (psiForm n k t hn).depth ≤ partialDepth (psi n k t) + 2 := by
  unfold psiForm
  calc (toB0 hn (psiMForm n k t)).depth ≤ (psiMForm n k t).depth + 2 := toB0_depth_le hn _
    _ = partialDepth (psi n k t) + 2 := by rw [psiMForm_depth]

theorem psiForm_eval {n k t : ℕ} (hn : 0 < n) {x : Fin n → Bool}
    (hx : (psi n k t).dom x) : (psiForm n k t hn).eval x = (psi n k t).val x := by
  unfold psiForm
  rw [toB0_eval]
  exact psiMForm_computes n k t x hx



/-! ### The comparisons `X_j` -/

/-- The uncertainty interval `I_j = [jt, (j+1)t)`. -/
def uncert (t j σ : ℕ) : Prop := j * t ≤ σ ∧ σ < (j + 1) * t

theorem uncert_iff_div {t : ℕ} (ht : 0 < t) {j σ : ℕ} :
    uncert t j σ ↔ σ / t = j := by
  unfold uncert
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h]; exact Nat.div_mul_le_self σ t
    · rw [← h]
      exact (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_succ_self _)

/-- The `j`-th comparison `X_j = Ψⁿ_{jt+(t−1)/2,(t+1)/2}`: the partial threshold
function whose uncertainty interval is `I_j`.  It takes the value `1` strictly
below `I_j`, `0` strictly above it, and is undefined on `I_j`. -/
def X (n t j : ℕ) : PartialBool n where
  dom x := ¬ uncert t j (onesCount x)
  val x := decide (onesCount x < j * t)

theorem X_dom_iff {n t j : ℕ} {x : Fin n → Bool} :
    (X n t j).dom x ↔ ¬ uncert t j (onesCount x) := Iff.rfl

theorem X_val_eq {n t j : ℕ} (x : Fin n → Bool) :
    (X n t j).val x = decide (onesCount x < j * t) := rfl

theorem X_val_true_iff {n t j : ℕ} (x : Fin n → Bool) :
    (X n t j).val x = true ↔ onesCount x < j * t := by
  rw [X_val_eq]; exact decide_eq_true_iff

theorem X_val_false_iff {n t j : ℕ} (x : Fin n → Bool) :
    (X n t j).val x = false ↔ j * t ≤ onesCount x := by
  rw [X_val_eq, decide_eq_false_iff_not, not_lt]

/-- The comparisons are monotone in `j`. -/
theorem X_mono {n t : ℕ} {x : Fin n → Bool} {j j' : ℕ} (h : j ≤ j') :
    ble ((X n t j).val x) ((X n t j').val x) := by
  refine ble_of_imp ?_
  intro h1
  rw [X_val_true_iff] at h1 ⊢
  have : j * t ≤ j' * t := Nat.mul_le_mul_right t h
  omega

/-- The interval index `J = ⌊σ/t⌋`, i.e. the index of the interval containing
`σ`. -/
def intervalIndex (n t : ℕ) (x : Fin n → Bool) : ℕ := onesCount x / t

theorem intervalIndex_le {n t : ℕ} (ht : 0 < t) (x : Fin n → Bool) (j : ℕ) :
    intervalIndex n t x ≤ j ↔ onesCount x < (j + 1) * t := by
  unfold intervalIndex
  rw [← Nat.lt_succ_iff]
  exact Nat.div_lt_iff_lt_mul ht

/-- `J′ = J + 1`: the first index `j` at which `X_j` takes the value `1`. -/
def Jprime (n t : ℕ) (x : Fin n → Bool) : ℕ := onesCount x / t + 1

theorem X_val_true_iff_Jprime {n t j : ℕ} (ht : 0 < t) (x : Fin n → Bool) :
    (X n t j).val x = true ↔ Jprime n t x ≤ j := by
  rw [X_val_true_iff, Jprime]
  constructor
  · intro h
    have : onesCount x / t < j := (Nat.div_lt_iff_lt_mul ht).mpr h
    omega
  · intro h
    have h' : onesCount x / t < j := by omega
    exact (Nat.div_lt_iff_lt_mul ht).mp h'

theorem X_undef_iff {n t j : ℕ} (ht : 0 < t) (x : Fin n → Bool) :
    ¬ (X n t j).dom x ↔ intervalIndex n t x = j := by
  rw [X_dom_iff, not_not, uncert_iff_div ht]
  rfl

/-- `X_{J−1} = 0` when the interval index is positive. -/
theorem X_pred_val_false {n t : ℕ} (ht : 0 < t) (x : Fin n → Bool)
    (h : 0 < intervalIndex n t x) :
    (X n t (intervalIndex n t x - 1)).val x = false := by
  rw [X_val_false_iff]
  unfold intervalIndex at h ⊢
  have := Nat.div_mul_le_self (onesCount x) t
  have h2 : (onesCount x / t - 1) * t ≤ onesCount x / t * t :=
    Nat.mul_le_mul_right t (by omega)
  omega

/-- `X_{J+1} = 1`. -/
theorem X_succ_val_true {n t : ℕ} (ht : 0 < t) (x : Fin n → Bool) :
    (X n t (intervalIndex n t x + 1)).val x = true := by
  rw [X_val_true_iff]
  unfold intervalIndex
  have : onesCount x / t < onesCount x / t + 1 := by omega
  exact (Nat.div_lt_iff_lt_mul ht).mp this

/-! ### Halves of `t ± 1` -/

theorem div2_pred_mul (m : ℕ) (hm : 1 ≤ m) : (2 * m - 1) / 2 = m - 1 :=
  Nat.div_eq_of_lt_le (k := m - 1) (n := 2) (m := 2 * m - 1) (by omega) (by omega)

theorem div2_succ_mul (m : ℕ) : (2 * m + 1) / 2 = m :=
  Nat.div_eq_of_lt_le (k := m) (n := 2) (m := 2 * m + 1) (by omega) (by omega)

/-- `⌊(t−1)/2⌋ + ⌊(t+1)/2⌋ ≤ t`. -/
theorem div2_pred_add_div2_succ_le (t : ℕ) : (t - 1) / 2 + (t + 1) / 2 ≤ t := by
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · have ht : t = 2 * k := by omega
    rw [ht]
    rcases k with _ | k
    · simp
    · rw [div2_pred_mul (k + 1) (by omega), div2_succ_mul (k + 1)]; omega
  · have ht : t = 2 * k + 1 := by omega
    rw [ht]
    have e1 : (2 * k + 1 - 1) / 2 = k := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_comm, Nat.mul_div_cancel _ (by norm_num)]
    have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, Nat.mul_comm,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [e1, e2]; omega

/-- `⌊(t+1)/2⌋ ≤ ⌊(t−1)/2⌋ + 1`. -/
theorem div2_succ_le (t : ℕ) : (t + 1) / 2 ≤ (t - 1) / 2 + 1 := by
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · have ht : t = 2 * k := by omega
    rw [ht]
    rcases k with _ | k
    · simp
    · rw [div2_pred_mul (k + 1) (by omega), div2_succ_mul (k + 1)]
      omega
  · have ht : t = 2 * k + 1 := by omega
    rw [ht]
    have e1 : (2 * k + 1 - 1) / 2 = k := by
      rw [show 2 * k + 1 - 1 = 2 * k by omega, Nat.mul_comm, Nat.mul_div_cancel _ (by norm_num)]
    have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, Nat.mul_comm,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [e1, e2]

/-- The comparison `X_j` is defined wherever the partial threshold function
`Ψⁿ_{jt+(t−1)/2,(t+1)/2}` is. -/
theorem X_dom_psi {n t j : ℕ} {x : Fin n → Bool} :
    (X n t j).dom x → (psi n (j * t + (t - 1) / 2) ((t + 1) / 2)).dom x := by
  simp only [X, psi, uncert]
  intro h
  have h' : onesCount x < j * t ∨ (j + 1) * t ≤ onesCount x := by
    by_contra hc
    push Not at hc
    exact h ⟨hc.1, hc.2⟩
  have hdiv := div2_pred_add_div2_succ_le t
  have hdiv2 := div2_succ_le t
  have hj : (j + 1) * t = j * t + t := by rw [Nat.succ_mul]
  rcases h' with h1 | h1
  · right; omega
  · left; omega

/-- On its domain the comparison `X_j` is the complement of
`Ψⁿ_{jt+(t−1)/2,(t+1)/2}`. -/
theorem X_val_psi {n t j : ℕ} (ht : 0 < t) {x : Fin n → Bool} (hx : (X n t j).dom x) :
    (X n t j).val x = !((psi n (j * t + (t - 1) / 2) ((t + 1) / 2)).val x) := by
  simp only [X, psi]
  have h' : onesCount x < j * t ∨ (j + 1) * t ≤ onesCount x := by
    by_contra hc
    push Not at hc
    exact hx ⟨hc.1, hc.2⟩
  have hdiv := div2_pred_add_div2_succ_le t
  have hdiv2 := div2_succ_le t
  have hj : (j + 1) * t = j * t + t := by rw [Nat.succ_mul]
  rcases h' with h1 | h1
  · have h2 : ¬ (j * t + (t - 1) / 2 + (t + 1) / 2 ≤ onesCount x) := by omega
    simp [h1, h2]
  · have h2 : j * t + (t - 1) / 2 + (t + 1) / 2 ≤ onesCount x := by omega
    have h3 : ¬ (onesCount x < j * t) := by omega
    simp [h3, h2]


/-! ### Binary digits -/

/-- The `i`-th binary digit of `m` is the parity of `m / 2^i`. -/
theorem testBit_eq_decide_div_mod (m : ℕ) : ∀ i : ℕ, m.testBit i = decide (m / 2 ^ i % 2 = 1)
  | 0 => by rw [Nat.testBit_zero]; norm_num
  | i + 1 => by
      rw [Nat.testBit_succ, testBit_eq_decide_div_mod (m / 2) i]
      congr 2
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- **Bit extraction.**  For `1 ≤ m ≤ 2^r` and `i < r`, the `i`-th binary digit
of `m` is set exactly when `m` lies in the upper half of one of the blocks of
size `2^{i+1}`, i.e. when `2^{i+1}p - 2^i - 1 < m ≤ 2^{i+1}p - 1` for some
`p ≤ 2^{r-i-1}`. -/
theorem testBit_eq_exists {r i m : ℕ} (hi : i < r) (hm1 : 1 ≤ m) (hm : m ≤ 2 ^ r) :
    m.testBit i = true ↔
      ∃ p : Fin (2 ^ (r - i - 1)),
        2 ^ (i + 1) * (p.val + 1) - 2 ^ i - 1 < m ∧ m ≤ 2 ^ (i + 1) * (p.val + 1) - 1 := by
  set P := 2 ^ (i + 1) with hP
  set Q := 2 ^ i with hQ
  have hP2 : P = 2 * Q := by rw [hP, hQ, pow_succ]; ring
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hPpos : 0 < P := by rw [hP]; positivity
  have hPQ : Q + 1 ≤ P := by omega
  set q := m / P with hq
  set r' := m % P with hr'
  have htm : P * q + r' = m := Nat.div_add_mod m P
  have hr'lt : r' < P := Nat.mod_lt m hPpos
  set t := P * q with ht
  have httm : t + r' = m := htm
  have hbit : m.testBit i = true ↔ Q ≤ r' := by
    rw [testBit_eq_decide_div_mod, ← hQ]
    have hdiv : m / Q = 2 * q + r' / Q := by
      have h1 : m = Q * (2 * q) + r' := by rw [← httm, ht, hP2]; ring
      rw [h1, Nat.mul_add_div hQpos]
    rw [hdiv]
    have hr'Q : r' / Q < 2 := by
      rw [Nat.div_lt_iff_lt_mul hQpos]; omega
    have hmod : (2 * q + r' / Q) % 2 = r' / Q := by
      rw [show 2 * q + r' / Q = r' / Q + q * 2 by ring, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hr'Q]
    rw [hmod, decide_eq_true_iff]
    constructor
    · intro h
      have h1 := (Nat.le_div_iff_mul_le hQpos).mp (le_of_eq h.symm)
      simpa using h1
    · intro h
      exact Nat.div_eq_of_lt_le (by simpa using h) (by omega)
  rw [hbit]
  have hpow : 2 ^ r = 2 ^ (r - i - 1) * P := by
    rw [hP, show r - i - 1 = r - (i + 1) by omega]
    exact (Nat.pow_sub_mul_pow 2 (m := i + 1) (n := r) (by omega)).symm
  constructor
  · intro hQr
    have htle : t ≤ m := by omega
    have htlt : t < 2 ^ r := by omega
    have hqle : q < 2 ^ (r - i - 1) := by
      rw [hpow, Nat.mul_comm] at htlt
      rw [ht] at htlt
      exact (Nat.mul_lt_mul_left hPpos).mp htlt
    refine ⟨⟨q, hqle⟩, ?_, ?_⟩
    · have h1 : P * (q + 1) - Q - 1 = t + (P - Q - 1) := by
        rw [ht, Nat.mul_succ]; omega
      rw [h1, ← httm]; omega
    · have h1 : P * (q + 1) - 1 = t + P - 1 := by
        rw [ht, Nat.mul_succ]
      rw [h1, ← httm]; omega
  · rintro ⟨p, hp1, hp2⟩
    set u := P * (p.val + 1) with hu
    have hupper : t + r' < u := by omega
    have hpge : q ≤ p.val := by
      by_contra hc
      push Not at hc
      have h1 : u ≤ P * q := by
        rw [hu]
        exact Nat.mul_le_mul_left P (by omega)
      omega
    have hlower : t + P ≤ u := by
      rw [hu, ht]
      calc P * q + P = P * (q + 1) := by ring
        _ ≤ P * (p.val + 1) := Nat.mul_le_mul_left P (by omega)
    omega


/-! ### The comparison `X_j` as a `B₀` formula -/

/-- The comparison `X_j` as a `B₀` formula. -/
noncomputable def Xform (n t j : ℕ) (hn : 0 < n) : Formula B0 n :=
  b0Not (psiForm n (j * t + (t - 1) / 2) ((t + 1) / 2) hn)

theorem Xform_eval {n t j : ℕ} (hn : 0 < n) (ht : 0 < t) {x : Fin n → Bool}
    (hx : (X n t j).dom x) : (Xform n t j hn).eval x = (X n t j).val x := by
  unfold Xform
  rw [b0Not_eval, psiForm_eval hn (X_dom_psi hx), X_val_psi ht hx]

/-! ### Depth of the comparisons -/

/-- The depth of the threshold function underlying the comparison `X_j`. -/
noncomputable def Th (n t j : ℕ) : ℕ :=
  partialDepth (psi n (j * t + (t - 1) / 2) ((t + 1) / 2))

theorem Xform_depth {n t j : ℕ} (hn : 0 < n) :
    (Xform n t j hn).depth ≤ Th n t j + 3 := by
  have h1 := psiForm_depth_le n (j * t + (t - 1) / 2) ((t + 1) / 2) hn
  have h2 := b0Not_depth_eq (psiForm n (j * t + (t - 1) / 2) ((t + 1) / 2) hn)
  unfold Xform Th
  omega

/-- The constant `0` over `B₀`. -/
def cfalse {n : ℕ} (hn : 0 < n) : Formula B0 n :=
  b0And (Formula.var (B := B0) ⟨0, hn⟩) (b0Not (Formula.var (B := B0) ⟨0, hn⟩))

/-- The constant `1` over `B₀`. -/
def ctrue {n : ℕ} (hn : 0 < n) : Formula B0 n :=
  b0Or (Formula.var (B := B0) ⟨0, hn⟩) (b0Not (Formula.var (B := B0) ⟨0, hn⟩))

theorem cfalse_eval {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (cfalse hn).eval x = false := by
  simp [cfalse, b0And_eval, b0Not_eval]

theorem ctrue_eval {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (ctrue hn).eval x = true := by
  simp [ctrue, b0Or_eval, b0Not_eval]

theorem cfalse_depth {n : ℕ} (hn : 0 < n) : (cfalse hn).depth ≤ 2 := by
  have h := b0And_depth_le (Formula.var (B := B0) ⟨0, hn⟩)
    (b0Not (Formula.var (B := B0) ⟨0, hn⟩))
  rw [b0Not_depth_eq, Formula.depth_var] at h
  unfold cfalse
  omega

theorem ctrue_depth {n : ℕ} (hn : 0 < n) : (ctrue hn).depth ≤ 2 := by
  have h := b0Or_depth_le (Formula.var (B := B0) ⟨0, hn⟩)
    (b0Not (Formula.var (B := B0) ⟨0, hn⟩))
  rw [b0Not_depth_eq, Formula.depth_var] at h
  unfold ctrue
  omega

/-- The hypotheses of Theorem 1 for the parameters of `X_j`. -/
abbrev okTh (n t j : ℕ) : Prop :=
  (t + 1) / 2 ≤ j * t + (t - 1) / 2 ∧ j * t + (t - 1) / 2 + (t + 1) / 2 ≤ n

/-- The depth of the comparison `X_j`, for the parameters satisfying the
hypotheses of Theorem 1 (and `0` otherwise). -/
noncomputable def ThB (n t j : ℕ) : ℕ := if okTh n t j then Th n t j else 0

/-- A `B₀` formula for `X_j` whose depth is controlled: the threshold formula
when Theorem 1 applies, and the appropriate constant at the two boundaries. -/
noncomputable def XformB (n t r j : ℕ) (hn : 0 < n) : Formula B0 n :=
  if okTh n t j then Xform n t j hn else if j = 0 then cfalse hn else ctrue hn

theorem XformB_depth {n t r j : ℕ} (hn : 0 < n) :
    (XformB n t r j hn).depth ≤ ThB n t j + 3 := by
  unfold XformB ThB
  split_ifs with h h0
  · exact Xform_depth hn
  · exact le_trans (cfalse_depth hn) (by omega)
  · exact le_trans (ctrue_depth hn) (by omega)

theorem half_le_kt {t j : ℕ} (ht : 0 < t) (hj : 1 ≤ j) :
    (t + 1) / 2 ≤ j * t + (t - 1) / 2 := by
  have h1 := div2_succ_le t
  have h2 : t ≤ j * t := Nat.le_mul_of_pos_left t hj
  omega

theorem kt_le_n {n t r j : ℕ} (ht : 0 < t) (hrn : n = 2 ^ r * t - 1)
    (hj : j + 1 < 2 ^ r) :
    j * t + (t - 1) / 2 + (t + 1) / 2 ≤ n := by
  have h1 := div2_pred_add_div2_succ_le t
  have h2 : (j + 1) * t ≤ (2 ^ r - 1) * t :=
    Nat.mul_le_mul_right t (by omega)
  have h3 : j * t + t = (j + 1) * t := by rw [Nat.succ_mul]
  have h4 : (2 ^ r - 1) * t = 2 ^ r * t - t := by rw [Nat.sub_mul, one_mul]
  have h5 : t ≤ 2 ^ r * t := Nat.le_mul_of_pos_left t (by positivity)
  omega

theorem XformB_eval {n t r j : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hrn : n = 2 ^ r * t - 1) (hj : j < 2 ^ r)
    {x : Fin n → Bool} (hx : (X n t j).dom x) :
    (XformB n t r j hn).eval x = (X n t j).val x := by
  unfold XformB
  split_ifs with h h0
  · exact Xform_eval hn ht hx
  · subst h0
    have hz : ¬ (onesCount x < 0) := by omega
    rw [X_val_eq, cfalse_eval]
    simp [hz]
  · have hj0 : j ≠ 0 := h0
    have hk2 : ¬ (j * t + (t - 1) / 2 + (t + 1) / 2 ≤ n) := by
      intro hle
      exact h ⟨half_le_kt ht (by omega), hle⟩
    have hval : (X n t j).val x = true := by
      rw [X_val_true_iff]
      have hdom : ¬ (j * t ≤ onesCount x ∧ onesCount x < (j + 1) * t) := hx
      have hσ : onesCount x ≤ n := onesCount_le x
      have hle1 : j * t + (t - 1) / 2 + (t + 1) / 2 ≤ (j + 1) * t := by
        have h3 : j * t + t = (j + 1) * t := by rw [Nat.succ_mul]
        have h1 := div2_pred_add_div2_succ_le t
        omega
      have hbig : n < (j + 1) * t := by omega
      have hdisj : onesCount x < j * t ∨ (j + 1) * t ≤ onesCount x := by
        by_contra hc
        push Not at hc
        exact hdom ⟨hc.1, hc.2⟩
      rcases hdisj with hlt | hge
      · exact hlt
      · omega
    rw [ctrue_eval, hval]

/-! ### The digits of equation (3) -/

/-- Left end of the upper half of block `p` at level `i`
(=`2^{i+1}p − 2^i − 1`, the paper's `2^{i+1}p − 2^i − 1` with `p` one-based). -/
def jlo (i p : ℕ) : ℕ := 2 ^ (i + 1) * p - 2 ^ i - 1

/-- Right end of block `p` at level `i` (=`2^{i+1}p − 1`). -/
def jhi (i p : ℕ) : ℕ := 2 ^ (i + 1) * p - 1

/-- The `p`-th conjunctive term of equation (3) for bit `i`. -/
noncomputable def Jterm (n t r i p : ℕ) (hn : 0 < n) : Formula B0 n :=
  b0And (b0Not (XformB n t r (jlo i p) hn)) (XformB n t r (jhi i p) hn)

/-- Equation (3): the `i`-th digit of the first-one operator `J′`, computed as a
balanced disjunction of `2^{r−i−1}` conjunctive terms. -/
noncomputable def Jcomp (n t r i : ℕ) (hn : 0 < n) : Formula B0 n :=
  orPow0 (r - i - 1) fun p => Jterm n t r i (p.val + 1) hn

/-- The `i`-th digit of `J′` as a partial function: it is defined wherever all
the comparisons entering (3) are defined. -/
def Jbit (n t r i : ℕ) : PartialBool n where
  dom x := ∀ p : Fin (2 ^ (r - i - 1)),
    (X n t (jlo i (p.val + 1))).dom x ∧ (X n t (jhi i (p.val + 1))).dom x
  val x := (Jprime n t x).testBit i

theorem Jbit_val (n t r i : ℕ) (x : Fin n → Bool) :
    (Jbit n t r i).val x = (Jprime n t x).testBit i := rfl

theorem Jbit_dom {n t r i : ℕ} {x : Fin n → Bool} (h : (Jbit n t r i).dom x)
    (p : Fin (2 ^ (r - i - 1))) :
    (X n t (jlo i (p.val + 1))).dom x ∧ (X n t (jhi i (p.val + 1))).dom x := h p

/-! ### Bounds on the block indices -/

theorem jlo_lt {i p r : ℕ} (hi : i < r) (hp : p ≤ 2 ^ (r - i - 1)) : jlo i p < 2 ^ r := by
  have hpow : 2 ^ (i + 1) * 2 ^ (r - i - 1) = 2 ^ r := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (i + 1) * p ≤ 2 ^ r := by
    rw [← hpow]; exact Nat.mul_le_mul_left _ hp
  have h3 : 0 < 2 ^ i := by positivity
  have h4 : 0 < 2 ^ r := by positivity
  unfold jlo
  omega

theorem jhi_lt {i p r : ℕ} (hi : i < r) (hp : p ≤ 2 ^ (r - i - 1)) : jhi i p < 2 ^ r := by
  have hpow : 2 ^ (i + 1) * 2 ^ (r - i - 1) = 2 ^ r := by
    rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ^ (i + 1) * p ≤ 2 ^ r := by
    rw [← hpow]; exact Nat.mul_le_mul_left _ hp
  have h4 : 0 < 2 ^ r := by positivity
  unfold jhi
  omega

/-! ### Equation (3) computes the digits of `J′` -/

theorem Jcomp_eval {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r) (hi : i < r)
    (hrn : n = 2 ^ r * t - 1) {x : Fin n → Bool} (hx : (Jbit n t r i).dom x) :
    (Jcomp n t r i hn).eval x = (Jbit n t r i).val x := by
  have hσ : onesCount x ≤ n := onesCount_le x
  have hJ1 : 1 ≤ Jprime n t x := by
    show 1 ≤ onesCount x / t + 1
    exact Nat.le_add_left 1 _
  have hJr : Jprime n t x ≤ 2 ^ r := by
    have hs : onesCount x < 2 ^ r * t := by omega
    have hd : onesCount x / t < 2 ^ r := (Nat.div_lt_iff_lt_mul ht).mpr hs
    show onesCount x / t + 1 ≤ 2 ^ r
    exact Nat.succ_le_of_lt hd
  have hpl : ∀ p : Fin (2 ^ (r - i - 1)), p.val + 1 ≤ 2 ^ (r - i - 1) := by
    intro p
    have := p.isLt
    omega
  have hiff : ((Jcomp n t r i hn).eval x = true) ↔ ((Jbit n t r i).val x = true) := by
    have e1 : ((Jcomp n t r i hn).eval x = true) ↔
        ∃ p : Fin (2 ^ (r - i - 1)),
          (X n t (jlo i (p.val + 1))).val x = false ∧
          (X n t (jhi i (p.val + 1))).val x = true := by
      unfold Jcomp
      rw [orPow0_eval]
      constructor
      · rintro ⟨p, hp⟩
        unfold Jterm at hp
        rw [b0And_eval, Bool.and_eq_true, b0Not_eval,
          XformB_eval hn ht hrn (jlo_lt hi (hpl p)) (Jbit_dom hx p).1,
          XformB_eval hn ht hrn (jhi_lt hi (hpl p)) (Jbit_dom hx p).2] at hp
        obtain ⟨h1, h2⟩ := hp
        exact ⟨p, by simpa using h1, h2⟩
      · rintro ⟨p, h1, h2⟩
        refine ⟨p, ?_⟩
        unfold Jterm
        rw [b0And_eval, b0Not_eval,
          XformB_eval hn ht hrn (jlo_lt hi (hpl p)) (Jbit_dom hx p).1,
          XformB_eval hn ht hrn (jhi_lt hi (hpl p)) (Jbit_dom hx p).2, h1, h2]
        rfl
    have e2 : (∃ p : Fin (2 ^ (r - i - 1)),
          (X n t (jlo i (p.val + 1))).val x = false ∧
          (X n t (jhi i (p.val + 1))).val x = true) ↔
        ∃ p : Fin (2 ^ (r - i - 1)),
          jlo i (p.val + 1) < Jprime n t x ∧ Jprime n t x ≤ jhi i (p.val + 1) := by
      constructor
      · rintro ⟨p, h1, h2⟩
        refine ⟨p, ?_, ?_⟩
        · have h := (X_val_false_iff (j := jlo i (p.val + 1)) x).mp h1
          exact Nat.lt_succ_iff.mpr ((Nat.le_div_iff_mul_le ht).mpr h)
        · have h := (X_val_true_iff (j := jhi i (p.val + 1)) x).mp h2
          have hlt : onesCount x / t < jhi i (p.val + 1) :=
            (Nat.div_lt_iff_lt_mul ht).mpr h
          exact Nat.succ_le_of_lt hlt
      · rintro ⟨p, h1, h2⟩
        refine ⟨p, ?_, ?_⟩
        · rw [X_val_false_iff]
          exact (Nat.le_div_iff_mul_le ht).mp (Nat.lt_succ_iff.mp h1)
        · rw [X_val_true_iff]
          exact (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_of_succ_le h2)
    have key : (Jprime n t x).testBit i = true ↔
        ∃ p : Fin (2 ^ (r - i - 1)),
          jlo i (p.val + 1) < Jprime n t x ∧ Jprime n t x ≤ jhi i (p.val + 1) :=
      testBit_eq_exists hi hJ1 hJr
    rw [Jbit_val, e1]
    exact e2.trans key.symm
  cases a : (Jcomp n t r i hn).eval x <;> cases b : (Jbit n t r i).val x <;> simp_all

/-! ### Depth of the digit formulae -/

/-- The largest depth of the threshold formula needed by the digit `i` of
equation (3). -/
noncomputable def hmax (n t r i : ℕ) : ℕ :=
  Finset.univ.sup (fun p : Fin (2 ^ (r - i - 1)) =>
    max (ThB n t (jlo i (p.val + 1))) (ThB n t (jhi i (p.val + 1))))

theorem Jterm_depth {n t r i p : ℕ} (hn : 0 < n) :
    (Jterm n t r i p hn).depth
      ≤ max (ThB n t (jlo i p)) (ThB n t (jhi i p)) + 5 := by
  have h1 := XformB_depth (n := n) (t := t) (r := r) (j := jlo i p) hn
  have h2 := XformB_depth (n := n) (t := t) (r := r) (j := jhi i p) hn
  have h3 := b0Not_depth_eq (XformB n t r (jlo i p) hn)
  have h4 := b0And_depth_le (b0Not (XformB n t r (jlo i p) hn))
    (XformB n t r (jhi i p) hn)
  have hm1 : ThB n t (jlo i p) ≤ max (ThB n t (jlo i p)) (ThB n t (jhi i p)) :=
    le_max_left _ _
  have hm2 : ThB n t (jhi i p) ≤ max (ThB n t (jlo i p)) (ThB n t (jhi i p)) :=
    le_max_right _ _
  unfold Jterm
  omega

theorem Jcomp_depth_le {n t r i : ℕ} (hn : 0 < n) :
    (Jcomp n t r i hn).depth ≤ (r - i - 1) + (hmax n t r i + 5) := by
  have h := orPow0_depth_le (r - i - 1)
    (fun p : Fin (2 ^ (r - i - 1)) => Jterm n t r i (p.val + 1) hn)
  refine le_trans h ?_
  apply Nat.add_le_add_left
  refine Finset.sup_le ?_
  intro p _
  calc (Jterm n t r i (p.val + 1) hn).depth
      ≤ max (ThB n t (jlo i (p.val + 1))) (ThB n t (jhi i (p.val + 1))) + 5 :=
        Jterm_depth hn
    _ ≤ hmax n t r i + 5 := by
        apply Nat.add_le_add_right
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (2 ^ (r - i - 1)))))
          (f := fun p : Fin (2 ^ (r - i - 1)) =>
            max (ThB n t (jlo i (p.val + 1))) (ThB n t (jhi i (p.val + 1))))
          (Finset.mem_univ p)

/-- **Depth of a digit of `J′`** (equation (3)). -/
theorem partialDepthB0_Jbit_le {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hi : i < r) (hrn : n = 2 ^ r * t - 1) :
    partialDepthB0 (Jbit n t r i) ≤ (r - i - 1) + (hmax n t r i + 5) :=
  le_trans (partialDepthB0_le (fun x hx => Jcomp_eval hn ht hr hi hrn hx))
    (Jcomp_depth_le hn)


/-! ### Corollary 1 on the depth of the first-one operator -/

/-- `log_{√5−1} 2`, the constant `log_{√5−1} 2` of Corollary 1. -/
noncomputable def L5 : ℝ := Real.logb (Real.sqrt 5 - 1) 2

theorem L5_ge_one : 1 ≤ L5 := by
  simpa [L5] using logb_two_le_logb_sqrt5 (u := 2) (by norm_num : (1:ℝ) ≤ 2)

theorem L5_pos : 0 < L5 := lt_of_lt_of_le one_pos L5_ge_one

theorem L5_nonneg : 0 ≤ L5 := le_of_lt L5_pos

theorem logb_sqrt5_eq (x : ℝ) : Real.logb (Real.sqrt 5 - 1) x = L5 * Real.logb 2 x := by
  have h := Real.mul_logb (a := Real.sqrt 5 - 1) (b := 2) (c := x)
    (by norm_num) (by norm_num) (by norm_num)
  rw [L5]
  exact h.symm

theorem logb_logb_choose_add_le {n a b : ℕ} (hn : 1 ≤ n) (ha : a ≤ n) (hb : b ≤ n) :
    Real.logb 2 (Real.logb 2 ((n.choose a + n.choose b : ℕ) : ℝ)) ≤ Real.logb 2 (n:ℝ) + 1 := by
  set N : ℕ := n.choose a + n.choose b
  have hNa : 1 ≤ n.choose a := Nat.choose_pos ha
  have hNb : 1 ≤ n.choose b := Nat.choose_pos hb
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hN2 : 2 ≤ N := by omega
  have hNn : N ≤ 2 ^ (n+1) := by
    have h1 := Nat.choose_le_two_pow n a
    have h2 := Nat.choose_le_two_pow n b
    have hp : (2:ℕ) ^ (n+1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    omega
  have hlog1 : Real.logb 2 (N : ℝ) ≤ (n : ℝ) + 1 := by
    have hle : Real.logb 2 (N : ℝ) ≤ Real.logb 2 ((2:ℝ) ^ (n+1)) := by
      refine Real.logb_le_logb_of_le (b := 2) (by norm_num) hNpos ?_
      exact_mod_cast hNn
    have hpow : Real.logb 2 ((2:ℝ) ^ (n+1)) = (n : ℝ) + 1 := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      push_cast; ring
    linarith
  have hlogpos : 0 < Real.logb 2 (N : ℝ) :=
    Real.logb_pos (b := 2) (by norm_num) (by exact_mod_cast hN2)
  have hstep1 : Real.logb 2 (Real.logb 2 (N : ℝ)) ≤ Real.logb 2 ((n : ℝ) + 1) := by
    refine Real.logb_le_logb_of_le (b := 2) (by norm_num) hlogpos ?_
    simpa using hlog1
  have hstep2 : Real.logb 2 ((n : ℝ) + 1) ≤ Real.logb 2 (2 * (n : ℝ)) := by
    refine Real.logb_le_logb_of_le (b := 2) (by norm_num) ?_ ?_
    · have : (0:ℝ) ≤ (n:ℝ) := by positivity
      linarith
    · have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
  have hstep3 : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) := by
    rw [Real.logb_mul (b := 2) (by norm_num) (by positivity)]
    rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  calc Real.logb 2 (Real.logb 2 (N : ℝ))
      ≤ Real.logb 2 ((n : ℝ) + 1) := hstep1
    _ ≤ Real.logb 2 (2 * (n : ℝ)) := hstep2
    _ = 1 + Real.logb 2 (n : ℝ) := hstep3
    _ = Real.logb 2 (n : ℝ) + 1 := by ring

theorem okTh_one_le {n t j : ℕ} (ht : 0 < t) (h : okTh n t j) : 1 ≤ j := by
  unfold okTh at h
  by_contra hj
  push Not at hj
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [Nat.zero_mul, Nat.zero_add] at h
  omega

set_option maxHeartbeats 1000000 in
theorem ThB_le {n t r j : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) (hj : j < 2 ^ r) :
    (ThB n t j : ℝ) ≤ L5 * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46009 := by
  unfold ThB
  split_ifs with hok
  · have hj1 : 1 ≤ j := okTh_one_le ht hok
    set k := j * t + (t - 1) / 2 with hk
    set t' := (t + 1) / 2 with ht'
    have ht'pos : 0 < t' := by omega
    have hkt : t' ≤ k := hok.1
    have hkn : k + t' ≤ n := hok.2
    have hTk : Th n t j = partialDepth (psi n k t') := by
      unfold Th
      rw [← hk, ← ht']
    have hmain := theorem1 (n := n) (k := k) (t := t') hn ht'pos hkt hkn
    have ht'posR : (0:ℝ) < (t':ℝ) := by exact_mod_cast ht'pos
    have hkposR : (0:ℝ) < (k:ℝ) := by
      have : 0 < k := lt_of_lt_of_le ht'pos hkt
      exact_mod_cast this
    have hqpos : (0:ℝ) < (k:ℝ)/(t':ℝ) := div_pos hkposR ht'posR
    have hk_le : k ≤ 2 * j * t := by
      have h1 : (t - 1) / 2 ≤ t := by
        have := Nat.div_le_self (t - 1) 2
        omega
      have h2 : j * t + t = (j + 1) * t := by rw [Nat.succ_mul]
      have h3 : (j + 1) * t ≤ 2 * j * t := by
        have : j + 1 ≤ 2 * j := by omega
        exact Nat.mul_le_mul_right t this
      omega
    have ht_le : t ≤ 2 * t' := by omega
    have hqle : (k:ℝ)/(t':ℝ) ≤ 4 * (j:ℝ) := by
      rw [div_le_iff₀ ht'posR]
      have h1 : (k:ℝ) ≤ 2 * (j:ℝ) * t := by exact_mod_cast hk_le
      have h2 : (t:ℝ) ≤ 2 * (t':ℝ) := by exact_mod_cast ht_le
      nlinarith
    have hmono := Real.logb_le_logb_of_le (b := Real.sqrt 5 - 1) sqrt5_sub_one_gt_one hqpos hqle
    have hlogj : Real.logb (Real.sqrt 5 - 1) (4 * (j:ℝ)) = 2 * L5 + L5 * Real.logb 2 (j:ℝ) := by
      rw [Real.logb_mul (b := Real.sqrt 5 - 1) (by norm_num) (by positivity)]
      rw [logb_sqrt5_eq (4:ℝ), logb_sqrt5_eq (j:ℝ)]
      have h4 : Real.logb 2 (4:ℝ) = 2 := by
        have : (4:ℝ) = 2 ^ (2:ℕ) := by norm_num
        rw [this, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
        norm_num
      rw [h4]; ring
    have ha : Real.logb (Real.sqrt 5 - 1) ((k:ℝ)/(t':ℝ)) ≤ 2 * L5 + L5 * Real.logb 2 (j:ℝ) := by
      calc Real.logb (Real.sqrt 5 - 1) ((k:ℝ)/(t':ℝ))
          ≤ Real.logb (Real.sqrt 5 - 1) (4 * (j:ℝ)) := hmono
        _ = 2 * L5 + L5 * Real.logb 2 (j:ℝ) := hlogj
    have hkjt : j * t ≤ k := by omega
    have hncast : (n:ℝ) = (2:ℝ)^r * (t:ℝ) - 1 := by
      rw [hrn]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ r * t)]
      ring
    have hpow2 : Real.logb 2 ((2:ℝ)^r) = (r:ℝ) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      ring
    have hnkpos : (0:ℝ) < (n:ℝ)/(k:ℝ) := div_pos (by exact_mod_cast hn) hkposR
    have hnat : n * j ≤ 2 ^ r * k := by
      have h1 : n ≤ 2 ^ r * t := by omega
      calc n * j ≤ (2 ^ r * t) * j := Nat.mul_le_mul_right j h1
        _ = 2 ^ r * (j * t) := by ring
        _ ≤ 2 ^ r * k := Nat.mul_le_mul_left _ hkjt
    have hnk_le : (n:ℝ)/(k:ℝ) ≤ (2:ℝ)^r / (j:ℝ) := by
      rw [div_le_div_iff₀ hkposR (by exact_mod_cast hj1)]
      exact_mod_cast hnat
    have hb : Real.logb 2 ((n:ℝ)/(k:ℝ)) ≤ (r:ℝ) - Real.logb 2 (j:ℝ) := by
      have hle := Real.logb_le_logb_of_le (b := 2) (by norm_num) hnkpos hnk_le
      have hdiv : Real.logb 2 ((2:ℝ)^r / (j:ℝ)) = (r:ℝ) - Real.logb 2 (j:ℝ) := by
        rw [Real.logb_div (by positivity) (by exact_mod_cast (Nat.ne_of_gt hj1)), hpow2]
      linarith [hle, hdiv]
    have hc := logb_logb_choose_add_le (n := n) (a := k + t') (b := k - t') (by omega) (by omega) (by omega)
    have hjle : Real.logb 2 (j:ℝ) ≤ (r:ℝ) := by
      have hjpos : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj1
      have hle : (j:ℝ) ≤ (2:ℝ)^r := by
        have : j ≤ 2 ^ r := by omega
        exact_mod_cast this
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hjpos hle
      have hpow : Real.logb 2 ((2:ℝ)^r) = (r:ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
        ring
      linarith [this]
    have hcoef : (0:ℝ) ≤ L5 - 1 := by linarith [L5_ge_one]
    have hmul : (L5 - 1) * Real.logb 2 (j:ℝ) ≤ (L5 - 1) * (r:ℝ) :=
      mul_le_mul_of_nonneg_left hjle hcoef
    rw [hTk]
    linarith [hmain, ha, hb, hc, hmul]
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hlog : 0 ≤ Real.logb 2 (n:ℝ) := Real.logb_nonneg (by norm_num) hn1
    have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
    have : (0:ℝ) ≤ L5 * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46009 := by
      nlinarith [L5_nonneg]
    simpa using this

noncomputable def ThMax (n r : ℕ) : ℕ :=
  ⌈L5 * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46009⌉₊

theorem ThB_le_ThMax {n t r j : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) (hj : j < 2 ^ r) :
    ThB n t j ≤ ThMax n r := by
  have h := ThB_le hn ht hr hrn hj
  have h1 : (ThB n t j : ℝ) ≤ ((ThMax n r : ℕ) : ℝ) := by
    unfold ThMax
    exact le_trans h (Nat.le_ceil _)
  exact_mod_cast h1

theorem hmax_le_ThMax {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) (hi : i < r) :
    hmax n t r i ≤ ThMax n r := by
  unfold hmax
  refine Finset.sup_le ?_
  intro p _
  refine max_le ?_ ?_
  · refine ThB_le_ThMax hn ht hr hrn ?_
    exact jlo_lt hi (by have := p.isLt; omega)
  · refine ThB_le_ThMax hn ht hr hrn ?_
    exact jhi_lt hi (by have := p.isLt; omega)

theorem Jbit_depth_le {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hi : i < r) (hrn : n = 2 ^ r * t - 1) :
    partialDepthB0 (Jbit n t r i) ≤ r + (ThMax n r + 5) := by
  have h1 := partialDepthB0_Jbit_le hn ht hr hi hrn
  have h2 := hmax_le_ThMax hn ht hr hrn hi
  have h3 : r - i - 1 ≤ r := by omega
  omega

theorem ThMax_cast_le {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) :
    (ThMax n r : ℝ) ≤ L5 * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46010 := by
  unfold ThMax
  have h0 : (0:ℝ) ≤ L5 * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46009 := by
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hl : 0 ≤ Real.logb 2 (n:ℝ) := Real.logb_nonneg (by norm_num) hn1
    have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
    nlinarith [L5_nonneg]
  have := Nat.ceil_lt_add_one h0
  linarith

theorem Jbit_depth_le_real {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hi : i < r) (hrn : n = 2 ^ r * t - 1) :
    (partialDepthB0 (Jbit n t r i) : ℝ)
      ≤ (L5 + 1) * (r:ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46015 := by
  have h1 : (partialDepthB0 (Jbit n t r i) : ℝ) ≤ ((r + (ThMax n r + 5) : ℕ) : ℝ) := by
    exact_mod_cast Jbit_depth_le hn ht hr hi hrn
  have h2 := ThMax_cast_le hn hr
  push_cast at h1
  linarith

theorem r_le_logb_nat {n t r : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) :
    (r:ℝ) ≤ Real.logb 2 ((n:ℝ)/t) + 1 := by
  have hncast : (n:ℝ) = (2:ℝ)^r * (t:ℝ) - 1 := by
    rw [hrn]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ r * t)]
    ring
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hpow : Real.logb 2 ((2:ℝ)^(r-1)) = ((r:ℝ) - 1) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    have : ((r - 1 : ℕ) : ℝ) = (r:ℝ) - 1 := by
      push_cast [Nat.cast_sub hr]
      ring
    rw [this]; ring
  have hge : (2:ℝ)^(r-1) ≤ (n:ℝ)/(t:ℝ) := by
    rw [le_div_iff₀ htR, hncast]
    have h2 : (2:ℝ)^r = 2 * 2^(r-1) := by
      conv_lhs => rw [show r = (r - 1) + 1 by omega]
      rw [pow_succ]
      ring
    have h4 : (1:ℝ) ≤ (2:ℝ)^(r-1) := one_le_pow₀ (by norm_num)
    have h5 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    nlinarith [h2, h4, h5]
  have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by positivity : (0:ℝ) < (2:ℝ)^(r-1)) hge
  linarith [hmono, hpow]

noncomputable def Jdepth (n t r : ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin r => partialDepthB0 (Jbit n t r i.val))

theorem Jdepth_le {n t r : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) :
    Jdepth n t r ≤ r + (ThMax n r + 5) := by
  unfold Jdepth
  refine Finset.sup_le ?_
  intro i _
  exact Jbit_depth_le hn ht hr i.isLt hrn

theorem corollary1 {n t r : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) :
    (Jdepth n t r : ℝ)
      ≤ (L5 + 1) * Real.logb 2 ((n:ℝ)/t) + 2 * Real.logb 2 (n:ℝ) + (3 * L5 + 46020) := by
  have h1 : (Jdepth n t r : ℝ) ≤ ((r + (ThMax n r + 5) : ℕ) : ℝ) := by
    exact_mod_cast Jdepth_le hn ht hr hrn
  have h2 := ThMax_cast_le hn hr
  have h3 := r_le_logb_nat hn ht hr hrn
  push_cast at h1
  have hcoef : (0:ℝ) ≤ L5 + 1 := by linarith [L5_nonneg]
  have hmul : (L5 + 1) * (r:ℝ) ≤ (L5 + 1) * (Real.logb 2 ((n:ℝ)/t) + 1) :=
    mul_le_mul_of_nonneg_left h3 hcoef
  linarith

/-! ### The block code `(B, H)` of Section 3 and rule (4) -/

/-- The `i`-th `s`-bit block of `m` (base `2^s` notation). -/
def blk (m s i : ℕ) : ℕ := m / 2 ^ (i * s) % 2 ^ s

theorem blk_lt (m s i : ℕ) : blk m s i < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)

/-- The number `[b_{l−1},…,b_i]` formed by the blocks from position `i` up. -/
def codeVal (b : ℕ → ℕ) (l s i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (l - i), b (i + j) * 2 ^ (j * s)

/-- The number subtracted from the senior part by the corrections `h_{i+1},…,h_{l−1}` of
rule (4) (the correction `h_i` is not yet known at this point). -/
def corrVal (h : ℕ → ℕ) (l s i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (l - i - 1), h (i + j + 1) * 2 ^ ((j + 1) * s)

/-- The value determined by the senior part of the code above block `i − 1`. -/
def decVal (b h : ℕ → ℕ) (l s i : ℕ) : ℤ :=
  (codeVal b l s i : ℤ) - (corrVal h l s i : ℤ)

theorem codeVal_step {b : ℕ → ℕ} {l s i : ℕ} (hi : i < l) :
    codeVal b l s i = b i + 2 ^ s * codeVal b l s (i + 1) := by
  unfold codeVal
  have h1 : l - i = (l - i - 1) + 1 := by omega
  rw [h1, Finset.sum_range_succ']
  have hsum : (∑ k ∈ Finset.range (l - i - 1), b (i + (k + 1)) * 2 ^ ((k + 1) * s))
      = 2 ^ s * ∑ k ∈ Finset.range (l - (i + 1)), b (i + 1 + k) * 2 ^ (k * s) := by
    have h2 : l - i - 1 = l - (i + 1) := by omega
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    have harg : i + (k + 1) = i + 1 + k := by omega
    rw [harg, Nat.succ_mul, pow_add]
    ring
  rw [hsum]
  simp only [Nat.add_zero, Nat.zero_mul, pow_zero, mul_one]
  rw [Nat.add_comm]

theorem corrVal_step {h : ℕ → ℕ} {l s i : ℕ} (hi : i + 1 < l) :
    corrVal h l s i = h (i + 1) * 2 ^ s + 2 ^ s * corrVal h l s (i + 1) := by
  unfold corrVal
  have h1 : l - i - 1 = (l - i - 2) + 1 := by omega
  rw [h1, Finset.sum_range_succ']
  have hsum : (∑ k ∈ Finset.range (l - i - 2), h (i + (k + 1) + 1) * 2 ^ ((k + 1 + 1) * s))
      = 2 ^ s * ∑ k ∈ Finset.range (l - (i + 1) - 1),
          h (i + 1 + k + 1) * 2 ^ ((k + 1) * s) := by
    have h2 : l - i - 2 = l - (i + 1) - 1 := by omega
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    have harg : i + (k + 1) + 1 = i + 1 + k + 1 := by omega
    rw [harg]
    have : (k + 1 + 1) * s = (k + 1) * s + s := by ring
    rw [this, pow_add]
    ring
  rw [hsum]
  simp only [Nat.add_zero, Nat.zero_add, Nat.one_mul, pow_zero, mul_one]
  rw [Nat.add_comm]

theorem decVal_step {b h : ℕ → ℕ} {l s i : ℕ} (hi : i + 1 < l) :
    decVal b h l s i
      = (b i : ℤ) - (h (i + 1) : ℤ) * 2 ^ s + 2 ^ s * decVal b h l s (i + 1) := by
  unfold decVal
  rw [codeVal_step (by omega), corrVal_step hi]
  push_cast
  ring

theorem decVal_self {b h : ℕ → ℕ} {l s : ℕ} : decVal b h l s l = 0 := by
  unfold decVal codeVal corrVal
  simp

/-- Splitting off the lowest block: `m % (a b) = m % a + (m / a % b) a`. -/
theorem mod_mul_add_mod (m a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    m % (a * b) = m % a + (m / a % b) * a := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  generalize hr : m % (a * b) = r
  have hlt : r < a * b := by rw [← hr]; exact Nat.mod_lt _ hab
  have hm : m = a * b * (m / (a * b)) + r := by
    rw [← hr]; exact (Nat.div_add_mod m (a * b)).symm
  have hm' : m = a * (b * (m / (a * b))) + r := by
    conv_lhs => rw [hm]
    rw [Nat.mul_assoc]
  have hdiv : m / a = b * (m / (a * b)) + r / a := by
    conv_lhs => rw [hm']
    rw [Nat.mul_add_div ha]
  have hra : r / a < b := by
    rw [Nat.div_lt_iff_lt_mul ha, Nat.mul_comm b a]; exact hlt
  have h1 : m / a % b = r / a := by
    rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt hra]
  have h2 : m % a = r % a := by
    conv_lhs => rw [hm']
    rw [Nat.mul_add_mod]
  have h3 : r = r / a * a + r % a := by
    have h := Nat.div_add_mod r a
    rw [Nat.mul_comm a (r / a)] at h
    exact h.symm
  have key : m % a + (m / a % b) * a = r := by
    rw [h1, h2]
    conv_rhs => rw [h3]
    rw [Nat.add_comm]
  rw [key]

/-- The blocks of `m` decode back to `m` (no corrections): `m % 2^{ls}` has exactly the
blocks `b_0, …, b_{l−1}`. -/
theorem codeVal_blk (m s l : ℕ) :
    codeVal (blk m s) l s 0 = m % 2 ^ (l * s) := by
  unfold codeVal
  induction l with
  | zero => simpa using (Nat.mod_one m).symm
  | succ l ih =>
      have hz : l + 1 - 0 = (l - 0) + 1 := by omega
      rw [hz, Finset.sum_range_succ, ih]
      have hpow : 2 ^ ((l + 1) * s) = 2 ^ (l * s) * 2 ^ s := by
        rw [Nat.succ_mul, pow_add]
      rw [hpow, mod_mul_add_mod m (2 ^ (l * s)) (2 ^ s) (Nat.two_pow_pos _) (Nat.two_pow_pos s)]
      unfold blk
      simp

/-! ### Rule (4): the three cases -/

/-- The correction bit `h_{i+1}` of rule (4), as a function of the decoded value `p` of the
senior part above block `i` and of the number `M` computed at stage `i`: it is `1` exactly
when the low two bits of the previous block are those of the new computation plus one. -/
def hbit (p M s : ℕ) : ℕ := if p % 4 = (M / 2 ^ s % 4 + 1) % 4 then 1 else 0

/-- The block `b_i` written into the code: the computed block `M % 2^s`, except in the case
`b ≡ a + 1 (mod 4)`, where the computed block is `[0…0]` and the code stores `[1…1]`. -/
def newBlk (p M s : ℕ) : ℕ :=
  if M / 2 ^ s % 4 = (p % 4 + 1) % 4 then 2 ^ s - 1 else M % 2 ^ s

theorem hbit_le_one (p M s : ℕ) : hbit p M s ≤ 1 := by
  unfold hbit; split <;> omega

theorem newBlk_lt (p M s : ℕ) : newBlk p M s < 2 ^ s := by
  unfold newBlk
  split
  · have := Nat.two_pow_pos s; omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos s)

theorem hbit_pos_iff (p M s : ℕ) :
    hbit p M s = 1 ↔ p % 4 = (M / 2 ^ s % 4 + 1) % 4 := by
  unfold hbit
  by_cases h : p % 4 = (M / 2 ^ s % 4 + 1) % 4
  · simp [h]
  · simp [h]

theorem newBlk_alt (p M s : ℕ) : newBlk p M s = M % 2 ^ s ∨ newBlk p M s = 2 ^ s - 1 := by
  unfold newBlk
  split
  · right; rfl
  · left; rfl

/-- The impossible case `a − b ≡ 2 (mod 4)` of the paper. -/
theorem residues_not_two {p k U : ℕ} (hp : p = U ∨ p = U + 1) (hk : k = U ∨ k = U + 1) :
    (p % 4 + 2) % 4 ≠ k % 4 := by
  rcases hp with h | h <;> rcases hk with h' | h' <;> rw [h, h'] <;> omega

/-- The three cases of the paper cover all possibilities. -/
theorem residues_trichotomy {p k U : ℕ} (hp : p = U ∨ p = U + 1) (hk : k = U ∨ k = U + 1) :
    p % 4 = k % 4 ∨ p % 4 = (k % 4 + 1) % 4 ∨ k % 4 = (p % 4 + 1) % 4 := by
  rcases hp with h | h <;> rcases hk with h' | h' <;> rw [h, h'] <;> omega


/-- **One step of rule (4).** Let `p` be the value decoded so far from the senior part above
block `i` (so `p = U` or `p = U + 1` for the true value `U`), and let `M` be the number
computed at stage `i` (`M = U * 2^s + …` up to `M = (U + 1) * 2^s`). Then the correction
bit `h_{i+1}` and the block `b_i` prescribed by the three cases of the paper satisfy: the
extended code decodes to `M` or to `M − 1`. -/
theorem step_arith {s U M p : ℕ} (hs : 2 ≤ s) (hp : p = U ∨ p = U + 1)
    (hk : M / 2 ^ s = U ∨ M / 2 ^ s = U + 1) (hMle : M ≤ (U + 1) * 2 ^ s) :
    (((p : ℤ) - (hbit p M s : ℤ)) * 2 ^ s + (newBlk p M s : ℤ) = (M : ℤ)) ∨
      ((((p : ℤ) - (hbit p M s : ℤ)) * 2 ^ s + (newBlk p M s : ℤ) = (M : ℤ) - 1) ∧
        M = (U + 1) * 2 ^ s) := by
  have h2s : 0 < 2 ^ s := Nat.two_pow_pos s
  have hMZ : ((M / 2 ^ s : ℕ) : ℤ) * 2 ^ s + ((M % 2 ^ s : ℕ) : ℤ) = (M : ℤ) := by
    have h := Nat.div_add_mod M (2 ^ s)
    rw [Nat.mul_comm] at h
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h'
    simpa using h'
  rcases hp with hp | hp <;> rcases hk with hk | hk
  · -- `a = b`: the block is unchanged and `h_{i+1} = 0`
    have h1 : ¬ (p % 4 = (M / 2 ^ s % 4 + 1) % 4) := by omega
    have h2 : ¬ (M / 2 ^ s % 4 = (p % 4 + 1) % 4) := by omega
    have hpz : p = M / 2 ^ s := by omega
    left
    unfold hbit newBlk
    rw [if_neg h1, if_neg h2, hpz]
    simp only [Nat.cast_zero]
    linarith [hMZ]
  · -- `b = a + 1`: the code stores `[1…1]`, `h_{i+1} = 0`
    have h1 : ¬ (p % 4 = (M / 2 ^ s % 4 + 1) % 4) := by omega
    have h2 : M / 2 ^ s % 4 = (p % 4 + 1) % 4 := by omega
    have hle : (U + 1) * 2 ^ s ≤ M := by
      have h := Nat.div_add_mod M (2 ^ s)
      rw [Nat.mul_comm] at h
      rw [hk] at h
      omega
    have hMval : M = (U + 1) * 2 ^ s := le_antisymm hMle hle
    refine Or.inr ⟨?_, hMval⟩
    unfold hbit newBlk
    rw [if_neg h1, if_pos h2]
    have hcu : ((2 ^ s - 1 : ℕ) : ℤ) = (2 : ℤ) ^ s - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ s), Nat.cast_one, Nat.cast_pow]
      norm_num
    rw [hp, hMval, hcu]
    push_cast
    ring
  · -- `a = b + 1`: `h_{i+1} = 1` and the block is unchanged
    have h1 : p % 4 = (M / 2 ^ s % 4 + 1) % 4 := by omega
    have h2 : ¬ (M / 2 ^ s % 4 = (p % 4 + 1) % 4) := by omega
    have hpz : p = M / 2 ^ s + 1 := by omega
    left
    unfold hbit newBlk
    rw [if_pos h1, if_neg h2, hpz]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [hMZ]
  · -- `a = b`: unchanged
    have h1 : ¬ (p % 4 = (M / 2 ^ s % 4 + 1) % 4) := by omega
    have h2 : ¬ (M / 2 ^ s % 4 = (p % 4 + 1) % 4) := by omega
    have hpz : p = M / 2 ^ s := by omega
    left
    unfold hbit newBlk
    rw [if_neg h1, if_neg h2, hpz]
    simp only [Nat.cast_zero]
    linarith [hMZ]

/-- `(a + 1) / 2^s` is either `a / 2^s` or `a / 2^s + 1`. -/
theorem div_succ_pow (s a : ℕ) :
    (a + 1) / 2 ^ s = a / 2 ^ s ∨ (a + 1) / 2 ^ s = a / 2 ^ s + 1 := by
  have h2 : 0 < 2 ^ s := Nat.two_pow_pos s
  have h1 : a / 2 ^ s ≤ (a + 1) / 2 ^ s := Nat.div_le_div_right (by omega)
  have h3 : (a + 1) / 2 ^ s ≤ a / 2 ^ s + 1 := by
    refine Nat.div_le_of_le_mul ?_
    have h := Nat.lt_mul_div_succ a h2
    omega
  omega

/-! ### The correction bit as a Boolean formula of four bits -/

/-- Value of a two-bit group `(low, high)`. -/
def twoBits (p q : Bool) : ℕ := (if p then 1 else 0) + 2 * (if q then 1 else 0)

/-- The correction bit `h_{i+1}` of rule (4) as a Boolean function of the two low bits `a`
of the previous block and the two overlapping bits `b` of the new computation: it equals
`1` exactly when `a ≡ b + 1 (mod 4)`. -/
def corrBool (a0 a1 b0 b1 : Bool) : Bool :=
  (a0 && !a1 && !b0 && !b1) || (!a0 && a1 && b0 && !b1) ||
    (a0 && a1 && !b0 && b1) || (!a0 && !a1 && b0 && b1)

theorem corrBool_spec (a0 a1 b0 b1 : Bool) :
    corrBool a0 a1 b0 b1 = true ↔ twoBits a0 a1 % 4 = (twoBits b0 b1 + 1) % 4 := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> decide

theorem corrBool_self (a0 a1 : Bool) : corrBool a0 a1 a0 a1 = false := by
  cases a0 <;> cases a1 <;> rfl

theorem twoBits_decide (m : ℕ) :
    twoBits (decide (m % 2 = 1)) (decide (m / 2 % 2 = 1)) = m % 4 := by
  unfold twoBits
  have h1 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h2 : m / 2 % 2 = 0 ∨ m / 2 % 2 = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    simp [h1, h2] <;> omega

/-- The Boolean formula `corrBool` reads the two low bits of `p` and of `k` and tests
`p ≡ k + 1 (mod 4)`. -/
theorem corrBool_bits (p k : ℕ) :
    corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
        (decide (k % 2 = 1)) (decide (k / 2 % 2 = 1)) = true ↔ p % 4 = (k % 4 + 1) % 4 := by
  rw [corrBool_spec, twoBits_decide, twoBits_decide, Nat.mod_mod_of_dvd p (dvd_refl 4)]

/-- The correction bit of rule (4) is computed by the Boolean formula `corrBool` applied to
the two low bits `a` of the previous block and the two overlapping bits `b` of the new
computation (bits `s` and `s + 1` of the number `M` computed at this stage). -/
theorem hbit_eq_corrBool (p M s : ℕ) :
    hbit p M s
      = if corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
          (decide (M / 2 ^ s % 2 = 1)) (decide (M / 2 ^ s / 2 % 2 = 1)) then 1 else 0 := by
  have key : hbit p M s = 1 ↔
      corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
        (decide (M / 2 ^ s % 2 = 1)) (decide (M / 2 ^ s / 2 % 2 = 1)) = true := by
    rw [hbit_pos_iff, corrBool_bits]
  by_cases h : corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
      (decide (M / 2 ^ s % 2 = 1)) (decide (M / 2 ^ s / 2 % 2 = 1)) = true
  · rw [if_pos h]
    exact key.mpr h
  · rw [if_neg h]
    have h1 := hbit_le_one p M s
    have h2 : hbit p M s ≠ 1 := fun hc => h (key.mp hc)
    omega

/-! ### Updating the code block by block -/

theorem codeVal_update {b : ℕ → ℕ} {l s i j v : ℕ} (hij : i < j) :
    codeVal (Function.update b i v) l s j = codeVal b l s j := by
  unfold codeVal
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Function.update_apply, if_neg (by omega)]

theorem corrVal_update {h : ℕ → ℕ} {l s i j v : ℕ} (hij : i ≤ j) :
    corrVal (Function.update h i v) l s j = corrVal h l s j := by
  unfold corrVal
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Function.update_apply, if_neg (by omega)]

/-- One step of the construction, at the level of the decoded values. -/
theorem decVal_update {b h : ℕ → ℕ} {l s i v w : ℕ} (hi : i + 1 < l) :
    decVal (Function.update b i v) (Function.update h (i + 1) w) l s i
      = (v : ℤ) - (w : ℤ) * 2 ^ s + 2 ^ s * decVal b h l s (i + 1) := by
  have hsame : decVal (Function.update b i v) (Function.update h (i + 1) w) l s (i + 1)
      = decVal b h l s (i + 1) := by
    unfold decVal
    rw [codeVal_update (by omega), corrVal_update (by omega)]
  rw [decVal_step hi, hsame, Function.update_apply, Function.update_apply, if_pos rfl,
    if_pos rfl]

theorem codeVal_last {b : ℕ → ℕ} {l s : ℕ} (hl : 1 ≤ l) :
    codeVal b l s (l - 1) = b (l - 1) := by
  unfold codeVal
  rw [show l - (l - 1) = 1 by omega, Finset.sum_range_one]
  simp

theorem corrVal_last {h : ℕ → ℕ} {l s : ℕ} (hl : 1 ≤ l) :
    corrVal h l s (l - 1) = 0 := by
  unfold corrVal
  rw [show l - (l - 1) - 1 = 0 by omega]
  simp

/-- **The code `(B, H)` of Lemma 1.** Suppose the numbers `M i` computed at the successive
stages of the scheme (`M i` is the true value `V / 2^{is}` at stage `i`, up to `+1`). Then
there are blocks `b i` and correction bits `h i` such that the code decodes to `V` or to
`V + 1`: the code approximates `V` with accuracy `±1`. -/
theorem exists_code {s l : ℕ} (hs : 2 ≤ s) {V : ℕ} (hV : V < 2 ^ (l * s))
    (M : ℕ → ℕ) (hM : ∀ i < l, M i = V / 2 ^ (i * s) ∨ M i = V / 2 ^ (i * s) + 1) :
    ∃ b h : ℕ → ℕ, (∀ i, b i < 2 ^ s) ∧ (∀ i, h i ≤ 1) ∧
      (decVal b h l s 0 = (V : ℤ) ∨ decVal b h l s 0 = (V : ℤ) + 1) := by
  have h2s : 0 < 2 ^ s := Nat.two_pow_pos s
  rcases Nat.eq_zero_or_pos l with hl0 | hl
  · subst hl0
    have hV0 : V = 0 := by simpa using hV
    subst hV0
    refine ⟨fun _ => 0, fun _ => 0, fun _ => h2s, fun _ => Nat.zero_le 1, ?_⟩
    rw [decVal_self]
    exact Or.inl (by norm_num)
  have key : ∀ m ≤ l - 1, ∃ b h : ℕ → ℕ, (∀ j, b j < 2 ^ s) ∧ (∀ j, h j ≤ 1) ∧
      (decVal b h l s m = ((V / 2 ^ (m * s) : ℕ) : ℤ) ∨
        decVal b h l s m = ((V / 2 ^ (m * s) : ℕ) : ℤ) + 1) := by
    intro m hm
    refine Nat.decreasingInduction (n := l - 1)
      (motive := fun m _ => ∃ b h : ℕ → ℕ, (∀ j, b j < 2 ^ s) ∧ (∀ j, h j ≤ 1) ∧
        (decVal b h l s m = ((V / 2 ^ (m * s) : ℕ) : ℤ) ∨
          decVal b h l s m = ((V / 2 ^ (m * s) : ℕ) : ℤ) + 1)) ?_ ?_ hm
    · -- step: from stage `k + 1` to stage `k`
      intro k hk ih
      obtain ⟨b, h, hb, hh, hv⟩ := ih
      have hklt : k + 1 < l := by omega
      set U := V / 2 ^ (k * s) / 2 ^ s with hUdef
      have hHdiv : V / 2 ^ ((k + 1) * s) = U := by
        rw [hUdef]
        conv_lhs => rw [show (k + 1) * s = k * s + s by ring]
        rw [pow_add, Nat.div_div_eq_div_mul]
      have hp2 : decVal b h l s (k + 1) = (U : ℤ) ∨ decVal b h l s (k + 1) = (U : ℤ) + 1 := by
        have h := hv
        rw [hHdiv] at h
        exact h
      obtain ⟨p, hpdef, hpdisj⟩ :
          ∃ p : ℕ, (p : ℤ) = decVal b h l s (k + 1) ∧ (p = U ∨ p = U + 1) := by
        rcases hp2 with h1 | h1
        · exact ⟨U, by rw [h1], Or.inl rfl⟩
        · exact ⟨U + 1, by rw [h1, Nat.cast_add, Nat.cast_one], Or.inr rfl⟩
      have hMk : M k = V / 2 ^ (k * s) ∨ M k = V / 2 ^ (k * s) + 1 := hM k (by omega)
      have hMdiv : M k / 2 ^ s = U ∨ M k / 2 ^ s = U + 1 := by
        rcases hMk with h1 | h1
        · exact Or.inl (by rw [h1, hUdef])
        · rcases div_succ_pow s (V / 2 ^ (k * s)) with h2 | h2
          · exact Or.inl (by rw [h1, h2, hUdef])
          · exact Or.inr (by rw [h1, h2, ← hUdef])
      have hMle : M k ≤ (U + 1) * 2 ^ s := by
        have hdm := Nat.div_add_mod (V / 2 ^ (k * s)) (2 ^ s)
        rw [Nat.mul_comm] at hdm
        have hmod : V / 2 ^ (k * s) % 2 ^ s < 2 ^ s := Nat.mod_lt _ h2s
        have hkey : V / 2 ^ (k * s) + 1 ≤ (U + 1) * 2 ^ s := by
          rw [hUdef]; nlinarith
        rcases hMk with h1 | h1 <;> omega
      have hstep := step_arith (s := s) (U := U) (M := M k) (p := p) hs hpdisj hMdiv hMle
      have hdv : decVal (Function.update b k (newBlk p (M k) s))
          (Function.update h (k + 1) (hbit p (M k) s)) l s k
          = ((p : ℤ) - (hbit p (M k) s : ℤ)) * 2 ^ s + (newBlk p (M k) s : ℤ) := by
        rw [decVal_update hklt, ← hpdef]
        ring
      refine ⟨Function.update b k (newBlk p (M k) s),
        Function.update h (k + 1) (hbit p (M k) s), ?_, ?_, ?_⟩
      · intro j
        by_cases hj : j = k
        · rw [Function.update_apply, if_pos hj]; exact newBlk_lt p (M k) s
        · rw [Function.update_apply, if_neg hj]; exact hb j
      · intro j
        by_cases hj : j = k + 1
        · rw [Function.update_apply, if_pos hj]; exact hbit_le_one p (M k) s
        · rw [Function.update_apply, if_neg hj]; exact hh j
      · rcases hstep with h1 | ⟨h1, h2⟩
        · rw [hdv, h1]
          rcases hMk with hm | hm
          · exact Or.inl (by rw [hm])
          · exact Or.inr (by rw [hm, Nat.cast_add, Nat.cast_one])
        · rw [hdv, h1]
          rcases hMk with hm | hm
          · exfalso
            have hq : M k / 2 ^ s = U + 1 := by
              rw [h2, Nat.mul_comm (U + 1) (2 ^ s), Nat.mul_div_right _ h2s]
            have hq' : M k / 2 ^ s = U := by rw [hm, ← hUdef]
            omega
          · refine Or.inl ?_
            rw [hm, Nat.cast_add, Nat.cast_one]
            ring
    · -- base case: the topmost block `l − 1` is written down directly
      have hl1 : 1 ≤ l := hl
      have hVlt : V / 2 ^ ((l - 1) * s) < 2 ^ s := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ((l - 1) * s)), Nat.mul_comm]
        have hpow : 2 ^ (l * s) = 2 ^ ((l - 1) * s) * 2 ^ s := by
          conv_lhs => rw [show l * s = (l - 1) * s + s by
            conv_lhs => rw [show l = l - 1 + 1 by omega]
            rw [Nat.add_mul, Nat.one_mul]]
          rw [pow_add]
        rw [← hpow]
        exact hV
      refine ⟨fun j => if j = l - 1 then V / 2 ^ ((l - 1) * s) else 0, fun _ => 0,
        ?_, ?_, ?_⟩
      · intro j
        show (if j = l - 1 then V / 2 ^ ((l - 1) * s) else 0) < 2 ^ s
        by_cases hj : j = l - 1
        · rw [if_pos hj]; exact hVlt
        · rw [if_neg hj]; exact h2s
      · intro j; exact Nat.zero_le 1
      · left
        have hcv : codeVal (fun j => if j = l - 1 then V / 2 ^ ((l - 1) * s) else 0) l s (l - 1)
            = V / 2 ^ ((l - 1) * s) := by
          rw [codeVal_last hl1]
          show (if l - 1 = l - 1 then V / 2 ^ ((l - 1) * s) else 0) = V / 2 ^ ((l - 1) * s)
          rw [if_pos rfl]
        unfold decVal
        rw [hcv, corrVal_last (h := fun _ => 0) hl1, Nat.cast_zero, sub_zero]
  obtain ⟨b, h, hb, hh, hv⟩ := key 0 (by omega)
  refine ⟨b, h, hb, hh, ?_⟩
  simpa using hv

/-- A literal of a `B₀` formula: `f` or its negation. -/
def lit {n : ℕ} (p : Bool) (f : Formula B0 n) : Formula B0 n := if p then f else b0Not f

theorem lit_eval {n : ℕ} (p : Bool) (f : Formula B0 n) (x : Fin n → Bool) :
    (lit p f).eval x = (if p then f.eval x else !(f.eval x)) := by
  unfold lit
  split_ifs <;> simp [b0Not_eval]

theorem lit_depth_le {n : ℕ} (p : Bool) (f : Formula B0 n) :
    (lit p f).depth ≤ f.depth + 1 := by
  unfold lit
  split_ifs
  · omega
  · rw [b0Not_depth_eq]

theorem and4_depth_le {n : ℕ} (a b c d : Formula B0 n) :
    (b0And (b0And a b) (b0And c d)).depth
      ≤ max (max a.depth b.depth) (max c.depth d.depth) + 2 := by
  have h1 := b0And_depth_le a b
  have h2 := b0And_depth_le c d
  have h3 := b0And_depth_le (b0And a b) (b0And c d)
  have h4 : max (b0And a b).depth (b0And c d).depth
      ≤ max (max a.depth b.depth) (max c.depth d.depth) + 1 := by
    apply max_le <;> omega
  omega

/-- The disjunctive normal form of `corrBool` over four given formulae. -/
def corrBuild {n : ℕ} (f0 f1 g0 g1 : Formula B0 n) : Formula B0 n :=
  b0Or (b0Or (b0And (b0And (lit true f0) (lit false f1)) (b0And (lit false g0) (lit false g1)))
             (b0And (b0And (lit false f0) (lit true f1)) (b0And (lit true g0) (lit false g1))))
        (b0Or (b0And (b0And (lit true f0) (lit true f1)) (b0And (lit false g0) (lit true g1)))
              (b0And (b0And (lit false f0) (lit false f1)) (b0And (lit true g0) (lit true g1))))

theorem corrBuild_depth_le {n : ℕ} (f0 f1 g0 g1 : Formula B0 n) (D : ℕ)
    (h0 : f0.depth ≤ D) (h1 : f1.depth ≤ D) (k0 : g0.depth ≤ D) (k1 : g1.depth ≤ D) :
    (corrBuild f0 f1 g0 g1).depth ≤ D + 5 := by
  have litb : ∀ (p : Bool) (f : Formula B0 n), f.depth ≤ D → (lit p f).depth ≤ D + 1 :=
    fun p f hf => le_trans (lit_depth_le p f) (by omega)
  have and4 : ∀ (a b c d : Formula B0 n), a.depth ≤ D + 1 → b.depth ≤ D + 1 →
      c.depth ≤ D + 1 → d.depth ≤ D + 1 →
      (b0And (b0And a b) (b0And c d)).depth ≤ D + 3 := by
    intro a b c d ha hb hc hd
    have := and4_depth_le a b c d
    omega
  have or2 : ∀ (N : ℕ) (a b : Formula B0 n), a.depth ≤ N → b.depth ≤ N →
      (b0Or a b).depth ≤ N + 1 := by
    intro N a b ha hb
    have := b0Or_depth_le a b
    omega
  have t0 := and4 _ _ _ _ (litb true f0 h0) (litb false f1 h1) (litb false g0 k0) (litb false g1 k1)
  have t1 := and4 _ _ _ _ (litb false f0 h0) (litb true f1 h1) (litb true g0 k0) (litb false g1 k1)
  have t2 := and4 _ _ _ _ (litb true f0 h0) (litb true f1 h1) (litb false g0 k0) (litb true g1 k1)
  have t3 := and4 _ _ _ _ (litb false f0 h0) (litb false f1 h1) (litb true g0 k0) (litb true g1 k1)
  have u0 := or2 (D + 3) _ _ t0 t1
  have u1 := or2 (D + 3) _ _ t2 t3
  have u2 := or2 (D + 4) _ _ u0 u1
  unfold corrBuild
  exact u2

theorem corrBuild_eval {n : ℕ} (f0 f1 g0 g1 : Formula B0 n) (x : Fin n → Bool) :
    (corrBuild f0 f1 g0 g1).eval x
      = corrBool (f0.eval x) (f1.eval x) (g0.eval x) (g1.eval x) := by
  cases h0 : f0.eval x <;> cases h1 : f1.eval x <;> cases k0 : g0.eval x <;> cases k1 : g1.eval x <;>
    simp [corrBuild, corrBool, lit_eval, b0Or_eval, b0And_eval, b0Not_eval, h0, h1, k0, k1]

/-! ### The scaled block computation -/

/-- Width of the intervals used at stage `i` of the block computation: `2^{is} t`. -/
def blkWidth (t i s : ℕ) : ℕ := 2 ^ (i * s) * t

/-- The exponent of the number of intervals at stage `i`: `(l − i) s`. -/
def blkCount (l s i : ℕ) : ℕ := (l - i) * s

theorem blkWidth_cast (t i s : ℕ) :
    ((blkWidth t i s : ℕ) : ℝ) = (2:ℝ) ^ (i * s) * (t:ℝ) := by
  unfold blkWidth
  push_cast
  ring

theorem pow_blkCount_mul_blkWidth {l s i t : ℕ} (hi : i ≤ l) :
    2 ^ blkCount l s i * blkWidth t i s = 2 ^ (l * s) * t := by
  unfold blkCount blkWidth
  rw [← Nat.mul_assoc, ← Nat.pow_add, ← Nat.add_mul, Nat.sub_add_cancel hi]

theorem ThMax_mono {n r₁ r₂ : ℕ} (h : r₁ ≤ r₂) : ThMax n r₁ ≤ ThMax n r₂ := by
  unfold ThMax
  refine Nat.ceil_mono ?_
  have hR : (r₁ : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast h
  nlinarith [L5_nonneg]

theorem ThB_le_ThMax_all {n t r j : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) : ThB n t j ≤ ThMax n r := by
  by_cases hj : j < 2 ^ r
  · exact ThB_le_ThMax hn ht hr hrn hj
  · unfold ThB
    split_ifs with hok
    · exfalso
      apply hj
      have h1 : j * t ≤ n := by have := hok.2; omega
      have h2 : j * t < 2 ^ r * t := by
        have h3 : 0 < 2 ^ r * t := Nat.mul_pos (Nat.two_pow_pos r) ht
        omega
      exact Nat.lt_of_mul_lt_mul_right h2
    · exact Nat.zero_le _

theorem hmax_le_ThMax_all {n t r i : ℕ} (hn : 0 < n) (ht : 0 < t) (hr : 1 ≤ r)
    (hrn : n = 2 ^ r * t - 1) : hmax n t r i ≤ ThMax n r := by
  unfold hmax
  refine Finset.sup_le ?_
  intro p _
  exact max_le (ThB_le_ThMax_all hn ht hr hrn) (ThB_le_ThMax_all hn ht hr hrn)

/-- The `q`-th bit of the interval number computed at stage `i` of the block scheme:
the first-one operator of (3) applied to the partition of `[0, n]` into `2^{(l−i)s}`
intervals of width `2^{is} t`. -/
noncomputable def blkBit (n t l s i q : ℕ) (hn : 0 < n) : Formula B0 n :=
  Jcomp n (blkWidth t i s) (blkCount l s i) q hn

theorem blkBit_depth_le {n t l s i q : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (blkBit n t l s i q hn).depth ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) := by
  have hile : i ≤ l := by omega
  have hm1 : 1 ≤ blkCount l s i := by
    unfold blkCount
    exact Nat.mul_pos (by omega) (by omega)
  have hW : 0 < blkWidth t i s := Nat.mul_pos (Nat.two_pow_pos (i * s)) ht
  have hnw : n = 2 ^ (blkCount l s i) * blkWidth t i s - 1 := by
    rw [hnr, pow_blkCount_mul_blkWidth hile]
  have h1 := Jcomp_depth_le (n := n) (t := blkWidth t i s) (r := blkCount l s i) (i := q) hn
  have h2 := hmax_le_ThMax_all (n := n) (t := blkWidth t i s) (r := blkCount l s i) (i := q)
    hn hW hm1 hnw
  unfold blkBit
  omega

theorem blkBit_depth_le_stage {n t l s i j q : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) (hj : i ≤ j) (hjl : j < l) :
    (blkBit n t l s j q hn).depth ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) := by
  have h1 := blkBit_depth_le (n := n) (t := t) (l := l) (s := s) (i := j) (q := q) hn ht hs hjl hnr
  have hc : blkCount l s j ≤ blkCount l s i := by
    unfold blkCount
    exact Nat.mul_le_mul_right s (by omega)
  have hT := ThMax_mono (n := n) hc
  omega

theorem blkBit_depth_real {n t l s i q : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (blkBit n t l s i q hn).depth
      ≤ (L5 + 1) * (blkCount l s i : ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46015 := by
  have hm1 : 1 ≤ blkCount l s i := by
    have h2 : 2 ≤ l - i := by omega
    have h3 : 2 * 1 ≤ (l - i) * s := Nat.mul_le_mul h2 hs
    unfold blkCount
    omega
  have h1 := blkBit_depth_le (i := i) (q := q) hn ht hs (by omega) hnr
  have h2 := ThMax_cast_le (n := n) (r := blkCount l s i) hn hm1
  have h3 : ((blkBit n t l s i q hn).depth : ℝ)
      ≤ ((blkCount l s i + (ThMax n (blkCount l s i) + 5) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

/-- The correction bit `h_{i+1}` of rule (4), as a formula: it compares the two low
bits of the previous block `b_{i+1}` (bits `0,1` of stage `i+1`) with the two bits of
the new computation that overlap it (bits `s, s+1` of stage `i`). -/
noncomputable def corrForm (n t l s i : ℕ) (hn : 0 < n) : Formula B0 n :=
  corrBuild (blkBit n t l s (i + 1) 0 hn) (blkBit n t l s (i + 1) 1 hn)
    (blkBit n t l s i s hn) (blkBit n t l s i (s + 1) hn)

/-- The test for the third case of rule (4), `b ≡ a + 1 (mod 4)`, in which the new
block has to be replaced by `[1…1]`. -/
noncomputable def onesForm (n t l s i : ℕ) (hn : 0 < n) : Formula B0 n :=
  corrBuild (blkBit n t l s i s hn) (blkBit n t l s i (s + 1) hn)
    (blkBit n t l s (i + 1) 0 hn) (blkBit n t l s (i + 1) 1 hn)

theorem corrForm_depth_le {n t l s i : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (corrForm n t l s i hn).depth ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) + 5 := by
  have h1 := blkBit_depth_le_stage (i := i) (j := i + 1) (q := 0) hn ht hs hi hnr (by omega) (by omega)
  have h2 := blkBit_depth_le_stage (i := i) (j := i + 1) (q := 1) hn ht hs hi hnr (by omega) (by omega)
  have h3 := blkBit_depth_le_stage (i := i) (j := i) (q := s) hn ht hs hi hnr (le_refl i) (by omega)
  have h4 := blkBit_depth_le_stage (i := i) (j := i) (q := s + 1) hn ht hs hi hnr (le_refl i) (by omega)
  have h5 := corrBuild_depth_le (blkBit n t l s (i + 1) 0 hn) (blkBit n t l s (i + 1) 1 hn)
    (blkBit n t l s i s hn) (blkBit n t l s i (s + 1) hn)
    (blkCount l s i + (ThMax n (blkCount l s i) + 5)) h1 h2 h3 h4
  unfold corrForm
  omega

theorem corrForm_depth_real {n t l s i : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (corrForm n t l s i hn).depth
      ≤ (L5 + 1) * (blkCount l s i : ℝ) + 2 * L5 + 2 * Real.logb 2 (n:ℝ) + 46015 + 5 := by
  have hm1 : 1 ≤ blkCount l s i := by
    have h2 : 2 ≤ l - i := by omega
    have h3 : 2 * 1 ≤ (l - i) * s := Nat.mul_le_mul h2 hs
    unfold blkCount
    omega
  have h1 := corrForm_depth_le hn ht hs hi hnr
  have h2 := ThMax_cast_le (n := n) (r := blkCount l s i) hn hm1
  have h3 : ((corrForm n t l s i hn).depth : ℝ)
      ≤ ((blkCount l s i + (ThMax n (blkCount l s i) + 5) + 5 : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h3
  linarith

/-- The `q`-th bit of the block `b_i` of the code: the bit computed at stage `i`, forced
to `1` in the third case of rule (4) (`b ≡ a + 1 (mod 4)`, where the block of
`J + 2^{is}` is `[0…0]` and the block of the code has to be `[1…1]`). -/
noncomputable def blkOut (n t l s i q : ℕ) (hn : 0 < n) : Formula B0 n :=
  b0Or (onesForm n t l s i hn) (blkBit n t l s i q hn)

theorem blkOut_depth_le {n t l s i q : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (blkOut n t l s i q hn).depth ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) + 6 := by
  have h1 := blkBit_depth_le_stage (i := i) (j := i) (q := q) hn ht hs hi hnr (le_refl i) (by omega)
  have h5 : (onesForm n t l s i hn).depth
      ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) + 5 := by
    unfold onesForm
    exact corrBuild_depth_le _ _ _ _
      (blkCount l s i + (ThMax n (blkCount l s i) + 5))
      (blkBit_depth_le_stage (i := i) (j := i) (q := s) hn ht hs hi hnr (le_refl i) (by omega))
      (blkBit_depth_le_stage (i := i) (j := i) (q := s + 1) hn ht hs hi hnr (le_refl i) (by omega))
      (blkBit_depth_le_stage (i := i) (j := i + 1) (q := 0) hn ht hs hi hnr (by omega) (by omega))
      (blkBit_depth_le_stage (i := i) (j := i + 1) (q := 1) hn ht hs hi hnr (by omega) (by omega))
  have h4 := b0Or_depth_le (onesForm n t l s i hn) (blkBit n t l s i q hn)
  unfold blkOut
  have hm : max (onesForm n t l s i hn).depth (blkBit n t l s i q hn).depth
      ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) + 5 := max_le h5 (by omega)
  omega

/-- The depth of the pair `(b_i, h_{i+1})` of Lemma 1. -/
noncomputable def codeDepth (n t l s i : ℕ) (hn : 0 < n) : ℕ :=
  max (Finset.univ.sup (fun q : Fin s => (blkOut n t l s i q.val hn).depth))
    (corrForm n t l s i hn).depth

theorem logb_two_inv_mul (n t i s : ℕ) (hn : 0 < n) (ht : 0 < t) :
    Real.logb 2 (((2:ℝ) ^ (i * s))⁻¹ * ((n:ℝ)/(t:ℝ)))
      = Real.logb 2 ((n:ℝ)/t) - (i * s) := by
  have hnR : (n:ℝ) ≠ 0 := by positivity
  have htR : (t:ℝ) ≠ 0 := by positivity
  rw [Real.logb_mul (by positivity : ((2:ℝ) ^ (i * s))⁻¹ ≠ 0) (by positivity : ((n:ℝ)/(t:ℝ)) ≠ 0)]
  rw [Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  push_cast
  ring


/-! ### Rule (4) computed by formulas, and the final bound of Lemma 1 -/

/-- The formula `corrForm` computes the Boolean function `corrBool` of the four relevant
code bits. -/
theorem corrForm_eval {n t l s i : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (corrForm n t l s i hn).eval x
      = corrBool ((blkBit n t l s (i + 1) 0 hn).eval x) ((blkBit n t l s (i + 1) 1 hn).eval x)
          ((blkBit n t l s i s hn).eval x) ((blkBit n t l s i (s + 1) hn).eval x) := by
  unfold corrForm
  exact corrBuild_eval _ _ _ _ x

/-- The formula `onesForm` computes the test `b ≡ a + 1 (mod 4)` of the third case of
rule (4). -/
theorem onesForm_eval {n t l s i : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (onesForm n t l s i hn).eval x
      = corrBool ((blkBit n t l s i s hn).eval x) ((blkBit n t l s i (s + 1) hn).eval x)
          ((blkBit n t l s (i + 1) 0 hn).eval x) ((blkBit n t l s (i + 1) 1 hn).eval x) := by
  unfold onesForm
  exact corrBuild_eval _ _ _ _ x

/-- The `q`-th output bit of block `i` is the disjunction of the new computed bit with the
test of the third case. -/
theorem blkOut_eval {n t l s i q : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (blkOut n t l s i q hn).eval x
      = ((onesForm n t l s i hn).eval x || (blkBit n t l s i q hn).eval x) := by
  unfold blkOut
  rw [b0Or_eval]

/-- The correction bit `h_{i+1}` of rule (4) is exactly the value computed by `corrForm`
applied to the two low bits of the previous block and the two overlapping bits of the new
computation. -/
theorem corrForm_computes_hbit {n t l s i : ℕ} (hn : 0 < n) {x : Fin n → Bool} (p M : ℕ)
    (h0 : (blkBit n t l s (i + 1) 0 hn).eval x = decide (p % 2 = 1))
    (h1 : (blkBit n t l s (i + 1) 1 hn).eval x = decide (p / 2 % 2 = 1))
    (h2 : (blkBit n t l s i s hn).eval x = decide (M / 2 ^ s % 2 = 1))
    (h3 : (blkBit n t l s i (s + 1) hn).eval x = decide (M / 2 ^ s / 2 % 2 = 1)) :
    (corrForm n t l s i hn).eval x
      = (if corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
          (decide (M / 2 ^ s % 2 = 1)) (decide (M / 2 ^ s / 2 % 2 = 1)) then true else false) := by
  rw [corrForm_eval, h0, h1, h2, h3]
  by_cases h : corrBool (decide (p % 2 = 1)) (decide (p / 2 % 2 = 1))
      (decide (M / 2 ^ s % 2 = 1)) (decide (M / 2 ^ s / 2 % 2 = 1)) = true <;> simp [h]

/-- A logarithmic growth estimate: `(l − i) s ≤ log₂(2^{−is} n/t) + 1` for `n = 2^{ls} t − 1`.
This is the `±1` slack hidden in the `O(1)` of Lemma 1. -/
theorem blkCount_le_logb {n t l s i : ℕ} (hn : 0 < n) (ht : 0 < t)
    (hi : i ≤ l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (blkCount l s i : ℝ) ≤ Real.logb 2 (((2:ℝ) ^ (i * s))⁻¹ * ((n:ℝ) / (t:ℝ))) + 1 := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have hnp1nat : n + 1 = 2 ^ (l * s) * t := by
    have h : 1 ≤ 2 ^ (l * s) * t := Nat.mul_pos (Nat.two_pow_pos _) ht
    omega
  have hnp1 : ((n:ℝ) + 1) = (2:ℝ) ^ (l * s) * (t:ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hnp1nat
    push_cast at h
    simpa using h
  have hfrac : (1/2:ℝ) ≤ (n:ℝ) / ((n:ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    linarith
  have hloghalf : Real.logb 2 (1/2:ℝ) = -1 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
  have hlogfrac : -1 ≤ Real.logb 2 ((n:ℝ) / ((n:ℝ) + 1)) := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num)
      (by norm_num : (0:ℝ) < 1/2) hfrac
    linarith [h, hloghalf]
  have hstep : ((n:ℝ) + 1) / (t:ℝ) = (2:ℝ) ^ (l * s) := by
    rw [hnp1]
    field_simp
  have hlogN : Real.logb 2 (((n:ℝ) + 1) / (t:ℝ)) = (l * s : ℝ) := by
    rw [hstep, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    push_cast
    ring
  have hdecomp : (n:ℝ) / (t:ℝ) = ((n:ℝ) / ((n:ℝ) + 1)) * (((n:ℝ) + 1) / (t:ℝ)) := by
    field_simp
  have hlogNt : Real.logb 2 ((n:ℝ) / (t:ℝ))
      = Real.logb 2 ((n:ℝ) / ((n:ℝ) + 1)) + (l * s : ℝ) := by
    rw [hdecomp, Real.logb_mul (by positivity) (by positivity), hlogN]
  rw [logb_two_inv_mul n t i s hn ht, hlogNt]
  have hcast : (blkCount l s i : ℝ) = ((l:ℝ) - (i:ℝ)) * (s:ℝ) := by
    unfold blkCount
    rw [Nat.cast_mul, Nat.cast_sub hi]
  rw [hcast]
  have hexp : ((l : ℝ) - (i : ℝ)) * (s : ℝ) = (l : ℝ) * (s : ℝ) - (i : ℝ) * (s : ℝ) := by
    ring
  linarith [hlogfrac, hexp]

/-- **Lemma 1, depth form.** The depth of the pair `(b_i, h_{i+1})` of the code of Lemma 1
is at most `blkCount + (ThMax blkCount + 5) + 6`. -/
theorem codeDepth_le {n t l s i : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    codeDepth n t l s i hn ≤ blkCount l s i + (ThMax n (blkCount l s i) + 5) + 6 := by
  unfold codeDepth
  refine max_le ?_ ?_
  · refine Finset.sup_le ?_
    intro q _
    exact le_trans (blkOut_depth_le (q := q.val) hn ht hs hi hnr) (by omega)
  · exact le_trans (corrForm_depth_le hn ht hs hi hnr) (by omega)

/-- **Lemma 1.** For `n = 2^{ls} t − 1`, the depth of the pair `(b_i, h_{i+1})` of the code
of a number approximating `J` with accuracy `±1`, written in the form `(B, H)` with
`s`-digit blocks, satisfies

`D_{B₀}(b_i, h_{i+1}) ≤ (log_{√5−1} 2 + 1) log₂(2^{−is} n/t) + 2 log₂ n + O(1)`.

The `O(1)` term is made explicit as `3·L5 + 46022`, where `L5 = log_{√5−1} 2`. -/
theorem lemma1 {n t l s i : ℕ} (hn : 0 < n) (ht : 0 < t) (hs : 1 ≤ s)
    (hi : i + 1 < l) (hnr : n = 2 ^ (l * s) * t - 1) :
    (codeDepth n t l s i hn : ℝ)
      ≤ (L5 + 1) * Real.logb 2 (((2:ℝ) ^ (i * s))⁻¹ * ((n:ℝ) / (t:ℝ)))
          + 2 * Real.logb 2 (n:ℝ) + (3 * L5 + 46022) := by
  have hile : i ≤ l := by omega
  have hm1 : 1 ≤ blkCount l s i := by
    unfold blkCount
    exact Nat.mul_pos (by omega) (by omega)
  have h1 : (codeDepth n t l s i hn : ℝ)
      ≤ ((blkCount l s i + (ThMax n (blkCount l s i) + 5) + 6 : ℕ) : ℝ) := by
    exact_mod_cast codeDepth_le hn ht hs hi hnr
  have h2 := ThMax_cast_le (n := n) (r := blkCount l s i) hn hm1
  have h3 := blkCount_le_logb hn ht hile hnr
  push_cast at h1
  have hcoef : (0:ℝ) ≤ L5 + 1 := by linarith [L5_nonneg]
  have hm := mul_le_mul_of_nonneg_left h3 hcoef
  linarith

end SymmFormulae
