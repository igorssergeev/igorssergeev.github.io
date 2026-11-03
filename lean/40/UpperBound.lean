module

public import Mathlib

/-!
# Upper bounds for the multiplicative complexity of classes of polynomials

This file formalises the upper bound of Theorem 1 of Sergeev,

* I. S. Sergeev, *On the multiplicative complexity of polynomials*, Discrete Math. Appl. **34**
  (2024) 29--32,

namely `μ(M_{d,n}) ≼ n ^ ⌈d / 2⌉`: for every polynomial `f` in `n` variables of total degree at
most `d`,

`μ(f) ≤ 2 · (n + 1) ^ ⌈d / 2⌉`,

with the constants given explicitly.  The paper's construction writes every polynomial of degree
at most `d` as a sum `f = ∑ᵤ Pᵤ · Qᵤ`, where the `Pᵤ` run over the monomials of degree at most
`K = ⌈d / 2⌉`, each `Pᵤ` is one multiplication away from a smaller monomial, each `Qᵤ` is a linear
combination of the monomials (free in the multiplicative model), and one further multiplication per
`u` computes `Pᵤ · Qᵤ`.

## Main definitions and results

Circuit-building tools:

* `ArithCircuit2.snocOut`, `snocOut_eval_last`, `snocOut_eval_castSucc` : extending a circuit by a
  gate and exposing it, with `snocOut_mulCount` for the effect on the multiplicative complexity.
* `ArithCircuit2.snocSet`, `snocSet_eval`, `snocSet_mulCount` : the single-output version.
* `Sergeev.unitTerm` : the unit monomial `∏_{j : Fin K} x (u j)`, of degree at most `K`, with
  `polyMu_unitTerm : μ(Pᵤ) ≤ K`; `polyMu_unitTerm_smul` and `polyMu_C_le` show that multiplying by
  a constant is free and that constants have complexity `0`.

Monomials and their two halves:

* `expo u i` is the exponent of `xᵢ` in the monomial of the padded vector `u`, and
  `unitTerm_eq_prod_pow` identifies `unitTerm R n K u` with `∏ i, xᵢ ^ expo u i`.
* `deg u` is the degree of that monomial and `parent u` is the monomial with one variable deleted;
  `unitTerm_update` builds the monomials one multiplication at a time (`deg_parent_lt` records that
  the parent has smaller rank).
* `fillFun m K` is the prefix fill of a monomial `m` with capacity `K`; `sum_min_prefix` computes
  the degrees of the two halves and `splitPair m K` produces the two padded vectors, with
  `expo_splitPair` (`expo` of the two halves adds up to `m`) and `exists_expo`.
* `unitTerm_split` and `eval_mul_unitTerm_split`: the product of the two halves of a monomial is
  the monomial.

The circuit:

* `CIdx` indexes the gates of the circuit computing `f` (the monomials `Pᵤ`, the scalar multiples
  `αᵤⱼ · Pᵥ` of second halves, the accumulators of the `Qᵤ`, the products `Pᵤ · Qᵤ`, and the final
  sum), `ord` ranks them, `op` gives their operations, `spec` the value each one should compute,
  `dagArgs` their arguments (with `ord` strictly decreasing), and `circuit` assembles them into a
  `DagCircuit (arithBasis R) n 1`, indexed by `cEquiv : CIdx ≃ Fin (card (CIdx _ _ _ _))`.
* `accVal_succ`, `totalVal_succ` and `eval_unitTerm_factor` are the one-step identities of the
  gate-by-gate computation.
* `circuit_nodeValue_spec`: the gate-by-gate verification that `circuit` computes `spec`, by strong
  induction on `ord`.
* `totalVal_spec`: the polynomial identity `∑ᵤ Pᵤ · Qᵤ = f`, obtained by regrouping the terms of
  `f.support` along the split `P = P' · P''`.
* `circuit_mulCount_le`: the circuit has at most `2 · (n + 1) ^ K` nonscalar multiplications, the
  `mono` and `prod` gates being the only ones.

The bounds:

* `polyMu_le_of_totalDegree : μ(f) ≤ 2 · (n + 1) ^ ⌈d / 2⌉` for `f.totalDegree ≤ d` and `0 < n`;
* `classMu_le_upper' : μ(M_{d,n}) ≤ 2 · (n + 1) ^ ⌈d / 2⌉` for all `n` (the case `n = 0` is
  `classMu_zero`, where every polynomial is a constant);
* `classMu_isBigO : μ(M_{d,n}) ≼ n ^ ⌈d / 2⌉` for a constant `d`.


## The refined upper bound for cubic polynomials

For `d = 3` the paper's second theorem improves the general construction by using only the
quadratic monomials `xᵢ xⱼ` whose two indices lie in the same half of the variable set.  Every
cubic monomial can be written as `x_l · xᵢ xⱼ` with `xᵢ xⱼ` of this restricted form, so

`f = c + ∑_l x_l · Q_l`,  `Q_l ∈ span{1, xᵢ, xᵢ xⱼ (same half)}`,

and a circuit needs only one multiplication per restricted quadratic monomial and one per `l`:

* `polyMu_le_cubic : μ(f) ≤ #(same-block pairs) + n` for `f.totalDegree ≤ 3`;
* `classMu_le_cubic : μ(M_{3,n}) ≤ #(same-block pairs) + n`.

The number of same-block pairs is `2 · C(⌈n/2⌉+1, 2) ∼ n²/4`, which is the paper's refined
upper bound `μ(M_{3,n}) ≲ n²/4`.

## Self-containedness

This file imports only Mathlib.  The circuit model of `MultcompPoly/Circuit.lean` and the
definitions `polyMu`, `classM`, `classMu` are now part of this file; `MultcompPoly/Circuit.lean`
re-exports them.

## Note on `n = 0`

The construction of this file presents every gate with two arguments, so it requires at least one
input; the degenerate case `n = 0` (finitely many constant polynomials, each of complexity `0`) is
treated separately by `polyMu_zero_var` and `classMu_zero`.
-/



@[expose] public section

universe u

namespace MultcompPoly

/-! ## Basic notions and the straight-line program presentation -/

/-- An operation of some arity on a carrier type `X`: a number of arguments together with the
function that the operation computes. -/
structure FuncOp (X : Type u) where
  /-- The number of arguments of the operation. -/
  arity : ℕ
  /-- The function computed by the operation. -/
  toFun : (Fin arity → X) → X

/-- A *basis* over `X`: a type of operations.  This is the paper's "basis (set of functions) `B`";
the set of functions in question is `{B.toFun op | op : B.Op}`. -/
structure Basis (X : Type u) where
  /-- The type of operations of the basis. -/
  Op : Type u
  /-- The arity and the function computed by each operation. -/
  toFuncOp : Op → FuncOp X

namespace Basis

variable {X : Type u} (B : Basis X)

/-- The arity of an operation of the basis. -/
def arity (op : B.Op) : ℕ := (B.toFuncOp op).arity

/-- The function computed by an operation of the basis. -/
def toFun (op : B.Op) : (Fin (B.arity op) → X) → X := (B.toFuncOp op).toFun

end Basis

/-- A circuit over a basis `B` with `k` inputs and `m` outputs.

The circuit has `size` gates, listed in a topological order: the arguments of gate `j` are
references to one of the `k` inputs or to one of the gates `0, …, j - 1`.  The `m` outputs of
the circuit are references to inputs or to gates.  The number of non-input vertices of the
underlying DAG is `size`.  (An operation of arity `0` gives a constant gate; the basis `A_R`
below contains such operations so that every polynomial is computable.) -/
structure Circuit {X : Type u} (B : Basis X) (k m : ℕ) where
  /-- The number of gates (non-input vertices) of the circuit. -/
  size : ℕ
  /-- The operation carried by each gate. -/
  gate : Fin size → B.Op
  /-- For gate `j`, the reference (input or earlier gate) feeding each of its arguments. -/
  args : (j : Fin size) → Fin (B.arity (gate j)) → Fin k ⊕ Fin j.val
  /-- The reference (input or gate) whose value is produced at each output. -/
  out : Fin m → Fin k ⊕ Fin size

namespace Circuit

variable {X : Type u} {B : Basis X} {k m : ℕ}

/-- The values of the gates `0, …, j - 1` of the circuit, on the input vector `x`. -/
def vals (c : Circuit B k m) (x : Fin k → X) : (j : ℕ) → j ≤ c.size → (Fin j → X)
  | 0, _ => Fin.elim0
  | j + 1, h => fun i =>
      if hi : i.val < j then vals c x j (Nat.le_of_succ_le h) ⟨i.val, hi⟩
      else
        B.toFun (c.gate ⟨j, Nat.lt_of_succ_le h⟩) fun t =>
          Sum.elim (fun a => x a) (fun a => vals c x j (Nat.le_of_succ_le h) a)
            (c.args ⟨j, Nat.lt_of_succ_le h⟩ t)

/-- The value computed at gate `j` of the circuit, on the input vector `x`. -/
def nodeValue (c : Circuit B k m) (x : Fin k → X) (j : Fin c.size) : X :=
  vals c x c.size (Nat.le_refl c.size) j

/-- The operator computed by the circuit: the values at its `m` outputs. -/
def eval (c : Circuit B k m) (x : Fin k → X) : Fin m → X :=
  fun o => match c.out o with
    | Sum.inl i => x i
    | Sum.inr j => nodeValue c x j

/-- The circuit `c` implements the operator `F` if its `m` outputs compute the `m` components of
`F`. -/
def Implements (c : Circuit B k m) (F : (Fin k → X) → Fin m → X) : Prop := c.eval = F

/-- Pointwise form of `Circuit.Implements`. -/
theorem implements_iff {c : Circuit B k m} {F : (Fin k → X) → Fin m → X} :
    c.Implements F ↔ ∀ x, c.eval x = F x :=
  ⟨fun h x => congrFun h x, fun h => funext h⟩

/-! ### Unfolding the evaluation of a circuit -/

/-- The values of a prefix of the gates agree with the values computed by the whole circuit. -/
theorem vals_succ (c : Circuit B k m) (x : Fin k → X) {n : ℕ} (h : n + 1 ≤ c.size)
    (i : Fin n) :
    c.vals x (n + 1) h (Fin.castSucc i) = c.vals x n (Nat.le_of_succ_le h) i := by
  simp only [Circuit.vals]
  split_ifs with hlt
  · exact congrArg (c.vals x n (Nat.le_of_succ_le h)) (Fin.ext rfl)
  · exact absurd i.isLt hlt

/-- The value at the last of `n + 1` gates is the operation of that gate applied to the values
of its arguments. -/
theorem vals_last (c : Circuit B k m) (x : Fin k → X) {n : ℕ} (h : n + 1 ≤ c.size) :
    c.vals x (n + 1) h ⟨n, Nat.lt_succ_self n⟩ =
      B.toFun (c.gate ⟨n, h⟩)
        (fun t => Sum.elim (fun a => x a) (fun g => c.vals x n (Nat.le_of_succ_le h) g)
          (c.args ⟨n, h⟩ t)) := by
  simp only [Circuit.vals]
  split_ifs with hlt
  · exact absurd hlt (Nat.lt_irrefl n)
  · rfl

/-- The value of a gate is the same as the value of that gate in the prefix of the gates ending
at it. -/
theorem vals_apply_of_le (c : Circuit B k m) (x : Fin k → X) :
    ∀ {n : ℕ} (hn : n ≤ c.size) (i : Fin n),
      c.vals x n hn i = c.nodeValue x ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := by
  have main : ∀ n, n ≤ c.size → (∀ hn' : n ≤ c.size, ∀ i : Fin n,
      c.vals x n hn' i = c.nodeValue x ⟨i.val, lt_of_lt_of_le i.isLt hn'⟩) := by
    intro n hle
    refine Nat.decreasingInduction (motive := fun n _ => ∀ hn' : n ≤ c.size, ∀ i : Fin n,
      c.vals x n hn' i = c.nodeValue x ⟨i.val, lt_of_lt_of_le i.isLt hn'⟩) ?_ ?_ hle
    · intro n hn ih hn' i
      have h1 : c.vals x n hn' i =
          c.vals x (n + 1) (hn : n + 1 ≤ c.size) (Fin.castSucc i) := by
        rw [vals_succ]
      rw [h1]
      exact ih (hn : n + 1 ≤ c.size) (Fin.castSucc i)
    · intro hn' i; rfl
  exact fun {n} hn i => main n hn hn i

/-- The value of gate `n` is the operation of that gate applied to the values of its arguments,
where an argument that is a gate refers to the value of that gate in the whole circuit. -/
theorem nodeValue_eq_aux (c : Circuit B k m) (x : Fin k → X) (n : ℕ) (hn : n < c.size) :
    c.nodeValue x ⟨n, hn⟩ =
      B.toFun (c.gate ⟨n, hn⟩) (fun t => Sum.elim (fun a => x a)
        (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le hn) g))
          (c.args ⟨n, hn⟩ t)) := by
  rw [← vals_apply_of_le (n := n + 1) c x hn ⟨n, Nat.lt_succ_self n⟩]
  rw [vals_last (n := n) (h := hn)]
  congr 1
  funext t
  cases hh : c.args ⟨n, hn⟩ t with
  | inl a => rfl
  | inr g => exact vals_apply_of_le (n := n) c x (Nat.le_of_succ_le hn) g

/-- Unfolding of the evaluation of a circuit at a gate: its value is the operation of the gate
applied to the values of the arguments, where an argument that is a gate refers to the value of
that gate in the whole circuit. -/
theorem nodeValue_eq (c : Circuit B k m) (x : Fin k → X) (j : Fin c.size) :
    c.nodeValue x j = B.toFun (c.gate j) (fun t => Sum.elim (fun a => x a)
      (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le j.isLt) g)) (c.args j t)) :=
  nodeValue_eq_aux c x j.val j.isLt

/-- The number of gates of `c` whose operation satisfies the Boolean predicate `p`. -/
def countGates (c : Circuit B k m) (p : B.Op → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin c.size => p (c.gate j)).card

/-- The number of gates of `c` whose operation satisfies `p` is at most the size of `c`. -/
theorem countGates_le (c : Circuit B k m) (p : B.Op → Bool) : c.countGates p ≤ c.size := by
  simpa [countGates] using
    Finset.card_filter_le (Finset.univ : Finset (Fin c.size)) (fun j => p (c.gate j))

/-- Counting with the constantly true predicate gives the size of the circuit. -/
theorem countGates_true (c : Circuit B k m) : c.countGates (fun _ => true) = c.size := by
  simp [countGates]

/-- The number of gates whose operation satisfies `p` is the cardinality of the subtype of such
gates. -/
theorem countGates_eq_card_subtype (c : Circuit B k m) (p : B.Op → Bool) :
    c.countGates p = Fintype.card {j : Fin c.size // p (c.gate j) = true} := by
  simp [countGates, Fintype.card_subtype]

/-- The complexity of a circuit: the number of its non-input vertices. -/
def complexity (c : Circuit B k m) : ℕ := c.size

@[simp] theorem complexity_eq (c : Circuit B k m) : c.complexity = c.size := rfl

/-- The circuit with no gates at all, whose `i`-th output is its `i`-th input. -/
def wires (B : Basis X) (k : ℕ) : Circuit B k k where
  size := 0
  gate := Fin.elim0
  args := fun j => j.elim0
  out := fun i => Sum.inl i

@[simp] theorem wires_eval (x : Fin k → X) : (wires B k).eval x = x := rfl

@[simp] theorem wires_complexity : (wires B k).complexity = 0 := rfl

@[simp] theorem wires_countGates (p : B.Op → Bool) : (wires B k).countGates p = 0 := rfl

end Circuit

/-- The complexity of an operator `F` implemented by circuits over the basis `B`: the minimal
number of non-input nodes of a circuit over `B` computing `F` (and `0` if no such circuit
exists). -/
noncomputable def complexityOf {X : Type u} (B : Basis X) {k m : ℕ}
    (F : (Fin k → X) → Fin m → X) : ℕ :=
  sInf {n : ℕ | ∃ c : Circuit B k m, c.Implements F ∧ c.complexity = n}

/-- A circuit implementing `F` has complexity at least the complexity of `F`. -/
theorem complexityOf_le {X : Type u} {B : Basis X} {k m : ℕ} {F : (Fin k → X) → Fin m → X}
    {c : Circuit B k m} (hc : c.Implements F) : complexityOf B F ≤ c.complexity :=
  Nat.sInf_le ⟨c, hc, rfl⟩

/-- If some circuit over `B` implements `F`, then some circuit implements `F` with exactly the
minimal complexity. -/
theorem exists_complexityOf_eq {X : Type u} {B : Basis X} {k m : ℕ}
    {F : (Fin k → X) → Fin m → X} (h : ∃ c : Circuit B k m, c.Implements F) :
    ∃ c : Circuit B k m, c.Implements F ∧ c.complexity = complexityOf B F := by
  obtain ⟨c₀, hc₀⟩ := h
  obtain ⟨c, hc⟩ := Nat.sInf_mem (s := {n | ∃ c : Circuit B k m, c.Implements F ∧ c.complexity = n})
    ⟨c₀.complexity, c₀, hc₀, rfl⟩
  exact ⟨c, hc.1, hc.2⟩

/-! ### The arithmetic basis `A_R` and the linear basis `Λ_R` -/

/-- The operations of the arithmetic basis `A_R = {+, -, *} ∪ {a · x | a ∈ R} ∪ {a | a ∈ R}`:
binary addition, binary subtraction, nonscalar multiplication, scalar multiplication by a
constant `a : R`, and the constant `a : R`. -/
inductive RingOp (R : Type u) : Type u
  /-- Binary addition. -/
  | add
  /-- Binary subtraction. -/
  | sub
  /-- Nonscalar multiplication. -/
  | mul
  /-- Scalar multiplication `x ↦ a * x` by the constant `a`. -/
  | smul (a : R)
  /-- The constant `a`. -/
  | const (a : R)

namespace RingOp

variable {R : Type u}

/-- The arity and semantics of each operation of `A_R`. -/
def toFuncOp [Ring R] : RingOp R → FuncOp R
  | add => ⟨2, fun v => v 0 + v 1⟩
  | sub => ⟨2, fun v => v 0 - v 1⟩
  | mul => ⟨2, fun v => v 0 * v 1⟩
  | smul a => ⟨1, fun v => a * v 0⟩
  | const a => ⟨0, fun _ => a⟩

/-- Tests whether an operation is the nonscalar multiplication gate. -/
def isMul : RingOp R → Bool
  | mul => true
  | _ => false

/-- Tests whether an operation is a constant gate. -/
def isConst : RingOp R → Bool
  | const _ => true
  | _ => false

/-- Tests whether an operation is a scalar multiplication gate. -/
def isScalarMul : RingOp R → Bool
  | smul _ => true
  | _ => false

end RingOp

/-- The arithmetic basis `A_R = {+, -, *} ∪ {a · x | a ∈ R} ∪ {a | a ∈ R}` over a ring `R`. -/
def arithBasis (R : Type u) [Ring R] : Basis R := ⟨RingOp R, RingOp.toFuncOp⟩

/-- The operations of the linear basis `Λ_R = {+, -} ∪ {a · x | a ∈ R}`: the scalar operations
of `A_R`, without nonscalar multiplication. -/
inductive LinearOp (R : Type u) : Type u
  /-- Binary addition. -/
  | add
  /-- Binary subtraction. -/
  | sub
  /-- Scalar multiplication `x ↦ a * x` by the constant `a`. -/
  | smul (a : R)

namespace LinearOp

variable {R : Type u}

/-- The arity and semantics of each operation of `Λ_R`. -/
def toFuncOp [Ring R] : LinearOp R → FuncOp R
  | add => ⟨2, fun v => v 0 + v 1⟩
  | sub => ⟨2, fun v => v 0 - v 1⟩
  | smul a => ⟨1, fun v => a * v 0⟩

/-- Tests whether an operation of `Λ_R` is a scalar multiplication gate. -/
def isScalarMul : LinearOp R → Bool
  | smul _ => true
  | _ => false

end LinearOp

/-- The linear basis `Λ_R = {+, -} ∪ {a · x | a ∈ R}` over a ring `R`. -/
def linearBasis (R : Type u) [Ring R] : Basis R := ⟨LinearOp R, LinearOp.toFuncOp⟩

/-- Arithmetic circuits over `R`: circuits over the basis `A_R`. -/
abbrev ArithmeticCircuit (R : Type u) [Ring R] (k m : ℕ) : Type u := Circuit (arithBasis R) k m

/-- Linear arithmetic circuits over `R`: circuits over the basis `Λ_R`. -/
abbrev LinearCircuit (R : Type u) [Ring R] (k m : ℕ) : Type u := Circuit (linearBasis R) k m

/-! ### Multiplicative complexity -/

/-- `µ(S)`: the multiplicative complexity of an arithmetic circuit `S` over `R`, i.e. the number
of its nonscalar multiplication gates. -/
def mulComplexity {R : Type u} [Ring R] {k m : ℕ} (S : ArithmeticCircuit R k m) : ℕ :=
  S.countGates RingOp.isMul

/-- `µ*(S)`: the scalar multiplicative complexity of an arithmetic circuit `S` over `R`, i.e. the
number of its scalar multiplication gates. -/
def scalarMulComplexity {R : Type u} [Ring R] {k m : ℕ} (S : ArithmeticCircuit R k m) : ℕ :=
  S.countGates RingOp.isScalarMul

theorem mulComplexity_le_size {R : Type u} [Ring R] {k m : ℕ} (S : ArithmeticCircuit R k m) :
    mulComplexity S ≤ S.size :=
  S.countGates_le RingOp.isMul

theorem scalarMulComplexity_le_size {R : Type u} [Ring R] {k m : ℕ}
    (S : ArithmeticCircuit R k m) : scalarMulComplexity S ≤ S.size :=
  S.countGates_le RingOp.isScalarMul

/-- `µ_R(F)`: the multiplicative complexity over `R` of the operator `F`, i.e. the minimal
multiplicative complexity of an arithmetic circuit over `R` implementing `F` (and `0` if `F` is
not computed by any arithmetic circuit). -/
noncomputable def mulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    (F : (Fin k → R) → Fin m → R) : ℕ :=
  sInf {n : ℕ | ∃ S : ArithmeticCircuit R k m, S.Implements F ∧ mulComplexity S = n}

/-- The scalar multiplicative complexity over `R` of the operator `F`: the minimal scalar
multiplicative complexity of an arithmetic circuit over `R` implementing `F`. -/
noncomputable def scalarMulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    (F : (Fin k → R) → Fin m → R) : ℕ :=
  sInf {n : ℕ | ∃ S : ArithmeticCircuit R k m, S.Implements F ∧ scalarMulComplexity S = n}

theorem mulComplexityOf_le {R : Type u} [Ring R] {k m : ℕ} {F : (Fin k → R) → Fin m → R}
    {S : ArithmeticCircuit R k m} (hS : S.Implements F) : mulComplexityOf F ≤ mulComplexity S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

theorem scalarMulComplexityOf_le {R : Type u} [Ring R] {k m : ℕ}
    {F : (Fin k → R) → Fin m → R} {S : ArithmeticCircuit R k m} (hS : S.Implements F) :
    scalarMulComplexityOf F ≤ scalarMulComplexity S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-! ### Examples -/

/-- The arithmetic circuit over `ℤ` with gates `g₀ = x₀ * x₁` and `g₁ = g₀ + x₀`, whose single
output is `g₁`; it computes `(x₀, x₁) ↦ x₀ * x₁ + x₀`. -/
def mulAddCircuit : ArithmeticCircuit ℤ 2 1 where
  size := 2
  gate := ![RingOp.mul, RingOp.add]
  args := fun j => match j with
    | 0 => ![Sum.inl 0, Sum.inl 1]
    | 1 => ![Sum.inr (0 : Fin 1), Sum.inl 0]
  out := fun _ => Sum.inr 1

/-- Evaluating the circuit on the input `(3, 5)` gives `3 * 5 + 3 = 18`. -/
example : mulAddCircuit.eval ![3, 5] 0 = 18 := by decide

/-- The circuit implements the operator `(x₀, x₁) ↦ x₀ * x₁ + x₀`. -/
theorem mulAddCircuit_implements :
    mulAddCircuit.Implements fun x : Fin 2 → ℤ => fun _ => x 0 * x 1 + x 0 := by
  funext x o
  fin_cases o
  simp [Circuit.eval, Circuit.nodeValue, Circuit.vals, mulAddCircuit, arithBasis, RingOp.toFuncOp,
    Basis.toFun, Matrix.cons_val_zero]

/-- The circuit has two gates. -/
example : mulAddCircuit.complexity = 2 := rfl

/-- It has a single nonscalar multiplication and no scalar multiplication. -/
example : mulComplexity mulAddCircuit = 1 := by decide

example : scalarMulComplexity mulAddCircuit = 0 := by decide

/-- The linear circuit over `ℤ` with gates `g₀ = 2 * x₀`, `g₁ = 3 * x₁` and `g₂ = g₀ + g₁`;
it computes `(x₀, x₁) ↦ 2 * x₀ + 3 * x₁`. -/
def linCircuit : LinearCircuit ℤ 2 1 where
  size := 3
  gate := ![LinearOp.smul 2, LinearOp.smul 3, LinearOp.add]
  args := fun j => match j with
    | 0 => ![Sum.inl 0]
    | 1 => ![Sum.inl 1]
    | 2 => ![Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)]
  out := fun _ => Sum.inr 2

/-- Evaluating the linear circuit on the input `(1, 1)` gives `2 + 3 = 5`. -/
example : linCircuit.eval ![1, 1] 0 = 5 := by decide

/-- The linear circuit has three gates, two of them scalar multiplications. -/
example : linCircuit.complexity = 3 := rfl

example : linCircuit.countGates LinearOp.isScalarMul = 2 := by decide

/-- `µ_ℤ(x₀ * x₁ + x₀) ≤ 1`: the multiplicative complexity of `x₀ * x₁ + x₀` is at most one,
witnessed by `mulAddCircuit`. -/
example : mulComplexityOf (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0) ≤ 1 :=
  mulComplexityOf_le mulAddCircuit_implements

/-- The complexity of `(x₀, x₁) ↦ x₀ * x₁ + x₀` over the basis `A_ℤ` is at most two, witnessed
by `mulAddCircuit`. -/
example : complexityOf (arithBasis ℤ) (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0)
    ≤ 2 :=
  complexityOf_le mulAddCircuit_implements

/-! ## Circuits as directed acyclic graphs

The section above uses the equivalent *straight-line program* presentation (gates listed in a
topological order).  This section gives the graph presentation itself and proves that the two
presentations agree: converting a circuit in either direction preserves the computed operator,
the number of gates, and the number of gates of any given type.

A directed acyclic graph on finitely many vertices can be equipped with a *rank* function that
strictly decreases along edges.  We store the graph as

* `size`, the number of gates (non-input vertices),
* `gate`, the operation labelling each gate,
* `order`, a rank function on the gates,
* `args`, which feeds each argument of each gate either from an input or from a gate of strictly
  smaller rank (the subtype `{g // order g < order j}` makes acyclicity hold by construction),
* `out`, the gate or input producing each output.

Compared to the straight-line-program presentation `Circuit`, the gates are *not* assumed to be
listed in a topological order: `order` is an arbitrary rank function witnessing acyclicity, and
gate `j` may depend on a gate with a larger index.

### Main results

* `DagCircuit.toSLP_eval`, `Circuit.toDag_eval` : both conversions preserve the operator
  (`DagCircuit.toSLP_nodeValue`, `Circuit.toDag_nodeValue` at the level of individual gates).
* `DagCircuit.toSLP_complexity`, `Circuit.toDag_complexity` : both preserve the complexity.
* `DagCircuit.toSLP_countGates`, `Circuit.toDag_countGates` : both preserve the number of gates
  of any given type, hence the multiplicative complexities.
* `DagCircuit.toSLP_toDag_eval`, `Circuit.toDag_toSLP_eval` (and their complexity and gate-count
  versions) : the round trips preserve the operator, the complexity and the gate counts.
* `MultcompPoly.dagComplexityOf_eq_complexityOf` and its multiplicative analogues
  `MultcompPoly.dagMulComplexityOf_eq_mulComplexityOf`,
  `MultcompPoly.dagScalarMulComplexityOf_eq_scalarMulComplexityOf` : the complexity of an operator
  is the same in the two presentations.
-/

/-- A circuit over a basis `B` with `k` inputs and `m` outputs, presented as a directed acyclic
graph: `size` gates, each labelled by an operation of `B`, ranked by `order`, whose arguments are
inputs or gates of strictly smaller rank, together with the `m` outputs. -/
structure DagCircuit {X : Type u} (B : Basis X) (k m : ℕ) where
  /-- The number of gates (non-input vertices) of the circuit. -/
  size : ℕ
  /-- The operation carried by each gate. -/
  gate : Fin size → B.Op
  /-- A rank function on the gates; it strictly decreases along the edges of the DAG. -/
  order : Fin size → ℕ
  /-- For gate `j`, the source (input or gate of smaller rank) of each of its arguments. -/
  args : (j : Fin size) → Fin (B.arity (gate j)) → Fin k ⊕ {g : Fin size // order g < order j}
  /-- The reference (input or gate) whose value is produced at each output. -/
  out : Fin m → Fin k ⊕ Fin size

namespace DagCircuit

variable {X : Type u} {B : Basis X} {k m : ℕ}

/-! ### Semantics -/

/-- The value computed at gate `j` of the circuit, on the input vector `x`.  This is well-founded
recursion on the rank of the gates, which decreases along every edge. -/
def nodeValue (c : DagCircuit B k m) (x : Fin k → X) (j : Fin c.size) : X :=
  (measure c.order).wf.fix (C := fun _ => X) (fun j rec =>
    B.toFun (c.gate j) fun t =>
      Sum.elim (fun a => x a) (fun g => rec g.1 g.2) (c.args j t)) j

/-- Unfolding of `DagCircuit.nodeValue`: the value of a gate is the operation of the gate applied
to the values of its arguments. -/
theorem nodeValue_eq (c : DagCircuit B k m) (x : Fin k → X) (j : Fin c.size) :
    c.nodeValue x j = B.toFun (c.gate j) (fun t =>
      Sum.elim (fun a => x a) (fun g => c.nodeValue x g.1) (c.args j t)) := by
  rw [nodeValue, WellFounded.fix_eq]
  simp only [nodeValue]

/-- The operator computed by the circuit: the values at its `m` outputs. -/
def eval (c : DagCircuit B k m) (x : Fin k → X) : Fin m → X :=
  fun o => match c.out o with
    | Sum.inl i => x i
    | Sum.inr j => c.nodeValue x j

/-- The circuit `c` implements the operator `F` if its `m` outputs compute the `m` components of
`F`. -/
def Implements (c : DagCircuit B k m) (F : (Fin k → X) → Fin m → X) : Prop := c.eval = F

/-- Pointwise form of `DagCircuit.Implements`. -/
theorem implements_iff {c : DagCircuit B k m} {F : (Fin k → X) → Fin m → X} :
    c.Implements F ↔ ∀ x, c.eval x = F x :=
  ⟨fun h x => congrFun h x, fun h => funext h⟩

/-! ### Complexity -/

/-- The complexity of a circuit: the number of its non-input vertices. -/
def complexity (c : DagCircuit B k m) : ℕ := c.size

@[simp] theorem complexity_eq (c : DagCircuit B k m) : c.complexity = c.size := rfl

/-- The number of gates of `c` whose operation satisfies the Boolean predicate `p`. -/
def countGates (c : DagCircuit B k m) (p : B.Op → Bool) : ℕ :=
  (Finset.univ.filter fun j : Fin c.size => p (c.gate j)).card

/-- The number of gates of `c` whose operation satisfies `p` is at most the size of `c`. -/
theorem countGates_le (c : DagCircuit B k m) (p : B.Op → Bool) : c.countGates p ≤ c.size := by
  simpa [countGates] using
    Finset.card_filter_le (Finset.univ : Finset (Fin c.size)) (fun j => p (c.gate j))

/-- Counting with the constantly true predicate gives the size of the circuit. -/
theorem countGates_true (c : DagCircuit B k m) : c.countGates (fun _ => true) = c.size := by
  simp [countGates]

/-- The number of gates whose operation satisfies `p` is the cardinality of the subtype of such
gates. -/
theorem countGates_eq_card_subtype (c : DagCircuit B k m) (p : B.Op → Bool) :
    c.countGates p = Fintype.card {j : Fin c.size // p (c.gate j) = true} := by
  simp [countGates, Fintype.card_subtype]

/-- The circuit with no gates at all, whose `i`-th output is its `i`-th input. -/
def wires (B : Basis X) (k : ℕ) : DagCircuit B k k where
  size := 0
  gate := Fin.elim0
  order := Fin.elim0
  args := fun j => j.elim0
  out := fun i => Sum.inl i

@[simp] theorem wires_eval (x : Fin k → X) : (wires B k).eval x = x := rfl

@[simp] theorem wires_complexity : (wires B k).complexity = 0 := rfl

@[simp] theorem wires_countGates (p : B.Op → Bool) : (wires B k).countGates p = 0 := rfl

/-! ### Topological sorting

The gates of a DAG can be listed in a topological order: sort them by the pair (rank, index),
encoded as the natural number `key j = order j * (size + 1) + j.val`.  The `key` is strictly
increasing in the rank and injective, so the number of gates with a smaller key is a strictly
monotone injective map `pos : Fin size → Fin size`, i.e. a permutation of the gates. -/

/-- The sort key of a gate: its rank, with the index as tie-breaker. -/
def key (c : DagCircuit B k m) (j : Fin c.size) : ℕ := c.order j * (c.size + 1) + j.val

theorem key_lt_key {c : DagCircuit B k m} {i j : Fin c.size} (h : c.order i < c.order j) :
    c.key i < c.key j := by
  have hi : i.val < c.size + 1 := Nat.lt_succ_of_lt i.isLt
  have h1 : c.order i * (c.size + 1) + i.val < (c.order i + 1) * (c.size + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left hi _
  have h2 : (c.order i + 1) * (c.size + 1) ≤ c.order j * (c.size + 1) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h)
  simp only [key]
  omega

theorem key_mod (c : DagCircuit B k m) (j : Fin c.size) :
    c.key j % (c.size + 1) = j.val := by
  have hj : j.val < c.size + 1 := Nat.lt_succ_of_lt j.isLt
  simp only [key, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj]

theorem key_injective (c : DagCircuit B k m) : Function.Injective c.key := by
  intro i j h
  have h' := congrArg (· % (c.size + 1)) h
  simp only [key_mod] at h'
  exact Fin.ext h'

/-- The position of gate `j` in the topological order: the number of gates with a smaller key. -/
def pos (c : DagCircuit B k m) (j : Fin c.size) : ℕ :=
  (Finset.univ.filter fun i : Fin c.size => c.key i < c.key j).card

theorem pos_lt (c : DagCircuit B k m) (j : Fin c.size) : c.pos j < c.size := by
  have hsub : (Finset.univ.filter fun i : Fin c.size => c.key i < c.key j) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
    have : j ∈ Finset.univ.filter fun i : Fin c.size => c.key i < c.key j := by
      rw [heq]; exact Finset.mem_univ j
    exact absurd (Finset.mem_filter.mp this).2 (lt_irrefl _)
  simpa [pos] using Finset.card_lt_card hsub

theorem pos_lt_pos {c : DagCircuit B k m} {i j : Fin c.size} (h : c.key i < c.key j) :
    c.pos i < c.pos j := by
  have hsub : (Finset.univ.filter fun x : Fin c.size => c.key x < c.key i) ⊂
      (Finset.univ.filter fun x : Fin c.size => c.key x < c.key j) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hx).2 h⟩, fun heq => ?_⟩
    have : i ∈ Finset.univ.filter fun x : Fin c.size => c.key x < c.key j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq] at this
    exact absurd (Finset.mem_filter.mp this).2 (lt_irrefl _)
  simpa [pos] using Finset.card_lt_card hsub

theorem pos_injective (c : DagCircuit B k m) : Function.Injective c.pos := by
  intro i j h
  rcases lt_trichotomy (c.key i) (c.key j) with hlt | heq | hgt
  · exact absurd h (ne_of_lt (c.pos_lt_pos hlt))
  · exact c.key_injective heq
  · exact absurd h.symm (ne_of_lt (c.pos_lt_pos hgt))

/-- The position of a gate, as an element of `Fin size`. -/
def posFin (c : DagCircuit B k m) (j : Fin c.size) : Fin c.size := ⟨c.pos j, c.pos_lt j⟩

theorem posFin_injective (c : DagCircuit B k m) : Function.Injective c.posFin :=
  fun _ _ h => c.pos_injective (congrArg Fin.val h)

theorem posFin_surjective (c : DagCircuit B k m) : Function.Surjective c.posFin := by
  intro p
  have hcard : (Finset.univ.image c.posFin).card = c.size := by
    rw [Finset.card_image_of_injective _ c.posFin_injective, Finset.card_univ, Fintype.card_fin]
  have heq : Finset.univ.image c.posFin = Finset.univ := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [hcard, Finset.card_univ, Fintype.card_fin]
  have : p ∈ Finset.univ.image c.posFin := by rw [heq]; exact Finset.mem_univ p
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp this
  exact ⟨j, hj⟩

/-- The permutation of the gates sorting them by rank: gate `j` is at position `equiv j`. -/
noncomputable def equiv (c : DagCircuit B k m) : Fin c.size ≃ Fin c.size where
  toFun := c.posFin
  invFun p := Classical.choose (c.posFin_surjective p)
  left_inv j := c.posFin_injective (Classical.choose_spec (c.posFin_surjective (c.posFin j)))
  right_inv p := Classical.choose_spec (c.posFin_surjective p)

theorem equiv_apply (c : DagCircuit B k m) (j : Fin c.size) :
    c.equiv j = ⟨c.pos j, c.pos_lt j⟩ := rfl

/-- The position of the gate at position `p` in the sorted order is `p.val`. -/
theorem pos_equiv_symm (c : DagCircuit B k m) (p : Fin c.size) :
    c.pos (c.equiv.symm p) = p.val := by
  have h := c.equiv.apply_symm_apply p
  rw [equiv_apply] at h
  exact congrArg Fin.val h

/-- The sorted order is a topological order: a gate of smaller rank sits at a smaller position. -/
theorem equiv_lt {c : DagCircuit B k m} {i j : Fin c.size}
    (h : c.order i < c.order j) : c.equiv i < c.equiv j := by
  rw [equiv_apply, equiv_apply, Fin.lt_def]
  exact c.pos_lt_pos (c.key_lt_key h)

/-! ### From DAGs to straight-line programs -/

/-- The straight-line program obtained by listing the gates of the DAG in a topological order.

This is an `abbrev` on purpose: all of its fields are the corresponding fields of the DAG
(reindexed), so that statements about `c.toSLP` reduce definitionally to statements about `c`,
which keeps the proofs below short. -/
noncomputable abbrev toSLP (c : DagCircuit B k m) : Circuit B k m where
  size := c.size
  gate := fun p => c.gate (c.equiv.symm p)
  args := fun p t => Sum.map id (fun g => (⟨c.pos g.1, by
    have h : c.pos g.1 < c.pos (c.equiv.symm p) := c.pos_lt_pos (c.key_lt_key g.2)
    rwa [c.pos_equiv_symm p] at h⟩ : Fin p.val)) (c.args (c.equiv.symm p) t)
  out := fun o => Sum.map id c.equiv (c.out o)

@[simp] theorem toSLP_size (c : DagCircuit B k m) : c.toSLP.size = c.size := rfl

@[simp] theorem toSLP_gate (c : DagCircuit B k m) (p : Fin c.size) :
    c.toSLP.gate p = c.gate (c.equiv.symm p) := rfl

/-- Unfolding of the arguments of the straight-line program: the arguments of the gate at
position `p` are the arguments of the gate sitting at position `p`, reindexed by the position of
the gate they point to. -/
theorem toSLP_args (c : DagCircuit B k m) (p : Fin c.size)
    (t : Fin (B.arity (c.gate (c.equiv.symm p)))) :
    c.toSLP.args p t = Sum.map id (fun g => (⟨c.pos g.1, by
      have h : c.pos g.1 < c.pos (c.equiv.symm p) := c.pos_lt_pos (c.key_lt_key g.2)
      rwa [c.pos_equiv_symm p] at h⟩ : Fin p.val)) (c.args (c.equiv.symm p) t) := rfl

/-- The straight-line program has the same number of gates as the DAG. -/
theorem toSLP_complexity (c : DagCircuit B k m) : c.toSLP.complexity = c.complexity := rfl

/-- Sorting the gates into a topological order does not change the number of gates of a given
type. -/
theorem toSLP_countGates (c : DagCircuit B k m) (p : B.Op → Bool) :
    c.toSLP.countGates p = c.countGates p := by
  rw [Circuit.countGates_eq_card_subtype, countGates_eq_card_subtype]
  refine Fintype.card_congr
    { toFun := fun q => ⟨c.equiv.symm (show Fin c.size from q.1), by
        show p (c.toSLP.gate (show Fin c.size from q.1)) = true
        rw [toSLP_gate]
        exact q.2⟩
      invFun := fun q => ⟨c.equiv q.1, by
        show p (c.toSLP.gate (c.equiv q.1)) = true
        rw [toSLP_gate, Equiv.symm_apply_apply]
        exact q.2⟩
      left_inv := fun q => by ext; simp
      right_inv := fun q => by ext; simp }

@[simp] theorem toSLP_out (c : DagCircuit B k m) (o : Fin m) :
    c.toSLP.out o = Sum.map id c.equiv (c.out o) := rfl

theorem equiv_symm_posFin (c : DagCircuit B k m) (g : Fin c.size) :
    c.equiv.symm ⟨c.pos g, c.pos_lt g⟩ = g :=
  c.equiv.left_inv g

/-- The value computed by the straight-line program at position `p` is the value computed by the
DAG at the gate sitting at position `p`. -/
theorem toSLP_nodeValue_aux (c : DagCircuit B k m) (x : Fin k → X) (p : Fin c.size) :
    c.toSLP.nodeValue x p = c.nodeValue x (c.equiv.symm p) := by
  induction h : p.val using Nat.strongRecOn generalizing p with
  | ind n ih =>
    rw [Circuit.nodeValue_eq c.toSLP x p, DagCircuit.nodeValue_eq]
    congr 1
    funext t
    rw [toSLP_args]
    cases hh : c.args (c.equiv.symm p) t with
    | inl a => rfl
    | inr g =>
      have hpos : c.pos g.1 < n := by
        have hlt : c.pos g.1 < c.pos (c.equiv.symm p) := c.pos_lt_pos (c.key_lt_key g.2)
        rw [c.pos_equiv_symm] at hlt
        omega
      have hstep := ih (c.pos g.1) hpos ⟨c.pos g.1, c.pos_lt g.1⟩ rfl
      rw [c.equiv_symm_posFin g.1] at hstep
      simpa only [Sum.map_inr, Sum.elim_inr, Fin.castLE] using hstep

/-- Sorting the gates into a topological order does not change the value computed at a gate. -/
theorem toSLP_nodeValue (c : DagCircuit B k m) (x : Fin k → X) (j : Fin c.size) :
    c.toSLP.nodeValue x (c.equiv j) = c.nodeValue x j := by
  have h1 : c.toSLP.nodeValue x (c.equiv j) = c.nodeValue x (c.equiv.symm (c.equiv j)) :=
    c.toSLP_nodeValue_aux x (c.equiv j)
  rwa [Equiv.symm_apply_apply] at h1

/-- The straight-line program obtained by sorting the gates of a DAG computes the same operator. -/
theorem toSLP_eval (c : DagCircuit B k m) : c.toSLP.eval = c.eval := by
  funext x o
  rw [Circuit.eval, DagCircuit.eval, toSLP_out]
  cases ho : c.out o with
  | inl a => rfl
  | inr g => exact c.toSLP_nodeValue x g

end DagCircuit

namespace Circuit

variable {X : Type u} {B : Basis X} {k m : ℕ}

/-- The arguments of the DAG gate corresponding to gate `j` of a straight-line program: an
argument that is a gate `g` becomes the gate `g`, whose rank `g.val` is smaller than `j.val`. -/
def toDagArgs (c : Circuit B k m) (j : Fin c.size) (t : Fin (B.arity (c.gate j))) :
    Fin k ⊕ {g : Fin c.size // g.val < j.val} :=
  Sum.map id (fun g => ⟨⟨g.val, lt_of_lt_of_le g.isLt (Nat.le_of_lt j.isLt)⟩, g.isLt⟩)
    (c.args j t)

/-- A straight-line program is a DAG whose rank function is the position of the gate.

This is an `abbrev` on purpose, so that statements about `c.toDag` reduce definitionally to
statements about `c` (see the note on `DagCircuit.toSLP`). -/
noncomputable abbrev toDag (c : Circuit B k m) : DagCircuit B k m where
  size := c.size
  gate := c.gate
  order := fun j => j.val
  args := c.toDagArgs
  out := c.out

@[simp] theorem toDag_gate (c : Circuit B k m) (j : Fin c.size) :
    c.toDag.gate j = c.gate j := rfl

@[simp] theorem toDag_order (c : Circuit B k m) (j : Fin c.size) :
    c.toDag.order j = j.val := rfl

@[simp] theorem toDag_out (c : Circuit B k m) (o : Fin m) :
    c.toDag.out o = c.out o := rfl

/-- Unfolding of the arguments of the DAG: the arguments of gate `j` are the arguments of gate
`j`, where an argument that is a gate `g` becomes the gate `g` of the DAG. -/
theorem toDag_args (c : Circuit B k m) (j : Fin c.size) (t : Fin (B.arity (c.gate j))) :
    c.toDag.args j t = Sum.map id (fun g =>
      ⟨⟨g.val, lt_of_lt_of_le g.isLt (Nat.le_of_lt j.isLt)⟩, g.isLt⟩) (c.args j t) := rfl

/-- The DAG has the same number of gates as the straight-line program. -/
theorem toDag_complexity (c : Circuit B k m) : c.toDag.complexity = c.complexity := rfl

/-- The DAG has as many gates of a given type as the straight-line program. -/
theorem toDag_countGates (c : Circuit B k m) (p : B.Op → Bool) :
    c.toDag.countGates p = c.countGates p := rfl

/-- The DAG obtained from a straight-line program computes the same value at every gate. -/
theorem toDag_nodeValue (c : Circuit B k m) (x : Fin k → X) (j : Fin c.size) :
    c.toDag.nodeValue x j = c.nodeValue x j := by
  induction h : j.val using Nat.strongRecOn generalizing j with
  | ind n ih =>
    rw [DagCircuit.nodeValue_eq, Circuit.nodeValue_eq]
    congr 1
    funext t
    rw [toDag_args]
    cases hh : c.args j t with
    | inl a => rfl
    | inr g => exact ih g.val (by omega) ⟨g.val, lt_of_lt_of_le g.isLt (Nat.le_of_lt j.isLt)⟩ rfl

/-- The DAG obtained from a straight-line program computes the same operator. -/
theorem toDag_eval (c : Circuit B k m) : c.toDag.eval = c.eval := by
  funext x o
  rw [DagCircuit.eval, Circuit.eval, toDag_out]
  cases ho : c.out o with
  | inl a => rfl
  | inr g => exact c.toDag_nodeValue x g

/-- Round trip: reading a straight-line program as a DAG and sorting it back computes the same
operator. -/
theorem toDag_toSLP_eval (c : Circuit B k m) : c.toDag.toSLP.eval = c.eval := by
  rw [DagCircuit.toSLP_eval, Circuit.toDag_eval]

/-- Round trip: the complexity is unchanged. -/
theorem toDag_toSLP_complexity (c : Circuit B k m) :
    c.toDag.toSLP.complexity = c.complexity := by
  rw [DagCircuit.toSLP_complexity, Circuit.toDag_complexity]

/-- Round trip: the number of gates of any given type is unchanged. -/
theorem toDag_toSLP_countGates (c : Circuit B k m) (p : B.Op → Bool) :
    c.toDag.toSLP.countGates p = c.countGates p := by
  rw [DagCircuit.toSLP_countGates, Circuit.toDag_countGates]

end Circuit

namespace DagCircuit

variable {X : Type u} {B : Basis X} {k m : ℕ}

/-! ### Round trips -/

/-- Round trip: sorting the gates of a DAG into a straight-line program and reading the DAG back
computes the same operator. -/
theorem toSLP_toDag_eval (c : DagCircuit B k m) : c.toSLP.toDag.eval = c.eval := by
  rw [Circuit.toDag_eval, DagCircuit.toSLP_eval]

/-- Round trip: the complexity is unchanged. -/
theorem toSLP_toDag_complexity (c : DagCircuit B k m) :
    c.toSLP.toDag.complexity = c.complexity := by
  rw [Circuit.toDag_complexity, DagCircuit.toSLP_complexity]

/-- Round trip: the number of gates of any given type is unchanged. -/
theorem toSLP_toDag_countGates (c : DagCircuit B k m) (p : B.Op → Bool) :
    c.toSLP.toDag.countGates p = c.countGates p := by
  rw [Circuit.toDag_countGates, DagCircuit.toSLP_countGates]

/-! ### The two presentations have the same complexity -/

/-- The complexity of an operator over a basis `B`, using the DAG presentation: the minimal
number of non-input vertices of a DAG circuit over `B` computing `F` (and `0` if no such circuit
exists). -/
noncomputable def dagComplexityOf {X : Type u} (B : Basis X) {k m : ℕ}
    (F : (Fin k → X) → Fin m → X) : ℕ :=
  sInf {n : ℕ | ∃ c : DagCircuit B k m, c.Implements F ∧ c.complexity = n}

end DagCircuit

/-- A DAG circuit implementing `F` has complexity at least the complexity of `F`. -/
theorem DagCircuit.dagComplexityOf_le {X : Type u} {B : Basis X} {k m : ℕ}
    {F : (Fin k → X) → Fin m → X} {c : DagCircuit B k m} (hc : c.Implements F) :
    DagCircuit.dagComplexityOf B F ≤ c.complexity :=
  Nat.sInf_le ⟨c, hc, rfl⟩

/-- The two presentations of circuits give the same complexity for an operator. -/
theorem dagComplexityOf_eq_complexityOf {X : Type u} {B : Basis X} {k m : ℕ}
    {F : (Fin k → X) → Fin m → X} :
    DagCircuit.dagComplexityOf B F = complexityOf B F := by
  have h : {n : ℕ | ∃ c : DagCircuit B k m, c.Implements F ∧ c.complexity = n}
      = {n : ℕ | ∃ c : Circuit B k m, c.Implements F ∧ c.complexity = n} := by
    ext n
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.toSLP, by rw [Circuit.Implements, c.toSLP_eval]; exact hc, c.toSLP_complexity⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.toDag, by rw [DagCircuit.Implements, c.toDag_eval]; exact hc, c.toDag_complexity⟩
  simp only [DagCircuit.dagComplexityOf, complexityOf, h]

/-! ### Arithmetic and linear DAG circuits, and multiplicative complexity -/

/-- Arithmetic DAG circuits over `R`: DAG circuits over the basis `A_R`. -/
abbrev DagArithmeticCircuit (R : Type u) [Ring R] (k m : ℕ) : Type u :=
  DagCircuit (arithBasis R) k m

/-- Linear arithmetic DAG circuits over `R`: DAG circuits over the basis `Λ_R`. -/
abbrev DagLinearCircuit (R : Type u) [Ring R] (k m : ℕ) : Type u :=
  DagCircuit (linearBasis R) k m

/-- `µ(S)` for a DAG circuit: the number of its nonscalar multiplication gates. -/
def dagMulComplexity {R : Type u} [Ring R] {k m : ℕ} (S : DagArithmeticCircuit R k m) : ℕ :=
  S.countGates RingOp.isMul

/-- `µ*(S)` for a DAG circuit: the number of its scalar multiplication gates. -/
def dagScalarMulComplexity {R : Type u} [Ring R] {k m : ℕ}
    (S : DagArithmeticCircuit R k m) : ℕ :=
  S.countGates RingOp.isScalarMul

/-- Sorting the gates of a DAG circuit into a topological order does not change its
multiplicative complexity. -/
theorem dagMulComplexity_toSLP {R : Type u} [Ring R] {k m : ℕ}
    (S : DagArithmeticCircuit R k m) : mulComplexity S.toSLP = dagMulComplexity S :=
  DagCircuit.toSLP_countGates S RingOp.isMul

/-- Sorting the gates of a DAG circuit into a topological order does not change its scalar
multiplicative complexity. -/
theorem dagScalarMulComplexity_toSLP {R : Type u} [Ring R] {k m : ℕ}
    (S : DagArithmeticCircuit R k m) : scalarMulComplexity S.toSLP = dagScalarMulComplexity S :=
  DagCircuit.toSLP_countGates S RingOp.isScalarMul

/-- The DAG of a straight-line program has the same multiplicative complexity. -/
theorem dagMulComplexity_toDag {R : Type u} [Ring R] {k m : ℕ}
    (S : ArithmeticCircuit R k m) : dagMulComplexity S.toDag = mulComplexity S := rfl

/-- The DAG of a straight-line program has the same scalar multiplicative complexity. -/
theorem dagScalarMulComplexity_toDag {R : Type u} [Ring R] {k m : ℕ}
    (S : ArithmeticCircuit R k m) : dagScalarMulComplexity S.toDag = scalarMulComplexity S := rfl

/-- `µ_R(F)` computed with the DAG presentation: the minimal multiplicative complexity of a DAG
circuit over `R` implementing `F`. -/
noncomputable def dagMulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    (F : (Fin k → R) → Fin m → R) : ℕ :=
  sInf {n : ℕ | ∃ S : DagArithmeticCircuit R k m, S.Implements F ∧ dagMulComplexity S = n}

/-- The scalar multiplicative complexity over `R`, computed with the DAG presentation. -/
noncomputable def dagScalarMulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    (F : (Fin k → R) → Fin m → R) : ℕ :=
  sInf {n : ℕ | ∃ S : DagArithmeticCircuit R k m, S.Implements F ∧ dagScalarMulComplexity S = n}

/-- A DAG circuit implementing `F` has multiplicative complexity at least `µ_R(F)`. -/
theorem dagMulComplexityOf_le {R : Type u} [Ring R] {k m : ℕ} {F : (Fin k → R) → Fin m → R}
    {S : DagArithmeticCircuit R k m} (hS : S.Implements F) :
    dagMulComplexityOf F ≤ dagMulComplexity S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- A DAG circuit implementing `F` has scalar multiplicative complexity at least the minimum. -/
theorem dagScalarMulComplexityOf_le {R : Type u} [Ring R] {k m : ℕ}
    {F : (Fin k → R) → Fin m → R} {S : DagArithmeticCircuit R k m} (hS : S.Implements F) :
    dagScalarMulComplexityOf F ≤ dagScalarMulComplexity S :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- The two presentations give the same multiplicative complexity. -/
theorem dagMulComplexityOf_eq_mulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    {F : (Fin k → R) → Fin m → R} : dagMulComplexityOf F = mulComplexityOf F := by
  have h : {n : ℕ | ∃ S : DagArithmeticCircuit R k m, S.Implements F ∧ dagMulComplexity S = n}
      = {n : ℕ | ∃ S : ArithmeticCircuit R k m, S.Implements F ∧ mulComplexity S = n} := by
    ext n
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.toSLP, by rw [Circuit.Implements, S.toSLP_eval]; exact hS,
        dagMulComplexity_toSLP S⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.toDag, by rw [DagCircuit.Implements, S.toDag_eval]; exact hS,
        dagMulComplexity_toDag S⟩
  simp only [dagMulComplexityOf, mulComplexityOf, h]

/-- The two presentations give the same scalar multiplicative complexity. -/
theorem dagScalarMulComplexityOf_eq_scalarMulComplexityOf {R : Type u} [Ring R] {k m : ℕ}
    {F : (Fin k → R) → Fin m → R} : dagScalarMulComplexityOf F = scalarMulComplexityOf F := by
  have h : {n : ℕ | ∃ S : DagArithmeticCircuit R k m, S.Implements F ∧
        dagScalarMulComplexity S = n}
      = {n : ℕ | ∃ S : ArithmeticCircuit R k m, S.Implements F ∧ scalarMulComplexity S = n} := by
    ext n
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.toSLP, by rw [Circuit.Implements, S.toSLP_eval]; exact hS,
        dagScalarMulComplexity_toSLP S⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.toDag, by rw [DagCircuit.Implements, S.toDag_eval]; exact hS,
        dagScalarMulComplexity_toDag S⟩
  simp only [dagScalarMulComplexityOf, scalarMulComplexityOf, h]

/-! ### Examples

The circuits below are the DAG counterparts of the examples above. -/

/-- The circuit `x₀ * x₁ + x₀` as a DAG whose gates are *not* listed in a topological order: gate
`0` is the addition and depends on gate `1`, the multiplication. -/
def mulAddDag : DagArithmeticCircuit ℤ 2 1 where
  size := 2
  gate := ![RingOp.add, RingOp.mul]
  order := ![1, 0]
  args := fun j => match j with
    | 0 => ![Sum.inr (⟨1, by decide⟩), Sum.inl 0]
    | 1 => ![Sum.inl 0, Sum.inl 1]
  out := fun _ => Sum.inr 0

/-- The multiplication gate of `mulAddDag` on the input `x`. -/
theorem mulAddDag_nodeValue_mul (x : Fin 2 → ℤ) :
    mulAddDag.nodeValue x ⟨1, by decide⟩ = x 0 * x 1 := by
  rw [DagCircuit.nodeValue_eq]
  simp [mulAddDag, arithBasis, RingOp.toFuncOp, Basis.toFun]

/-- The addition gate of `mulAddDag` on the input `x`. -/
theorem mulAddDag_nodeValue_add (x : Fin 2 → ℤ) :
    mulAddDag.nodeValue x ⟨0, by decide⟩ = mulAddDag.nodeValue x ⟨1, by decide⟩ + x 0 := by
  rw [DagCircuit.nodeValue_eq]
  simp [mulAddDag, arithBasis, RingOp.toFuncOp, Basis.toFun]

/-- Evaluating the DAG circuit on the input `(3, 5)` gives `3 * 5 + 3 = 18`, although the gates
are not in a topological order. -/
example : mulAddDag.eval ![3, 5] 0 = 18 := by
  show mulAddDag.nodeValue ![3, 5] ⟨0, by decide⟩ = 18
  rw [mulAddDag_nodeValue_add, mulAddDag_nodeValue_mul]
  norm_num

/-- The DAG circuit implements the operator `(x₀, x₁) ↦ x₀ * x₁ + x₀`. -/
theorem mulAddDag_implements :
    mulAddDag.Implements fun x : Fin 2 → ℤ => fun _ => x 0 * x 1 + x 0 := by
  funext x o
  fin_cases o
  show mulAddDag.nodeValue x ⟨0, by decide⟩ = x 0 * x 1 + x 0
  rw [mulAddDag_nodeValue_add, mulAddDag_nodeValue_mul]

/-- The DAG circuit has two gates. -/
example : mulAddDag.complexity = 2 := rfl

/-- It has a single nonscalar multiplication. -/
example : dagMulComplexity mulAddDag = 1 := by
  decide

/-- It has no scalar multiplication. -/
example : dagScalarMulComplexity mulAddDag = 0 := by
  decide

/-- Sorting the gates of `mulAddDag` into a topological order gives a straight-line program that
computes the same operator. -/
example : mulAddDag.toSLP.eval ![3, 5] 0 = 18 := by
  rw [DagCircuit.toSLP_eval]
  show mulAddDag.nodeValue ![3, 5] ⟨0, by decide⟩ = 18
  rw [mulAddDag_nodeValue_add, mulAddDag_nodeValue_mul]
  norm_num

/-- Sorting the gates into a topological order preserves the complexity... -/
example : mulAddDag.toSLP.complexity = mulAddDag.complexity :=
  DagCircuit.toSLP_complexity mulAddDag

/-- ... and the number of nonscalar multiplications. -/
example : mulAddDag.toSLP.countGates RingOp.isMul = dagMulComplexity mulAddDag :=
  DagCircuit.toSLP_countGates mulAddDag RingOp.isMul

/-- Going back to a DAG changes nothing. -/
example : mulAddDag.toSLP.toDag.toSLP.complexity = mulAddDag.complexity := by
  rw [DagCircuit.toSLP_complexity, Circuit.toDag_complexity, DagCircuit.toSLP_complexity]

/-- `µ_ℤ(x₀ * x₁ + x₀) ≤ 1` witnessed by the DAG circuit. -/
example : dagMulComplexityOf (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0) ≤ 1 := by
  have h : dagMulComplexity mulAddDag = 1 := by decide
  calc dagMulComplexityOf (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0)
      ≤ dagMulComplexity mulAddDag := dagMulComplexityOf_le mulAddDag_implements
    _ = 1 := h

/-- The complexity of `(x₀, x₁) ↦ x₀ * x₁ + x₀` over `A_ℤ` is at most two, witnessed by the
DAG circuit. -/
example : DagCircuit.dagComplexityOf (arithBasis ℤ)
    (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0) ≤ 2 :=
  DagCircuit.dagComplexityOf_le mulAddDag_implements

/-- The complexity of `x₀ * x₁ + x₀` is the same in the two presentations. -/
example : DagCircuit.dagComplexityOf (arithBasis ℤ)
      (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0)
    = complexityOf (arithBasis ℤ) (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0) :=
  dagComplexityOf_eq_complexityOf

/-- The multiplicative complexity of `x₀ * x₁ + x₀` is the same in the two presentations. -/
example : dagMulComplexityOf (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0)
    = mulComplexityOf (fun x : Fin 2 → ℤ => fun _ : Fin 1 => x 0 * x 1 + x 0) :=
  dagMulComplexityOf_eq_mulComplexityOf

end MultcompPoly

namespace MultcompPoly
namespace Sergeev


open MvPolynomial

/-! ## Complexity of polynomials and of classes -/

variable {R : Type u} [CommRing R] {n : ℕ}

/-- `µ(f)`: the multiplicative complexity of the polynomial `f`, i.e. of the polynomial function
`x ↦ f x` on `Fin n → R`. -/
noncomputable def polyMu (f : MvPolynomial (Fin n) R) : ℕ :=
  mulComplexityOf fun x : Fin n → R => fun _ : Fin 1 => f.eval x

/-- The class `M_{d,n}` of polynomials in `n` variables of total degree at most `d`. -/
def classM (d n : ℕ) : Set (MvPolynomial (Fin n) R) := {f | f.totalDegree ≤ d}

/-- `µ(M_{d,n})`: the complexity of the class `M_{d,n}`, i.e. the maximum of `µ(f)` over the
class (the paper's `µ(M)` for a class `M`). -/
noncomputable def classMu (d n : ℕ) : ℕ :=
  ⨆ f : {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d}, polyMu f.1

theorem classMu_le {d n B : ℕ}
    (h : ∀ f : {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d}, polyMu f.1 ≤ B) :
    classMu (R := R) d n ≤ B := by
  unfold classMu
  haveI : Nonempty {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d} := ⟨⟨0, by simp⟩⟩
  exact ciSup_le h

theorem le_classMu {d n : ℕ} (B : ℕ)
    (hb : ∀ f : {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d}, polyMu f.1 ≤ B)
    (f : {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d}) :
    polyMu f.1 ≤ classMu (R := R) d n := by
  unfold classMu
  haveI : Nonempty {f : MvPolynomial (Fin n) R // f.totalDegree ≤ d} := ⟨f⟩
  exact le_ciSup ⟨B, by rintro _ ⟨i, rfl⟩; exact hb i⟩ f

end Sergeev
end MultcompPoly

@[expose] public section


namespace MultcompPoly

/-! ## Operations displayed with two arguments -/

/-- The operations of the arithmetic basis used in the upper-bound construction, displayed with
two arguments (the second argument of a scalar multiplication is ignored).  This is a local copy
of `UpperOp`, so that the file only depends on Mathlib. -/
inductive UpperOp (R : Type u) : Type u
  /-- Binary addition. -/
  | add
  /-- Binary subtraction. -/
  | sub
  /-- Nonscalar multiplication. -/
  | mul
  /-- Scalar multiplication `x ↦ a * x` (of the first argument). -/
  | smul (a : R)
  /-- The constant `a` (both arguments are ignored). -/
  | const (a : R)

namespace UpperOp

variable {R : Type u}

/-- The operation of `A_R` corresponding to an operation displayed with two arguments. -/
def toRingOp : UpperOp R → RingOp R
  | add => .add
  | sub => .sub
  | mul => .mul
  | smul a => .smul a
  | const a => .const a

variable [CommRing R]

/-- The value computed by an operation applied to two arguments. -/
def eval : UpperOp R → R → R → R
  | add, u, v => u + v
  | sub, u, v => u - v
  | mul, u, v => u * v
  | smul a, u, _ => a * u
  | const a, _, _ => a

/-- Tests whether an operation is the nonscalar multiplication gate. -/
def isMul : UpperOp R → Bool
  | mul => true
  | _ => false

omit [CommRing R] in
@[simp] theorem isMul_toRingOp (op : UpperOp R) :
    RingOp.isMul (toRingOp op) = isMul op := by
  cases op <;> rfl

/-- Which of the two displayed argument slots reads the argument of the corresponding operation
of `A_R`. -/
def projArgB : (op : UpperOp R) → Fin ((arithBasis R).arity (toRingOp op)) → Fin 2
  | .add => id
  | .sub => id
  | .mul => id
  | .smul _ => fun _ => 0
  | .const _ => Fin.elim0

theorem eval_toRingOp (op : UpperOp R) (v : Fin 2 → R) :
    (arithBasis R).toFun (toRingOp op) (fun t => v (projArgB op t))
      = eval op (v 0) (v 1) := by
  cases op <;> rfl

end UpperOp


namespace Sergeev

open MvPolynomial

/-- The monomial `∏_{j : Fin K} x (u j)`, where a slot `u j = n` contributes the factor `1`.
These are the "unit monomials" of degree at most `K` used in the upper-bound construction. -/
noncomputable def unitTerm (R : Type u) [CommRing R] (n K : ℕ) (u : Fin K → Fin (n + 1)) :
    MvPolynomial (Fin n) R :=
  ∏ j : Fin K, if h : (u j).val < n then
    (MvPolynomial.X ⟨(u j).val, h⟩ : MvPolynomial (Fin n) R) else 1

theorem unitTerm_succ (R : Type u) [CommRing R] {n K : ℕ}
    (u : Fin (K + 1) → Fin (n + 1)) :
    unitTerm R n (K + 1) u
      = unitTerm R n K (fun j => u (Fin.castSucc j))
        * (if h : (u (Fin.last K)).val < n then
            (MvPolynomial.X ⟨(u (Fin.last K)).val, h⟩ : MvPolynomial (Fin n) R) else 1) := by
  rw [unitTerm, Fin.prod_univ_castSucc]
  rfl

end Sergeev

/-! ## Monomials, their exponents, and the two halves of a monomial

A monomial of degree at most `K` in `n` variables is encoded by a *padded vector*
`u : Fin K → Fin (n + 1)`: the entry `⟨i, _⟩` with `i < n` is the variable `xᵢ`, while the padding
value `Fin.last n` is an empty slot.  The monomial itself is `unitTerm R n K u` (of degree at most
`K`), and there are exactly `(n + 1) ^ K` padded vectors.

* `expo u i` is the exponent of `xᵢ` in `unitTerm R n K u`, and `unitTerm_eq_prod_pow` expresses
  the monomial as `∏ i, xᵢ ^ expo u i`.
* `deg u` is the degree of the monomial, i.e. the number of non-padding entries.
* `parent u` is the monomial with one variable deleted, so that the monomials are computed one
  multiplication at a time (`unitTerm_update`).
* `fillFun m K` is the prefix fill of a monomial `m` with capacity `K`: its first `K` occurrences
  in the order of the variables.  `sum_fillFun` and `sum_compl_fillFun` give the degrees of the two
  halves, and `splitPair` produces the two padded vectors. -/

namespace Sergeev

section Monomials

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The exponent of the variable `xᵢ` in the padded vector `u`. -/
def expo {j : ℕ} (u : Fin j → Fin (n + 1)) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun t => u t = Fin.castSucc i).card

theorem expo_snoc {j : ℕ} (u : Fin j → Fin (n + 1)) (a : Fin (n + 1)) (i : Fin n) :
    expo (Fin.snoc u a) i = expo u i + (if a = Fin.castSucc i then 1 else 0) := by
  simp only [expo, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]

theorem expo_snoc_last {j : ℕ} (u : Fin j → Fin (n + 1)) (i : Fin n) :
    expo (Fin.snoc u (Fin.last n)) i = expo u i := by
  have hne : Fin.last n ≠ Fin.castSucc i := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
    omega
  rw [expo_snoc, if_neg hne, add_zero]

/-- The factor of `unitTerm R n j u` at position `t`. -/
noncomputable def unitFac {j : ℕ} (u : Fin j → Fin (n + 1)) (t : Fin j) : MvPolynomial (Fin n) R :=
  if h : (u t).val < n then MvPolynomial.X ⟨(u t).val, h⟩ else 1

theorem unitTerm_eq_prod {j : ℕ} (u : Fin j → Fin (n + 1)) :
    unitTerm R n j u = ∏ t : Fin j, unitFac u t := rfl
theorem prod_pow_of_ite (a : Fin (n + 1)) :
    (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^
        (if a = Fin.castSucc i then 1 else 0))
      = if h : a.val < n then MvPolynomial.X ⟨a.val, h⟩ else 1 := by
  classical
  split_ifs with ha
  · refine (Finset.prod_eq_single_of_mem (⟨a.val, ha⟩ : Fin n) (Finset.mem_univ _) ?_).trans ?_
    · intro b _ hb
      have hne : ¬ (a = Fin.castSucc b) := by
        intro hc
        have hv : a.val = b.val := congrArg Fin.val hc
        exact hb (Fin.ext hv.symm)
      rw [if_neg hne, pow_zero]
    · have hpos : a = Fin.castSucc (⟨a.val, ha⟩ : Fin n) := Fin.ext rfl
      rw [if_pos hpos, pow_one]
  · refine Finset.prod_eq_one fun i _ => ?_
    have hne : ¬ (a = Fin.castSucc i) := by
      intro hc
      have hv : a.val = i.val := congrArg Fin.val hc
      omega
    rw [if_neg hne, pow_zero]

theorem unitTerm_eq_prod_pow (K : ℕ) (u : Fin K → Fin (n + 1)) :
    unitTerm R n K u = ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ expo u i := by
  induction K with
  | zero => simp [unitTerm, expo]
  | succ K ih =>
      rw [unitTerm_succ, ih (fun j => u (Fin.castSucc j))]
      have hprod : (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ expo u i)
          = ∏ i : Fin n, ((MvPolynomial.X i : MvPolynomial (Fin n) R) ^
                expo (fun j : Fin K => u (Fin.castSucc j)) i *
              (MvPolynomial.X i) ^ (if u (Fin.last K) = Fin.castSucc i then 1 else 0)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        have heta : Fin.snoc (fun j : Fin K => u (Fin.castSucc j)) (u (Fin.last K)) = u := by
          funext t
          rcases Fin.eq_castSucc_or_eq_last t with ⟨t', rfl⟩ | rfl
          · rw [Fin.snoc_castSucc]
          · rw [Fin.snoc_last]
        conv_lhs => rw [← heta]
        rw [expo_snoc, pow_add]
      rw [hprod, Finset.prod_mul_distrib, prod_pow_of_ite]

theorem eval_unitTerm (K : ℕ) (u : Fin K → Fin (n + 1)) (x : Fin n → R) :
    (unitTerm R n K u).eval x = ∏ i : Fin n, x i ^ expo u i := by
  rw [unitTerm_eq_prod_pow]
  simp

/-- The number of non-padding entries of a padded vector, i.e. the degree of the monomial. -/
def deg {j : ℕ} (u : Fin j → Fin (n + 1)) : ℕ :=
  (Finset.univ.filter fun t => (u t).val < n).card

theorem deg_le {j : ℕ} (u : Fin j → Fin (n + 1)) : deg u ≤ j := by
  simpa [deg] using
    Finset.card_filter_le (s := (Finset.univ : Finset (Fin j))) (p := fun t => (u t).val < n)

/-- The positions at which the padded vector `u` carries a variable. -/
def npSet {j : ℕ} (u : Fin j → Fin (n + 1)) : Finset (Fin j) :=
  Finset.univ.filter fun t => (u t).val < n

theorem deg_eq_card {j : ℕ} (u : Fin j → Fin (n + 1)) : deg u = (npSet u).card := rfl

theorem mem_npSet {j : ℕ} {u : Fin j → Fin (n + 1)} {t : Fin j} :
    t ∈ npSet u ↔ (u t).val < n := by
  simp [npSet]

/-- Deleting one variable from a monomial: replace one non-padding entry by padding. -/
noncomputable def parent {j : ℕ} (u : Fin j → Fin (n + 1)) : Fin j → Fin (n + 1) :=
  if h : (npSet u).Nonempty then Function.update u ((npSet u).max' h) (Fin.last n) else u

theorem parent_eq_update {j : ℕ} {u : Fin j → Fin (n + 1)} (h : (npSet u).Nonempty) :
    ∃ t : Fin j, (u t).val < n ∧ parent u = Function.update u t (Fin.last n) :=
  ⟨_, mem_npSet.1 ((npSet u).max'_mem h), by rw [parent]; exact dif_pos h⟩

theorem deg_parent_lt {j : ℕ} {u : Fin j → Fin (n + 1)} (h : (npSet u).Nonempty) :
    deg (parent u) < deg u := by
  obtain ⟨t, ht, hpar⟩ := parent_eq_update h
  have hset : npSet (Function.update u t (Fin.last n)) = (npSet u).erase t := by
    ext s
    rw [mem_npSet, Finset.mem_erase, mem_npSet, Function.update_apply]
    by_cases hst : s = t
    · subst hst; simp
    · rw [if_neg hst]; simp [hst]
  rw [deg_eq_card, deg_eq_card, hpar, hset, Finset.card_erase_of_mem (mem_npSet.2 ht)]
  have : 0 < (npSet u).card := Finset.card_pos.2 h
  omega

theorem unitTerm_update {j : ℕ} {u : Fin j → Fin (n + 1)} {t : Fin j} (h : (u t).val < n) :
    unitTerm R n j u = unitTerm R n j (Function.update u t (Fin.last n)) * unitFac u t := by
  rw [unitTerm_eq_prod, unitTerm_eq_prod,
    ← Finset.prod_erase_mul _ (unitFac u) (Finset.mem_univ t)]
  congr 1
  rw [← Finset.prod_erase_mul _ (unitFac (Function.update u t (Fin.last n))) (Finset.mem_univ t),
    show unitFac (Function.update u t (Fin.last n)) t = 1 from by simp [unitFac], mul_one]
  refine Finset.prod_congr rfl fun s hs => ?_
  have hst : s ≠ t := (Finset.mem_erase.1 hs).1
  simp [unitFac, Function.update_apply, hst]

theorem unitTerm_eq_one_of_npSet_eq_empty {j : ℕ} {u : Fin j → Fin (n + 1)}
    (h : npSet u = ∅) : unitTerm R n j u = 1 := by
  rw [unitTerm_eq_prod, Finset.prod_eq_one]
  intro t _
  have hlt : ¬ ((u t).val < n) := by
    intro hc
    have hmem : t ∈ npSet u := mem_npSet.2 hc
    simp [h] at hmem
  simp [unitFac, hlt]

/-- The first `K` occurrences of the monomial `m`, in the order of the variables. -/
def fillFun (m : Fin n → ℕ) (K : ℕ) (i : Fin n) : ℕ :=
  min (m i) (K - ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), m j)

theorem fillFun_le (m : Fin n → ℕ) (K : ℕ) (i : Fin n) : fillFun m K i ≤ m i :=
  Nat.min_le_left _ _

theorem sum_min_prefix {α : Type*} [LinearOrder α] [DecidableEq α] (s : Finset α) (m : α → ℕ)
    (K : ℕ) :
    (∑ i ∈ s, min (m i) (K - ∑ j ∈ s.filter (fun j => j < i), m j) = min (∑ i ∈ s, m i) K)
    ∧ (∑ i ∈ s, (m i - min (m i) (K - ∑ j ∈ s.filter (fun j => j < i), m j))
        = ∑ i ∈ s, m i - min (∑ i ∈ s, m i) K) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have h1 : (insert a s).filter (fun j => j < a) = s := by
        rw [Finset.filter_insert, if_neg (lt_irrefl a),
          Finset.filter_true_of_mem (fun x hx => hlt x hx)]
      have h2 : ∀ i ∈ s, (insert a s).filter (fun j => j < i) = s.filter (fun j => j < i) := by
        intro i hi
        rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt (hlt i hi)))]
      have h3 : ¬ a ∈ s := by
        intro hc
        exact absurd (hlt a hc) (lt_irrefl a)
      constructor
      · have hcongr : (∑ i ∈ s, min (m i) (K - ∑ j ∈ (insert a s).filter (fun j => j < i), m j))
            = ∑ i ∈ s, min (m i) (K - ∑ j ∈ s.filter (fun j => j < i), m j) :=
          Finset.sum_congr rfl (fun i hi => by rw [h2 i hi])
        rw [Finset.sum_insert h3, Finset.sum_insert h3, h1, hcongr, ih1]
        omega
      · have hcongr : (∑ i ∈ s, (m i - min (m i) (K - ∑ j ∈ (insert a s).filter (fun j => j < i), m j)))
            = ∑ i ∈ s, (m i - min (m i) (K - ∑ j ∈ s.filter (fun j => j < i), m j)) :=
          Finset.sum_congr rfl (fun i hi => by rw [h2 i hi])
        rw [Finset.sum_insert h3, Finset.sum_insert h3, h1, hcongr, ih2]
        omega

/-! ### Splitting a monomial into two halves of degree at most `K` -/

theorem sum_update_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) {a : ι}
    (ha : 0 < f a) : ∑ i, Function.update f a (f a - 1) i = (∑ i, f i) - 1 := by
  rw [← Finset.add_sum_erase (Finset.univ : Finset ι) (Function.update f a (f a - 1))
    (Finset.mem_univ a)]
  have h1 : ∀ i ∈ (Finset.univ : Finset ι).erase a, Function.update f a (f a - 1) i = f i := by
    intro i hi
    rw [Function.update_apply, if_neg (Finset.mem_erase.1 hi).1]
  have h2 : (∑ i ∈ (Finset.univ : Finset ι).erase a, Function.update f a (f a - 1) i)
      = ∑ i ∈ (Finset.univ : Finset ι).erase a, f i := Finset.sum_congr rfl h1
  rw [h2, Function.update_apply, if_pos rfl,
    ← Finset.add_sum_erase (Finset.univ : Finset ι) f (Finset.mem_univ a)]
  omega

/-- Every exponent vector of total degree at most `K` is the exponent vector of a padded vector
of length `K` (pad with empty slots). -/
theorem exists_expo (w : Fin n → ℕ) :
    ∀ (K : ℕ), (∑ i, w i ≤ K) → ∃ u : Fin K → Fin (n + 1), expo u = w := by
  intro K
  induction K generalizing w with
  | zero =>
      intro h
      refine ⟨fun t => t.elim0, ?_⟩
      have hw : ∀ i, w i = 0 := by
        intro i
        have h1 : w i ≤ ∑ j, w j :=
          Finset.single_le_sum (f := w) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      funext i
      simp [expo, hw i]
  | succ K ih =>
      intro h
      by_cases hK : ∑ i, w i ≤ K
      · obtain ⟨u, hu⟩ := ih w hK
        exact ⟨Fin.snoc u (Fin.last n), by funext i; rw [expo_snoc_last, hu]⟩
      · obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, 0 < w i0 := by
          by_contra hcon
          have hz : ∑ i, w i = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            by_contra hne
            exact hcon ⟨i, Nat.pos_of_ne_zero hne⟩
          omega
        obtain ⟨u', hu'⟩ := ih (fun i => Function.update w i0 (w i0 - 1) i) (by
          rw [sum_update_nat w hi0]
          omega)
        refine ⟨Fin.snoc u' (Fin.castSucc i0), ?_⟩
        funext i
        have hu'' : expo u' i = Function.update w i0 (w i0 - 1) i := congrFun hu' i
        rw [expo_snoc, hu'']
        by_cases hii : i = i0
        · subst hii
          rw [Function.update_apply, if_pos rfl]
          simp
          omega
        · have h1 : Function.update w i0 (w i0 - 1) i = w i := by
            rw [Function.update_apply, if_neg hii]
          have h2 : ¬ ((Fin.castSucc i0 : Fin (n + 1)) = Fin.castSucc i) := by
            intro hc
            exact hii (Fin.castSucc_inj.1 hc).symm
          rw [h1, if_neg h2, add_zero]

theorem exists_expo_weak (w : Fin n → ℕ) (K : ℕ) :
    ∃ u : Fin K → Fin (n + 1), (∑ i, w i ≤ K → expo u = w) := by
  by_cases h : ∑ i, w i ≤ K
  · obtain ⟨u, hu⟩ := exists_expo w K h
    exact ⟨u, fun _ => hu⟩
  · exact ⟨fun _ => Fin.last n, fun hc => absurd hc h⟩

/-- An enumeration of the occurrences of the exponent vector `w` by a padded vector of length `K`
(correct when the degree is at most `K`). -/
noncomputable def enumVec (w : Fin n → ℕ) (K : ℕ) : Fin K → Fin (n + 1) :=
  Classical.choose (exists_expo_weak w K)

theorem expo_enumVec {w : Fin n → ℕ} {K : ℕ} (h : ∑ i, w i ≤ K) :
    expo (enumVec w K) = w :=
  Classical.choose_spec (exists_expo_weak w K) h

theorem sum_fillFun (m : Fin n → ℕ) (K : ℕ) :
    ∑ i, fillFun m K i = min (∑ i, m i) K := by
  simpa [fillFun] using (sum_min_prefix (Finset.univ : Finset (Fin n)) m K).1

theorem sum_compl_fillFun (m : Fin n → ℕ) (K : ℕ) :
    ∑ i, (m i - fillFun m K i) = ∑ i, m i - min (∑ i, m i) K := by
  simpa [fillFun] using (sum_min_prefix (Finset.univ : Finset (Fin n)) m K).2

/-- The two halves of a monomial: the padded vectors of its first `K` occurrences and of the
remaining occurrences. -/
noncomputable def splitPair (m : Fin n → ℕ) (K : ℕ) :
    (Fin K → Fin (n + 1)) × (Fin K → Fin (n + 1)) :=
  (enumVec (fillFun m K) K, enumVec (fun i => m i - fillFun m K i) K)

/-- The two halves add up to the monomial they split, if its degree is at most `2 K`. -/
theorem expo_splitPair (m : Fin n → ℕ) (K : ℕ) (h : ∑ i, m i ≤ 2 * K) :
    expo (splitPair m K).1 + expo (splitPair m K).2 = m := by
  have h1 : expo (splitPair m K).1 = fillFun m K :=
    expo_enumVec (by rw [sum_fillFun]; exact Nat.min_le_right _ _)
  have h2 : expo (splitPair m K).2 = fun i => m i - fillFun m K i :=
    expo_enumVec (by rw [sum_compl_fillFun]; omega)
  funext i
  simp only [Pi.add_apply, h1, h2]
  exact Nat.add_sub_of_le (fillFun_le m K i)

/-- Each half has degree at most `K`. -/
theorem deg_splitPair (m : Fin n → ℕ) (K : ℕ) :
    deg (splitPair m K).1 ≤ K ∧ deg (splitPair m K).2 ≤ K :=
  ⟨deg_le _, deg_le _⟩

/-! ### The circuit computing a polynomial of degree at most `2 K`

The paper's construction is realised as a DAG circuit over `A_R`:

* `mono u` computes the monomial `Pᵤ` (one multiplication per monomial, deleting one variable at a
  time, `parent`);
* `smul u j` computes the scalar multiple `αᵤⱼ · Pᵥ` of a second half;
* `acc u j` accumulates the linear combination `Qᵤ = ∑ⱼ αᵤⱼ Pᵥ` (additions only);
* `prod u` computes `Pᵤ · Qᵤ` (one multiplication per monomial);
* `total j` accumulates the final sum (additions only).

Only the `mono` and `prod` gates are nonscalar multiplications. -/
section Circuit

variable {R : Type u} [CommRing R] {n : ℕ} {K : ℕ} (hn : 0 < n)

/-- The monomials of degree at most `K`, indexed by padded vectors of length `K`. -/
abbrev MonoIdx (n K : ℕ) : Type := Fin K → Fin (n + 1)

/-- The number of monomials of degree at most `K` in `n` variables. -/
def monoCount (n K : ℕ) : ℕ := Fintype.card (MonoIdx n K)

theorem monoCount_eq (n K : ℕ) : monoCount n K = (n + 1) ^ K := by
  simp [monoCount, MonoIdx]

/-- The enumeration of the monomials of degree at most `K`. -/
noncomputable def monoEquiv (n K : ℕ) : Fin (monoCount n K) ≃ MonoIdx n K :=
  (Fintype.equivFin (MonoIdx n K)).symm

variable {f : MvPolynomial (Fin n) R}

/-- The `j`-th monomial of the support of `f`. -/
noncomputable def suppAt (f : MvPolynomial (Fin n) R) (j : Fin f.support.card) : Fin n →₀ ℕ :=
  (((Fintype.equivFin ↥f.support).symm
    (Fin.cast (Fintype.card_coe f.support).symm j) : ↥f.support) : Fin n →₀ ℕ)

theorem suppAt_mem (f : MvPolynomial (Fin n) R) (j : Fin f.support.card) :
    suppAt f j ∈ f.support :=
  ((Fintype.equivFin ↥f.support).symm (Fin.cast (Fintype.card_coe f.support).symm j) :
    ↥f.support).2

/-- The first half of the `j`-th monomial of the support. -/
noncomputable def fstHalf (f : MvPolynomial (Fin n) R) (j : Fin f.support.card) : MonoIdx n K :=
  (splitPair (fun i => suppAt f j i) K).1

/-- The second half of the `j`-th monomial of the support. -/
noncomputable def sndHalf (f : MvPolynomial (Fin n) R) (j : Fin f.support.card) : MonoIdx n K :=
  (splitPair (fun i => suppAt f j i) K).2

/-- The coefficient of the `j`-th monomial of the support, attached to the monomial `u` when `u`
is its first half and to nothing otherwise. -/
noncomputable def coeffUV (f : MvPolynomial (Fin n) R) (u : MonoIdx n K)
    (j : Fin f.support.card) : R :=
  if fstHalf f j = u then f.coeff (suppAt f j) else 0

/-- The value at `x` of the term `αᵤⱼ · Pᵥ` of the linear combination `Qᵤ`. -/
noncomputable def termVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (u : MonoIdx n K)
    (j : Fin f.support.card) : R :=
  coeffUV f u j * (unitTerm R n K (sndHalf f j)).eval x

/-- The value at `x` of the linear combination `Qᵤ` truncated after `j` terms. -/
noncomputable def accVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (u : MonoIdx n K)
    (j : Fin (f.support.card + 1)) : R :=
  ∑ t : Fin j.val, termVal f x u (Fin.castLE (Nat.le_of_lt_succ j.isLt) t)

/-- The value at `x` of the product `Pᵤ · Qᵤ`. -/
noncomputable def prodVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (u : MonoIdx n K) : R :=
  (unitTerm R n K u).eval x * accVal f x u ⟨f.support.card, Nat.lt_succ_self _⟩

/-- The value at `x` of the final sum, truncated after `j` terms. -/
noncomputable def totalVal (f : MvPolynomial (Fin n) R) (x : Fin n → R)
    (j : Fin (monoCount n K + 1)) : R :=
  ∑ t : Fin j.val,
    prodVal f x (monoEquiv n K (Fin.castLE (Nat.le_of_lt_succ j.isLt) t))

/-- The gates of the circuit computing `f`. -/
inductive CIdx (R : Type u) [CommRing R] (n K : ℕ) (f : MvPolynomial (Fin n) R) : Type u
  /-- The monomial `Pᵤ`. -/
  | mono (u : MonoIdx n K)
  /-- The scalar multiple `αᵤⱼ · Pᵥ`. -/
  | smul (u : MonoIdx n K) (j : Fin f.support.card)
  /-- The truncated linear combination `Qᵤ`. -/
  | acc (u : MonoIdx n K) (j : Fin (f.support.card + 1))
  /-- The product `Pᵤ · Qᵤ`. -/
  | prod (u : MonoIdx n K)
  /-- The truncated final sum. -/
  | total (j : Fin (monoCount n K + 1))

/-- The gate indices as a nested sum type, for the `Fintype` instance. -/
abbrev CIdxSum (R : Type u) [CommRing R] (n K : ℕ) (f : MvPolynomial (Fin n) R) : Type :=
  MonoIdx n K ⊕ ((MonoIdx n K) × Fin f.support.card) ⊕
    ((MonoIdx n K) × Fin (f.support.card + 1)) ⊕ MonoIdx n K ⊕ Fin (monoCount n K + 1)

/-- The equivalence between the gate indices and the corresponding nested sum type. -/
noncomputable def cIdxSumEquiv : CIdx R n K f ≃ CIdxSum R n K f where
  toFun
    | .mono u => Sum.inl u
    | .smul u j => Sum.inr (Sum.inl (u, j))
    | .acc u j => Sum.inr (Sum.inr (Sum.inl (u, j)))
    | .prod u => Sum.inr (Sum.inr (Sum.inr (Sum.inl u)))
    | .total j => Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))
  invFun
    | Sum.inl u => .mono u
    | Sum.inr (Sum.inl (u, j)) => .smul u j
    | Sum.inr (Sum.inr (Sum.inl (u, j))) => .acc u j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl u))) => .prod u
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr j))) => .total j
  left_inv i := by cases i <;> rfl
  right_inv s := by
    rcases s with (u | ⟨u, j⟩ | ⟨u, j⟩ | u | j) <;> rfl

noncomputable instance : Fintype (CIdx R n K f) :=
  Fintype.ofEquiv _ (cIdxSumEquiv (R := R) (n := n) (K := K) (f := f)).symm

/-- The index equivalence presenting the gates as `Fin size`. -/
noncomputable def cEquiv : CIdx R n K f ≃ Fin (Fintype.card (CIdx R n K f)) :=
  Fintype.equivFin _

/-- The poset ranking making the circuit acyclic. -/
def ord : CIdx R n K f → ℕ
  | .mono u => deg u + 1
  | .smul _ _ => K + 2
  | .acc _ j => K + 3 + j.val
  | .prod _ => K + f.support.card + 4
  | .total j => K + f.support.card + 5 + j.val

/-- The operation carried by each gate. -/
noncomputable def op : CIdx R n K f → UpperOp R
  | .mono u => if (npSet u).Nonempty then UpperOp.mul else UpperOp.const 1
  | .smul u j => UpperOp.smul (coeffUV f u j)
  | .acc _ j => if j.val = 0 then UpperOp.const 0 else UpperOp.add
  | .prod _ => UpperOp.mul
  | .total j => if j.val = 0 then UpperOp.const 0 else UpperOp.add

/-- The value that each gate is meant to compute. -/
noncomputable def spec (f : MvPolynomial (Fin n) R) (x : Fin n → R) : CIdx R n K f → R
  | .mono u => (unitTerm R n K u).eval x
  | .smul u j => termVal f x u j
  | .acc u j => accVal f x u j
  | .prod u => prodVal f x u
  | .total j => totalVal f x j

/-- The two arguments of each gate, as elements of `CIdx` (inputs are `Sum.inl`, gates are
`Sum.inr`, and the rank of a gate argument is strictly smaller). -/
noncomputable def dagArgs (i : CIdx R n K f) :
    Fin 2 → Fin n ⊕ {g : CIdx R n K f // ord g < ord i} := by
  match i with
  | .mono u =>
      by_cases h : (npSet u).Nonempty
      · exact ![Sum.inl ⟨(u ((npSet u).max' h)).val, mem_npSet.1 ((npSet u).max'_mem h)⟩,
          Sum.inr ⟨CIdx.mono (parent u), by
            simp only [ord]
            exact Nat.succ_lt_succ (deg_parent_lt h)⟩]
      · exact fun _ => Sum.inl ⟨0, hn⟩
  | .smul u j =>
      exact ![Sum.inr ⟨CIdx.mono (sndHalf f j), by
          simp only [ord]
          have := deg_le (sndHalf (K := K) f j)
          omega⟩,
        Sum.inl ⟨0, hn⟩]
  | .acc u j =>
      by_cases h : j.val = 0
      · exact fun _ => Sum.inl ⟨0, hn⟩
      · exact ![Sum.inr ⟨CIdx.acc u ⟨j.val - 1, by have := j.isLt; omega⟩, by
            simp only [ord]; omega⟩,
          Sum.inr ⟨CIdx.smul u ⟨j.val - 1, by have := j.isLt; omega⟩, by
            simp only [ord]; omega⟩]
  | .prod u =>
      exact ![Sum.inr ⟨CIdx.mono u, by simp only [ord]; have := deg_le u; omega⟩,
        Sum.inr ⟨CIdx.acc u ⟨f.support.card, Nat.lt_succ_self _⟩, by
          simp only [ord]; omega⟩]
  | .total j =>
      by_cases h : j.val = 0
      · exact fun _ => Sum.inl ⟨0, hn⟩
      · exact ![Sum.inr ⟨CIdx.total ⟨j.val - 1, by have := j.isLt; omega⟩, by
            simp only [ord]; omega⟩,
          Sum.inr ⟨CIdx.prod (monoEquiv n K ⟨j.val - 1, by have := j.isLt; omega⟩), by
            simp only [ord]; omega⟩]

theorem parent_update {j : ℕ} {u : Fin j → Fin (n + 1)} (h : (npSet u).Nonempty) :
    parent u = Function.update u ((npSet u).max' h) (Fin.last n) := by
  rw [parent]; exact dif_pos h

/-- One step of the multiplicative construction of the monomials. -/
theorem eval_unitTerm_factor (x : Fin n → R) {u : MonoIdx n K} (h : (npSet u).Nonempty) :
    x ⟨(u ((npSet u).max' h)).val, mem_npSet.1 ((npSet u).max'_mem h)⟩ *
        (unitTerm R n K (parent u)).eval x = (unitTerm R n K u).eval x := by
  have hu : (u ((npSet u).max' h)).val < n := mem_npSet.1 ((npSet u).max'_mem h)
  rw [parent_update h, unitTerm_update hu, map_mul, mul_comm (x _)]
  congr 1
  simp [unitFac, hu]

theorem accVal_zero (x : Fin n → R) (u : MonoIdx n K) :
    accVal f x u ⟨0, Nat.succ_pos f.support.card⟩ = 0 := by
  simp [accVal]

theorem accVal_succ (x : Fin n → R) (u : MonoIdx n K) (k : ℕ) (hk : k < f.support.card) :
    accVal f x u (⟨k + 1, by omega⟩ : Fin (f.support.card + 1)) =
      accVal f x u (⟨k, by omega⟩ : Fin (f.support.card + 1)) + termVal f x u ⟨k, hk⟩ := by
  unfold accVal
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem totalVal_zero (x : Fin n → R) :
    totalVal f x ⟨0, Nat.succ_pos (monoCount n K)⟩ = 0 := by
  simp [totalVal]

theorem totalVal_succ (x : Fin n → R) (k : ℕ) (hk : k < monoCount n K) :
    totalVal f x (⟨k + 1, by omega⟩ : Fin (monoCount n K + 1)) =
      totalVal f x (⟨k, by omega⟩ : Fin (monoCount n K + 1)) + prodVal f x (monoEquiv n K ⟨k, hk⟩) := by
  unfold totalVal
  rw [Fin.sum_univ_castSucc]
  congr 1


/-- The gate of the DAG circuit corresponding to `i`. -/
noncomputable def cgate (j : Fin (Fintype.card (CIdx R n K f))) : RingOp R :=
  UpperOp.toRingOp (op (cEquiv.symm j))

/-- The rank of the gate `j`, so that it strictly decreases along the edges. -/
noncomputable def corder (j : Fin (Fintype.card (CIdx R n K f))) : ℕ :=
  ord (cEquiv.symm j)

/-- The arguments of the gate `j`, with the rank proof. -/
noncomputable def cargs (j : Fin (Fintype.card (CIdx R n K f))) (t : Fin ((arithBasis R).arity (cgate j))) :
    Fin n ⊕ {g : Fin (Fintype.card (CIdx R n K f)) // corder g < corder j} :=
  Sum.map id (fun g : {g : CIdx R n K f // ord g < ord (cEquiv.symm j)} =>
      ⟨cEquiv g.1, by
        show ord (cEquiv.symm (cEquiv g.1)) < ord (cEquiv.symm j)
        rw [Equiv.symm_apply_apply]
        exact g.2⟩)
    (dagArgs (hn := hn) (cEquiv.symm j) (UpperOp.projArgB (op (cEquiv.symm j)) t))

/-- The DAG circuit computing `f`, with one multiplication per monomial for the `mono` gates and
one for each `prod` gate. -/
noncomputable abbrev circuit : DagCircuit (arithBasis R) n 1 where
  size := Fintype.card (CIdx R n K f)
  gate := cgate (K := K) (f := f)
  order := corder (n := n) (K := K) (f := f)
  args := cargs (hn := hn) (K := K) (f := f)
  out _ := Sum.inr (cEquiv (.total ⟨monoCount n K, Nat.lt_succ_self _⟩))

/-- The value computed at the argument slot `s` of gate `i`, using the values of the sub-gates
(which have strictly smaller rank). -/
noncomputable def argV (x : Fin n → R) (i : CIdx R n K f) : Fin 2 → R :=
  fun s => Sum.elim (fun a => x a)
    (fun g : {g : CIdx R n K f // ord g < ord i} =>
      (circuit (hn := hn) (K := K) (f := f)).nodeValue x (cEquiv g.1))
    (dagArgs (hn := hn) i s)

/-- Reindexing the arguments by `cEquiv` does not change the values read from the wires. -/
theorem cargs_elim (x : Fin n → R) (j : Fin (Fintype.card (CIdx R n K f)))
    (t : Fin ((arithBasis R).arity (cgate (K := K) (f := f) j))) :
    Sum.elim (fun a => x a)
        (fun g : {g : Fin (Fintype.card (CIdx R n K f)) //
          corder (K := K) (f := f) g < corder (K := K) (f := f) j} =>
          (circuit (hn := hn) (K := K) (f := f)).nodeValue x g.1)
        (cargs (hn := hn) (K := K) (f := f) j t)
      = Sum.elim (fun a => x a)
          (fun g : {g : CIdx R n K f // ord g < ord (cEquiv.symm j)} =>
            (circuit (hn := hn) (K := K) (f := f)).nodeValue x (cEquiv g.1))
          (dagArgs (hn := hn) (cEquiv.symm j) (UpperOp.projArgB (op (cEquiv.symm j)) t)) := by
  cases h : dagArgs (hn := hn) (cEquiv.symm j) (UpperOp.projArgB (op (cEquiv.symm j)) t) with
  | inl a => simp [cargs, h]
  | inr g => simp [cargs, h]

/-- The value of a gate is the operation of the gate applied to the values of its arguments. -/
theorem circuit_nodeValue_unfold (x : Fin n → R) (j : Fin (Fintype.card (CIdx R n K f))) :
    (circuit (hn := hn) (K := K) (f := f)).nodeValue x j =
      UpperOp.eval (op (cEquiv.symm j))
        (argV (hn := hn) (K := K) (f := f) x (cEquiv.symm j) 0)
        (argV (hn := hn) (K := K) (f := f) x (cEquiv.symm j) 1) := by
  rw [DagCircuit.nodeValue_eq]
  rw [show (fun t => Sum.elim (fun a => x a)
        (fun g : {g : Fin (Fintype.card (CIdx R n K f)) //
          corder (K := K) (f := f) g < corder (K := K) (f := f) j} =>
            (circuit (hn := hn) (K := K) (f := f)).nodeValue x g.1)
        ((circuit (hn := hn) (K := K) (f := f)).args j t))
      = fun t => argV (hn := hn) (K := K) (f := f) x (cEquiv.symm j)
          (UpperOp.projArgB (op (cEquiv.symm j)) t) from by
    funext t
    exact cargs_elim (hn := hn) (K := K) (f := f) x j t]
  exact UpperOp.eval_toRingOp (op (cEquiv.symm j))
    (argV (hn := hn) (K := K) (f := f) x (cEquiv.symm j))








theorem accVal_congr {x : Fin n → R} {u : MonoIdx n K} {j j' : Fin (f.support.card + 1)}
    (h : j.val = j'.val) : accVal f x u j = accVal f x u j' := by
  rw [Fin.ext h]

theorem totalVal_congr {x : Fin n → R} {j j' : Fin (monoCount n K + 1)}
    (h : j.val = j'.val) : totalVal f x j = totalVal f x j' := by
  rw [Fin.ext h]

/-- The gate-by-gate verification that the circuit computes the prescribed values. -/
theorem circuit_nodeValue_spec (x : Fin n → R) (i : CIdx R n K f) :
    (circuit (hn := hn) (K := K) (f := f)).nodeValue x (cEquiv i) = spec f x i := by
  suffices h : ∀ m, ∀ i : CIdx R n K f, ord i = m →
      (circuit (hn := hn) (K := K) (f := f)).nodeValue x (cEquiv i) = spec f x i from h _ i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro i hi
    have ihg : ∀ g : {g : CIdx R n K f // ord g < ord i},
        (circuit (hn := hn) (K := K) (f := f)).nodeValue x (cEquiv g.1) = spec f x g.1 := by
      intro g
      exact ihm (ord g.1) (by have := g.2; omega) g.1 rfl
    have hunf := circuit_nodeValue_unfold (hn := hn) (K := K) (f := f) x (cEquiv i)
    rw [show cEquiv.symm (cEquiv i) = i from Equiv.symm_apply_apply cEquiv i] at hunf
    rw [hunf]
    cases i with
    | mono u =>
      by_cases hnp : (npSet u).Nonempty
      · simp only [op, if_pos hnp, dif_pos hnp, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [ihg ⟨CIdx.mono (parent u), by
          simp only [ord]; exact Nat.succ_lt_succ (deg_parent_lt hnp)⟩]
        simp only [spec]
        exact eval_unitTerm_factor x hnp
      · have h0 : npSet u = ∅ := Finset.not_nonempty_iff_eq_empty.1 hnp
        simp only [op, if_neg hnp, dif_neg hnp, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [unitTerm_eq_one_of_npSet_eq_empty (R := R) (n := n) (j := K) h0]
        simp
    | smul u j0 =>
      simp only [op, spec, argV, dagArgs, UpperOp.eval, termVal, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [ihg ⟨CIdx.mono (sndHalf f j0), by
        simp only [ord]; have := deg_le (sndHalf (K := K) f j0); omega⟩]
      simp only [spec]
    | acc u j0 =>
      by_cases hj0 : j0.val = 0
      · simp only [op, if_pos hj0, dif_pos hj0, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [accVal_congr (f := f) (x := x) (u := u) (j := j0) (j' := ⟨0, by omega⟩) (by simp [hj0])]
        exact (accVal_zero (f := f) x u).symm
      · have hk : j0.val - 1 < f.support.card := by have := j0.isLt; omega
        simp only [op, if_neg hj0, dif_neg hj0, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [ihg ⟨CIdx.acc u ⟨j0.val - 1, by have := j0.isLt; omega⟩, by simp only [ord]; omega⟩,
          ihg ⟨CIdx.smul u ⟨j0.val - 1, by have := j0.isLt; omega⟩, by simp only [ord]; omega⟩]
        simp only [spec]
        rw [accVal_congr (f := f) (x := x) (u := u) (j := j0)
          (j' := ⟨j0.val - 1 + 1, by omega⟩)
          (by simp only [Fin.val_mk]; omega)]
        exact (accVal_succ (n := n) (K := K) (f := f) x u (j0.val - 1) hk).symm
    | prod u =>
      simp only [op, spec, argV, dagArgs, UpperOp.eval, prodVal, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [ihg ⟨CIdx.mono u, by simp only [ord]; have := deg_le u; omega⟩,
        ihg ⟨CIdx.acc u ⟨f.support.card, Nat.lt_succ_self _⟩, by simp only [ord]; omega⟩]
      simp only [spec]
    | total j0 =>
      by_cases hj0 : j0.val = 0
      · simp only [op, if_pos hj0, dif_pos hj0, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [totalVal_congr (f := f) (x := x) (j := j0) (j' := ⟨0, by omega⟩) (by simp [hj0])]
        exact (totalVal_zero (f := f) x).symm
      · have hk : j0.val - 1 < monoCount n K := by have := j0.isLt; omega
        simp only [op, if_neg hj0, dif_neg hj0, spec, argV, dagArgs, UpperOp.eval,
          Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        rw [ihg ⟨CIdx.total ⟨j0.val - 1, by have := j0.isLt; omega⟩, by simp only [ord]; omega⟩,
          ihg ⟨CIdx.prod (monoEquiv n K ⟨j0.val - 1, by have := j0.isLt; omega⟩),
            by simp only [ord]; omega⟩]
        simp only [spec]
        rw [totalVal_congr (f := f) (x := x) (j := j0)
          (j' := ⟨j0.val - 1 + 1, by omega⟩)
          (by simp only [Fin.val_mk]; omega)]
        exact (totalVal_succ (n := n) (K := K) (f := f) x (j0.val - 1) hk).symm



/-! ### The polynomial identity `∑ᵤ Pᵤ · Qᵤ = f` -/

/-- An enumeration of the support of `f` by `Fin f.support.card`, refining `suppAt`. -/
noncomputable def suppEquiv (f : MvPolynomial (Fin n) R) : Fin f.support.card ≃ ↥f.support :=
  (finCongr (Fintype.card_coe f.support).symm).trans (Fintype.equivFin ↥f.support).symm

theorem suppEquiv_apply (f : MvPolynomial (Fin n) R) (j : Fin f.support.card) :
    ((suppEquiv f j : ↥f.support) : Fin n →₀ ℕ) = suppAt f j := rfl

/-- The product of the two halves of a monomial is the monomial. -/
theorem unitTerm_split (m : Fin n → ℕ) (K : ℕ) (h : ∑ i, m i ≤ 2 * K) :
    unitTerm R n K (splitPair m K).1 * unitTerm R n K (splitPair m K).2
      = ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ m i := by
  rw [unitTerm_eq_prod_pow (R := R) (n := n) K (splitPair m K).1,
    unitTerm_eq_prod_pow (R := R) (n := n) K (splitPair m K).2,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  rw [← Pi.add_apply, expo_splitPair m K h]

/-- The product of the two halves of a monomial, evaluated. -/
theorem eval_mul_unitTerm_split (m : Fin n → ℕ) (K : ℕ) (h : ∑ i, m i ≤ 2 * K)
    (x : Fin n → R) :
    (unitTerm R n K (splitPair m K).1).eval x * (unitTerm R n K (splitPair m K).2).eval x
      = ∏ i : Fin n, x i ^ m i := by
  rw [← map_mul, unitTerm_split m K h]
  simp

/-- The product of the two halves of the monomial of `f` at `j`, evaluated. -/
theorem eval_mul_halves (x : Fin n → R) (j : Fin f.support.card)
    (h : ∑ i, (suppAt f j) i ≤ 2 * K) :
    (unitTerm R n K (fstHalf f j)).eval x * (unitTerm R n K (sndHalf f j)).eval x
      = ∏ i : Fin n, x i ^ (suppAt f j) i := by
  have := eval_mul_unitTerm_split (fun i => suppAt f j i) K h x
  simpa [fstHalf, sndHalf] using this

/-- The full linear combination `Qᵤ`. -/
theorem accVal_full (x : Fin n → R) (u : MonoIdx n K) :
    accVal f x u ⟨f.support.card, Nat.lt_succ_self _⟩
      = ∑ j : Fin f.support.card, termVal f x u j := by
  simp [accVal]

/-- The final sum is a sum over all monomials. -/
theorem totalVal_last (x : Fin n → R) :
    totalVal f x ⟨monoCount n K, Nat.lt_succ_self _⟩
      = ∑ u : MonoIdx n K, prodVal f x u := by
  have hlast : totalVal f x ⟨monoCount n K, Nat.lt_succ_self _⟩
      = ∑ t : Fin (monoCount n K), prodVal f x (monoEquiv n K t) := by
    simp [totalVal]
  rw [hlast]
  exact Equiv.sum_comp (monoEquiv n K) (fun u => prodVal f x u)

/-- The circuit computes `f`: the final sum is `f` evaluated at `x`. -/
theorem totalVal_spec (x : Fin n → R) (hdeg : ∀ m ∈ f.support, ∑ i, m i ≤ 2 * K) :
    totalVal f x ⟨monoCount n K, Nat.lt_succ_self _⟩ = f.eval x := by
  rw [totalVal_last]
  have step1 : ∀ u : MonoIdx n K, prodVal f x u
      = ∑ j : Fin f.support.card, (unitTerm R n K u).eval x * termVal f x u j := by
    intro u
    rw [prodVal, accVal_full, Finset.mul_sum]
  simp only [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ j : Fin f.support.card,
      (∑ u : MonoIdx n K, (unitTerm R n K u).eval x * termVal f x u j)
        = f.coeff (suppAt f j) * ∏ i : Fin n, x i ^ (suppAt f j) i := by
    intro j
    rw [Finset.sum_eq_single (fstHalf f j)]
    · rw [show termVal f x (fstHalf f j) j
          = f.coeff (suppAt f j) * (unitTerm R n K (sndHalf f j)).eval x from by
        simp [termVal, coeffUV]]
      rw [← eval_mul_halves (K := K) x j (hdeg _ (suppAt_mem f j))]
      ring
    · intro u _ hne
      rw [show (unitTerm R n K u).eval x * termVal f x u j = 0 from by
        rw [termVal, coeffUV, if_neg (Ne.symm hne), zero_mul, mul_zero]]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  simp only [step2]
  rw [MvPolynomial.eval_eq']
  conv_rhs => rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (suppEquiv f) _ _ (fun j => rfl)

/-! ### The number of nonscalar multiplications -/

/-- Only the `mono` and `prod` gates can be nonscalar multiplications. -/
theorem isMul_op_smul (u : MonoIdx n K) (j : Fin f.support.card) :
    UpperOp.isMul (op (CIdx.smul u j)) = false := rfl

theorem isMul_op_acc (u : MonoIdx n K) (j : Fin (f.support.card + 1)) :
    UpperOp.isMul (op (CIdx.acc u j)) = false := by
  simp only [op]
  split_ifs <;> rfl

theorem isMul_op_prod (u : MonoIdx n K) :
    UpperOp.isMul (op (CIdx.prod u : CIdx R n K f)) = true := rfl

theorem isMul_op_total (j : Fin (monoCount n K + 1)) :
    UpperOp.isMul (op (CIdx.total j : CIdx R n K f)) = false := by
  simp only [op]
  split_ifs <;> rfl

/-- A nonscalar multiplication gate of the circuit is either a `mono` gate or a `prod` gate. -/
theorem isMul_op_cases (i : CIdx R n K f) (hi : UpperOp.isMul (op i) = true) :
    (∃ u, i = CIdx.mono u) ∨ (∃ u, i = CIdx.prod u) := by
  match i with
  | .mono u => exact Or.inl ⟨u, rfl⟩
  | .prod u => exact Or.inr ⟨u, rfl⟩
  | .smul u j => exact absurd hi (by rw [isMul_op_smul]; simp)
  | .acc u j => exact absurd hi (by rw [isMul_op_acc]; simp)
  | .total j => exact absurd hi (by rw [isMul_op_total]; simp)

/-- The monomials of the `mono` and `prod` gates carrying a nonscalar multiplication. -/
noncomputable def mulGateMap (q : {i : CIdx R n K f // UpperOp.isMul (op i) = true}) :
    MonoIdx n K ⊕ MonoIdx n K :=
  match q.1 with
  | .mono u => Sum.inl u
  | .prod u => Sum.inr u
  | .smul u _ => Sum.inl u
  | .acc u _ => Sum.inl u
  | .total _ => Sum.inl fun _ => Fin.last n

theorem mulGateMap_injective : Function.Injective (mulGateMap (n := n) (K := K) (f := f)) := by
  rintro ⟨i, hi⟩ ⟨i', hi'⟩ hab
  rcases isMul_op_cases i hi with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases isMul_op_cases i' hi' with ⟨u', rfl⟩ | ⟨u', rfl⟩
    · simp only [mulGateMap, Sum.inl.injEq] at hab
      subst hab
      rfl
    · exact absurd hab (by simp [mulGateMap])
  · rcases isMul_op_cases i' hi' with ⟨u', rfl⟩ | ⟨u', rfl⟩
    · exact absurd hab (by simp [mulGateMap])
    · simp only [mulGateMap, Sum.inr.injEq] at hab
      subst hab
      rfl

/-- The nonscalar multiplication gates of the circuit, reindexed by `CIdx`. -/
noncomputable def mulGateEquiv :
    {j : Fin (Fintype.card (CIdx R n K f)) //
      RingOp.isMul ((circuit (hn := hn) (K := K) (f := f)).gate j) = true}
      ≃ {i : CIdx R n K f // UpperOp.isMul (op i) = true} where
  toFun q := ⟨cEquiv.symm q.1, by
    show UpperOp.isMul (op (cEquiv.symm q.1)) = true
    rw [← UpperOp.isMul_toRingOp]
    exact q.2⟩
  invFun q := ⟨cEquiv q.1, by
    show RingOp.isMul ((circuit (hn := hn) (K := K) (f := f)).gate (cEquiv q.1)) = true
    rw [show (circuit (hn := hn) (K := K) (f := f)).gate (cEquiv q.1)
        = UpperOp.toRingOp (op (cEquiv.symm (cEquiv q.1))) from rfl,
      UpperOp.isMul_toRingOp, Equiv.symm_apply_apply]
    exact q.2⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp

/-- The circuit has at most one nonscalar multiplication per monomial for the `mono` gates and one
per `prod` gate, hence at most `2 · |P_{K,n}|`. -/
theorem circuit_mulCount_le :
    dagMulComplexity (circuit (hn := hn) (K := K) (f := f)) ≤ 2 * monoCount n K := by
  calc dagMulComplexity (circuit (hn := hn) (K := K) (f := f))
      = Fintype.card {j : Fin (Fintype.card (CIdx R n K f)) //
          RingOp.isMul ((circuit (hn := hn) (K := K) (f := f)).gate j) = true} := by
        simp only [dagMulComplexity, DagCircuit.countGates]
        exact (Fintype.card_subtype _).symm
    _ = Fintype.card {i : CIdx R n K f // UpperOp.isMul (op i) = true} :=
        Fintype.card_congr (mulGateEquiv (hn := hn) (K := K) (f := f))
    _ ≤ Fintype.card (MonoIdx n K ⊕ MonoIdx n K) :=
        Fintype.card_le_of_injective _ (mulGateMap_injective (n := n) (K := K) (f := f))
    _ = monoCount n K + monoCount n K := by rw [Fintype.card_sum]; rfl
    _ = 2 * monoCount n K := by ring



/-! ### The upper bound for `polyMu` and `classMu` -/

/-- The circuit computes `f`, provided every monomial of `f` splits into two halves of degree at
most `K`. -/
theorem circuit_eval (hn : 0 < n) (hdeg : ∀ m ∈ f.support, ∑ i, m i ≤ 2 * K) (x : Fin n → R) :
    (circuit (hn := hn) (K := K) (f := f)).eval x = fun _ => f.eval x := by
  funext o
  have hout : (circuit (hn := hn) (K := K) (f := f)).out o
      = Sum.inr (cEquiv (CIdx.total ⟨monoCount n K, Nat.lt_succ_self _⟩)) := rfl
  rw [DagCircuit.eval, hout]
  show (circuit (hn := hn) (K := K) (f := f)).nodeValue x
      (cEquiv (CIdx.total ⟨monoCount n K, Nat.lt_succ_self _⟩)) = f.eval x
  rw [circuit_nodeValue_spec]
  exact totalVal_spec x hdeg

/-- `μ(f) ≤ 2 · (n + 1) ^ K` for every polynomial whose monomials split into two halves of degree
at most `K`. -/
theorem polyMu_le (hn : 0 < n) (hdeg : ∀ m ∈ f.support, ∑ i, m i ≤ 2 * K) :
    polyMu f ≤ 2 * monoCount n K := by
  have himp : (circuit (hn := hn) (K := K) (f := f)).toSLP.Implements
      (fun x (_ : Fin 1) => f.eval x) := by
    rw [Circuit.implements_iff]
    intro x
    rw [DagCircuit.toSLP_eval]
    exact circuit_eval hn hdeg x
  have hμ : mulComplexity ((circuit (hn := hn) (K := K) (f := f)).toSLP) ≤ 2 * monoCount n K := by
    rw [dagMulComplexity_toSLP]
    exact circuit_mulCount_le (hn := hn) (K := K) (f := f)
  exact (mulComplexityOf_le himp).trans hμ

/-- `μ(f) ≤ 2 · (n + 1) ^ ⌈d / 2⌉` for every polynomial of total degree at most `d`. -/
theorem polyMu_le_of_totalDegree (hn : 0 < n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.totalDegree ≤ d) : polyMu f ≤ 2 * (n + 1) ^ ((d + 1) / 2) := by
  have hdeg : ∀ m ∈ f.support, ∑ i, m i ≤ 2 * ((d + 1) / 2) := by
    intro m hm
    have h1 : (m.sum fun _ e => e) ≤ f.totalDegree := MvPolynomial.le_totalDegree hm
    have h2 : (m.sum fun _ e => e) = ∑ i : Fin n, m i := by
      rw [Finsupp.sum_fintype]; intro i; rfl
    have h3 : d ≤ 2 * ((d + 1) / 2) := by omega
    omega
  have h := polyMu_le hn (K := (d + 1) / 2) (f := f) hdeg
  rwa [monoCount_eq] at h

/-- The upper bound `μ(M_{d,n}) ≤ 2 · (n + 1) ^ ⌈d / 2⌉` of Theorem 1. -/
theorem classMu_le_upper (hn : 0 < n) (d : ℕ) :
    classMu (R := R) d n ≤ 2 * (n + 1) ^ ((d + 1) / 2) := by
  refine classMu_le fun f => ?_
  exact polyMu_le_of_totalDegree hn d f.1 f.2


end Circuit


/-! ### The case of no variables, and the asymptotic form -/

/-- The constant circuit with no inputs. -/
noncomputable def constCirc0 (R : Type u) [CommRing R] (a : R) : Circuit (arithBasis R) 0 1 where
  size := 1
  gate _ := RingOp.const a
  args _ t := t.elim0
  out _ := Sum.inr ⟨0, Nat.one_pos⟩

theorem constCirc0_eval (R : Type u) [CommRing R] (a : R) (x : Fin 0 → R) :
    (constCirc0 R a).eval x 0 = a := by
  rw [Circuit.eval]
  show (constCirc0 R a).nodeValue x ⟨0, Nat.one_pos⟩ = a
  rw [Circuit.nodeValue_eq]
  rfl

theorem constCirc0_mulComplexity (R : Type u) [CommRing R] (a : R) :
    mulComplexity (constCirc0 R a) = 0 := by
  simp [mulComplexity, Circuit.countGates, constCirc0, RingOp.isMul]

/-- In no variables every polynomial is a constant, so its multiplicative complexity is `0`. -/
theorem polyMu_zero_var (f : MvPolynomial (Fin 0) R) : polyMu f ≤ 0 := by
  rw [MvPolynomial.eq_C_of_isEmpty f]
  have himp : (constCirc0 R (f.coeff 0)).Implements
      (fun x (_ : Fin 1) => ((MvPolynomial.C (f.coeff 0)) : MvPolynomial (Fin 0) R).eval x) := by
    rw [Circuit.implements_iff]
    intro x
    funext o
    rw [Subsingleton.elim o 0, constCirc0_eval, MvPolynomial.eval_C]
  have hμ : mulComplexity (constCirc0 R (f.coeff 0)) ≤ 0 := by
    rw [constCirc0_mulComplexity]
  exact (mulComplexityOf_le himp).trans hμ

/-- The upper bound in the degenerate case of no variables. -/
theorem classMu_zero (d : ℕ) : classMu (R := R) d 0 ≤ 2 := by
  have h : classMu (R := R) d 0 ≤ 0 := by
    refine classMu_le fun f => ?_
    exact polyMu_zero_var (R := R) f.1
  omega

/-- The upper bound `μ(M_{d,n}) ≤ 2 · (n + 1) ^ ⌈d / 2⌉` of Theorem 1, in all cases. -/
theorem classMu_le_upper' (d n : ℕ) :
    classMu (R := R) d n ≤ 2 * (n + 1) ^ ((d + 1) / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := classMu_zero (R := R) d
    simpa using this
  · exact classMu_le_upper hn d

/-- Theorem 1, upper bound: `μ(M_{d,n}) ≼ n ^ ⌈d / 2⌉` for a constant `d`. -/
theorem classMu_isBigO (d : ℕ) :
    (fun n : ℕ => (classMu (R := R) d n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => ((n : ℝ)) ^ ((d + 1) / 2)) := by
  refine Asymptotics.IsBigO.of_bound ((2 : ℝ) * 2 ^ ((d + 1) / 2)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn1
  have hn1' : (0:ℕ) < n := hn1
  have h1 : classMu (R := R) d n ≤ 2 * (n + 1) ^ ((d + 1) / 2) := classMu_le_upper' d n
  have h2 : (n + 1) ^ ((d + 1) / 2) ≤ (2 * n) ^ ((d + 1) / 2) := by
    refine Nat.pow_le_pow_left (by omega) _
  have h3 : (2 * n) ^ ((d + 1) / 2) = 2 ^ ((d + 1) / 2) * n ^ ((d + 1) / 2) := by
    rw [mul_pow]
  have hclass : ((classMu (R := R) d n : ℕ) : ℝ) ≤
      (2 * (n + 1) ^ ((d + 1) / 2) : ℕ) := by exact_mod_cast h1
  have hmono : ((2 * (n + 1) ^ ((d + 1) / 2) : ℕ) : ℝ) ≤
      (2 * (2 * n) ^ ((d + 1) / 2) : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 h2
  have hsplit : ((2 * (2 * n) ^ ((d + 1) / 2) : ℕ) : ℝ)
      = 2 * (2 ^ ((d + 1) / 2) * (n : ℝ) ^ ((d + 1) / 2)) := by
    rw [h3]
    push_cast
    ring
  have hnn : (0:ℝ) ≤ ((classMu (R := R) d n : ℕ) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ)) ^ ((d + 1) / 2))]
  calc ((classMu (R := R) d n : ℕ) : ℝ)
      ≤ (2 * (2 * n) ^ ((d + 1) / 2) : ℕ) := hclass.trans hmono
    _ = 2 * (2 ^ ((d + 1) / 2) * (n : ℝ) ^ ((d + 1) / 2)) := hsplit
    _ = 2 * 2 ^ ((d + 1) / 2) * (n : ℝ) ^ ((d + 1) / 2) := by ring

end Monomials

variable {R : Type u} [CommRing R] {n : ℕ}

open MvPolynomial

def SameBlock (i j : Fin n) : Prop := decide (i.val < n / 2) = decide (j.val < n / 2)

theorem sameBlock_refl (i : Fin n) : SameBlock i i := rfl
theorem sameBlock_symm {i j : Fin n} (h : SameBlock i j) : SameBlock j i := h.symm

abbrev PairIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2 ∧ SameBlock p.1 p.2}

instance : DecidablePred (fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ SameBlock p.1 p.2) := by
  intro p
  unfold SameBlock
  infer_instance

instance : Fintype (PairIdx n) := by
  dsimp [PairIdx]
  infer_instance

instance : DecidableEq (PairIdx n) := by
  dsimp [PairIdx]
  infer_instance

noncomputable def mkPair (i j : Fin n) (h : SameBlock i j) : PairIdx n :=
  if hij : i ≤ j then ⟨(i, j), hij, h⟩ else ⟨(j, i), le_of_not_ge hij, h.symm⟩

noncomputable def pairExp (p : PairIdx n) : Fin n →₀ ℕ :=
  Finsupp.single p.1.1 1 + Finsupp.single p.1.2 1

inductive Term (n : ℕ)
  | one
  | var (i : Fin n)
  | pair (p : PairIdx n)
  deriving DecidableEq, Fintype

noncomputable def termExp : Term n → Fin n →₀ ℕ
  | .one => 0
  | .var i => Finsupp.single i 1
  | .pair p => pairExp p

noncomputable def termPoly (t : Term n) : MvPolynomial (Fin n) R :=
  MvPolynomial.monomial (termExp t) 1

def HasRep (m : Fin n →₀ ℕ) : Prop := ∃ (l : Fin n) (t : Term n), m = termExp t + Finsupp.single l 1

lemma exists_rep_default (hn : 0 < n) (m : Fin n →₀ ℕ) :
    ∃ r : Fin n × Term n, HasRep (n := n) m → m = termExp r.2 + Finsupp.single r.1 1 := by
  classical
  by_cases h : HasRep (n := n) m
  · obtain ⟨l, t, ht⟩ := h
    exact ⟨(l, t), fun _ => ht⟩
  · exact ⟨(⟨0, hn⟩, .one), fun hh => absurd hh h⟩

noncomputable def rep (hn : 0 < n) (m : Fin n →₀ ℕ) : Fin n × Term n :=
  Classical.choose (exists_rep_default hn m)

noncomputable def repL (hn : 0 < n) (m : Fin n →₀ ℕ) : Fin n := (rep hn m).1
noncomputable def repT (hn : 0 < n) (m : Fin n →₀ ℕ) : Term n := (rep hn m).2

theorem rep_spec (hn : 0 < n) {m : Fin n →₀ ℕ} (h : HasRep (n := n) m) :
    m = termExp (repT hn m) + Finsupp.single (repL hn m) 1 :=
  Classical.choose_spec (exists_rep_default hn m) h



lemma single_two (a : Fin n) : (Finsupp.single a 2 : Fin n →₀ ℕ) = Finsupp.single a 1 + Finsupp.single a 1 := by
  rw [← Finsupp.single_add]

lemma single_three (a : Fin n) :
    (Finsupp.single a 3 : Fin n →₀ ℕ) = (Finsupp.single a 1 + Finsupp.single a 1) + Finsupp.single a 1 := by
  rw [← Finsupp.single_add, ← Finsupp.single_add]

lemma hasRep_card_one {m : Fin n →₀ ℕ} (hs : m.support.card = 1)
    (hdeg : m.sum (fun _ e => e) ≤ 3) : HasRep m := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hs
  have hm_eq : m = Finsupp.single a (m a) := (Finsupp.support_eq_singleton.mp ha).2
  have ha_pos : 0 < m a := by
    have : a ∈ m.support := by rw [ha]; simp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp this)
  have hdeg' : m a ≤ 3 := by
    have h : m.sum (fun _ e => e) = m a := by rw [hm_eq]; simp
    omega
  interval_cases m a
  · exact ⟨a, .one, by rw [hm_eq]; simp [termExp]⟩
  · refine ⟨a, .var a, ?_⟩
    rw [hm_eq]
    simpa [termExp] using single_two a
  · refine ⟨a, .pair (mkPair a a (sameBlock_refl a)), ?_⟩
    rw [hm_eq]
    simpa [termExp, pairExp, mkPair] using single_three a

lemma hasRep_card_two {m : Fin n →₀ ℕ} (hs : m.support.card = 2)
    (hdeg : m.sum (fun _ e => e) ≤ 3) : HasRep m := by
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hs
  have hm_eq : m = Finsupp.single a (m a) + Finsupp.single b (m b) := by
    have h := Finsupp.sum_single m
    rw [Finsupp.sum, hsupp, Finset.sum_pair hab] at h
    exact h.symm
  have ha_pos : 0 < m a := by
    have : a ∈ m.support := by rw [hsupp]; simp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp this)
  have hb_pos : 0 < m b := by
    have : b ∈ m.support := by rw [hsupp]; simp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp this)
  have hdeg' : m a + m b ≤ 3 := by
    have h : m.sum (fun _ e => e) = m a + m b := by
      rw [Finsupp.sum, hsupp, Finset.sum_pair hab]
    omega
  have ha12 : m a = 1 ∨ m a = 2 := by omega
  have hb12 : m b = 1 ∨ m b = 2 := by omega
  rcases ha12 with ha1 | ha2 <;> rcases hb12 with hb1 | hb2
  · refine ⟨a, .var b, ?_⟩
    rw [hm_eq, ha1, hb1]
    simp [termExp, add_comm]
  · refine ⟨a, .pair (mkPair b b (sameBlock_refl b)), ?_⟩
    rw [hm_eq, ha1, hb2]
    simp [termExp, pairExp, mkPair, single_two, add_assoc, add_comm, add_left_comm]
  · refine ⟨b, .pair (mkPair a a (sameBlock_refl a)), ?_⟩
    rw [hm_eq, ha2, hb1]
    simp [termExp, pairExp, mkPair, single_two, add_assoc, add_comm, add_left_comm]
  · omega


lemma exists_sameBlock_pair_of_card_three {m : Fin n →₀ ℕ} (hs : m.support.card = 3) :
    ∃ i ∈ m.support, ∃ j ∈ m.support, i ≠ j ∧ SameBlock i j := by
  have hcard : (Finset.univ : Finset Bool).card < m.support.card := by simp [hs]
  have hmaps : Set.MapsTo (fun i : Fin n => decide (i.val < n / 2)) ↑m.support
      ↑(Finset.univ : Finset Bool) := by
    intro i hi
    simp
    omega
  obtain ⟨i, hi, j, hj, hij, hbij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨i, hi, j, hj, hij, hbij⟩

lemma hasRep_card_three {m : Fin n →₀ ℕ} (hs : m.support.card = 3)
    (hdeg : m.sum (fun _ e => e) ≤ 3) : HasRep m := by
  obtain ⟨i, hi, j, hj, hij, hsame⟩ := exists_sameBlock_pair_of_card_three (n := n) hs
  have hcard_i : (m.support.erase i).card = 2 := by
    rw [Finset.card_erase_of_mem hi, hs]
  have hj' : j ∈ m.support.erase i := by
    rw [Finset.mem_erase]
    exact ⟨hij.symm, hj⟩
  have hcard_ij : ((m.support.erase i).erase j).card = 1 := by
    rw [Finset.card_erase_of_mem hj', hcard_i]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard_ij
  have hk_mem : k ∈ (m.support.erase i).erase j := by rw [hk]; simp
  have hkj : k ≠ j := (Finset.mem_erase.mp hk_mem).1
  have hk_i_mem : k ∈ m.support.erase i := (Finset.mem_erase.mp hk_mem).2
  have hki : k ≠ i := (Finset.mem_erase.mp hk_i_mem).1
  have hk_mem_s : k ∈ m.support := (Finset.mem_erase.mp hk_i_mem).2
  have hsupp : m.support = {i, j, k} := by
    rw [← Finset.insert_erase hi, ← Finset.insert_erase hj', hk]
  have hsum : m.sum (fun _ e => e) = m i + m j + m k := by
    rw [Finsupp.sum, hsupp]
    rw [Finset.sum_insert (by simp [hij, hki.symm]),
      Finset.sum_insert (by simp [hkj.symm]), Finset.sum_singleton]
    ring
  have hi_pos : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
  have hj_pos : 0 < m j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
  have hk_pos : 0 < m k := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk_mem_s)
  have hi1 : m i = 1 := by omega
  have hj1 : m j = 1 := by omega
  have hk1 : m k = 1 := by omega
  have hm_eq : m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 := by
    have h := Finsupp.sum_single m
    rw [Finsupp.sum, hsupp] at h
    rw [Finset.sum_insert (by simp [hij, hki.symm]),
      Finset.sum_insert (by simp [hkj.symm]), Finset.sum_singleton] at h
    rw [hi1, hj1, hk1] at h
    simpa [add_assoc] using h.symm
  refine ⟨k, .pair (mkPair i j hsame), ?_⟩
  rw [hm_eq]
  by_cases hij' : i ≤ j <;>
    simp [termExp, pairExp, mkPair, hij', add_assoc, add_comm, add_left_comm]

lemma hasRep_of_ne_zero {m : Fin n →₀ ℕ} (hm0 : m ≠ 0)
    (hdeg : m.sum (fun _ e => e) ≤ 3) : HasRep m := by
  have hne : m.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hm0 (Finsupp.support_eq_empty.mp h)
  have hpos : 0 < m.support.card := Finset.card_pos.mpr hne
  have hcardle : m.support.card ≤ 3 := by
    rw [Finset.card_eq_sum_ones]
    calc (∑ x ∈ m.support, 1) ≤ ∑ x ∈ m.support, m x := by
          apply Finset.sum_le_sum
          intro i hi
          have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
          omega
      _ = m.sum (fun _ e => e) := rfl
      _ ≤ 3 := hdeg
  have hc : m.support.card = 1 ∨ m.support.card = 2 ∨ m.support.card = 3 := by omega
  rcases hc with h1 | h2 | h3
  · exact hasRep_card_one h1 hdeg
  · exact hasRep_card_two h2 hdeg
  · exact hasRep_card_three h3 hdeg

lemma monomial_rep (hn : 0 < n) {m : Fin n →₀ ℕ} (hm0 : m ≠ 0)
    (hdeg : m.sum (fun _ e => e) ≤ 3) (c : R) :
    MvPolynomial.monomial m c =
      MvPolynomial.C c * (termPoly (repT hn m) * MvPolynomial.X (repL hn m)) := by
  conv_lhs => rw [rep_spec hn (hasRep_of_ne_zero hm0 hdeg)]
  simp only [termPoly, MvPolynomial.X]
  rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.C_mul_monomial]
  simp

noncomputable def coeffQ (hn : 0 < n) (f : MvPolynomial (Fin n) R) (l : Fin n) (t : Term n) : R :=
  ∑ m ∈ f.support.filter (fun m => m ≠ 0 ∧ repL hn m = l ∧ repT hn m = t), f.coeff m

noncomputable def cubicRHS (hn : 0 < n) (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  MvPolynomial.C (f.coeff 0) +
    ∑ l : Fin n, MvPolynomial.X l *
      (∑ t : Term n, MvPolynomial.C (coeffQ hn f l t) * termPoly t)

lemma cubicRHS_eq_sum (hn : 0 < n) (f : MvPolynomial (Fin n) R) :
    cubicRHS hn f = MvPolynomial.C (f.coeff 0) +
      ∑ p : Fin n × Term n,
        MvPolynomial.C (coeffQ hn f p.1 p.2) * (termPoly p.2 * MvPolynomial.X p.1) := by
  unfold cubicRHS
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  simp only [Prod.fst, Prod.snd]
  ring

lemma sum_erase_eq (hn : 0 < n) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ 3) :
    ∑ m ∈ f.support.erase 0, MvPolynomial.monomial m (f.coeff m)
      = ∑ p : Fin n × Term n,
          MvPolynomial.C (coeffQ hn f p.1 p.2) * (termPoly p.2 * MvPolynomial.X p.1) := by
  rw [← Finset.sum_fiberwise (f.support.erase 0)
    (fun m => (repL hn m, repT hn m))
    (fun m => MvPolynomial.monomial m (f.coeff m))]
  refine Finset.sum_congr rfl ?_
  rintro ⟨l, t⟩ _
  have hfilter : (f.support.erase 0).filter (fun m => (repL hn m, repT hn m) = (l, t))
      = f.support.filter (fun m => m ≠ 0 ∧ repL hn m = l ∧ repT hn m = t) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, Prod.mk.injEq]
    tauto
  rw [hfilter]
  calc ∑ m ∈ f.support.filter (fun m => m ≠ 0 ∧ repL hn m = l ∧ repT hn m = t),
        MvPolynomial.monomial m (f.coeff m)
      = ∑ m ∈ f.support.filter (fun m => m ≠ 0 ∧ repL hn m = l ∧ repT hn m = t),
          MvPolynomial.C (f.coeff m) * (termPoly t * MvPolynomial.X l) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        have hm0 : m ≠ 0 := (Finset.mem_filter.mp hm).2.1
        have hms : m ∈ f.support := (Finset.mem_filter.mp hm).1
        have hdegm : m.sum (fun _ e => e) ≤ 3 := by
          have h1 := MvPolynomial.le_totalDegree hms
          omega
        have hmrep := (Finset.mem_filter.mp hm).2
        have hl : repL hn m = l := hmrep.2.1
        have ht : repT hn m = t := hmrep.2.2
        simpa [hl, ht] using monomial_rep hn hm0 hdegm (f.coeff m)
    _ = (∑ m ∈ f.support.filter (fun m => m ≠ 0 ∧ repL hn m = l ∧ repT hn m = t),
          MvPolynomial.C (f.coeff m)) * (termPoly t * MvPolynomial.X l) := by
        rw [Finset.sum_mul]
    _ = MvPolynomial.C (coeffQ hn f l t) * (termPoly t * MvPolynomial.X l) := by
        rw [← map_sum]
        rfl

lemma cubic_decomp (hn : 0 < n) (f : MvPolynomial (Fin n) R) (hf : f.totalDegree ≤ 3) :
    f = cubicRHS hn f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [cubicRHS_eq_sum]
  by_cases h0 : 0 ∈ f.support
  · rw [← Finset.sum_erase_add _ _ h0]
    change (∑ m ∈ f.support.erase 0, MvPolynomial.monomial m (f.coeff m)) +
        MvPolynomial.C (f.coeff 0) = _
    rw [sum_erase_eq hn f hf]
    abel
  · have hc0 : f.coeff 0 = 0 := by
      by_contra h
      exact h0 (by simpa [MvPolynomial.mem_support_iff] using h)
    have hg0 : (fun m => MvPolynomial.monomial m (f.coeff m)) 0 = 0 := by
      simp [hc0]
    rw [← Finset.sum_erase (s := f.support) hg0]
    rw [sum_erase_eq hn f hf]
    simp [hc0]

section Circuit

variable (hn : 0 < n) {f : MvPolynomial (Fin n) R}

noncomputable def termEquiv : Fin (Fintype.card (Term n)) ≃ Term n :=
  (Fintype.equivFin (Term n)).symm

/-- The gates of the cubic circuit. -/
inductive CubicIdx (R : Type u) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n) R) : Type u
  | mono (p : PairIdx n)
  | smul (l : Fin n) (t : Term n)
  | acc (l : Fin n) (j : Fin (Fintype.card (Term n) + 1))
  | prod (l : Fin n)
  | cstOne
  | cst
  | total (j : Fin (n + 1))

abbrev CubicIdxSum (R : Type u) [CommRing R] (n : ℕ) (f : MvPolynomial (Fin n) R) : Type :=
  PairIdx n ⊕ ((Fin n × Term n) ⊕ ((Fin n × Fin (Fintype.card (Term n) + 1)) ⊕
    (Fin n ⊕ (Unit ⊕ (Unit ⊕ Fin (n + 1))))))

noncomputable def cubicIdxEquiv : CubicIdx R n f ≃ CubicIdxSum R n f where
  toFun
    | .mono p => Sum.inl p
    | .smul l t => Sum.inr (Sum.inl (l, t))
    | .acc l j => Sum.inr (Sum.inr (Sum.inl (l, j)))
    | .prod l => Sum.inr (Sum.inr (Sum.inr (Sum.inl l)))
    | .cstOne => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
    | .cst => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
    | .total j => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j)))))
  invFun
    | Sum.inl p => .mono p
    | Sum.inr (Sum.inl (l, t)) => .smul l t
    | Sum.inr (Sum.inr (Sum.inl (l, j))) => .acc l j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl l))) => .prod l
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) => .cstOne
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) => .cst
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))) => .total j
  left_inv i := by cases i <;> rfl
  right_inv s := by
    rcases s with (p | ⟨l,t⟩ | ⟨l,j⟩ | l | ⟨⟩ | ⟨⟩ | j) <;> rfl

noncomputable instance : Fintype (CubicIdx R n f) :=
  Fintype.ofEquiv _ (cubicIdxEquiv (R := R) (n := n) (f := f)).symm

noncomputable def cubicEquiv : CubicIdx R n f ≃ Fin (Fintype.card (CubicIdx R n f)) :=
  Fintype.equivFin _

/-- The value accumulated in `Q_l` after the first `j` terms. -/
noncomputable def cubicAccVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (l : Fin n) (j : Fin (Fintype.card (Term n) + 1)) : R :=
  ∑ i : Fin j.val,
    coeffQ hn f l (termEquiv (n := n) ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩) *
      (termPoly (termEquiv (n := n) ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩)).eval x

/-- The product `x_l * Q_l`. -/
noncomputable def cubicProdVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (l : Fin n) : R :=
  x l * cubicAccVal hn f x l ⟨Fintype.card (Term n), Nat.lt_succ_self _⟩

/-- The final sum of the `n` products, starting from the constant term. -/
noncomputable def cubicTotalVal (f : MvPolynomial (Fin n) R) (x : Fin n → R) (j : Fin (n + 1)) : R :=
  (∑ i : Fin j.val, cubicProdVal hn f x ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩) +
    f.coeff 0

theorem cubicAccVal_congr {x : Fin n → R} {l : Fin n} {j j' : Fin (Fintype.card (Term n) + 1)}
    (h : j.val = j'.val) : cubicAccVal hn f x l j = cubicAccVal hn f x l j' := by
  rw [Fin.ext h]

theorem cubicAccVal_zero (x : Fin n → R) (l : Fin n) :
    cubicAccVal hn f x l ⟨0, Nat.succ_pos _⟩ = 0 := by
  simp [cubicAccVal]

theorem cubicAccVal_succ (x : Fin n → R) (l : Fin n) (k : ℕ) (hk : k < Fintype.card (Term n)) :
    cubicAccVal hn f x l ⟨k + 1, by omega⟩ =
      cubicAccVal hn f x l ⟨k, by omega⟩ +
        coeffQ hn f l (termEquiv (n := n) ⟨k, hk⟩) *
          (termPoly (termEquiv (n := n) ⟨k, hk⟩)).eval x := by
  unfold cubicAccVal
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem cubicTotalVal_congr {x : Fin n → R} {j j' : Fin (n + 1)}
    (h : j.val = j'.val) : cubicTotalVal hn f x j = cubicTotalVal hn f x j' := by
  rw [Fin.ext h]

theorem cubicTotalVal_zero (x : Fin n → R) :
    cubicTotalVal hn f x ⟨0, Nat.succ_pos _⟩ = f.coeff 0 := by
  simp [cubicTotalVal]

theorem cubicTotalVal_succ (x : Fin n → R) (k : ℕ) (hk : k < n) :
    cubicTotalVal hn f x ⟨k + 1, by omega⟩ =
      cubicTotalVal hn f x ⟨k, by omega⟩ + cubicProdVal hn f x ⟨k, hk⟩ := by
  unfold cubicTotalVal
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc]
  abel

/-- The operation of a gate. -/
noncomputable def cubicOp : CubicIdx R n f → UpperOp R
  | .mono _ => UpperOp.mul
  | .smul l t => UpperOp.smul (coeffQ hn f l t)
  | .acc _ j => if j.val = 0 then UpperOp.const 0 else UpperOp.add
  | .prod _ => UpperOp.mul
  | .cstOne => UpperOp.const 1
  | .cst => UpperOp.const (f.coeff 0)
  | .total j => if j.val = 0 then UpperOp.const (f.coeff 0) else UpperOp.add

/-- The rank of a gate. -/
def cubicOrd : CubicIdx R n f → ℕ
  | .mono _ => 0
  | .smul _ _ => 1
  | .acc _ j => 2 + j.val
  | .prod _ => 3 + Fintype.card (Term n)
  | .cstOne => 0
  | .cst => 0
  | .total j => 4 + Fintype.card (Term n) + j.val

/-- The arguments of a gate. -/
noncomputable def cubicArgs (i : CubicIdx R n f) :
    Fin 2 → Fin n ⊕ {g : CubicIdx R n f // cubicOrd g < cubicOrd i} := by
  cases i with
  | mono p => exact ![Sum.inl p.1.1, Sum.inl p.1.2]
  | smul l t =>
      refine fun _ => ?_
      cases t with
      | one => exact Sum.inr ⟨.cstOne, by simp [cubicOrd]⟩
      | var j => exact Sum.inl j
      | pair p => exact Sum.inr ⟨.mono p, by simp [cubicOrd]⟩
  | acc l j =>
      by_cases hj : j.val = 0
      · exact fun _ => Sum.inl ⟨0, hn⟩
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hlt : j.val - 1 < j.val := Nat.sub_lt hjpos (by decide)
        have hjle : j.val ≤ Fintype.card (Term n) := by have := j.isLt; omega
        have hjcard : j.val - 1 < Fintype.card (Term n) :=
          lt_of_lt_of_le hlt hjle
        have hjcard' : j.val - 1 < Fintype.card (Term n) + 1 :=
          Nat.lt_succ_of_le (le_trans (Nat.sub_le _ _) hjle)
        exact ![Sum.inr ⟨.acc l ⟨j.val - 1, hjcard'⟩, by
            simp only [cubicOrd]
            exact Nat.add_lt_add_left hlt 2⟩,
          Sum.inr ⟨.smul l (termEquiv (n := n) ⟨j.val - 1, hjcard⟩),
            by simp only [cubicOrd]; omega⟩]
  | prod l => exact ![Sum.inl l, Sum.inr ⟨.acc l ⟨Fintype.card (Term n), Nat.lt_succ_self _⟩,
      by simp [cubicOrd]⟩]
  | cstOne => exact fun _ => Sum.inl ⟨0, hn⟩
  | cst => exact fun _ => Sum.inl ⟨0, hn⟩
  | total j =>
      by_cases hj : j.val = 0
      · exact fun _ => Sum.inl ⟨0, hn⟩
      · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
        have hlt : j.val - 1 < j.val := Nat.sub_lt hjpos (by decide)
        have hjlen : j.val - 1 < n := by
          have := j.isLt; omega
        exact ![Sum.inr ⟨.total ⟨j.val - 1, Nat.lt_succ_of_lt hjlen⟩,
            by simp only [cubicOrd]; exact Nat.add_lt_add_left hlt _⟩,
          Sum.inr ⟨.prod ⟨j.val - 1, hjlen⟩, by simp only [cubicOrd]; omega⟩]

/-- The value computed by a gate. -/
noncomputable def cubicSpec (x : Fin n → R) : CubicIdx R n f → R
  | .mono p => (termPoly (.pair p)).eval x
  | .smul l t => coeffQ hn f l t * (termPoly t).eval x
  | .acc l j => cubicAccVal hn f x l j
  | .prod l => cubicProdVal hn f x l
  | .cstOne => 1
  | .cst => f.coeff 0
  | .total j => cubicTotalVal hn f x j

/-- The operation of the gate `j` of the DAG circuit. -/
noncomputable def cubicGate (hn : 0 < n) (j : Fin (Fintype.card (CubicIdx R n f))) : RingOp R :=
  UpperOp.toRingOp (cubicOp hn (f := f) ((cubicEquiv (R := R) (n := n) (f := f)).symm j))

/-- The rank of the gate `j`. -/
noncomputable def cubicOrder (j : Fin (Fintype.card (CubicIdx R n f))) : ℕ :=
  cubicOrd (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))

/-- The arguments of the gate `j`. -/
noncomputable def cubicCargs (hn : 0 < n) (j : Fin (Fintype.card (CubicIdx R n f)))
    (t : Fin ((arithBasis R).arity (cubicGate hn j))) :
    Fin n ⊕ {g : Fin (Fintype.card (CubicIdx R n f)) // cubicOrder g < cubicOrder j} :=
  Sum.map id (fun g : {g : CubicIdx R n f // cubicOrd (f := f) g < cubicOrd (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))} =>
      ⟨(cubicEquiv (R := R) (n := n) (f := f)) g.1, by
        show cubicOrd (f := f) ((cubicEquiv (R := R) (n := n) (f := f)).symm
          ((cubicEquiv (R := R) (n := n) (f := f)) g.1)) <
            cubicOrd (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))
        rw [Equiv.symm_apply_apply]
        exact g.2⟩)
    (cubicArgs hn (((cubicEquiv (R := R) (n := n) (f := f)).symm j))
      (UpperOp.projArgB (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))) t))

/-- The DAG circuit computing `f`, with one multiplication per pair and one per variable. -/
noncomputable abbrev cubicCircuit (hn : 0 < n) : DagCircuit (arithBasis R) n 1 where
  size := Fintype.card (CubicIdx R n f)
  gate := cubicGate hn
  order := cubicOrder
  args := cubicCargs hn
  out _ := Sum.inr ((cubicEquiv (R := R) (n := n) (f := f)) (.total ⟨n, Nat.lt_succ_self n⟩))

/-- The value computed at the argument slot `s` of gate `i`. -/
noncomputable def cubicArgV (hn : 0 < n) (x : Fin n → R) (i : CubicIdx R n f) : Fin 2 → R :=
  fun s => Sum.elim (fun a => x a)
    (fun g : {g : CubicIdx R n f // cubicOrd (f := f) g < cubicOrd (f := f) i} =>
      (cubicCircuit (f := f) hn).nodeValue x ((cubicEquiv (R := R) (n := n) (f := f)) g.1))
    (cubicArgs hn i s)

/-- Reindexing the arguments by `cubicEquiv` does not change the values read from the wires. -/
theorem cubicCargs_elim (hn : 0 < n) (x : Fin n → R) (j : Fin (Fintype.card (CubicIdx R n f)))
    (t : Fin ((arithBasis R).arity (cubicGate hn j))) :
    Sum.elim (fun a => x a)
        (fun g : {g : Fin (Fintype.card (CubicIdx R n f)) //
          cubicOrder g < cubicOrder j} =>
          (cubicCircuit (f := f) hn).nodeValue x g.1)
        (cubicCargs hn j t)
      = Sum.elim (fun a => x a)
          (fun g : {g : CubicIdx R n f // cubicOrd (f := f) g < cubicOrd (f := f)
            (((cubicEquiv (R := R) (n := n) (f := f)).symm j))} =>
            (cubicCircuit (f := f) hn).nodeValue x ((cubicEquiv (R := R) (n := n) (f := f)) g.1))
          (cubicArgs hn (((cubicEquiv (R := R) (n := n) (f := f)).symm j))
            (UpperOp.projArgB (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))) t)) := by
  cases h : cubicArgs hn (((cubicEquiv (R := R) (n := n) (f := f)).symm j))
      (UpperOp.projArgB (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))) t) with
  | inl a => simp [cubicCargs, h]
  | inr g => simp [cubicCargs, h]

/-- Unfolding of the value of a gate of the cubic circuit. -/
theorem cubicCircuit_nodeValue_unfold (hn : 0 < n) (x : Fin n → R) (j : Fin (Fintype.card (CubicIdx R n f))) :
    (cubicCircuit (f := f) hn).nodeValue x j =
      UpperOp.eval (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j)))
        (cubicArgV hn x (((cubicEquiv (R := R) (n := n) (f := f)).symm j)) 0)
        (cubicArgV hn x (((cubicEquiv (R := R) (n := n) (f := f)).symm j)) 1) := by
  rw [DagCircuit.nodeValue_eq]
  rw [show (fun t => Sum.elim (fun a => x a)
        (fun g : {g : Fin (Fintype.card (CubicIdx R n f)) //
          cubicOrder g < cubicOrder j} =>
            (cubicCircuit (f := f) hn).nodeValue x g.1)
        ((cubicCircuit hn).args j t))
      = fun t => cubicArgV hn x (((cubicEquiv (R := R) (n := n) (f := f)).symm j))
          (UpperOp.projArgB (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j))) t) from by
    funext t
    exact cubicCargs_elim hn x j t]
  exact UpperOp.eval_toRingOp (cubicOp hn (f := f) (((cubicEquiv (R := R) (n := n) (f := f)).symm j)))
    (cubicArgV hn x (((cubicEquiv (R := R) (n := n) (f := f)).symm j)))

/-- The gate-by-gate verification that the cubic circuit computes `cubicSpec`. -/
theorem cubicCircuit_nodeValue_spec (x : Fin n → R) (i : CubicIdx R n f) :
    (cubicCircuit (f := f) hn).nodeValue x ((cubicEquiv (R := R) (n := n) (f := f)) i) =
      cubicSpec hn x i := by
  suffices h : ∀ m, ∀ i : CubicIdx R n f, cubicOrd (f := f) i = m →
      (cubicCircuit (f := f) hn).nodeValue x ((cubicEquiv (R := R) (n := n) (f := f)) i) =
        cubicSpec hn x i from h _ i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro i hi
    have ihg : ∀ g : {g : CubicIdx R n f // cubicOrd (f := f) g < cubicOrd (f := f) i},
        (cubicCircuit (f := f) hn).nodeValue x ((cubicEquiv (R := R) (n := n) (f := f)) g.1) =
          cubicSpec hn x g.1 := by
      intro g
      exact ihm (cubicOrd (f := f) g.1) (by have := g.2; omega) g.1 rfl
    have hunf := cubicCircuit_nodeValue_unfold hn x ((cubicEquiv (R := R) (n := n) (f := f)) i)
    rw [show (cubicEquiv (R := R) (n := n) (f := f)).symm
        ((cubicEquiv (R := R) (n := n) (f := f)) i) = i from
      Equiv.symm_apply_apply _ _] at hunf
    rw [hunf]
    cases i with
    | mono p =>
        have hterm : termPoly (.pair p) =
            (MvPolynomial.X p.1.1 : MvPolynomial (Fin n) R) * MvPolynomial.X p.1.2 := by
          simp [termPoly, termExp, pairExp, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]
        simp only [cubicSpec]
        rw [hterm]
        simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval,
          MvPolynomial.eval_mul, MvPolynomial.eval_X]
    | smul l t =>
        cases t with
        | one =>
            simp only [cubicArgV, cubicArgs, cubicOp, cubicSpec, UpperOp.eval, Sum.elim_inr,
              Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
            rw [ihg ⟨.cstOne, by simp [cubicOrd]⟩]
            simp [cubicSpec, termPoly, termExp]
        | var j =>
            have hterm : termPoly (.var j) = (MvPolynomial.X j : MvPolynomial (Fin n) R) := rfl
            simp only [cubicSpec]
            rw [hterm]
            simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, UpperOp.eval, MvPolynomial.eval_X]
        | pair p =>
            simp only [cubicArgV, cubicArgs, cubicOp, cubicSpec, UpperOp.eval, Sum.elim_inr,
              Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
            rw [ihg ⟨.mono p, by simp [cubicOrd]⟩]
            simp [cubicSpec]
    | acc l j =>
        by_cases hj : j.val = 0
        · have hj0 : j = ⟨0, Nat.succ_pos _⟩ := Fin.ext hj
          simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval, hj0]
          exact (cubicAccVal_zero (f := f) hn x l).symm
        · have hk : j.val - 1 < Fintype.card (Term n) := by
            have := j.isLt; omega
          simp only [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval, hj, dif_neg,
            not_false_eq_true, Sum.elim_inr, Sum.elim_inl, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons]
          rw [ihg ⟨.acc l ⟨j.val - 1, by omega⟩, by
              simp only [cubicOrd]
              exact Nat.add_lt_add_left (Nat.sub_lt (Nat.pos_of_ne_zero hj) (by decide)) 2⟩,
            ihg ⟨.smul l (termEquiv (n := n) ⟨j.val - 1, hk⟩), by
              simp only [cubicOrd]; omega⟩]
          simp only [cubicSpec]
          rw [cubicAccVal_congr (hn := hn) (f := f) (j := j)
            (j' := ⟨j.val - 1 + 1, by omega⟩)
            (by
              have hj1 : 1 ≤ j.val := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj)
              exact (Nat.sub_add_cancel hj1).symm)]
          exact (cubicAccVal_succ (f := f) hn x l (j.val - 1) hk).symm
    | prod l =>
        simp only [cubicArgV, cubicArgs, cubicOp, cubicSpec, UpperOp.eval, Sum.elim_inr, Sum.elim_inl,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [ihg ⟨.acc l ⟨Fintype.card (Term n), Nat.lt_succ_self _⟩, by simp [cubicOrd]⟩]
        simp [cubicSpec, cubicProdVal]
    | cstOne => simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval]
    | cst => simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval]
    | total j =>
        by_cases hj : j.val = 0
        · have hj0 : j = ⟨0, Nat.succ_pos _⟩ := Fin.ext hj
          simp [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval, hj0]
          exact (cubicTotalVal_zero (f := f) hn x).symm
        · have hk : j.val - 1 < n := by have := j.isLt; omega
          simp only [cubicArgV, cubicArgs, cubicOp, cubicSpec, cubicOrd, UpperOp.eval, hj, dif_neg,
            not_false_eq_true, Sum.elim_inr, Sum.elim_inl, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons]
          rw [ihg ⟨.total ⟨j.val - 1, by omega⟩, by
              simp only [cubicOrd]
              exact Nat.add_lt_add_left (Nat.sub_lt (Nat.pos_of_ne_zero hj) (by decide)) _⟩,
            ihg ⟨.prod ⟨j.val - 1, hk⟩, by simp only [cubicOrd]; omega⟩]
          simp only [cubicSpec]
          rw [cubicTotalVal_congr (hn := hn) (f := f) (j := j)
            (j' := ⟨j.val - 1 + 1, by omega⟩)
            (by
              have hj1 : 1 ≤ j.val := Nat.one_le_of_lt (Nat.pos_of_ne_zero hj)
              exact (Nat.sub_add_cancel hj1).symm)]
          exact (cubicTotalVal_succ (f := f) hn x (j.val - 1) hk).symm

/-- The final value of the cubic circuit is the value of `cubicRHS`. -/
theorem cubicTotalVal_full_eq (x : Fin n → R) :
    cubicTotalVal hn f x ⟨n, Nat.lt_succ_self n⟩ = (cubicRHS hn f).eval x := by
  simp only [cubicTotalVal, cubicProdVal, cubicAccVal, cubicRHS, map_add, MvPolynomial.eval_C]
  have hsum : (∑ i : Fin n, x i * ∑ i_1 : Fin (Fintype.card (Term n)),
          coeffQ hn f i (termEquiv (n := n) i_1) *
            (termPoly (termEquiv (n := n) i_1)).eval x)
      = (eval x) (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) *
          (∑ t : Term n, MvPolynomial.C (coeffQ hn f i t) * termPoly t)) := by
    calc (∑ i : Fin n, x i * ∑ i_1 : Fin (Fintype.card (Term n)),
          coeffQ hn f i (termEquiv (n := n) i_1) *
            (termPoly (termEquiv (n := n) i_1)).eval x)
        = ∑ i : Fin n, x i * (∑ t : Term n,
            coeffQ hn f i t * (termPoly t).eval x) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          congr 1
          exact Equiv.sum_comp (termEquiv (n := n))
            (fun t : Term n => coeffQ hn f i t * (termPoly t).eval x)
      _ = (eval x) (∑ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) R) *
            (∑ t : Term n, MvPolynomial.C (coeffQ hn f i t) * termPoly t)) := by
          simp [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.eval_add,
            MvPolynomial.eval_sum, MvPolynomial.eval_C, Finset.mul_sum, Finset.sum_mul]
  rw [hsum, add_comm]

/-- The cubic circuit computes `f`. -/
theorem cubicCircuit_eval (hf : f.totalDegree ≤ 3) (x : Fin n → R) :
    (cubicCircuit (f := f) hn).eval x = fun _ => f.eval x := by
  funext o
  have hout : (cubicCircuit (f := f) hn).out o =
      Sum.inr ((cubicEquiv (R := R) (n := n) (f := f)) (.total ⟨n, Nat.lt_succ_self n⟩)) := rfl
  rw [DagCircuit.eval, hout]
  show (cubicCircuit (f := f) hn).nodeValue x
      ((cubicEquiv (R := R) (n := n) (f := f)) (.total ⟨n, Nat.lt_succ_self n⟩)) = f.eval x
  rw [cubicCircuit_nodeValue_spec]
  rw [show cubicSpec hn x (.total ⟨n, Nat.lt_succ_self n⟩) =
      cubicTotalVal hn f x ⟨n, Nat.lt_succ_self n⟩ from rfl]
  rw [cubicTotalVal_full_eq, ← cubic_decomp hn f hf]

/-- A default same-block pair, used only to define a total map on all gates. -/
noncomputable def defaultPair (hn : 0 < n) : PairIdx n :=
  mkPair ⟨0, hn⟩ ⟨0, hn⟩ (sameBlock_refl _)

/-- The multiplicative gates are exactly the monomial gates and the product gates. -/
lemma isMul_cubicOp_cases (i : CubicIdx R n f)
    (hi : UpperOp.isMul (cubicOp hn (f := f) i) = true) :
    (∃ p : PairIdx n, i = .mono p) ∨ (∃ l : Fin n, i = .prod l) := by
  cases i with
  | mono p => exact Or.inl ⟨p, rfl⟩
  | prod l => exact Or.inr ⟨l, rfl⟩
  | smul l t => simp [cubicOp, UpperOp.isMul] at hi
  | acc l j => by_cases hj : j.val = 0 <;> simp [cubicOp, hj, UpperOp.isMul] at hi
  | cstOne => simp [cubicOp, UpperOp.isMul] at hi
  | cst => simp [cubicOp, UpperOp.isMul] at hi
  | total j => by_cases hj : j.val = 0 <;> simp [cubicOp, hj, UpperOp.isMul] at hi

/-- The injection from the multiplication gates to `PairIdx ⊕ Fin n`. -/
noncomputable def cubicMulMap (i : CubicIdx R n f) : PairIdx n ⊕ Fin n :=
  match i with
  | .mono p => Sum.inl p
  | .prod l => Sum.inr l
  | _ => Sum.inl (defaultPair hn)

theorem cubicMulMap_injective :
    Function.Injective (fun q : {i : CubicIdx R n f // UpperOp.isMul (cubicOp hn (f := f) i) = true} =>
      cubicMulMap hn (f := f) q.1) := by
  rintro ⟨i, hi⟩ ⟨i', hi'⟩ hab
  rcases isMul_cubicOp_cases hn (f := f) i hi with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · rcases isMul_cubicOp_cases hn (f := f) i' hi' with ⟨p', rfl⟩ | ⟨l', rfl⟩
    · simp only [cubicMulMap, Sum.inl.injEq] at hab
      subst hab
      rfl
    · simp [cubicMulMap] at hab
  · rcases isMul_cubicOp_cases hn (f := f) i' hi' with ⟨p', rfl⟩ | ⟨l', rfl⟩
    · simp [cubicMulMap] at hab
    · simp only [cubicMulMap, Sum.inr.injEq] at hab
      subst hab
      rfl

/-- The equivalence between the multiplication gates of the DAG circuit and the corresponding
`CubicIdx` gates. -/
noncomputable def cubicMulGateEquiv :
    {j : Fin (Fintype.card (CubicIdx R n f)) //
      RingOp.isMul ((cubicCircuit hn (f := f)).gate j) = true}
      ≃ {i : CubicIdx R n f // UpperOp.isMul (cubicOp hn (f := f) i) = true} where
  toFun q := ⟨(cubicEquiv (R := R) (n := n) (f := f)).symm q.1, by
    show UpperOp.isMul (cubicOp hn (f := f) ((cubicEquiv (R := R) (n := n) (f := f)).symm q.1)) = true
    rw [← UpperOp.isMul_toRingOp]
    exact q.2⟩
  invFun q := ⟨(cubicEquiv (R := R) (n := n) (f := f)) q.1, by
    show RingOp.isMul ((cubicCircuit hn (f := f)).gate
      ((cubicEquiv (R := R) (n := n) (f := f)) q.1)) = true
    rw [show (cubicCircuit hn (f := f)).gate
        ((cubicEquiv (R := R) (n := n) (f := f)) q.1)
        = UpperOp.toRingOp (cubicOp hn (f := f)
          ((cubicEquiv (R := R) (n := n) (f := f)).symm
            ((cubicEquiv (R := R) (n := n) (f := f)) q.1))) from rfl,
      UpperOp.isMul_toRingOp, Equiv.symm_apply_apply]
    exact q.2⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp

/-- The cubic circuit has at most one multiplication per same-block pair and one per variable. -/
theorem cubicCircuit_mulCount_le :
    dagMulComplexity (cubicCircuit hn (f := f)) ≤ Fintype.card (PairIdx n) + n := by
  calc dagMulComplexity (cubicCircuit hn (f := f))
      = Fintype.card {j : Fin (Fintype.card (CubicIdx R n f)) //
          RingOp.isMul ((cubicCircuit hn (f := f)).gate j) = true} := by
        simp only [dagMulComplexity, DagCircuit.countGates]
        exact (Fintype.card_subtype _).symm
    _ = Fintype.card {i : CubicIdx R n f // UpperOp.isMul (cubicOp hn (f := f) i) = true} :=
        Fintype.card_congr (cubicMulGateEquiv hn (f := f))
    _ ≤ Fintype.card (PairIdx n ⊕ Fin n) :=
        Fintype.card_le_of_injective _ (cubicMulMap_injective hn (f := f))
    _ = Fintype.card (PairIdx n) + n := by simp

/-- The cubic upper bound: `μ(f) ≤ #(same-block pairs) + n`. -/
theorem polyMu_le_cubic (hn : 0 < n) (hf : f.totalDegree ≤ 3) :
    polyMu f ≤ Fintype.card (PairIdx n) + n := by
  have himp : (cubicCircuit hn (f := f)).toSLP.Implements
      (fun x (_ : Fin 1) => f.eval x) := by
    rw [Circuit.implements_iff]
    intro x
    rw [DagCircuit.toSLP_eval]
    exact cubicCircuit_eval hn hf x
  have hμ : mulComplexity ((cubicCircuit hn (f := f)).toSLP) ≤
      Fintype.card (PairIdx n) + n := by
    rw [dagMulComplexity_toSLP]
    exact cubicCircuit_mulCount_le hn (f := f)
  exact (mulComplexityOf_le himp).trans hμ

/-- The refined upper bound for the class `M_{3,n}`: `μ(M_{3,n}) ≤ #(same-block pairs) + n`. -/
theorem classMu_le_cubic (hn : 0 < n) :
    classMu (R := R) 3 n ≤ Fintype.card (PairIdx n) + n := by
  refine classMu_le fun f => ?_
  exact polyMu_le_cubic hn f.2


end Circuit

end Sergeev

end MultcompPoly
