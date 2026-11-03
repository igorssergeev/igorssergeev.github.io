module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lower bound for `μ(M_{d,n})` at odd `d`

Formalisation of the argument of `cubic_th1.pdf`, giving the lower half of Theorem 1 of
Sergeev for odd `d`: `μ(M_{d,n}) ≽ n ^ ⌈d / 2⌉`, with the sharp constant
`μ(M_{d,n}) ≥ (1 - o(1)) (⌈d/2⌉ - 1)! n^{⌈d/2⌉} / (3 d!)`.

This file is **self-contained**: it imports nothing but Mathlib.  To make that possible it also
carries its own copy of the arithmetic-circuit data (`ArithOp2`, `ArithCircuit2` with its
one-step and polynomial semantics) and of the Steinitz argument.  

## The argument

Let `d = 2h - 1` be odd and let `f` be computed by an arithmetic circuit with `s` nonscalar
multiplications.  Writing `u_j` for the polynomial computed at the `j`-th multiplication gate,
`A_j`, `B_j` for the polynomials at its two arguments, and `a_j`, `b_j` for the sums of the
homogeneous components of `A_j`, `B_j` of degree `< h`, the paper proves by induction on `j` that
for every `h ≤ k ≤ d`

  `u_j^{[k]} = ∑_{t=h}^{k} ∑_{i<j} c_{i,t} · (a_i b_i)^{[t]}`,

where `c_{i,t}` is homogeneous of degree `k - t`.  Products of two components of degree `≥ h`
cannot contribute to a component of degree `≤ d = 2h - 1`, which is what makes the truncation at
`h` legitimate.

Consequently the degree-`d` component of anything computed by the circuit has the form

  `f^{[d]} = ∑_j (c_j · a_j · b_j)^{[d]}`

with `deg c_j ≤ d - h` and `deg a_j, deg b_j < h`.  The map `(c, a, b) ↦ ∑_j (c_j a_j b_j)^{[d]}`
is polynomial in the coefficients of the `3s` polynomials, so its image is a polynomial image of a
space of dimension `3s · C(n+h-1, h-1)`.  Since the space of degree-`d` forms has dimension
`C(n+d-1, d)`, Steinitz's lemma produces a degree-`d` form that is *not* of this shape, hence is
not computable with `s` multiplications.  Optimising `s`, and using the exact dimension
`C(n+h-1,h-1)` of the low-part space, gives
`μ(M_{d,n}) ≥ C(n+d-1,d) / (3 C(n+h-1,h-1))`, which is
`(1 - o(1)) (h-1)! n^{⌈d/2⌉} / (3 d!)` with `h = ⌈d/2⌉ = (d+1)/2`.

## Contents

* the arithmetic-circuit model: `ArithOp2` with its evaluation `ArithOp2.eval`, the structure
  `ArithCircuit2` with the gate values `vals`/`nodeValue`/`eval` and the polynomials
  `polys`/`nodePoly`/`outPoly`, and the nonscalar count `mulCount`;
* a self-contained copy of Steinitz's lemma (`exists_not_mem_range'`);
* the product rule for homogeneous components (`homogeneousComponent_mul`), together with the
  low/high decomposition of a polynomial at height `h` (`lowPart`, `hiPart`) and its interaction
  with homogeneous components;
* the circuit bookkeeping: `mulGate`, `argPoly`, `nodePoly_eq_polyEval`, the linear representation
  of the value at every gate and argument (`exists_linRep_node`, `exists_linRep_arg`);
* the ambient span `ambSet` of the shapes `K · (a_j b_j)^{[t]}` together with its closure
  properties under multiplication (`amb_mul_homogeneous`, `amb_mul_homogeneous_right`) and the
  three-region decomposition of a degree-`k` component of a product
  (`homogeneousComponent_mul_split`, `sum_filter_lowPart_eq`), and `hcomp_argPoly_mem`;
* **part I** of the paper: the multiplication-gate step `hcomp_mul_step` and the induction over the
  gates `graded_mem`;
* **part II** of the paper: the extraction `exists_repr` / `exists_repr_pad` of the shape
  `f^{[d]} = ∑_j (c_j · a_j · b_j)^{[d]}` with `deg c_j ≤ d - h`;
* the **parameter count**: the monomial index sets `Param.MonoLt`, `Param.PIdx`, the generic
  parameterised family `Param.formExpr`, its image `Param.Phi` and the monomial decomposition
  `Param.as_sum_monomials`;
* the **Steinitz step** `Param.exists_form_not_computable`: when `3 s · #MonoLt < #(Sym (Fin n) d)`
  some degree-`d` form is not computed by any circuit with `s` nonscalar multiplications;
* the resulting bounds, stated for circuits: `Param.odd_lower_bound_numeric` and
  `Param.odd_lower_bound_div_choose` produce a form of degree at most `d` that needs at least
  `C(n+d-1,d) / (3 C(n+h-1,h-1))` nonscalar multiplications, with
  `Param.odd_lower_bound_choose` the corresponding counting form;
* the **exact count**: the hockey-stick identity `Param.sum_range_choose_pred` and the exact
  dimensions `Param.card_MonoLt_eq` / `Param.card_MonoLt_eq'`;
* the **sharp asymptotics** `Param.odd_lower_bound_asymptotic_sharp` (in `(1 - ε)` form, for
  every `ε > 0`) and `Param.odd_lower_bound_asymptotic_sharp'` (for every constant `c < 1`),
  giving `(1 - o(1)) (h-1)! n^{⌈d/2⌉} / (3 d!) ≤ C(n+d-1,d) / (3 C(n+h-1,h-1))` from
  `C(n+d-1,d) ≥ n^d / d!` and `C(n+h-1,h-1) ≤ (1+δ) n^{h-1}/(h-1)!`.
-/

@[expose] public section

universe u

open scoped Topology

namespace MultcompPoly
/-! ## The circuit model (self-contained copy) -/

/-! ## Arithmetic circuits with two arguments per gate -/

/-- The operations of the arithmetic basis `A_R`, displayed with two arguments (the second
argument of a scalar multiplication is ignored). -/
inductive ArithOp2 (R : Type u) : Type u
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

namespace ArithOp2

variable [CommRing R]

/-- The value computed by an operation applied to two arguments. -/
def eval : ArithOp2 R → R → R → R
  | add, u, v => u + v
  | sub, u, v => u - v
  | mul, u, v => u * v
  | smul a, u, _ => a * u
  | const a, _, _ => a

/-- Tests whether an operation is the nonscalar multiplication gate. -/
def isMul : ArithOp2 R → Bool
  | mul => true
  | _ => false

/-- Tests whether an operation is a scalar multiplication gate. -/
def isSmul : ArithOp2 R → Bool
  | smul _ => true
  | _ => false

/-- The scalar multiplier of a scalar multiplication gate, if any. -/
def smulOf : ArithOp2 R → Option R
  | smul a => some a
  | _ => none

end ArithOp2

/-- A straight-line arithmetic circuit over a commutative ring `R`, all of whose gates take
exactly two arguments.  Gate `j` may only read the inputs or the gates of smaller index. -/
structure ArithCircuit2 (R : Type u) [CommRing R] (k m : ℕ) where
  /-- The number of gates. -/
  size : ℕ
  /-- The operation of each gate. -/
  gate : Fin size → ArithOp2 R
  /-- The two wires feeding each gate: inputs or earlier gates. -/
  args : (j : Fin size) → Fin 2 → Fin k ⊕ Fin j.val
  /-- The wire feeding each output. -/
  out : Fin m → Fin k ⊕ Fin size

namespace ArithCircuit2

variable {R : Type u} [CommRing R] {k m : ℕ}

/-- The values of the gates `0, …, n - 1` of the circuit, on the input vector `x`. -/
def vals (c : ArithCircuit2 R k m) (x : Fin k → R) : (n : ℕ) → n ≤ c.size → (Fin n → R)
  | 0, _ => Fin.elim0
  | n + 1, h => fun i =>
      if hi : i.val < n then vals c x n (Nat.le_of_succ_le h) ⟨i.val, hi⟩
      else
        (c.gate ⟨n, Nat.lt_of_succ_le h⟩).eval
          (Sum.elim (fun a => x a) (fun g => vals c x n (Nat.le_of_succ_le h) g)
            (c.args ⟨n, Nat.lt_of_succ_le h⟩ 0))
          (Sum.elim (fun a => x a) (fun g => vals c x n (Nat.le_of_succ_le h) g)
            (c.args ⟨n, Nat.lt_of_succ_le h⟩ 1))

/-- The value computed at gate `j` of the circuit, on the input vector `x`. -/
def nodeValue (c : ArithCircuit2 R k m) (x : Fin k → R) (j : Fin c.size) : R :=
  c.vals x c.size (Nat.le_refl c.size) j

/-- The value of a wire (an input or a gate). -/
def wireValue (c : ArithCircuit2 R k m) (x : Fin k → R) : Fin k ⊕ Fin c.size → R :=
  Sum.elim x (c.nodeValue x)

/-- The operator computed by the circuit. -/
def eval (c : ArithCircuit2 R k m) (x : Fin k → R) : Fin m → R :=
  fun o => c.wireValue x (c.out o)

@[simp] theorem wireValue_inl (c : ArithCircuit2 R k m) (x : Fin k → R) (i : Fin k) :
    c.wireValue x (Sum.inl i) = x i := rfl

@[simp] theorem wireValue_inr (c : ArithCircuit2 R k m) (x : Fin k → R) (j : Fin c.size) :
    c.wireValue x (Sum.inr j) = c.nodeValue x j := rfl

/-- The values of a prefix of the gates agree with the values computed by the whole circuit. -/
theorem vals_succ (c : ArithCircuit2 R k m) (x : Fin k → R) {n : ℕ} (h : n + 1 ≤ c.size)
    (i : Fin n) :
    c.vals x (n + 1) h (Fin.castSucc i) = c.vals x n (Nat.le_of_succ_le h) i := by
  simp only [ArithCircuit2.vals]
  split_ifs with hlt
  · exact congrArg (c.vals x n (Nat.le_of_succ_le h)) (Fin.ext rfl)
  · exact absurd i.isLt hlt

/-- The value at the last of `n + 1` gates is the operation of that gate applied to the values
of its arguments. -/
theorem vals_last (c : ArithCircuit2 R k m) (x : Fin k → R) {n : ℕ} (h : n + 1 ≤ c.size) :
    c.vals x (n + 1) h ⟨n, Nat.lt_succ_self n⟩ =
      (c.gate ⟨n, h⟩).eval
        (Sum.elim (fun a => x a) (fun g => c.vals x n (Nat.le_of_succ_le h) g)
          (c.args ⟨n, h⟩ 0))
        (Sum.elim (fun a => x a) (fun g => c.vals x n (Nat.le_of_succ_le h) g)
          (c.args ⟨n, h⟩ 1)) := by
  simp only [ArithCircuit2.vals]
  split_ifs with hlt
  · exact absurd hlt (Nat.lt_irrefl n)
  · rfl

/-- The value of a gate is the same as its value in the prefix of the gates ending at it. -/
theorem vals_apply_of_le (c : ArithCircuit2 R k m) (x : Fin k → R) :
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
theorem nodeValue_eq_aux (c : ArithCircuit2 R k m) (x : Fin k → R) (n : ℕ) (hn : n < c.size) :
    c.nodeValue x ⟨n, hn⟩ =
      (c.gate ⟨n, hn⟩).eval
        (Sum.elim (fun a => x a)
          (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le hn) g)) (c.args ⟨n, hn⟩ 0))
        (Sum.elim (fun a => x a)
          (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le hn) g)) (c.args ⟨n, hn⟩ 1)) := by
  rw [← vals_apply_of_le (n := n + 1) c x hn ⟨n, Nat.lt_succ_self n⟩]
  rw [vals_last (n := n) (h := hn)]
  have h0 : ∀ (s : Fin 2) (w : Fin k ⊕ Fin n), c.args ⟨n, hn⟩ s = w ->
      Sum.elim (fun a => x a) (fun g => c.vals x n (Nat.le_of_succ_le hn) g) w
        = Sum.elim (fun a => x a)
            (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le hn) g)) w := by
    intro s w hw
    cases w with
    | inl a => rfl
    | inr g => exact vals_apply_of_le (n := n) c x (Nat.le_of_succ_le hn) g
  rw [h0 0 _ rfl, h0 1 _ rfl]

/-- Unfolding of the value of a gate. -/
theorem nodeValue_eq (c : ArithCircuit2 R k m) (x : Fin k → R) (j : Fin c.size) :
    c.nodeValue x j =
      (c.gate j).eval
        (Sum.elim (fun a => x a)
          (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le j.isLt) g)) (c.args j 0))
        (Sum.elim (fun a => x a)
          (fun g => c.nodeValue x (Fin.castLE (Nat.le_of_succ_le j.isLt) g)) (c.args j 1)) :=
  nodeValue_eq_aux c x j.val j.isLt

/-- The number of gates whose operation satisfies the Boolean predicate `p`. -/
noncomputable def countGates (c : ArithCircuit2 R k m) (p : ArithOp2 R → Bool) : ℕ :=
  ∑ j : Fin c.size, if p (c.gate j) then 1 else 0

theorem countGates_le (c : ArithCircuit2 R k m) (p : ArithOp2 R → Bool) :
    c.countGates p ≤ c.size := by
  simp only [countGates]
  calc ∑ j : Fin c.size, (if p (c.gate j) then 1 else 0) ≤ ∑ _j : Fin c.size, 1 := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs <;> simp
    _ = c.size := by simp

/-- The number of nonscalar multiplications of the circuit. -/
noncomputable def mulCount (c : ArithCircuit2 R k m) : ℕ := c.countGates ArithOp2.isMul

end ArithCircuit2

/-! ## Polynomial semantics -/

namespace ArithOp2

variable {R : Type u} [CommRing R] {k : ℕ}

/-- The operation applied to the polynomials computed by its arguments. -/
noncomputable def polyEval (op : ArithOp2 R) (v : Fin 2 → MvPolynomial (Fin k) R) : MvPolynomial (Fin k) R :=
  match op with
  | add => v 0 + v 1
  | sub => v 0 - v 1
  | mul => v 0 * v 1
  | smul a => MvPolynomial.C a * v 0
  | const a => MvPolynomial.C a

theorem polyEval_eval (op : ArithOp2 R) (v : Fin 2 → MvPolynomial (Fin k) R) (x : Fin k → R) :
    (op.polyEval v).eval x = op.eval ((v 0).eval x) ((v 1).eval x) := by
  cases op <;> simp [polyEval, eval]

end ArithOp2

namespace ArithCircuit2

variable {R : Type u} [CommRing R] {k m : ℕ}

/-- The polynomials computed by the gates `0, …, n - 1` of the circuit. -/
noncomputable def polys (c : ArithCircuit2 R k m) :
    (n : ℕ) → n ≤ c.size → (Fin n → MvPolynomial (Fin k) R)
  | 0, _ => Fin.elim0
  | n + 1, h => fun i =>
      if hi : i.val < n then polys c n (Nat.le_of_succ_le h) ⟨i.val, hi⟩
      else
        (c.gate ⟨n, Nat.lt_of_succ_le h⟩).polyEval
          (fun t => Sum.elim (fun a => MvPolynomial.X a)
            (fun g => polys c n (Nat.le_of_succ_le h) g) (c.args ⟨n, Nat.lt_of_succ_le h⟩ t))

/-- The polynomial computed at gate `j` of the circuit. -/
noncomputable def nodePoly (c : ArithCircuit2 R k m) (j : Fin c.size) :
    MvPolynomial (Fin k) R :=
  c.polys c.size (Nat.le_refl c.size) j

/-- The polynomial computed at a wire (an input or a gate). -/
noncomputable def wirePoly (c : ArithCircuit2 R k m) : Fin k ⊕ Fin c.size →
    MvPolynomial (Fin k) R :=
  Sum.elim (fun a => MvPolynomial.X a) c.nodePoly

/-- The polynomial computed at each output of the circuit. -/
noncomputable def outPoly (c : ArithCircuit2 R k m) (o : Fin m) : MvPolynomial (Fin k) R :=
  c.wirePoly (c.out o)

theorem polys_succ (c : ArithCircuit2 R k m) {n : ℕ} (h : n + 1 ≤ c.size)
    (i : Fin n) :
    c.polys (n + 1) h (Fin.castSucc i) = c.polys n (Nat.le_of_succ_le h) i := by
  simp only [ArithCircuit2.polys]
  split_ifs with hlt
  · exact congrArg (c.polys n (Nat.le_of_succ_le h)) (Fin.ext rfl)
  · exact absurd i.isLt hlt

theorem polys_last (c : ArithCircuit2 R k m) {n : ℕ} (h : n + 1 ≤ c.size) :
    c.polys (n + 1) h ⟨n, Nat.lt_succ_self n⟩ =
      (c.gate ⟨n, h⟩).polyEval
        (fun t => Sum.elim (fun a => MvPolynomial.X a)
          (fun g => c.polys n (Nat.le_of_succ_le h) g) (c.args ⟨n, h⟩ t)) := by
  simp only [ArithCircuit2.polys]
  split_ifs with hlt
  · exact absurd hlt (Nat.lt_irrefl n)
  · rfl

theorem polys_apply_of_le (c : ArithCircuit2 R k m) :
    ∀ {n : ℕ} (hn : n ≤ c.size) (i : Fin n),
      c.polys n hn i = c.nodePoly ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := by
  have main : ∀ n, n ≤ c.size → (∀ hn' : n ≤ c.size, ∀ i : Fin n,
      c.polys n hn' i = c.nodePoly ⟨i.val, lt_of_lt_of_le i.isLt hn'⟩) := by
    intro n hle
    refine Nat.decreasingInduction (motive := fun n _ => ∀ hn' : n ≤ c.size, ∀ i : Fin n,
      c.polys n hn' i = c.nodePoly ⟨i.val, lt_of_lt_of_le i.isLt hn'⟩) ?_ ?_ hle
    · intro n hn ih hn' i
      have h1 : c.polys n hn' i =
          c.polys (n + 1) (hn : n + 1 ≤ c.size) (Fin.castSucc i) := by
        rw [polys_succ]
      rw [h1]
      exact ih (hn : n + 1 ≤ c.size) (Fin.castSucc i)
    · intro hn' i; rfl
  exact fun {n} hn i => main n hn hn i

/-- The evaluation of the polynomial computed at a gate is the value of the gate. -/
theorem eval_polys (c : ArithCircuit2 R k m) (x : Fin k → R) :
    ∀ (n : ℕ) (hn : n ≤ c.size) (i : Fin n), (c.polys n hn i).eval x = c.vals x n hn i := by
  intro n
  induction n with
  | zero => intro hn i; exact i.elim0
  | succ n ih =>
    intro hn i
    refine Fin.lastCases ?_ ?_ i
    · have hlast : (Fin.last n : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext rfl
      rw [hlast, polys_last, vals_last]
      have harg : ∀ t : Fin 2,
          ((fun t => Sum.elim (fun a => MvPolynomial.X a)
            (fun g => c.polys n (Nat.le_of_succ_le hn) g) (c.args ⟨n, hn⟩ t)) t).eval x
          = (fun t => Sum.elim (fun a => x a)
            (fun g => c.vals x n (Nat.le_of_succ_le hn) g) (c.args ⟨n, hn⟩ t)) t := by
        intro t
        cases hh : c.args ⟨n, hn⟩ t with
        | inl a =>
            simp only [hh, Sum.elim_inl]
            simp
        | inr g =>
            simp only [hh, Sum.elim_inr]
            exact ih (Nat.le_of_succ_le hn) g
      rw [ArithOp2.polyEval_eval]
      rw [harg 0, harg 1]
    · intro i'
      rw [polys_succ (h := hn) (i := i'), vals_succ (h := hn) (i := i')]
      exact ih (Nat.le_of_succ_le hn) i'

/-- The evaluation of the polynomial computed at a wire is the value of the wire. -/
@[simp] theorem eval_wirePoly (c : ArithCircuit2 R k m) (x : Fin k → R)
    (w : Fin k ⊕ Fin c.size) : (c.wirePoly w).eval x = c.wireValue x w := by
  cases w with
  | inl a => simp [ArithCircuit2.wirePoly]
  | inr j => exact eval_polys c x c.size (Nat.le_refl c.size) j

/-- The evaluation of the polynomial computed at an output is the value of the output. -/
theorem eval_outPoly (c : ArithCircuit2 R k m) (x : Fin k → R) (o : Fin m) :
    (c.outPoly o).eval x = c.eval x o :=
  eval_wirePoly c x (c.out o)

end ArithCircuit2

/-! ## The polynomial at a gate -/

namespace ArithCircuit2

variable {R : Type u} [CommRing R] {k m : ℕ}

/-- The polynomial computed at gate `n` is the operation of that gate applied to the polynomials
computed at its arguments. -/
theorem nodePoly_eq_aux (c : ArithCircuit2 R k m) (n : ℕ) (hn : n < c.size) :
    c.nodePoly ⟨n, hn⟩ =
      (c.gate ⟨n, hn⟩).polyEval
        (fun t => Sum.elim (fun a => MvPolynomial.X a)
          (fun g => c.nodePoly (Fin.castLE (Nat.le_of_succ_le hn) g)) (c.args ⟨n, hn⟩ t)) := by
  rw [← polys_apply_of_le (n := n + 1) c hn ⟨n, Nat.lt_succ_self n⟩]
  rw [polys_last (n := n) (h := hn)]
  have harg : ∀ t : Fin 2,
      ((fun t => Sum.elim (fun a => MvPolynomial.X a)
        (fun g => c.polys n (Nat.le_of_succ_le hn) g) (c.args ⟨n, hn⟩ t)) t)
      = ((fun t => Sum.elim (fun a => MvPolynomial.X a)
        (fun g => c.nodePoly (Fin.castLE (Nat.le_of_succ_le hn) g)) (c.args ⟨n, hn⟩ t)) t) := by
    intro t
    cases hh : c.args ⟨n, hn⟩ t with
    | inl a => simp only [hh, Sum.elim_inl]
    | inr g => simp only [hh, Sum.elim_inr]
               exact polys_apply_of_le (n := n) c (Nat.le_of_succ_le hn) g
  rw [funext harg]

/-- The polynomial computed at a gate. -/
theorem nodePoly_eq (c : ArithCircuit2 R k m) (j : Fin c.size) :
    c.nodePoly j =
      (c.gate j).polyEval
        (fun t => Sum.elim (fun a => MvPolynomial.X a)
          (fun g => c.nodePoly (Fin.castLE (Nat.le_of_succ_le j.isLt) g)) (c.args j t)) :=
  nodePoly_eq_aux c j.val j.isLt

/-- The polynomial computed at a gate, in terms of the polynomials computed at the wires of the
circuit. -/
theorem nodePoly_eq' (c : ArithCircuit2 R k m) (j : Fin c.size) :
    c.nodePoly j = (c.gate j).polyEval
      (fun t => c.wirePoly (Sum.map id (Fin.castLE (le_of_lt j.isLt)) (c.args j t))) := by
  rw [nodePoly_eq]
  congr 1
  funext t
  cases h : c.args j t with
  | inl a => rfl
  | inr g => rfl

end ArithCircuit2

namespace Sergeev

open MvPolynomial

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000

/-! ## The product rule for homogeneous components -/

section HComp

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- The `d`-component of a monomial is the monomial itself iff the monomial has degree `d`. -/
theorem homogeneousComponent_monomial_self {m : σ →₀ ℕ} {r : R} :
    homogeneousComponent m.degree (monomial m r) = monomial m r :=
  homogeneousComponent_eq_self (isHomogeneous_monomial r rfl)

theorem homogeneousComponent_monomial_of_ne {m : σ →₀ ℕ} {r : R} {s : ℕ}
    (h : s ≠ m.degree) : homogeneousComponent s (monomial m r) = 0 := by
  rw [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
  simp [h]

theorem homogeneousComponent_mul_monomial_monomial (m n : σ →₀ ℕ) (r c : R) (k : ℕ) :
    homogeneousComponent k (monomial m r * monomial n c) =
      ∑ s ∈ Finset.range (k + 1), homogeneousComponent s (monomial m r) *
        homogeneousComponent (k - s) (monomial n c) := by
  rw [monomial_mul_monomial]
  have hdeg : (m + n).degree = m.degree + n.degree := map_add _ _ _
  by_cases hAB : m.degree + n.degree = k
  · subst k
    conv_lhs => rw [← hdeg]
    rw [homogeneousComponent_monomial_self]
    rw [Finset.sum_eq_single m.degree]
    · rw [homogeneousComponent_monomial_self,
        show m.degree + n.degree - m.degree = n.degree by omega,
        homogeneousComponent_monomial_self, monomial_mul_monomial]
    · intro s _ hs
      rw [homogeneousComponent_monomial_of_ne hs, zero_mul]
    · intro h
      exact absurd (by simp only [Finset.mem_range]; omega) h
  · rw [homogeneousComponent_monomial_of_ne (by rw [hdeg]; exact fun h => hAB h.symm)]
    rw [Finset.sum_eq_zero]
    intro s hs
    simp only [Finset.mem_range] at hs
    by_cases hsm : s = m.degree
    · subst hsm
      rw [homogeneousComponent_monomial_of_ne (by omega : k - m.degree ≠ n.degree), mul_zero]
    · rw [homogeneousComponent_monomial_of_ne hsm, zero_mul]

theorem homogeneousComponent_mul_monomial (m : σ →₀ ℕ) (r : R) (q : MvPolynomial σ R) (k : ℕ) :
    homogeneousComponent k (monomial m r * q) =
      ∑ s ∈ Finset.range (k + 1), homogeneousComponent s (monomial m r) *
        homogeneousComponent (k - s) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial n c => exact homogeneousComponent_mul_monomial_monomial m n r c k
  | add p q hp hq => simp only [mul_add, map_add, Finset.sum_add_distrib, hp, hq]

/-- **The product rule for homogeneous components.** -/
theorem homogeneousComponent_mul (p q : MvPolynomial σ R) (k : ℕ) :
    homogeneousComponent k (p * q) =
      ∑ s ∈ Finset.range (k + 1), homogeneousComponent s p *
        homogeneousComponent (k - s) q := by
  have hp : p = ∑ v ∈ p.support, monomial v (p.coeff v) := MvPolynomial.as_sum p
  nth_rewrite 1 [hp]
  rw [Finset.sum_mul, map_sum]
  rw [Finset.sum_congr rfl (fun m _ => homogeneousComponent_mul_monomial m (p.coeff m) q k)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← Finset.sum_mul, ← map_sum, ← hp]

/-- A homogeneous polynomial of degree different from `k` has zero `k`-component. -/
theorem homogeneousComponent_eq_zero_of_isHomogeneous {p : MvPolynomial σ R} {m : ℕ}
    (hp : p.IsHomogeneous m) {k : ℕ} (h : m ≠ k) : homogeneousComponent k p = 0 := by
  rw [homogeneousComponent_of_mem (m := k) hp]
  simp [Ne.symm h]

/-- Multiplying by a form of degree `a` shifts the `b`-component to the `(a+b)`-component. -/
theorem homogeneousComponent_mul_homogeneous {p q : MvPolynomial σ R} {a b k : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (h : a + b = k) :
    homogeneousComponent k (p * q) = p * q := by
  subst k
  exact homogeneousComponent_eq_self (hp.mul hq)

end HComp

end Sergeev

/-! ## The multiplication gates and the argument polynomials of a circuit -/

namespace ArithCircuit2

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000

variable {R : Type u} [CommRing R] {N m : ℕ}

theorem mulCount_eq_card (c : ArithCircuit2 R N m) :
    c.mulCount = Fintype.card {g : Fin c.size // c.gate g = ArithOp2.mul} := by
  classical
  rw [ArithCircuit2.mulCount, ArithCircuit2.countGates]
  symm
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : c.gate j = ArithOp2.mul
  · simp [h, ArithOp2.isMul]
  · have his : ArithOp2.isMul (c.gate j) = false := by
      cases hg : c.gate j <;> simp_all [ArithOp2.isMul]
    simp [h, his]

/-- The indexing equivalence between `Fin c.mulCount` and the multiplication gates of `c`. -/
noncomputable def mulGateEquiv (c : ArithCircuit2 R N m) :
    Fin c.mulCount ≃ {g : Fin c.size // c.gate g = ArithOp2.mul} := by
  classical
  exact (Fintype.equivFinOfCardEq c.mulCount_eq_card.symm).symm

/-- The `j`-th nonscalar multiplication gate of a circuit, in the order of computation. -/
noncomputable def mulGate (c : ArithCircuit2 R N m) (j : Fin c.mulCount) : Fin c.size :=
  (c.mulGateEquiv j).1

theorem gate_mulGate (c : ArithCircuit2 R N m) (j : Fin c.mulCount) :
    c.gate (c.mulGate j) = ArithOp2.mul :=
  (c.mulGateEquiv j).2

theorem mulGate_injective (c : ArithCircuit2 R N m) : Function.Injective c.mulGate := by
  intro i j h
  have h' : c.mulGateEquiv i = c.mulGateEquiv j := Subtype.ext h
  exact c.mulGateEquiv.injective h'

theorem exists_mulGate (c : ArithCircuit2 R N m) {g : Fin c.size} (h : c.gate g = ArithOp2.mul) :
    ∃ j : Fin c.mulCount, c.mulGate j = g := by
  obtain ⟨j, hj⟩ := c.mulGateEquiv.surjective ⟨g, h⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- The polynomial computed at the `t`-th argument wire of gate `j`. -/
noncomputable def argPoly (c : ArithCircuit2 R N m) (j : Fin c.size) (t : Fin 2) :
    MvPolynomial (Fin N) R :=
  Sum.elim (fun a : Fin N => (MvPolynomial.X a : MvPolynomial (Fin N) R))
    (fun g : Fin j.val => c.nodePoly ⟨g.val, lt_trans g.isLt j.isLt⟩) (c.args j t)

@[simp] theorem argPoly_inl (c : ArithCircuit2 R N m) (j : Fin c.size) (t : Fin 2)
    (a : Fin N) (h : c.args j t = Sum.inl a) : c.argPoly j t = MvPolynomial.X a := by
  rw [ArithCircuit2.argPoly, h]; rfl

@[simp] theorem argPoly_inr (c : ArithCircuit2 R N m) (j : Fin c.size) (t : Fin 2)
    (g : Fin j.val) (h : c.args j t = Sum.inr g) :
    c.argPoly j t = c.nodePoly ⟨g.val, lt_trans g.isLt j.isLt⟩ := by
  rw [ArithCircuit2.argPoly, h]; rfl

/-- The polynomial at a gate is the gate operation applied to the argument polynomials. -/
theorem nodePoly_eq_polyEval (c : ArithCircuit2 R N m) (j : Fin c.size) :
    c.nodePoly j = (c.gate j).polyEval (fun t => c.argPoly j t) := by
  rw [nodePoly_eq']
  congr 1
  funext t
  rw [ArithCircuit2.argPoly]
  cases hh : c.args j t with
  | inl a => rfl
  | inr g => exact congrArg c.nodePoly (Fin.ext rfl)

end ArithCircuit2

section DegreeTools

variable {σ : Type*} {R : Type*} [CommRing R]

theorem totalDegree_neg (p : MvPolynomial σ R) : (-p).totalDegree = p.totalDegree := by
  have h1 : (-p).totalDegree ≤ p.totalDegree := by
    have := MvPolynomial.totalDegree_smul_le (-1 : R) p
    simpa using this
  have h2 : p.totalDegree ≤ (-p).totalDegree := by
    have := MvPolynomial.totalDegree_smul_le (-1 : R) (-p)
    simpa using this
  omega

theorem totalDegree_sub_le (p q : MvPolynomial σ R) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans (le_of_eq ?_)
  rw [totalDegree_neg]

theorem C_mul_smul (a r : R) (p : MvPolynomial σ R) :
    (MvPolynomial.C a : MvPolynomial σ R) * (r • p) = (a * r) • p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← MvPolynomial.C_mul]

end DegreeTools

namespace ArithCircuit2

variable {R : Type u} [CommRing R] [Nontrivial R] {N m : ℕ}

/-- Every gate value is a linear combination of the values of the nonscalar multiplication gates
up to and including that gate, plus a polynomial of degree at most one. -/
theorem exists_linRep_node (c : ArithCircuit2 R N m) (g : Fin c.size) :
    ∃ (α : Fin c.size → R) (ℓ : MvPolynomial (Fin N) R),
      ℓ.totalDegree ≤ 1 ∧
      c.nodePoly g = (∑ i : Fin c.size, α i • c.nodePoly i) + ℓ ∧
      ∀ i, α i ≠ 0 → i.val ≤ g.val ∧ c.gate i = ArithOp2.mul := by
  suffices H : ∀ n, ∀ g : Fin c.size, g.val < n →
      ∃ (α : Fin c.size → R) (ℓ : MvPolynomial (Fin N) R),
        ℓ.totalDegree ≤ 1 ∧
        c.nodePoly g = (∑ i : Fin c.size, α i • c.nodePoly i) + ℓ ∧
        ∀ i, α i ≠ 0 → i.val ≤ g.val ∧ c.gate i = ArithOp2.mul from
    H (g.val + 1) g (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro g h; omega
  | succ n ih =>
    intro g hg
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hlt | heq
    · exact ih g hlt
    have harg : ∀ t : Fin 2, ∃ (α : Fin c.size → R) (ℓ : MvPolynomial (Fin N) R),
        ℓ.totalDegree ≤ 1 ∧ c.argPoly g t = (∑ i : Fin c.size, α i • c.nodePoly i) + ℓ ∧
        ∀ i, α i ≠ 0 → i.val < g.val ∧ c.gate i = ArithOp2.mul := by
      intro t
      cases hh : c.args g t with
      | inl a =>
          refine ⟨0, MvPolynomial.X a, ?_, ?_, ?_⟩
          · simpa using MvPolynomial.totalDegree_X (σ := Fin N) (R := R) a
          · rw [argPoly_inl c g t a hh]; simp
          · intro i hi; simp at hi
      | inr g' =>
          have hlt' : (⟨g'.val, lt_trans g'.isLt g.isLt⟩ : Fin c.size).val < n := by
            show g'.val < n
            omega
          obtain ⟨α, ℓ, hdeg, hrep, hsupp⟩ := ih ⟨g'.val, lt_trans g'.isLt g.isLt⟩ hlt'
          exact ⟨α, ℓ, hdeg, by rw [argPoly_inr c g t g' hh]; exact hrep,
            fun i hi => ⟨lt_of_le_of_lt (hsupp i hi).1 g'.isLt, (hsupp i hi).2⟩⟩
    obtain ⟨α₀, ℓ₀, hdeg₀, hrep₀, hsupp₀⟩ := harg 0
    obtain ⟨α₁, ℓ₁, hdeg₁, hrep₁, hsupp₁⟩ := harg 1
    cases hop : c.gate g with
    | add =>
        refine ⟨fun i => α₀ i + α₁ i, ℓ₀ + ℓ₁, ?_, ?_, ?_⟩
        · exact (MvPolynomial.totalDegree_add _ _).trans (max_le hdeg₀ hdeg₁)
        · rw [nodePoly_eq_polyEval c g, hop]
          simp only [ArithOp2.polyEval]
          rw [hrep₀, hrep₁]
          simp only [add_smul, Finset.sum_add_distrib]
          abel
        · intro i hi
          rcases eq_or_ne (α₀ i) 0 with h0 | h0
          · have h1 : α₁ i ≠ 0 := by
              intro h1; exact hi (by simp [h0, h1])
            exact ⟨le_of_lt (hsupp₁ i h1).1, (hsupp₁ i h1).2⟩
          · exact ⟨le_of_lt (hsupp₀ i h0).1, (hsupp₀ i h0).2⟩
    | sub =>
        refine ⟨fun i => α₀ i - α₁ i, ℓ₀ - ℓ₁, ?_, ?_, ?_⟩
        · exact (totalDegree_sub_le ℓ₀ ℓ₁).trans (max_le hdeg₀ hdeg₁)
        · rw [nodePoly_eq_polyEval c g, hop]
          simp only [ArithOp2.polyEval]
          rw [hrep₀, hrep₁]
          simp only [sub_smul, Finset.sum_sub_distrib]
          abel
        · intro i hi
          rcases eq_or_ne (α₀ i) 0 with h0 | h0
          · have h1 : α₁ i ≠ 0 := by
              intro h1; exact hi (by simp [h0, h1])
            exact ⟨le_of_lt (hsupp₁ i h1).1, (hsupp₁ i h1).2⟩
          · exact ⟨le_of_lt (hsupp₀ i h0).1, (hsupp₀ i h0).2⟩
    | smul a =>
        refine ⟨fun i => a * α₀ i, MvPolynomial.C a * ℓ₀, ?_, ?_, ?_⟩
        · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
          rw [MvPolynomial.totalDegree_C]
          omega
        · rw [nodePoly_eq_polyEval c g, hop]
          simp only [ArithOp2.polyEval]
          rw [hrep₀, mul_add, Finset.mul_sum]
          refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) rfl
          exact C_mul_smul a (α₀ i) (c.nodePoly i)
        · intro i hi
          have h0 : α₀ i ≠ 0 := fun h0 => hi (by simp [h0])
          exact ⟨le_of_lt (hsupp₀ i h0).1, (hsupp₀ i h0).2⟩
    | const a =>
        refine ⟨0, MvPolynomial.C a, ?_, ?_, ?_⟩
        · simp
        · rw [nodePoly_eq_polyEval c g, hop]
          simp only [ArithOp2.polyEval]
          simp
        · intro i hi; simp at hi
    | mul =>
        refine ⟨fun i => if i = g then 1 else 0, 0, by simp, ?_, ?_⟩
        · rw [Finset.sum_eq_single g]
          · rw [nodePoly_eq_polyEval c g, hop]
            simp [ArithOp2.polyEval]
          · intro b _ hb; simp [hb]
          · intro h; exact absurd (Finset.mem_univ g) h
        · intro i hi
          by_cases hig : i = g
          · subst hig; exact ⟨le_rfl, hop⟩
          · simp [hig] at hi

/-- The polynomial at an argument wire is a linear combination of *strictly earlier* nonscalar
multiplication gates, plus a polynomial of degree at most one. -/
theorem exists_linRep_arg (c : ArithCircuit2 R N m) (j : Fin c.size) (t : Fin 2) :
    ∃ (α : Fin c.size → R) (ℓ : MvPolynomial (Fin N) R),
      ℓ.totalDegree ≤ 1 ∧
      c.argPoly j t = (∑ i : Fin c.size, α i • c.nodePoly i) + ℓ ∧
      ∀ i, α i ≠ 0 → i.val < j.val ∧ c.gate i = ArithOp2.mul := by
  cases hh : c.args j t with
  | inl a =>
      refine ⟨0, MvPolynomial.X a, ?_, ?_, ?_⟩
      · simpa using MvPolynomial.totalDegree_X (σ := Fin N) (R := R) a
      · rw [ArithCircuit2.argPoly_inl c j t a hh]; simp
      · intro i hi; simp at hi
  | inr g =>
      obtain ⟨α, ℓ, hdeg, hrep, hsupp⟩ := c.exists_linRep_node ⟨g.val, lt_trans g.isLt j.isLt⟩
      exact ⟨α, ℓ, hdeg, by rw [ArithCircuit2.argPoly_inr c j t g hh]; exact hrep,
        fun i hi => ⟨lt_of_le_of_lt (hsupp i hi).1 g.isLt, (hsupp i hi).2⟩⟩

end ArithCircuit2

namespace Sergeev

section LowHigh

variable {R : Type u} [CommRing R] {N : ℕ}

/-- The sum of the homogeneous components of `p` of degree `< h`. -/
noncomputable def lowPart (h : ℕ) (p : MvPolynomial (Fin N) R) : MvPolynomial (Fin N) R :=
  ∑ s ∈ Finset.range h, MvPolynomial.homogeneousComponent s p

/-- The sum of the homogeneous components of `p` of degree `≥ h`. -/
noncomputable def hiPart (h : ℕ) (p : MvPolynomial (Fin N) R) : MvPolynomial (Fin N) R :=
  p - lowPart h p

theorem homogeneousComponent_lowPart {h s : ℕ} (p : MvPolynomial (Fin N) R) :
    MvPolynomial.homogeneousComponent s (lowPart h p) =
      if s < h then MvPolynomial.homogeneousComponent s p else 0 := by
  rw [lowPart, map_sum]
  split_ifs with hs
  · refine (Finset.sum_eq_single s ?_ ?_).trans ?_
    · intro b _ hb
      rw [MvPolynomial.homogeneousComponent_of_mem
        (MvPolynomial.homogeneousComponent_isHomogeneous b p)]
      simp [show s ≠ b from fun h => hb h.symm]
    · intro h; exact absurd (Finset.mem_range.2 hs) h
    · rw [MvPolynomial.homogeneousComponent_eq_self
        (MvPolynomial.homogeneousComponent_isHomogeneous s p)]
  · refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_range] at hb
    rw [MvPolynomial.homogeneousComponent_of_mem
      (MvPolynomial.homogeneousComponent_isHomogeneous b p)]
    split_ifs with hsb
    · omega
    · rfl

theorem homogeneousComponent_hiPart {h s : ℕ} (p : MvPolynomial (Fin N) R) :
    MvPolynomial.homogeneousComponent s (hiPart h p) =
      if s < h then 0 else MvPolynomial.homogeneousComponent s p := by
  rw [hiPart, map_sub, homogeneousComponent_lowPart]
  split_ifs with hs
  · simp [hs]
  · simp [hs]

theorem lowPart_add_hiPart (h : ℕ) (p : MvPolynomial (Fin N) R) :
    lowPart h p + hiPart h p = p := by
  rw [hiPart]; abel

theorem lowPart_eq_self_of_totalDegree_lt {h : ℕ} {p : MvPolynomial (Fin N) R}
    (hp : p.totalDegree < h) : lowPart h p = p := by
  have hsum : p = ∑ s ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent s p :=
    (MvPolynomial.sum_homogeneousComponent (φ := p)).symm
  rw [lowPart]
  conv_rhs => rw [hsum]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro s hs hs2
    rw [Finset.mem_range] at hs2
    exact MvPolynomial.homogeneousComponent_eq_zero s p (by omega)

theorem hiPart_eq_zero_of_totalDegree_lt {h : ℕ} {p : MvPolynomial (Fin N) R}
    (hp : p.totalDegree < h) : hiPart h p = 0 := by
  rw [hiPart, lowPart_eq_self_of_totalDegree_lt hp, sub_self]

theorem lowPart_add (h : ℕ) (p q : MvPolynomial (Fin N) R) :
    lowPart h (p + q) = lowPart h p + lowPart h q := by
  rw [lowPart, lowPart, lowPart, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => map_add _ _ _

theorem lowPart_smul (h : ℕ) (a : R) (p : MvPolynomial (Fin N) R) :
    lowPart h (a • p) = a • lowPart h p := by
  rw [lowPart, lowPart, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => map_smul _ a p

theorem lowPart_sum {ι : Type*} (h : ℕ) (s : Finset ι) (f : ι → MvPolynomial (Fin N) R) :
    lowPart h (∑ i ∈ s, f i) = ∑ i ∈ s, lowPart h (f i) := by
  simp only [lowPart, map_sum]
  rw [Finset.sum_comm]

theorem hiPart_add (h : ℕ) (p q : MvPolynomial (Fin N) R) :
    hiPart h (p + q) = hiPart h p + hiPart h q := by
  rw [hiPart, hiPart, hiPart, lowPart_add]; abel

theorem hiPart_smul (h : ℕ) (a : R) (p : MvPolynomial (Fin N) R) :
    hiPart h (a • p) = a • hiPart h p := by
  rw [hiPart, hiPart, lowPart_smul, smul_sub]

theorem hiPart_sum {ι : Type*} (h : ℕ) (s : Finset ι) (f : ι → MvPolynomial (Fin N) R) :
    hiPart h (∑ i ∈ s, f i) = ∑ i ∈ s, hiPart h (f i) := by
  rw [hiPart, lowPart_sum, ← Finset.sum_sub_distrib]
  rfl

/-- The three-region decomposition of the `k`-th component of a product. -/
theorem homogeneousComponent_mul_split {h k : ℕ} (hk : k ≤ 2 * h - 1)
    (p q : MvPolynomial (Fin N) R) :
    MvPolynomial.homogeneousComponent k (p * q) =
      (∑ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
          MvPolynomial.homogeneousComponent s p *
            MvPolynomial.homogeneousComponent (k - s) (lowPart h q))
      + (∑ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
          MvPolynomial.homogeneousComponent s p *
            MvPolynomial.homogeneousComponent (k - s) (hiPart h q))
      + (∑ s ∈ (Finset.range (k + 1)).filter (fun s => ¬ s < h),
          MvPolynomial.homogeneousComponent s p *
            MvPolynomial.homogeneousComponent (k - s) q) := by
  rw [homogeneousComponent_mul,
    ← Finset.sum_filter_add_sum_filter_not (Finset.range (k + 1)) (fun s => s < h)
      (fun s => MvPolynomial.homogeneousComponent s p *
        MvPolynomial.homogeneousComponent (k - s) q)]
  congr 1
  have hsplit : ∀ s : ℕ, MvPolynomial.homogeneousComponent s p *
      MvPolynomial.homogeneousComponent (k - s) q =
      MvPolynomial.homogeneousComponent s p *
        MvPolynomial.homogeneousComponent (k - s) (lowPart h q) +
      MvPolynomial.homogeneousComponent s p *
        MvPolynomial.homogeneousComponent (k - s) (hiPart h q) := by
    intro s
    have hq : MvPolynomial.homogeneousComponent (k - s) q =
        MvPolynomial.homogeneousComponent (k - s) (lowPart h q) +
          MvPolynomial.homogeneousComponent (k - s) (hiPart h q) := by
      conv_lhs => rw [← lowPart_add_hiPart h q]
      rw [map_add]
    rw [hq, mul_add]
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib]

/-- The first region of the decomposition is the corresponding component of the product of the
low parts. -/
theorem sum_filter_lowPart_eq {h k : ℕ} (hk : k ≤ 2 * h - 1)
    (p q : MvPolynomial (Fin N) R) :
    (∑ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
        MvPolynomial.homogeneousComponent s p *
          MvPolynomial.homogeneousComponent (k - s) (lowPart h q))
      = MvPolynomial.homogeneousComponent k (lowPart h p * lowPart h q) := by
  have hlhs : ∀ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
      MvPolynomial.homogeneousComponent s p = MvPolynomial.homogeneousComponent s (lowPart h p) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [homogeneousComponent_lowPart, if_pos hs.2]
  have hlhs2 : (∑ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
        MvPolynomial.homogeneousComponent s p *
          MvPolynomial.homogeneousComponent (k - s) (lowPart h q))
      = ∑ s ∈ (Finset.range (k + 1)).filter (fun s => s < h),
          MvPolynomial.homogeneousComponent s (lowPart h p) *
            MvPolynomial.homogeneousComponent (k - s) (lowPart h q) :=
    Finset.sum_congr rfl fun s hs => by rw [hlhs s hs]
  rw [hlhs2, homogeneousComponent_mul]
  refine Finset.sum_subset (s₁ := (Finset.range (k + 1)).filter (fun s => s < h))
    (s₂ := Finset.range (k + 1))
    (f := fun s => MvPolynomial.homogeneousComponent s (lowPart h p) *
      MvPolynomial.homogeneousComponent (k - s) (lowPart h q)) ?_ ?_
  · exact Finset.filter_subset (fun s => s < h) (Finset.range (k + 1))
  · intro s hs hsnot
    have hsh : ¬ s < h := by
      intro hc
      exact hsnot (Finset.mem_filter.2 ⟨hs, hc⟩)
    rw [homogeneousComponent_lowPart]
    rw [if_neg hsh]
    exact zero_mul _

end LowHigh

end Sergeev

/-! ## The ambient span of the degree-`k` components, and the induction of part I -/

namespace ArithCircuit2

open MvPolynomial Sergeev

variable {R : Type u} [CommRing R] [Nontrivial R] {N m : ℕ}

/-- The low part of the `t`-th argument polynomial of gate `i`. -/
noncomputable def lowArg (c : ArithCircuit2 R N m) (h : ℕ) (i : Fin c.size) (t : Fin 2) :
    MvPolynomial (Fin N) R :=
  lowPart h (c.argPoly i t)

/-- `v_{j,k}`: the `k`-th component of the product of the low parts of the two arguments of the
`j`-th nonscalar multiplication gate. -/
noncomputable def vPoly (c : ArithCircuit2 R N m) (h : ℕ) (j : Fin c.mulCount) (k : ℕ) :
    MvPolynomial (Fin N) R :=
  MvPolynomial.homogeneousComponent k (c.lowArg h (c.mulGate j) 0 * c.lowArg h (c.mulGate j) 1)

/-- The ambient set of degree-`k` component shapes available after the multiplication gates with
index `< G`. -/
noncomputable def ambSet (c : ArithCircuit2 R N m) (h k G : ℕ) : Set (MvPolynomial (Fin N) R) :=
  {q | ∃ (j : Fin c.mulCount) (t : ℕ), (c.mulGate j).val < G ∧ h ≤ t ∧ t ≤ k ∧
      ∃ K : MvPolynomial (Fin N) R, K.IsHomogeneous (k - t) ∧ q = K * c.vPoly h j t}

/-- The submodule generated by the inputs, the constant `1` and the values of the gates before
`G`. -/
noncomputable def gateSpan (c : ArithCircuit2 R N m) (G : ℕ) : Submodule R (MvPolynomial (Fin N) R) :=
  Submodule.span R ({1} ∪ (Set.range (fun i : Fin N => (MvPolynomial.X i : MvPolynomial (Fin N) R))
    ∪ {q | ∃ j : Fin c.size, j.val < G ∧ q = c.nodePoly j}))

theorem ambSet_mono (c : ArithCircuit2 R N m) (h k G G' : ℕ) (hGG' : G ≤ G') : c.ambSet h k G ⊆ c.ambSet h k G' := by
  rintro q ⟨j, t, hj, ht1, ht2, K, hK, rfl⟩
  exact ⟨j, t, lt_of_lt_of_le hj hGG', ht1, ht2, K, hK, rfl⟩

theorem vPoly_mem_ambSet (c : ArithCircuit2 R N m) (h k G : ℕ) (j : Fin c.mulCount) (hj : (c.mulGate j).val < G)
    (hk : h ≤ k) : c.vPoly h j k ∈ c.ambSet h k G :=
  ⟨j, k, hj, hk, le_rfl, 1,
    by simpa using MvPolynomial.isHomogeneous_one (σ := Fin N) (R := R),
    (one_mul (c.vPoly h j k)).symm⟩

/-- Multiplying a member of the ambient span at level `s` by a form of degree `k - s` lands in the
ambient span at level `k`. -/
theorem amb_mul_homogeneous (c : ArithCircuit2 R N m) {h k s G : ℕ} (hsk : s ≤ k)
    {K : MvPolynomial (Fin N) R} (hK : K.IsHomogeneous (k - s)) {p : MvPolynomial (Fin N) R}
    (hp : p ∈ Submodule.span R (c.ambSet h s G)) :
    K * p ∈ Submodule.span R (c.ambSet h k G) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, t, hj, ht1, ht2, K', hK', rfl⟩ := hx
      refine Submodule.subset_span ⟨j, t, hj, ht1, ht2.trans hsk, K * K', ?_, ?_⟩
      · have hd : (k - s) + (s - t) = k - t := by omega
        exact hd ▸ hK.mul hK'
      · rw [mul_assoc]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih

theorem mem_span_ambSet_mono (c : ArithCircuit2 R N m) {h k G G' : ℕ} (hGG' : G ≤ G')
    {x : MvPolynomial (Fin N) R} (hx : x ∈ Submodule.span R (c.ambSet h k G)) :
    x ∈ Submodule.span R (c.ambSet h k G') :=
  Submodule.span_mono (c.ambSet_mono h k G G' hGG') hx

theorem argPoly_mem_gateSpan (c : ArithCircuit2 R N m) (j : Fin c.size) (t : Fin 2) :
    c.argPoly j t ∈ c.gateSpan j.val := by
  cases hh : c.args j t with
  | inl a =>
      rw [argPoly_inl c j t a hh]
      exact Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩))
  | inr g =>
      rw [argPoly_inr c j t g hh]
      exact Submodule.subset_span
        (Or.inr (Or.inr ⟨⟨g.val, lt_trans g.isLt j.isLt⟩, g.isLt, rfl⟩))

theorem nodePoly_mem_gateSpan (c : ArithCircuit2 R N m) (j : Fin c.size) : c.nodePoly j ∈ c.gateSpan (j.val + 1) :=
  Submodule.subset_span (Or.inr (Or.inr ⟨j, Nat.lt_succ_self _, rfl⟩))

theorem gateSpan_mono (c : ArithCircuit2 R N m) {G G' : ℕ} (h : G ≤ G') : c.gateSpan G ≤ c.gateSpan G' := by
  refine Submodule.span_mono ?_
  rintro q (hq | hq | ⟨j, hj, rfl⟩)
  · exact Or.inl hq
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr ⟨j, lt_of_lt_of_le hj h, rfl⟩)

/-- A component of the polynomial at an argument wire lies in the ambient span, provided the gate
is not later than `G`. -/
theorem hcomp_argPoly_mem (c : ArithCircuit2 R N m) {h d s G : ℕ} (hh : 2 ≤ h) (hs1 : h ≤ s)
    (hs2 : s ≤ d)
    (j : Fin c.size) (t : Fin 2) (hj : j.val ≤ G)
    (IH : ∀ (s : ℕ), h ≤ s → s ≤ d → ∀ (jj : Fin c.size), jj.val < G →
      MvPolynomial.homogeneousComponent s (c.nodePoly jj) ∈ Submodule.span R (c.ambSet h s G)) :
    MvPolynomial.homogeneousComponent s (c.argPoly j t) ∈ Submodule.span R (c.ambSet h s G) := by
  cases hh : c.args j t with
  | inl a =>
      rw [argPoly_inl c j t a hh]
      have : MvPolynomial.homogeneousComponent s (MvPolynomial.X a : MvPolynomial (Fin N) R) = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [MvPolynomial.totalDegree_X]
        omega
      rw [this]; exact Submodule.zero_mem _
  | inr g =>
      rw [argPoly_inr c j t g hh]
      exact IH s hs1 hs2 _ (lt_of_lt_of_le g.isLt hj)


/-- Multiplying by a form of degree `a` extracts the `b`-component, where `a + b = k`. -/
theorem homogeneousComponent_mul_component {h k a b : ℕ} {K : MvPolynomial (Fin N) R}
    (hK : K.IsHomogeneous a) (p : MvPolynomial (Fin N) R) (hb : b ≤ k) (hab : a + b = k) :
    homogeneousComponent k (K * p) = K * homogeneousComponent b p := by
  rw [homogeneousComponent_mul]
  rw [Finset.sum_eq_single a]
  · have hka : k - a = b := by omega
    rw [hka, homogeneousComponent_eq_self hK]
  · intro s _ hs
    have : homogeneousComponent s K = 0 :=
      homogeneousComponent_eq_zero_of_isHomogeneous hK (by omega)
    rw [this, zero_mul]
  · intro hge
    exact absurd (Finset.mem_range.2 (by omega)) hge

/-- Right multiplication version of `amb_mul_homogeneous`. -/
theorem amb_mul_homogeneous_right (c : ArithCircuit2 R N m) {h k s G : ℕ} (hsk : s ≤ k)
    {K : MvPolynomial (Fin N) R} (hK : K.IsHomogeneous (k - s)) {p : MvPolynomial (Fin N) R}
    (hp : p ∈ Submodule.span R (c.ambSet h s G)) :
    p * K ∈ Submodule.span R (c.ambSet h k G) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, t, hj, ht1, ht2, K', hK', rfl⟩ := hx
      refine Submodule.subset_span ⟨j, t, hj, ht1, ht2.trans hsk, K' * K, ?_, ?_⟩
      · have hd : (s - t) + (k - s) = k - t := by omega
        exact hd ▸ hK'.mul hK
      · rw [mul_assoc, mul_comm (c.vPoly h j t) K, ← mul_assoc]
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [add_mul]; exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

/-- The multiplication-gate step of the induction of part I of `cubic_th1.pdf`: the `k`-component
of the value of a nonscalar multiplication gate lies in the ambient span at level `k`, generated by
the `v_{i,t}` of the gates before it and the `v_{j,k}` of the gate itself. -/
theorem hcomp_mul_step (c : ArithCircuit2 R N m) {h d k : ℕ} (hk1 : h ≤ k)
    (hk2 : k ≤ 2 * h - 1) (hk : k ≤ d) (j : Fin c.mulCount)
    (hp : ∀ s, h ≤ s → s ≤ d →
      MvPolynomial.homogeneousComponent s (c.argPoly (c.mulGate j) 0) ∈
        Submodule.span R (c.ambSet h s (c.mulGate j).val))
    (hq : ∀ s, h ≤ s → s ≤ d →
      MvPolynomial.homogeneousComponent s (c.argPoly (c.mulGate j) 1) ∈
        Submodule.span R (c.ambSet h s (c.mulGate j).val)) :
    MvPolynomial.homogeneousComponent k (c.nodePoly (c.mulGate j)) ∈
      Submodule.span R (c.ambSet h k ((c.mulGate j).val + 1)) := by
  have hmul : c.nodePoly (c.mulGate j)
      = c.argPoly (c.mulGate j) 0 * c.argPoly (c.mulGate j) 1 := by
    rw [nodePoly_eq_polyEval, c.gate_mulGate]
    simp [ArithOp2.polyEval]
  rw [hmul, homogeneousComponent_mul_split hk2]
  have mono : ∀ x : MvPolynomial (Fin N) R,
      x ∈ Submodule.span R (c.ambSet h k (c.mulGate j).val) →
      x ∈ Submodule.span R (c.ambSet h k ((c.mulGate j).val + 1)) :=
    fun x hx => c.mem_span_ambSet_mono (Nat.le_succ _) hx
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · rw [sum_filter_lowPart_eq hk2]
    exact Submodule.subset_span (c.vPoly_mem_ambSet h k _ j (Nat.lt_succ_self _) hk1)
  · apply Submodule.sum_mem
    intro s hs
    rw [Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hsk, hsh⟩ := hs
    rw [homogeneousComponent_hiPart]
    split_ifs with hks
    · rw [mul_zero]; exact Submodule.zero_mem _
    · have hs1 : h ≤ k - s := by omega
      have hs2 : k - s ≤ d := by omega
      have hK : (MvPolynomial.homogeneousComponent s (c.argPoly (c.mulGate j) 0)).IsHomogeneous
          (k - (k - s)) := by
        rw [show k - (k - s) = s by omega]
        exact MvPolynomial.homogeneousComponent_isHomogeneous (n := s) (φ := _)
      exact mono _ (amb_mul_homogeneous c (k := k) (s := k - s) (G := (c.mulGate j).val)
        (by omega) hK (hq (k - s) hs1 hs2))
  · apply Submodule.sum_mem
    intro s hs
    rw [Finset.mem_filter, Finset.mem_range] at hs
    obtain ⟨hsk, hsh⟩ := hs
    have hs1 : h ≤ s := by omega
    have hs2 : s ≤ d := by omega
    have hK : (MvPolynomial.homogeneousComponent (k - s) (c.argPoly (c.mulGate j) 1)).IsHomogeneous
        (k - s) := MvPolynomial.homogeneousComponent_isHomogeneous (n := k - s) (φ := _)
    have h := amb_mul_homogeneous c (k := k) (s := s) (G := (c.mulGate j).val) (by omega) hK
      (hp s hs1 hs2)
    rw [mul_comm]
    exact mono _ h


/-- **Part I of `cubic_th1.pdf`.**  Fix `h` with `2 ≤ h` and `d ≤ 2h - 1`.  For every gate `g` of
the circuit and every `k` with `h ≤ k ≤ d`, the degree-`k` homogeneous component of the value of `g`
lies in the ambient span generated by the `v_{i,t}` of the nonscalar multiplication gates that come
before `g` (indices `< G`, where `g.val < G`). -/
theorem graded_mem (c : ArithCircuit2 R N m) {h d : ℕ} (hh : 2 ≤ h) (hd : d ≤ 2 * h - 1) :
    ∀ G, ∀ g : Fin c.size, g.val < G → ∀ k, h ≤ k → k ≤ d →
      MvPolynomial.homogeneousComponent k (c.nodePoly g) ∈ Submodule.span R (c.ambSet h k G) := by
  intro G
  induction G with
  | zero => intro g hg; omega
  | succ G ih =>
    intro g hg k hk1 hk2
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hg) with hlt | heq
    · exact c.mem_span_ambSet_mono (Nat.le_succ G) (ih g hlt k hk1 hk2)
    · have harg : ∀ s, h ≤ s → s ≤ d → ∀ t : Fin 2,
          MvPolynomial.homogeneousComponent s (c.argPoly g t) ∈
            Submodule.span R (c.ambSet h s G) :=
        fun s hs1 hs2 t =>
          c.hcomp_argPoly_mem hh hs1 hs2 g t (le_of_eq heq)
            (fun s hs1 hs2 jj hj => ih jj hj s hs1 hs2)
      have hmono : ∀ {k : ℕ} {x : MvPolynomial (Fin N) R},
          x ∈ Submodule.span R (c.ambSet h k G) →
          x ∈ Submodule.span R (c.ambSet h k (G + 1)) :=
        fun hx => c.mem_span_ambSet_mono (Nat.le_succ G) hx
      cases hop : c.gate g with
      | add =>
        have hnode : c.nodePoly g = c.argPoly g 0 + c.argPoly g 1 := by
          rw [nodePoly_eq_polyEval, hop]; simp [ArithOp2.polyEval]
        rw [hnode, map_add]
        exact hmono (Submodule.add_mem _ (harg k hk1 hk2 0) (harg k hk1 hk2 1))
      | sub =>
        have hnode : c.nodePoly g = c.argPoly g 0 - c.argPoly g 1 := by
          rw [nodePoly_eq_polyEval, hop]; simp [ArithOp2.polyEval]
        rw [hnode, map_sub]
        exact hmono (Submodule.sub_mem _ (harg k hk1 hk2 0) (harg k hk1 hk2 1))
      | smul a =>
        have hnode : c.nodePoly g = MvPolynomial.C a * c.argPoly g 0 := by
          rw [nodePoly_eq_polyEval, hop]; simp [ArithOp2.polyEval]
        have hs : a • MvPolynomial.homogeneousComponent k (c.argPoly g 0) ∈
            Submodule.span R (c.ambSet h k G) := Submodule.smul_mem _ a (harg k hk1 hk2 0)
        rw [hnode, MvPolynomial.homogeneousComponent_C_mul]
        exact hmono (by rwa [MvPolynomial.smul_eq_C_mul] at hs)
      | const a =>
        have hnode : c.nodePoly g = MvPolynomial.C a := by
          rw [nodePoly_eq_polyEval, hop]; simp [ArithOp2.polyEval]
        have hzero : MvPolynomial.homogeneousComponent k (MvPolynomial.C a : MvPolynomial (Fin N) R) = 0 :=
          MvPolynomial.homogeneousComponent_eq_zero (n := k) (φ := (MvPolynomial.C a : MvPolynomial (Fin N) R))
            (by rw [MvPolynomial.totalDegree_C]; omega)
        rw [hnode, hzero]
        exact Submodule.zero_mem _
      | mul =>
        obtain ⟨j, hj⟩ : ∃ j : Fin c.mulCount, c.mulGate j = g := by
          refine ⟨c.mulGateEquiv.symm ⟨g, hop⟩, ?_⟩
          simp [mulGate, Equiv.apply_symm_apply]
        have hargj : ∀ s, h ≤ s → s ≤ d → ∀ t : Fin 2,
            MvPolynomial.homogeneousComponent s (c.argPoly (c.mulGate j) t) ∈
              Submodule.span R (c.ambSet h s (c.mulGate j).val) := by
          intro s hs1 hs2 t
          rw [hj, heq]
          exact harg s hs1 hs2 t
        have hres := c.hcomp_mul_step hk1 (by omega) hk2 j
          (fun s hs1 hs2 => hargj s hs1 hs2 0) (fun s hs1 hs2 => hargj s hs1 hs2 1)
        rw [hj, heq] at hres
        exact hres


theorem totalDegree_lowPart_le (h : ℕ) (p : MvPolynomial (Fin N) R) :
    (lowPart h p).totalDegree ≤ h - 1 := by
  rw [lowPart]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [Finset.mem_range] at hs
  exact (MvPolynomial.homogeneousComponent_isHomogeneous (n := s) (φ := p)).totalDegree_le.trans
    (by omega)

/-- **Part II of `cubic_th1.pdf`.**  Every element of the ambient span at level `d` is a sum of
shapes `(K_j · a_j · b_j)^{[d]}`, where `a_j`, `b_j` are the low parts of the arguments of the
`j`-th multiplication gate and `deg K_j ≤ d - h`. -/
theorem exists_repr_span (c : ArithCircuit2 R N m) {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    {x : MvPolynomial (Fin N) R} (hx : x ∈ Submodule.span R (c.ambSet h d c.size)) :
    ∃ K : Fin c.mulCount → MvPolynomial (Fin N) R,
      (∀ j, (K j).totalDegree ≤ d - h) ∧
      x = ∑ j, MvPolynomial.homogeneousComponent d
        (K j * c.lowArg h (c.mulGate j) 0 * c.lowArg h (c.mulGate j) 1) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, t, _, ht1, ht2, K', hK', rfl⟩ := hy
    refine ⟨fun j' => if j' = j then K' else 0, ?_, ?_⟩
    · intro j'
      dsimp only
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos rfl]
        exact hK'.totalDegree_le.trans (by omega)
      · rw [if_neg hj']
        simp
    · rw [Finset.sum_eq_single j]
      · dsimp only
        rw [if_pos rfl, mul_assoc,
          homogeneousComponent_mul_component (h := d) (k := d) (a := d - t) (b := t) hK' _ ht2 (by omega)]
        rfl
      · intro b _ hbj
        dsimp only
        rw [if_neg hbj, zero_mul, zero_mul, map_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
  | zero => exact ⟨0, fun j => by simp, by simp⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨Ky, hKy, hKy'⟩ := ihy
    obtain ⟨Kz, hKz, hKz'⟩ := ihz
    refine ⟨Ky + Kz, fun j => ?_, ?_⟩
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hKy j) (hKz j))
    · rw [hKy', hKz', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, add_mul, add_mul, map_add]
  | smul a y _ ih =>
    obtain ⟨Ky, hKy, hKy'⟩ := ih
    refine ⟨a • Ky, fun j => ?_, ?_⟩
    · exact (MvPolynomial.totalDegree_smul_le a (Ky j)).trans (hKy j)
    · rw [hKy', Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_mul_assoc, smul_mul_assoc, map_smul]

/-- The degree-`d` component of any polynomial computed by the circuit is a sum of shapes
`(K_j · a_j · b_j)^{[d]}` with `deg K_j ≤ d - h`. -/
theorem exists_repr (c : ArithCircuit2 R N m) {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    (o : Fin m) :
    ∃ K : Fin c.mulCount → MvPolynomial (Fin N) R,
      (∀ j, (K j).totalDegree ≤ d - h) ∧
      MvPolynomial.homogeneousComponent d (c.outPoly o) =
        ∑ j, MvPolynomial.homogeneousComponent d
          (K j * c.lowArg h (c.mulGate j) 0 * c.lowArg h (c.mulGate j) 1) := by
  cases ho : c.out o with
  | inl a =>
    refine ⟨0, fun j => by simp, ?_⟩
    have hX : c.outPoly o = (MvPolynomial.X a : MvPolynomial (Fin N) R) := by
      rw [ArithCircuit2.outPoly, ho]; rfl
    rw [hX, MvPolynomial.homogeneousComponent_eq_zero
      (n := d) (φ := (MvPolynomial.X a : MvPolynomial (Fin N) R)) (by
        rw [MvPolynomial.totalDegree_X]; omega)]
    simp
  | inr g =>
    have hnode : c.outPoly o = c.nodePoly g := by rw [ArithCircuit2.outPoly, ho]; rfl
    rw [hnode]
    exact c.exists_repr_span hd hh (c.graded_mem hh (le_of_eq hd) c.size g g.isLt d
      (by omega) le_rfl)

/-! ### Status of the induction

The induction of part I of `cubic_th1.pdf` is complete:

* `homogeneousComponent_mul_split`, `sum_filter_lowPart_eq`: the three-region decomposition of a
  degree-`k` component of a product (two components of degree `≥ h` cannot contribute to a
  component of degree `k ≤ 2h - 1`);
* `ambSet`, `amb_mul_homogeneous`, `amb_mul_homogeneous_right`: the ambient span of the `v_{j,t}`
  and its closure under multiplication by forms of complementary degree;
* `homogeneousComponent_mul_component`: the step extracting one component of a product with a
  form;
* `hcomp_argPoly_mem`: components of the argument polynomials lie in the ambient span;
* `hcomp_mul_step`: the multiplication-gate step;
* `graded_mem`: the induction over the gates — for every gate `g` and every `h ≤ k ≤ d ≤ 2h-1`,
  the `k`-component of the value of `g` lies in the ambient span generated by the multiplication
  gates before it;
* `exists_repr`, `exists_repr_pad`: the degree-`d` component of the output has the shape
  `∑_j (c_j · a_j · b_j)^{[d]}` with `deg c_j ≤ d - h` and `deg a_j, deg b_j < h`.
-/

end ArithCircuit2

namespace Sergeev

namespace Param

open MvPolynomial

variable {K : Type} [CommRing K] {n : ℕ}

noncomputable def monOf {k : ℕ} (s : Sym (Fin n) k) : Fin n →₀ ℕ :=
  (Sym.equivNatSum (Fin n) k s : Fin n →₀ ℕ)

lemma monOf_degree {k : ℕ} (s : Sym (Fin n) k) : (monOf s).degree = k :=
  (Sym.equivNatSum (Fin n) k s).2

abbrev MonoLt (n h : ℕ) := Σ k : Fin h, Sym (Fin n) k

noncomputable def monI {h : ℕ} (u : MonoLt n h) : Fin n →₀ ℕ := monOf u.2

lemma monI_degree {h : ℕ} (u : MonoLt n h) : (monI u).degree = u.1.val := monOf_degree u.2

lemma monI_injective {h : ℕ} : Function.Injective (monI (n := n) (h := h)) := by
  rintro ⟨k, s⟩ ⟨k', s'⟩ hEq
  have h1 : (monI (n := n) (h := h) ⟨k, s⟩).degree = (monI ⟨k', s'⟩).degree := by rw [hEq]
  rw [monI_degree, monI_degree] at h1
  have hk : k = k' := Fin.ext h1
  subst hk
  have hs : s = s' := by
    apply (Sym.equivNatSum (Fin n) k.val).injective
    exact Subtype.ext hEq
  rw [hs]

theorem as_sum_monomials {h : ℕ} {p : MvPolynomial (Fin n) K} (hp : p.totalDegree < h) :
    p = ∑ u : MonoLt n h, MvPolynomial.monomial (monI u) (p.coeff (monI u)) := by
  classical
  have hsub : p.support ⊆ Finset.univ.image (monI (n := n) (h := h)) := by
    intro m hm
    have hdeg : m.degree < h := (MvPolynomial.le_totalDegree hm).trans_lt hp
    refine Finset.mem_image.mpr ⟨⟨⟨m.degree, hdeg⟩,
      (Sym.equivNatSum (Fin n) m.degree).symm ⟨m, rfl⟩⟩, Finset.mem_univ _, ?_⟩
    simp [monI, monOf]
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [← Finset.sum_image (f := fun m => MvPolynomial.monomial m (p.coeff m))
    (g := monI (n := n) (h := h)) (fun x _ y _ hxy => monI_injective hxy)]
  have hzero : ∀ m ∈ Finset.univ.image (monI (n := n) (h := h)), m ∉ p.support →
      MvPolynomial.monomial m (p.coeff m) = 0 := by
    intro m _ hm
    rw [MvPolynomial.notMem_support_iff] at hm
    rw [hm, MvPolynomial.monomial_zero]
  exact Finset.sum_subset hsub hzero

/-- `map` of a ring hom commutes with taking homogeneous components. -/
theorem map_homogeneousComponent {L : Type*} [CommRing L] {σ : Type*}
    (f : K →+* L) (m : ℕ) (p : MvPolynomial σ K) :
    MvPolynomial.map f (MvPolynomial.homogeneousComponent m p)
      = MvPolynomial.homogeneousComponent m (MvPolynomial.map f p) := by
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent,
    MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_map]
  split_ifs with h
  · rfl
  · exact map_zero f

/-- The parameter index set: one coefficient per monomial of degree `< h`, for each of the three
polynomials attached to each of the `s` multiplication gates. -/
abbrev PIdx (n h s : ℕ) := Fin s × Fin 3 × MonoLt n h

/-- The generic polynomial with coefficients among the parameters. -/
noncomputable def genExpr {h s : ℕ} (j : Fin s) (u : Fin 3) :
    MvPolynomial (Fin n) (MvPolynomial (PIdx n h s) K) :=
  ∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (MvPolynomial.X (j, u, a))

noncomputable def formExpr {h d s : ℕ} : MvPolynomial (Fin n) (MvPolynomial (PIdx n h s) K) :=
  ∑ j : Fin s, MvPolynomial.homogeneousComponent d
    (genExpr (K := K) j 0 * genExpr (K := K) j 1 * genExpr (K := K) j 2)

noncomputable def phiExpr {h d s : ℕ} (m : Sym (Fin n) d) : MvPolynomial (PIdx n h s) K :=
  (formExpr (K := K) (h := h) (d := d) (s := s)).coeff (monOf m)

lemma eval_genExpr {h s : ℕ} (e : PIdx n h s → K) (j : Fin s) (u : Fin 3) :
    MvPolynomial.map (MvPolynomial.eval e) (genExpr (K := K) (h := h) (s := s) j u)
      = ∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, u, a)) := by
  rw [genExpr, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_X]

lemma eval_formExpr {h d s : ℕ} (e : PIdx n h s → K)
    (X₀ X₁ X₂ : Fin s → MvPolynomial (Fin n) K)
    (hX₀ : ∀ j, (X₀ j).totalDegree < h) (hX₁ : ∀ j, (X₁ j).totalDegree < h)
    (hX₂ : ∀ j, (X₂ j).totalDegree < h)
    (he₀ : ∀ (j : Fin s) (a : MonoLt n h), e (j, 0, a) = (X₀ j).coeff (monI a))
    (he₁ : ∀ (j : Fin s) (a : MonoLt n h), e (j, 1, a) = (X₁ j).coeff (monI a))
    (he₂ : ∀ (j : Fin s) (a : MonoLt n h), e (j, 2, a) = (X₂ j).coeff (monI a)) :
    MvPolynomial.map (MvPolynomial.eval e) (formExpr (K := K) (h := h) (d := d) (s := s))
      = ∑ j : Fin s, MvPolynomial.homogeneousComponent d (X₀ j * X₁ j * X₂ j) := by
  rw [formExpr, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h₀ : (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 0, a))) = X₀ j := by
    conv_lhs => rw [show (fun a : MonoLt n h => MvPolynomial.monomial (monI a) (e (j, 0, a)))
        = (fun a => MvPolynomial.monomial (monI a) ((X₀ j).coeff (monI a))) from by
      funext a; rw [he₀ j a]]
    exact (as_sum_monomials (K := K) (hX₀ j)).symm
  have h₁ : (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 1, a))) = X₁ j := by
    conv_lhs => rw [show (fun a : MonoLt n h => MvPolynomial.monomial (monI a) (e (j, 1, a)))
        = (fun a => MvPolynomial.monomial (monI a) ((X₁ j).coeff (monI a))) from by
      funext a; rw [he₁ j a]]
    exact (as_sum_monomials (K := K) (hX₁ j)).symm
  have h₂ : (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 2, a))) = X₂ j := by
    conv_lhs => rw [show (fun a : MonoLt n h => MvPolynomial.monomial (monI a) (e (j, 2, a)))
        = (fun a => MvPolynomial.monomial (monI a) ((X₂ j).coeff (monI a))) from by
      funext a; rw [he₂ j a]]
    exact (as_sum_monomials (K := K) (hX₂ j)).symm
  have hm : MvPolynomial.map (MvPolynomial.eval e)
        (genExpr (K := K) (h := h) (s := s) j 0 * genExpr (K := K) (h := h) (s := s) j 1
          * genExpr (K := K) (h := h) (s := s) j 2)
      = (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 0, a)))
        * (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 1, a)))
        * (∑ a : MonoLt n h, MvPolynomial.monomial (monI a) (e (j, 2, a))) := by
    rw [map_mul, map_mul, eval_genExpr, eval_genExpr, eval_genExpr]
  rw [map_homogeneousComponent, hm, h₀, h₁, h₂]

noncomputable def mkE {h s : ℕ} (Kf Af Bf : Fin s → MvPolynomial (Fin n) K) :
    PIdx n h s → K :=
  fun abc =>
    if abc.2.1 = 0 then (Kf abc.1).coeff (monI abc.2.2)
    else if abc.2.1 = 1 then (Af abc.1).coeff (monI abc.2.2)
    else (Bf abc.1).coeff (monI abc.2.2)

lemma mkE_zero {h s : ℕ} (Kf Af Bf : Fin s → MvPolynomial (Fin n) K) (j : Fin s)
    (a : MonoLt n h) : mkE Kf Af Bf (j, 0, a) = (Kf j).coeff (monI a) := by
  simp [mkE]

lemma mkE_one {h s : ℕ} (Kf Af Bf : Fin s → MvPolynomial (Fin n) K) (j : Fin s)
    (a : MonoLt n h) : mkE Kf Af Bf (j, 1, a) = (Af j).coeff (monI a) := by
  simp [mkE, show (1 : Fin 3) ≠ 0 by decide]

lemma mkE_two {h s : ℕ} (Kf Af Bf : Fin s → MvPolynomial (Fin n) K) (j : Fin s)
    (a : MonoLt n h) : mkE Kf Af Bf (j, 2, a) = (Bf j).coeff (monI a) := by
  simp [mkE, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]

theorem Fin.sum_univ_of_le {M : Type*} [AddCommMonoid M] {s' s : ℕ} (h : s' ≤ s)
    (F : Fin s → M) (hF : ∀ j : Fin s, s' ≤ j.val → F j = 0) :
    ∑ j : Fin s, F j = ∑ j : Fin s', F (Fin.castLE h j) := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  have h1 : (∑ i ∈ Finset.range s', if hi : i < s then F ⟨i, hi⟩ else 0)
      = ∑ i ∈ Finset.range s, if hi : i < s then F ⟨i, hi⟩ else 0 := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [Finset.mem_range] at hx hx'
      have hxs : s' ≤ x := by omega
      rw [dif_pos hx, hF ⟨x, hx⟩ hxs]
  rw [← h1]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  rw [dif_pos hi, dif_pos (lt_of_lt_of_le hi h)]
  congr 1

variable {R : Type} [CommRing R] [Nontrivial R] {N m : ℕ}

/-- The representation of the degree-`d` component, indexed by `Fin s` for any `s` at least the
number of multiplication gates. -/
theorem exists_repr_pad (c : ArithCircuit2 R N m) {h d s : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    (o : Fin m) (hmul : c.mulCount ≤ s) :
    ∃ K A B : Fin s → MvPolynomial (Fin N) R,
      (∀ j, (K j).totalDegree < h) ∧ (∀ j, (A j).totalDegree < h) ∧
        (∀ j, (B j).totalDegree < h) ∧
        MvPolynomial.homogeneousComponent d (c.outPoly o)
          = ∑ j : Fin s, MvPolynomial.homogeneousComponent d (K j * A j * B j) := by
  obtain ⟨K₀, hK₀, hsum⟩ := c.exists_repr hd hh o
  let A₀ : Fin c.mulCount → MvPolynomial (Fin N) R := fun j => c.lowArg h (c.mulGate j) 0
  let B₀ : Fin c.mulCount → MvPolynomial (Fin N) R := fun j => c.lowArg h (c.mulGate j) 1
  have hK₀' : ∀ j, (K₀ j).totalDegree < h := fun j => by
    have := hK₀ j
    omega
  have hA₀ : ∀ j, (A₀ j).totalDegree < h := fun j => by
    have := ArithCircuit2.totalDegree_lowPart_le h (c.argPoly (c.mulGate j) 0)
    show (lowPart h (c.argPoly (c.mulGate j) 0)).totalDegree < h
    omega
  have hB₀ : ∀ j, (B₀ j).totalDegree < h := fun j => by
    have := ArithCircuit2.totalDegree_lowPart_le h (c.argPoly (c.mulGate j) 1)
    show (lowPart h (c.argPoly (c.mulGate j) 1)).totalDegree < h
    omega
  let K : Fin s → MvPolynomial (Fin N) R :=
    fun j => if hj : j.val < c.mulCount then K₀ ⟨j.val, hj⟩ else 0
  let A : Fin s → MvPolynomial (Fin N) R :=
    fun j => if hj : j.val < c.mulCount then A₀ ⟨j.val, hj⟩ else 0
  let B : Fin s → MvPolynomial (Fin N) R :=
    fun j => if hj : j.val < c.mulCount then B₀ ⟨j.val, hj⟩ else 0
  have hK : ∀ j, (K j).totalDegree < h := by
    intro j
    by_cases hj : j.val < c.mulCount
    · simp only [K]
      rw [dif_pos hj]
      exact hK₀' ⟨j.val, hj⟩
    · simp only [K]
      rw [dif_neg hj]
      simp only [MvPolynomial.totalDegree_zero]
      omega
  have hA : ∀ j, (A j).totalDegree < h := by
    intro j
    by_cases hj : j.val < c.mulCount
    · simp only [A]
      rw [dif_pos hj]
      exact hA₀ ⟨j.val, hj⟩
    · simp only [A]
      rw [dif_neg hj]
      simp only [MvPolynomial.totalDegree_zero]
      omega
  have hB : ∀ j, (B j).totalDegree < h := by
    intro j
    by_cases hj : j.val < c.mulCount
    · simp only [B]
      rw [dif_pos hj]
      exact hB₀ ⟨j.val, hj⟩
    · simp only [B]
      rw [dif_neg hj]
      simp only [MvPolynomial.totalDegree_zero]
      omega
  refine ⟨K, A, B, hK, hA, hB, ?_⟩
  have hstep : ∀ j : Fin s, c.mulCount ≤ j.val →
      MvPolynomial.homogeneousComponent d (K j * A j * B j) = 0 := by
    intro j hj
    have h0 : K j = 0 := by
      simp only [K]
      rw [dif_neg (by omega)]
    have h1 : A j = 0 := by
      simp only [A]
      rw [dif_neg (by omega)]
    rw [h0, h1, zero_mul, zero_mul, map_zero]
  rw [hsum, Fin.sum_univ_of_le hmul _ hstep]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hKj : K (Fin.castLE hmul j) = K₀ j := by
    simp only [K]
    rw [dif_pos (show (Fin.castLE hmul j).val < c.mulCount from j.isLt)]
    congr 1
  have hAj : A (Fin.castLE hmul j) = A₀ j := by
    simp only [A]
    rw [dif_pos (show (Fin.castLE hmul j).val < c.mulCount from j.isLt)]
    congr 1
  have hBj : B (Fin.castLE hmul j) = B₀ j := by
    simp only [B]
    rw [dif_pos (show (Fin.castLE hmul j).val < c.mulCount from j.isLt)]
    congr 1
  rw [hKj, hAj, hBj]


variable [IsDomain K] [Infinite K]

/-! ### Steinitz's lemma

A self-contained copy of the argument of `MultcompPoly/Steinitz.lean`, so that this file imports
only Mathlib: for `q < p`, a polynomial map `K^q → K^p` misses some point. -/

section SteinitzAux

variable {p q : ℕ}

theorem not_algebraicIndependent' (hpq : q < p) (f : Fin p → MvPolynomial (Fin q) K) :
    ¬ AlgebraicIndependent K f := by
  intro hf
  have hle : (p : Cardinal.{0}) ≤ (q : Cardinal.{0}) := by
    have h := hf.cardinalMk_le_trdeg
    simpa [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin] using h
  have : p ≤ q := Nat.cast_le.1 hle
  omega

theorem exists_annihilating_polynomial' (hpq : q < p) (f : Fin p → MvPolynomial (Fin q) K) :
    ∃ P : MvPolynomial (Fin p) K, P ≠ 0 ∧ aeval f P = 0 := by
  by_contra h
  refine not_algebraicIndependent' hpq f ?_
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  exact h ⟨P, hP0, hP⟩

theorem exists_eval_ne_zero' {P : MvPolynomial (Fin p) K} (hP : P ≠ 0) :
    ∃ a : Fin p → K, eval a P ≠ 0 := by
  by_contra h
  push Not at h
  exact hP (MvPolynomial.funext fun a => by rw [h a]; simp)

theorem not_surjective' (hpq : q < p) (f : Fin p → MvPolynomial (Fin q) K) :
    ¬ Function.Surjective fun x : Fin q → K => fun i => eval x (f i) := by
  obtain ⟨P, hP0, hP⟩ := exists_annihilating_polynomial' hpq f
  obtain ⟨a, ha⟩ := exists_eval_ne_zero' hP0
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj a
  apply ha
  have h1 := congrArg (MvPolynomial.aeval x) hP
  rw [MvPolynomial.comp_aeval_apply, map_zero] at h1
  simpa [hx] using h1

theorem exists_not_mem_range' (hpq : q < p) (f : Fin p → MvPolynomial (Fin q) K) :
    ∃ y : Fin p → K, ∀ x : Fin q → K, (fun i => eval x (f i)) ≠ y := by
  by_contra h
  push Not at h
  exact not_surjective' hpq f fun y => h y

end SteinitzAux


lemma monOf_injective {k : ℕ} : Function.Injective (monOf (n := n) (k := k)) := by
  intro s t h
  exact (Sym.equivNatSum (Fin n) k).injective (Subtype.ext h)

/-- The image point of the parametrisation: evaluate the parameterised form at `e`. -/
noncomputable def Phi {h d s : ℕ} (e : PIdx n h s → K) (m : Sym (Fin n) d) : K :=
  MvPolynomial.eval e (phiExpr (K := K) (h := h) (d := d) (s := s) m)

lemma coeff_sum_monomials {d : ℕ} (y : Sym (Fin n) d → K) (m : Sym (Fin n) d) :
    (∑ m' : Sym (Fin n) d, MvPolynomial.monomial (monOf m') (y m')).coeff (monOf m) = y m := by
  classical
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => hb (monOf_injective h)
  · intro h; exact absurd (Finset.mem_univ m) h

lemma isHomogeneous_sum_monomials {d : ℕ} (y : Sym (Fin n) d → K) :
    (∑ m' : Sym (Fin n) d, MvPolynomial.monomial (monOf m') (y m')).IsHomogeneous d := by
  classical
  have := MvPolynomial.IsHomogeneous.sum (Finset.univ : Finset (Sym (Fin n) d))
    (fun m' => MvPolynomial.monomial (monOf m') (y m')) d
    (fun i _ => MvPolynomial.isHomogeneous_monomial (y i) (monOf_degree i))
  simpa using this

/-- **The Steinitz step of `cubic_th1.pdf`.**  If the parameter space is too small, some
degree-`d` form is not computable by any circuit with at most `s` nonscalar multiplications. -/
theorem exists_form_not_computable (hn : 0 < n) {h d s : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    (hcard : Fintype.card (PIdx n h s) < Fintype.card (Sym (Fin n) d)) :
    ∃ g : MvPolynomial (Fin n) K, g.IsHomogeneous d ∧
      ∀ c : ArithCircuit2 K n 1, c.mulCount ≤ s → c.outPoly 0 ≠ g := by
  classical
  let eQ : Sym (Fin n) d ≃ Fin (Fintype.card (Sym (Fin n) d)) := Fintype.equivFin _
  let eP : PIdx n h s ≃ Fin (Fintype.card (PIdx n h s)) := Fintype.equivFin _
  obtain ⟨y, hy⟩ := exists_not_mem_range' hcard
    (fun i : Fin (Fintype.card (Sym (Fin n) d)) =>
      MvPolynomial.rename eP (phiExpr (K := K) (h := h) (d := d) (s := s) (eQ.symm i)))
  refine ⟨∑ m : Sym (Fin n) d, MvPolynomial.monomial (monOf m) (y (eQ m)),
    isHomogeneous_sum_monomials (fun m => y (eQ m)), ?_⟩
  intro c hc heq
  obtain ⟨Kf, Af, Bf, hKf, hAf, hBf, hsum⟩ := exists_repr_pad (N := n) (m := 1) c hd hh 0 hc
  set e : PIdx n h s → K := mkE Kf Af Bf with he
  have hform : MvPolynomial.map (MvPolynomial.eval e)
      (formExpr (K := K) (h := h) (d := d) (s := s))
      = ∑ j : Fin s, MvPolynomial.homogeneousComponent d (Kf j * Af j * Bf j) :=
    eval_formExpr e Kf Af Bf hKf hAf hBf
      (fun j a => mkE_zero Kf Af Bf j a) (fun j a => mkE_one Kf Af Bf j a)
      (fun j a => mkE_two Kf Af Bf j a)
  have hkey : ∀ m : Sym (Fin n) d, y (eQ m) = Phi e m := by
    intro m
    have h1 : y (eQ m)
        = (∑ m' : Sym (Fin n) d, MvPolynomial.monomial (monOf m') (y (eQ m'))).coeff (monOf m) :=
      (coeff_sum_monomials (fun m' => y (eQ m')) m).symm
    have h2 : (∑ m' : Sym (Fin n) d, MvPolynomial.monomial (monOf m') (y (eQ m')))
        = MvPolynomial.homogeneousComponent d (c.outPoly 0) := by
      rw [heq, homogeneousComponent_eq_self (isHomogeneous_sum_monomials (fun m' => y (eQ m')))]
    rw [h1, h2, hsum, ← hform, MvPolynomial.coeff_map]
    rfl
  refine hy (fun i => e (eP.symm i)) ?_
  funext i
  rw [MvPolynomial.eval_rename]
  have hcomp : ((fun i => e (eP.symm i)) ∘ eP) = e := by
    funext a; simp
  rw [hcomp]
  have hh2 := hkey (eQ.symm i)
  rw [Equiv.apply_symm_apply] at hh2
  exact hh2.symm

/-- **Lower bound at odd `d = 2h-1`, numeric form.**  When the parameter count
`3 s · #MonoLt n h` is smaller than the number `C(n+d-1,d)` of degree-`d` monomials, some form
of degree `d` is not computed by any circuit with at most `s` nonscalar multiplications. -/
theorem odd_lower_bound_numeric (hn : 0 < n) {h d s : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    (hcard : Fintype.card (PIdx n h s) < Fintype.card (Sym (Fin n) d)) :
    ∃ g : MvPolynomial (Fin n) K, g.totalDegree ≤ d ∧
      ∀ c : ArithCircuit2 K n 1, c.mulCount ≤ s → c.outPoly 0 ≠ g :=
  ⟨_, (exists_form_not_computable (K := K) (n := n) hn hd hh hcard).choose_spec.1.totalDegree_le,
    (exists_form_not_computable (K := K) (n := n) hn hd hh hcard).choose_spec.2⟩

lemma card_PIdx (n h s : ℕ) :
    Fintype.card (PIdx n h s) = s * 3 * Fintype.card (MonoLt n h) := by
  simp only [PIdx, Fintype.card_prod, Fintype.card_fin]
  ring

lemma card_MonoLt (n h : ℕ) :
    Fintype.card (MonoLt n h) = ∑ k : Fin h, (n + k.val - 1).choose k.val := by
  simp only [MonoLt, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sym.card_sym_eq_choose]
  simp

lemma card_sym_form (n d : ℕ) :
    Fintype.card (Sym (Fin n) d) = (n + d - 1).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp

/-- Hockey-stick identity in the shape needed below:
`∑_{k=0}^{h} C(n+k-1,k) = C(n+h,h)`. -/
lemma sum_range_choose_pred (n : ℕ) : ∀ h : ℕ,
    (∑ k ∈ Finset.range (h + 1), (n + k - 1).choose k) = (n + h).choose h
  | 0 => by simp
  | h + 1 => by
    rw [Finset.sum_range_succ, sum_range_choose_pred n h,
      show n + (h + 1) - 1 = n + h by omega,
      show n + (h + 1) = n + h + 1 by omega, Nat.choose_succ_succ']

/-- The exact number of monomials of degree `< h + 1` in `n` variables,
`C(n+h,h)`; equivalently the number of monomials of degree `≤ h`. -/
lemma card_MonoLt_eq (n h : ℕ) : Fintype.card (MonoLt n (h + 1)) = (n + h).choose h := by
  rw [card_MonoLt, Fin.sum_univ_eq_sum_range (fun k => (n + k - 1).choose k) (h + 1)]
  exact sum_range_choose_pred n h

/-- The exact dimension of the space of polynomials of degree `< h` in `n ≥ 1` variables:
`C(n+h-1,h-1)`. -/
lemma card_MonoLt_eq' (n h : ℕ) (hn : 0 < n) (hh : 1 ≤ h) :
    Fintype.card (MonoLt n h) = (n + h - 1).choose (h - 1) := by
  have hcard := card_MonoLt_eq n (h - 1)
  rw [show h - 1 + 1 = h by omega] at hcard
  rw [show n + (h - 1) = n + h - 1 by omega] at hcard
  exact hcard

/-- From a counting hypothesis `3 s M < q` that produces a witness for every `s`, deduce the
quotient form: some form of degree at most `d` is computed by no circuit with fewer than
`q / (3 M)` nonscalar multiplications. -/
lemma exists_form_of_count {L : Type u} [CommRing L] {m : ℕ} {d : ℕ} (M q : ℕ) (hM : 0 < M)
    (hbound : ∀ s : ℕ, 3 * s * M < q →
      ∃ g : MvPolynomial (Fin m) L, g.totalDegree ≤ d ∧
        ∀ c : ArithCircuit2 L m 1, c.mulCount ≤ s → c.outPoly 0 ≠ g) :
    ∃ g : MvPolynomial (Fin m) L, g.totalDegree ≤ d ∧
      ∀ c : ArithCircuit2 L m 1, c.outPoly 0 = g → q / (3 * M) ≤ c.mulCount := by
  classical
  rcases Nat.eq_zero_or_pos (q / (3 * M)) with h0 | hpos
  · refine ⟨0, by simp, fun c _ => ?_⟩
    rw [h0]
    exact Nat.zero_le _
  · have h1 : (3 * M) * (q / (3 * M)) ≤ q := Nat.mul_div_le q (3 * M)
    have h2 : 3 * (q / (3 * M) - 1) * M = (3 * M) * (q / (3 * M)) - 3 * M := by
      have h3 : 3 * (q / (3 * M) - 1) * M = (3 * M) * (q / (3 * M) - 1) := by ring
      rw [h3, Nat.mul_sub_left_distrib]
      ring
    have hlt : 3 * (q / (3 * M) - 1) * M < q := by
      rw [h2]
      have hX : 0 < (3 * M) * (q / (3 * M)) := by
        have : 0 < q / (3 * M) := hpos
        positivity
      have hY : 0 < 3 * M := by positivity
      exact (Nat.sub_lt hX hY).trans_le h1
    obtain ⟨g, hg, hg'⟩ := hbound (q / (3 * M) - 1) hlt
    refine ⟨g, hg, fun c hc => ?_⟩
    by_contra hcon
    have hle : c.mulCount ≤ q / (3 * M) - 1 := Nat.le_sub_one_of_lt (by omega)
    exact hg' c hle hc

/-- **Lower bound at odd `d = 2h-1` with the exact dimension count.**  The dimension of the
space of low parts is `C(n+h-1,h-1)`, so `3 s C(n+h-1,h-1) < C(n+d-1,d)` parameters do not
suffice. -/
theorem odd_lower_bound_choose (hn : 0 < n) {h d s : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    (hcard : 3 * s * (n + h - 1).choose (h - 1) < (n + d - 1).choose d) :
    ∃ g : MvPolynomial (Fin n) K, g.totalDegree ≤ d ∧
      ∀ c : ArithCircuit2 K n 1, c.mulCount ≤ s → c.outPoly 0 ≠ g := by
  refine odd_lower_bound_numeric (K := K) hn hd hh ?_
  rw [card_PIdx, card_sym_form, card_MonoLt_eq' n h hn (by omega), Nat.mul_comm s 3]
  exact hcard

/-- **Lower bound at odd `d = 2h-1`** in quotient form, with the exact dimension count:
some form of degree at most `d` needs at least `C(n+d-1,d) / (3 C(n+h-1,h-1))` nonscalar
multiplications. -/
theorem odd_lower_bound_div_choose (hn : 0 < n) {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h) :
    ∃ g : MvPolynomial (Fin n) K, g.totalDegree ≤ d ∧
      ∀ c : ArithCircuit2 K n 1, c.outPoly 0 = g →
        (n + d - 1).choose d / (3 * (n + h - 1).choose (h - 1)) ≤ c.mulCount :=
  exists_form_of_count (L := K) (m := n) (d := d) ((n + h - 1).choose (h - 1))
    ((n + d - 1).choose d) (Nat.choose_pos (by omega))
    fun s hs => odd_lower_bound_choose (K := K) (n := n) hn hd hh hs

/-! ### The asymptotics of the counting bound -/

/-- `n ^ d ≤ d! * C(n+d-1,d)`. -/
lemma pow_le_factorial_mul_choose (n d : ℕ) (hd : 1 ≤ d) :
    n ^ d ≤ d.factorial * (n + d - 1).choose d := by
  have h1 : (n + d - 1 + 1 - d) ^ d ≤ (n + d - 1).descFactorial d :=
    Nat.pow_sub_le_descFactorial (n + d - 1) d
  rw [show n + d - 1 + 1 - d = n by omega] at h1
  rwa [Nat.descFactorial_eq_factorial_mul_choose] at h1

/-- `C / M - 1 < C / M` for the natural division, as a real inequality. -/
lemma nat_div_cast_gt (C M : ℕ) (hM : 0 < M) : (C : ℝ) / M - 1 < (C / M : ℕ) := by
  have h1 : C = M * (C / M) + C % M := (Nat.div_add_mod C M).symm
  have h2 : C % M < M := Nat.mod_lt C hM
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have h3 : (C : ℝ) = (M : ℝ) * (C / M : ℕ) + ((C % M : ℕ) : ℝ) := by
    conv_lhs => rw [h1]
    push_cast
    ring
  have h4 : ((C % M : ℕ) : ℝ) / (M : ℝ) < 1 := by
    rw [div_lt_one (by exact_mod_cast hM)]
    exact_mod_cast h2
  have hq : ((C / M : ℕ) : ℝ) = (C : ℝ) / M - ((C % M : ℕ) : ℝ) / M := by
    rw [h3, add_div, mul_div_cancel_left₀ _ hM0]
    ring
  linarith

/-- For fixed `k` and every `δ > 0`, eventually `(n + k) ^ k ≤ (1 + δ) n ^ k`. -/
lemma eventually_add_pow_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, (((n + k : ℕ) : ℝ)) ^ k ≤ (1 + δ) * (n : ℝ) ^ k := by
  have hdiv : Filter.Tendsto (fun n : ℕ => (k : ℝ) / (n : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)
  have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) + (k : ℝ) / (n : ℝ)) Filter.atTop
      (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hdiv
  have hcont : ContinuousAt (fun x : ℝ => x ^ k) 1 := by fun_prop
  have hlim : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) + (k : ℝ) / (n : ℝ)) ^ k) Filter.atTop
      (𝓝 1) := by
    have hcomp : Filter.Tendsto
        (fun n : ℕ => ((fun x : ℝ => x ^ k)
          ((fun n : ℕ => (1 : ℝ) + (k : ℝ) / (n : ℝ)) n))) Filter.atTop (𝓝 ((1 : ℝ) ^ k)) :=
      hcont.tendsto.comp h1
    simpa [one_pow] using hcomp
  have hlt : (1 : ℝ) < 1 + δ := by linarith
  have hgood : ∀ᶠ n : ℕ in Filter.atTop,
      ((1 : ℝ) + (k : ℝ) / (n : ℝ)) ^ k < 1 + δ :=
    hlim.eventually (isOpen_Iio.mem_nhds hlt)
  filter_upwards [hgood, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hkey : (((n + k : ℕ) : ℝ)) = (n : ℝ) * (1 + (k : ℝ) / (n : ℝ)) := by
    push_cast
    field_simp
  rw [hkey, mul_pow]
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  calc (n : ℝ) ^ k * (1 + (k : ℝ) / (n : ℝ)) ^ k
      ≤ (n : ℝ) ^ k * (1 + δ) := mul_le_mul_of_nonneg_left hn.le hnn
    _ = (1 + δ) * (n : ℝ) ^ k := by ring

/-- **The sharp asymptotic form of the odd lower bound.**  For `d = 2h - 1` and every `ε > 0`,
eventually the lower bound of `odd_lower_bound_div_choose` dominates
`(1 - ε) (h-1)! n^{⌈d/2⌉} / (3 d!)`:

`(1 - ε) (h-1)! n^h / (3 d!) ≤ C(n+d-1,d) / (3 C(n+h-1,h-1))`. -/
theorem odd_lower_bound_asymptotic_sharp {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      (1 - ε) * ((((h - 1).factorial : ℝ) * (n : ℝ) ^ h) / (3 * (d.factorial : ℝ))) ≤
        (((n + d - 1).choose d / (3 * (n + h - 1).choose (h - 1)) : ℕ) : ℝ) := by
  intro ε hε
  rcases le_or_gt 1 ε with hε1 | hε1
  · filter_upwards with n
    have h0 : (1 - ε) *
        ((((h - 1).factorial : ℝ) * (n : ℝ) ^ h) / (3 * (d.factorial : ℝ))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h1 : (0 : ℝ) ≤ (((n + d - 1).choose d / (3 * (n + h - 1).choose (h - 1)) : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  · set η : ℝ := ε / 2 with hη
    have hη1 : η < 1 := by rw [hη]; linarith
    set δ : ℝ := η / (1 - η) with hδ
    have hδ0 : 0 < δ := by
      rw [hδ]
      exact div_pos (by rw [hη]; linarith) (by linarith)
    have hcoef : (1 - η) * (1 + δ) = 1 := by
      rw [hδ]
      field_simp
      ring
    filter_upwards [eventually_add_pow_le (h - 1) hδ0,
      Filter.eventually_ge_atTop (max 1 (Nat.ceil (6 * (d.factorial : ℝ) / ε)))] with n hpow hge
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hge
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hn0R : (0 : ℝ) < (n : ℝ) := by linarith
    have hd3 : (0 : ℝ) < 3 * (d.factorial : ℝ) := by
      have hpos : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
      linarith
    have hnbig : 6 * (d.factorial : ℝ) / ε ≤ (n : ℝ) := by
      have hc : (Nat.ceil (6 * (d.factorial : ℝ) / ε) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (le_max_right _ _) hge)
      exact le_trans (Nat.le_ceil _) hc
    set C1 : ℝ := ((n + d - 1).choose d : ℝ) with hC1
    set C2 : ℝ := ((n + h - 1).choose (h - 1) : ℝ) with hC2
    set T : ℝ := ((h - 1).factorial : ℝ) * (n : ℝ) ^ h / (3 * (d.factorial : ℝ)) with hT
    have hC1pos : 0 < C1 := by
      rw [hC1]
      exact_mod_cast (Nat.choose_pos (n := n + d - 1) (k := d) (by omega))
    have hC2pos : 0 < C2 := by
      rw [hC2]
      exact_mod_cast (Nat.choose_pos (n := n + h - 1) (k := h - 1) (by omega))
    have hA : (n : ℝ) ^ d ≤ (d.factorial : ℝ) * C1 := by
      rw [hC1]
      exact_mod_cast pow_le_factorial_mul_choose n d (by omega)
    have hfac : ((h - 1).factorial : ℝ) * C2 ≤ (1 + δ) * (n : ℝ) ^ (h - 1) := by
      have hdesc : (n + h - 1).descFactorial (h - 1) ≤ (n + h - 1) ^ (h - 1) :=
        Nat.descFactorial_le_pow _ _
      have hcast1 : (((n + h - 1).descFactorial (h - 1) : ℕ) : ℝ)
          = ((h - 1).factorial : ℝ) * C2 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, hC2]
        push_cast
        ring
      have hcast2 : (((n + h - 1) ^ (h - 1) : ℕ) : ℝ) = ((n + h - 1 : ℕ) : ℝ) ^ (h - 1) := by
        push_cast
        ring
      have hidx : ((n + h - 1 : ℕ) : ℝ) = ((n + (h - 1) : ℕ) : ℝ) := by
        rw [show n + h - 1 = n + (h - 1) by omega]
      calc ((h - 1).factorial : ℝ) * C2
          = (((n + h - 1).descFactorial (h - 1) : ℕ) : ℝ) := hcast1.symm
        _ ≤ (((n + h - 1) ^ (h - 1) : ℕ) : ℝ) := by exact_mod_cast hdesc
        _ = ((n + h - 1 : ℕ) : ℝ) ^ (h - 1) := hcast2
        _ = ((n + (h - 1) : ℕ) : ℝ) ^ (h - 1) := by rw [hidx]
        _ ≤ (1 + δ) * (n : ℝ) ^ (h - 1) := hpow
    have hB : ((h - 1).factorial : ℝ) * (n : ℝ) ^ h * C2 ≤ (1 + δ) * (n : ℝ) ^ d := by
      have hnpow : (0 : ℝ) ≤ (n : ℝ) ^ h := by positivity
      have hmul := mul_le_mul_of_nonneg_left hfac hnpow
      calc ((h - 1).factorial : ℝ) * (n : ℝ) ^ h * C2
          = (n : ℝ) ^ h * (((h - 1).factorial : ℝ) * C2) := by ring
        _ ≤ (n : ℝ) ^ h * ((1 + δ) * (n : ℝ) ^ (h - 1)) := hmul
        _ = (1 + δ) * ((n : ℝ) ^ h * (n : ℝ) ^ (h - 1)) := by ring
        _ = (1 + δ) * (n : ℝ) ^ d := by
            rw [← pow_add, show h + (h - 1) = d by omega]
    have hmain : (1 - η) * (((h - 1).factorial : ℝ) * (n : ℝ) ^ h * C2) ≤
        C1 * (d.factorial : ℝ) := by
      have h1 : (1 - η) * (((h - 1).factorial : ℝ) * (n : ℝ) ^ h * C2) ≤
          (1 - η) * ((1 + δ) * (n : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left hB (by linarith)
      have h2 : (1 - η) * ((1 + δ) * (n : ℝ) ^ d) = (n : ℝ) ^ d := by
        rw [← mul_assoc, hcoef, one_mul]
      have h3 : (n : ℝ) ^ d ≤ C1 * (d.factorial : ℝ) := by
        rw [mul_comm C1 (d.factorial : ℝ)]
        exact hA
      linarith
    have hreal : (1 - η) * T ≤ C1 / (3 * C2) := by
      rw [hT, ← mul_div_assoc, div_le_div_iff₀ hd3 (by linarith [hC2pos])]
      nlinarith [hmain]
    have hslack0 : 1 ≤ η * ((n : ℝ) ^ h / (3 * (d.factorial : ℝ))) := by
      have hkey : 6 * (d.factorial : ℝ) ≤ ε * (n : ℝ) := by
        have hh := mul_le_mul_of_nonneg_right hnbig hε.le
        rw [div_mul_cancel₀ _ hε.ne'] at hh
        rwa [mul_comm (n : ℝ) ε] at hh
      have hpow1 : (n : ℝ) ≤ (n : ℝ) ^ h := by
        calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (n : ℝ) ^ h := pow_le_pow_right₀ hn1R (by omega)
      have hmono : (ε / 2) * (n : ℝ) ≤ (ε / 2) * (n : ℝ) ^ h :=
        mul_le_mul_of_nonneg_left hpow1 (by positivity)
      rw [hη, ← mul_div_assoc, le_div_iff₀ hd3]
      nlinarith
    have hbase : (n : ℝ) ^ h / (3 * (d.factorial : ℝ)) ≤ T := by
      rw [hT]
      have hf : (1 : ℝ) ≤ ((h - 1).factorial : ℝ) := by
        have hpos : 0 < (h - 1).factorial := Nat.factorial_pos _
        exact_mod_cast hpos
      have hnn : (0 : ℝ) ≤ (n : ℝ) ^ h := by positivity
      exact div_le_div_of_nonneg_right (by nlinarith) hd3.le
    have hslack : 1 ≤ η * T := by
      have hη0 : 0 ≤ η := by rw [hη]; positivity
      exact hslack0.trans (mul_le_mul_of_nonneg_left hbase hη0)
    have hMpos' : 0 < 3 * ((n + h - 1).choose (h - 1)) := by
      have hpos : 0 < (n + h - 1).choose (h - 1) := Nat.choose_pos (by omega)
      omega
    have hnat := nat_div_cast_gt ((n + d - 1).choose d)
      (3 * ((n + h - 1).choose (h - 1))) hMpos'
    have hcast : ((3 * ((n + h - 1).choose (h - 1)) : ℕ) : ℝ) = 3 * C2 := by
      rw [hC2]
      push_cast
      ring
    have hcast1 : (((n + d - 1).choose d : ℕ) : ℝ) = C1 := hC1.symm
    rw [hcast, hcast1] at hnat
    have heps : (1 - ε) * T = (1 - η) * T - η * T := by
      rw [hη]
      ring
    rw [heps]
    nlinarith [hreal, hslack, hnat]

/-- The `(1 - o(1))` form of `odd_lower_bound_asymptotic_sharp`: for every constant `c < 1`,
eventually `c (h-1)! n^h / (3 d!) ≤ C(n+d-1,d) / (3 C(n+h-1,h-1))`. -/
theorem odd_lower_bound_asymptotic_sharp' {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h)
    {c : ℝ} (hc : c < 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      c * ((((h - 1).factorial : ℝ) * (n : ℝ) ^ h) / (3 * (d.factorial : ℝ))) ≤
        (((n + d - 1).choose d / (3 * (n + h - 1).choose (h - 1)) : ℕ) : ℝ) := by
  have hε : 0 < 1 - c := by linarith
  filter_upwards [odd_lower_bound_asymptotic_sharp hd hh (1 - c) hε] with n hn
  convert hn using 1
  ring

/-- **The sharp asymptotic lower bound, stated for circuits.**  For odd `d = 2h - 1` and every
`ε > 0`, for all sufficiently large `n` there is a form `g` of degree at most `d` such that every
circuit computing `g` needs at least `(1 - ε) (h-1)! n^h / (3 d!)` nonscalar multiplications:

`μ(g) ≥ (1 - o(1)) (h-1)! n^{⌈d/2⌉} / (3 d!)`. -/
theorem odd_lower_bound_asymptotic_circuit {h d : ℕ} (hd : d = 2 * h - 1) (hh : 2 ≤ h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
      ∃ g : MvPolynomial (Fin n) K, g.totalDegree ≤ d ∧
        ∀ c : ArithCircuit2 K n 1, c.outPoly 0 = g →
          (1 - ε) * ((((h - 1).factorial : ℝ) * (n : ℝ) ^ h) /
            (3 * (d.factorial : ℝ))) ≤ (c.mulCount : ℝ) := by
  intro ε hε
  filter_upwards [odd_lower_bound_asymptotic_sharp hd hh ε hε,
    Filter.eventually_ge_atTop 1] with n hlow hn1
  obtain ⟨g, hg, hc⟩ := odd_lower_bound_div_choose (K := K) (n := n) hn1 hd hh
  exact ⟨g, hg, fun c hceq => hlow.trans (by exact_mod_cast hc c hceq)⟩

end Param

end Sergeev

end MultcompPoly
