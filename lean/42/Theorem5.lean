/-
# Theorem 5 of (Sergeev, Math. Notes 115 (3), 2024)

Theorem 5 of the notes states that for every `n` there is a sum-free Sidon set `B` of
cardinality `n` with complexity `L(B) = n + O(n^(2/3))`.  Its proof rests on the classical
Bose–Chowla construction of dense `B_k`-sets, which the notes recall on p. 388:

> Let `GF(q) = {α_1, …, α_q}`, and let `x` be a primitive element of the field `GF(q^k)`.
> Write `D[q,k] = {d_i | x^{d_i} = x + α_i, 1 ≤ d_i < q^k}`.  The set `D[q,k]` (as is easy to
> check) is a `B_k`-set of cardinality `q`.

The file formalizes Theorem 5 in full.  It begins with the Bose–Chowla lemma:
`BoseChowla.isBkSeq_of_pow_eq` below says that `D[q,k]` has pairwise distinct `k`-term sums,
`BoseChowla.card` says that it has `q` elements, and `BoseChowla.exists_isBkSeq` combines the two,
producing the exponents `d_i`; the theorem itself is `Theorem5.theorem5` at the end of the file.

The file is self-contained: its only import is `Mathlib`.  The handful of notions it needs from the
general framework of the notes are re-declared here under their original names, so — exactly like
`Theorem4.lean` — this file must not be imported together with the modules `Theorem4` or `H-is-Bk-set`.

## Main results

* `BoseChowla.isBkSeq_of_pow_eq` : for any choice of exponents `d` with `x ^ d a = x + α`, the set
  `{d a}` is a `B_k`-set.
* `BoseChowla.card` : it has `q = |F|` elements.
* `BoseChowla.aeval_ne_zero` : no nonzero polynomial of degree `< k` over `GF(q)` vanishes at a
  primitive element; this is the only field-theoretic input.
* `BoseChowla.exists_isBkSeq` : for `k ≥ 2` such exponents exist, so `D[q,k]` is a `B_k`-set with
  `q` elements.
* `BoseChowla.exists_isBkSeq_range` : the same, with all exponents in the canonical range
  `1 ≤ d_i < q^k`.
* `BoseChowla.exists_bc_data` : the concrete case `k = 2` over `GF(q)`: exponents `d : ZMod q → ℕ`
  with `1 ≤ d a < q²` such that `cycD d 2 ⊆ ZMod (q² - 1)` is a `B_2`-set of `q` elements.
* `Theorem5.theorem5` : for every `n` there is a sum-free Sidon set `B` with `|B| = n` and
  `L(B) ≤ n + 96 (n + 1)^(2/3)`, i.e. `L(B) = n + O(n^(2/3))`;
  `Theorem5.theorem5_of_one_le` is the shape stated in the notes, `L(B) ≤ n + 192 n^(2/3)` for
  `n ≥ 1`.
* `Theorem5.theorem5_core` : the combinatorial core with explicit parameters: if `m ≥ 2` and
  `16 n² ≤ m³`, then `L(B) ≤ n + 16 m`.

The canonical representatives `1 ≤ d_i < q^k` are supplied by
`BoseChowla.exists_isBkSeq_range`.  Since `x` is primitive, its order divides `q^k - 1`; replacing
every exponent by its residue in `[1, q^k - 1]` therefore does not change the powers, and the
`B_k` property is transported (`BoseChowla.exists_range_of_pow_eq`, `BoseChowla.pow_canon`).
The range is used in `BoseChowla.isBkSeq_zmod` and `BoseChowla.exists_bc_data`: it makes the map
`d a ↦ (d a : ZMod (q^k - 1))` injective, so the cyclic version `cycD d k` of `D[q,k]` still has
`q` elements, and the `B_k` property survives the passage to the group `ZMod (q^k - 1)` in which
`D` is closed under addition of indices modulo `q^k - 1`.

## The proof

Let `d_{i_1} + ⋯ + d_{i_k} = d_{j_1} + ⋯ + d_{j_k}` be two equal `k`-term sums.  Raising the
primitive element `x` to these powers gives

`∏_{t=1}^{k} (x + α_{i_t}) = x^{d_{i_1} + ⋯ + d_{i_k}} = x^{d_{j_1} + ⋯ + d_{j_k}}
 = ∏_{t=1}^{k} (x + α_{j_t})`.

Both products are the value at `x` of a monic polynomial of degree `k` with coefficients in
`GF(q)`; their difference has degree `< k`.  Since `x` is a primitive element, hence
`GF(q)(x) = GF(q^k)` has degree `k` over `GF(q)`, no nonzero polynomial of degree `< k` over
`GF(q)` vanishes at `x`.  So the two polynomials coincide, and as both split into linear
factors this forces the multisets of their roots `{-α_{i_t}}` and `{-α_{j_t}}` to coincide.
As the `α_i` are pairwise distinct, `{i_1, …, i_k} = {j_1, …, j_k}` and the sums were equal
as multisets.

In the formalization the field `GF(q)` is an arbitrary finite field `F`, `GF(q^k)` an
arbitrary field extension `E` of `F` of degree `k` (`Module.finrank F E = k`), and `x : E` is
primitive in the sense that every nonzero element of `E` is a power of `x` (the paper's
“primitive element of `GF(q^k)`”, i.e. a generator of the multiplicative group).

The main lemma `BoseChowla.isBkSeq_of_pow_eq` is stated for an arbitrary choice `d` of the
exponents, i.e. any function `d : F → ℕ` with `x ^ d a = x + C a` for all `a`; this is the
precise amount of information about `D[q,k]` used by the argument, and it is independent of
the choice of the representatives `1 ≤ d_i < q^k` (which differ by multiples of the order of
`x`).  `BoseChowla.boseChowlaSet` is the resulting set for the choice supplied by
`Classical.choose`.  The canonical range is then imposed afterwards: `BoseChowla.pow_mod_card`
shows that reducing an exponent modulo `q^k - 1` does not change the power of `x`, so
`BoseChowla.exists_isBkSeq_range` produces representatives in `[1, q^k - 1]` without losing the
`B_k` property.

## Theorem 5

The file is self-contained and imports only `Mathlib`.  The 
elementary API used afterwards (`Theorem5.AddChain.exists_append`, `Theorem5.setL_le_of_seq`,
`Theorem5.setL_le_add_card`) is proved here.

The construction follows the notes, with one substitution in the choice of the dense `B_4`-set
`A`.  The notes take `A = N + (D[q²,4] ∖ {1}) ⊆ [N, 2N - 1]` with `N = (4m)^4`, using only
`|A| = q² - 1 ≥ m - 1` and `L(A) = O(m)`.  Here `A r = {5^r + 5^i | i < r}` is used instead
(`Theorem5.A`): it lies in `[5^r, 2·5^r)` (`A_ge`, `A_lt`), has `r` elements (`A_card`), is a
`B_4`-set (`A_isBkSeq`, from the uniqueness of the base-5 digits of its pair sums) and satisfies
`L(A r) ≤ 4 r` (`setL_A_le`, via the powers `powSet r = {5^i | i ≤ r}`).  This avoids
instantiating the nested field extensions `GF(q) ⊆ GF(q²) ⊆ GF(q⁴)` and keeps the asymptotics,
since the argument only needs the elements of `A` to dominate `4m`.

Given `m ≥ 2`, pick a prime `q` with `m ≤ q² < 4m` (`exists_prime_sq_between`, from Bertrand's
postulate) and put `r = q² - 1`.  With `D = cycD d 2 ⊆ ZMod r` from `exists_bc_data`, let
`B′ = {a_i + a_j | ((i + j) mod r) ∈ D}` be the set of `Bp r D`; then:

* `Bp_subset_A_add` : every element of `B′` is a sum of two elements of `A r`;
* `card_Pairs` and `two_mul_card_Bp_ge` : `|B′| ≥ r·q/2`, since the `r·|D| = r·q` pairs
  `(i, j)` of `Pairs r D` have at most two preimages each under `pval`;
* `Bp_isBkSeq` : `B′` is a Sidon set — a nontrivial quadruple
  `a_i + a_j, a_{i'} + a_{j'}, a_i + a_{j'}, a_{i'} + a_j` in `B′` would give the `B_2` relation
  `(i + j') + (i' + j) = (i + j) + (i' + j')` inside `D` while `pval_inj_two` and
  `pairing_eq_of_sum` show that the `B_4` property of `A r` forces the two pairings to agree;
* `Bp_sumFree` : `B′` is sum-free, since all its elements lie in `[2·5^r, 4·5^r)` (`Bp_ge`,
  `Bp_lt`), so the sum of two of them exceeds every element.

Choosing `B ⊆ B′` with `|B| = n ≤ |B′|` (`theorem5_core`, using `16 n² ≤ m³`) gives a sum-free
Sidon set of size `n` with `L(B) ≤ L(A r) + |B| ≤ 4 r + n ≤ n + 16 m`.  Finally `theorem5` takes
`m = 3⌈(n+1)^(2/3)⌉`: then `m ≥ 2`, `16 n² ≤ m³` (because `n² ≤ (n+1)² ≤ ⌈(n+1)^(2/3)⌉³`) and
`16 m ≤ 96 (n+1)^(2/3)`.
-/
import Mathlib

noncomputable section

open Polynomial

/-! ## The framework of Theorem 4

Only a handful of notions from the paper's general framework are needed below: `k`-sum-distinct
sets (`BkSet.IsBkSeq`), ordinary addition chains (`Theorem4.AddChain`) with the set complexity
`L(S)` (`Theorem4.setL`) and sum-freeness (`Theorem4.SumFree`).  They are reproduced here, so that
the file needs nothing beyond `Mathlib`.
-/

namespace BkSet

noncomputable section

/-- A `k`-sum-distinct set. -/
def IsBkSeq {G : Type*} [AddCommMonoid G] (k : ℕ) (B : Finset G) : Prop :=
  ∀ s t : Multiset G, (∀ x ∈ s, x ∈ B) → (∀ x ∈ t, x ∈ B) →
    s.card = k → t.card = k → s.sum = t.sum → s = t

end

end BkSet

namespace Theorem4

open Finset

/-! ### Ordinary addition chains -/

/-- The pool of values available at step `k` of an ordinary addition chain: the initial value `1`
together with the entries computed so far. -/
def npPool (y : ℕ → ℕ) (k : ℕ) : Option (Fin k) → ℕ
  | none => 1
  | some j => y (j : ℕ)

@[simp]
theorem npPool_none (y : ℕ → ℕ) (k : ℕ) : npPool y k none = 1 := rfl

@[simp]
theorem npPool_some (y : ℕ → ℕ) {k : ℕ} (j : Fin k) : npPool y k (some j) = y (j : ℕ) := rfl

/-- An ordinary addition chain `1, y 0, …, y (L-1)`: every entry is the sum of two values available
before it, namely `1` or an earlier entry. -/
structure AddChain where
  /-- the length of the chain, i.e. the number of additions -/
  L : ℕ
  /-- the entries of the chain -/
  y : ℕ → ℕ
  /-- every entry is the sum of two available values -/
  valid : ∀ k < L, ∃ x z : Option (Fin k), y k = npPool y k x + npPool y k z

namespace AddChain

/-- The chain computes every number of the finite set `S`: each element of `S` is either `1` or one
of the entries of the chain. -/
def Computes (c : AddChain) (S : Finset ℕ) : Prop := ∀ a ∈ S, a = 1 ∨ ∃ k < c.L, c.y k = a

/-- `Computes` is monotone in the set. -/
theorem Computes.mono {c : AddChain} {S T : Finset ℕ} (h : c.Computes T) (hST : S ⊆ T) :
    c.Computes S := fun a ha => h a (hST ha)

/-- The "increment" chain `1, 2, 3, …, M` of length `M - 1`, which computes every number up to
`M`. -/
def incr (M : ℕ) : AddChain where
  L := M - 1
  y := fun k => k + 2
  valid := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      exact ⟨none, none, by norm_num⟩
    · refine ⟨some ⟨k - 1, by omega⟩, none, ?_⟩
      simp only [npPool_some, npPool_none]
      omega

@[simp]
theorem incr_L (M : ℕ) : (incr M).L = M - 1 := rfl

@[simp]
theorem incr_y (M k : ℕ) : (incr M).y k = k + 2 := rfl

/-- The increment chain computes every number in the interval `[1, M]`. -/
theorem incr_computes (M : ℕ) {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a ∧ a ≤ M) :
    (incr M).Computes S := by
  intro a ha
  obtain ⟨ha1, haM⟩ := h a ha
  rcases Nat.eq_or_lt_of_le ha1 with h1 | h2
  · exact Or.inl h1.symm
  · refine Or.inr ⟨a - 2, ?_, ?_⟩
    · simp only [incr_L]
      omega
    · simp only [incr_y]
      omega

/-- Some chain computes `S`, provided `S` contains no zero. -/
theorem exists_computes (S : Finset ℕ) (h : ∀ a ∈ S, 1 ≤ a) : ∃ c : AddChain, c.Computes S := by
  refine ⟨incr (∑ a ∈ S, a), incr_computes _ ?_⟩
  intro a ha
  exact ⟨h a ha, Finset.single_le_sum (f := fun x => x) (fun x _ => Nat.zero_le x) ha⟩

end AddChain

/-- `L(S)`: the length of a shortest ordinary addition chain computing the finite set `S`. -/
def setL (S : Finset ℕ) : ℕ := sInf {l | ∃ c : AddChain, c.L = l ∧ c.Computes S}

/-- A chain computing `S` bounds `setL S` from above. -/
theorem setL_le {S : Finset ℕ} {c : AddChain} (h : c.Computes S) : setL S ≤ c.L :=
  Nat.sInf_le ⟨c, rfl, h⟩

/-- The set of lengths of chains computing `S` is nonempty. -/
theorem setL_nonempty {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a) :
    {l | ∃ c : AddChain, c.L = l ∧ c.Computes S}.Nonempty := by
  obtain ⟨c, hc⟩ := AddChain.exists_computes S h
  exact ⟨c.L, c, rfl, hc⟩

/-- A shortest chain computing `S` exists. -/
theorem exists_optimal {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a) :
    ∃ c : AddChain, c.L = setL S ∧ c.Computes S :=
  Nat.sInf_mem (setL_nonempty h)

/-- A set is sum-free if `B + B` is disjoint from `B`. -/
def SumFree (B : Finset ℕ) : Prop := ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B

/-- The `B_k` property is inherited by subsets. -/
theorem isBkSeq_subset {k : ℕ} {B C : Finset ℕ} (h : BkSet.IsBkSeq k B) (hCB : C ⊆ B) :
    BkSet.IsBkSeq k C :=
  fun s t hs ht => h s t (fun x hx => hCB (hs x hx)) (fun x hx => hCB (ht x hx))

end Theorem4

namespace BoseChowla

/-! ## Polynomials with roots `-α` -/

section Poly

variable {F : Type*} [Field F]

/-- `prodPoly s = ∏_{a ∈ s} (X + C a)`, the monic polynomial of degree `s.card` whose roots are
the elements of `s` with the sign changed. -/
def prodPoly (s : Multiset F) : F[X] :=
  (s.map fun a => X + C a).prod

theorem prodPoly_cons (a : F) (s : Multiset F) :
    prodPoly (a ::ₘ s) = (X + C a) * prodPoly s := by
  simp [prodPoly]

theorem prodPoly_monic (s : Multiset F) : (prodPoly s).Monic := by
  induction s using Multiset.induction_on with
  | empty => simp [prodPoly]
  | cons a s ih => rw [prodPoly_cons]; exact (monic_X_add_C a).mul ih

theorem prodPoly_natDegree (s : Multiset F) : (prodPoly s).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [prodPoly]
  | cons a s ih =>
      rw [prodPoly_cons, (monic_X_add_C a).natDegree_mul (prodPoly_monic s),
        natDegree_X_add_C, ih, Multiset.card_cons]
      omega

/-- The polynomial `∏_{a ∈ s} (X + C a)` determines the multiset `s`. -/
theorem prodPoly_injective : Function.Injective (prodPoly (F := F)) := by
  intro s t h
  have h' : (s.map fun a => X - C (-a)).prod = (t.map fun a => X - C (-a)).prod := by
    simpa only [prodPoly, sub_neg_eq_add, C_neg] using h
  have hneg : s.map Neg.neg = t.map Neg.neg := by
    have key : ((s.map Neg.neg).map fun b => X - C b).prod
        = ((t.map Neg.neg).map fun b => X - C b).prod := by
      simpa only [Multiset.map_map, Function.comp_def] using h'
    simpa only [roots_multiset_prod_X_sub_C] using congrArg roots key
  simpa only [Multiset.map_map, Function.comp_def, neg_neg, Multiset.map_id'] using
    congrArg (Multiset.map Neg.neg) hneg

end Poly

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Evaluation of `prodPoly` at an element of the extension. -/
theorem aeval_prodPoly (x : E) (s : Multiset F) :
    aeval x (prodPoly s) = (s.map fun a => x + algebraMap F E a).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [prodPoly]
  | cons a s ih =>
      rw [prodPoly_cons, map_mul, ih, Multiset.map_cons, Multiset.prod_cons]
      congr 1
      simp

end Extension

section Powers

variable {F M : Type*} [CommMonoid M]

/-- `x ^ (sum of a multiset of exponents)` is the product of the corresponding powers. -/
theorem pow_multiset_sum (x : M) (s : Multiset F) (g : F → ℕ) :
    x ^ (s.map g).sum = (s.map fun a => x ^ g a).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons,
      pow_add, ih]

end Powers

/-! ## Primitive elements have no relations of degree `< k` -/

section Primitive

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {k : ℕ} {x : E}

variable (hfin : Module.finrank F E = k) (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y)

include hfin hx in
/-- A primitive element generates the field extension, so its minimal polynomial has degree
`k = [E : F]`. -/
theorem natDegree_minpoly : (minpoly F x).natDegree = k := by
  have htop : IntermediateField.adjoin F {x} = ⊤ := by
    refine le_antisymm le_top ?_
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact (IntermediateField.adjoin F {x}).zero_mem
    · obtain ⟨n, rfl⟩ := hx y hy
      exact Subfield.pow_mem _
        (Subfield.subset_closure (Set.mem_union_right _ (Set.mem_singleton x))) n
  have := IntermediateField.adjoin.finrank (IsIntegral.of_finite F x)
  rw [htop, IntermediateField.finrank_top', hfin] at this
  exact this.symm

include hfin hx in
/-- **No polynomial relation of degree `< k`**: a nonzero polynomial over `GF(q)` of degree
`< k = [E : F]` does not vanish at the primitive element `x`.  This is the ingredient of the
Bose–Chowla argument supplied by primitivity. -/
theorem aeval_ne_zero {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree < k) :
    aeval x p ≠ 0 := by
  intro hroot
  have hdvd : minpoly F x ∣ p := minpoly.dvd F x hroot
  have hle : (minpoly F x).natDegree ≤ p.natDegree := natDegree_le_of_dvd hdvd hp
  rw [natDegree_minpoly hfin hx] at hle
  omega

include hfin hx in
/-- `x + α` is never zero: otherwise `x = -α` would be a root of the degree-one polynomial
`X + C α`, contradicting `aeval_ne_zero` and `k ≥ 2`. -/
theorem add_algebraMap_ne_zero (hk : 2 ≤ k) (a : F) : x + algebraMap F E a ≠ 0 := by
  intro h
  have hp : (X + C a : F[X]) ≠ 0 := (monic_X_add_C a).ne_zero
  have hdeg : (X + C a : F[X]).natDegree < k := by
    rw [natDegree_X_add_C]; omega
  refine aeval_ne_zero hfin hx hp hdeg ?_
  simpa using h

end Primitive

/-! ## The Bose–Chowla set `D[q,k]` -/

section BoseChowlaSet

variable {F : Type*} [Fintype F]

/-- A choice of the exponents `d_i`: for an exponent function `d` with `x ^ d a = x + α`, the set
`{d a | a : F}` is the Bose–Chowla set `D[q,k] = {d_i | x ^ d_i = x + α_i}`. -/
def boseChowlaSet (d : F → ℕ) : Finset ℕ :=
  Finset.univ.image d

theorem mem_boseChowlaSet {d : F → ℕ} {e : ℕ} :
    e ∈ boseChowlaSet d ↔ ∃ a : F, d a = e := by
  simp only [boseChowlaSet, Finset.mem_image, Finset.mem_univ, true_and]

end BoseChowlaSet

section BoseChowla

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F]

variable {x : E} {d : F → ℕ} (hd : ∀ a : F, x ^ d a = x + algebraMap F E a)

omit [Fintype F] in
include hd in
/-- Distinct `α` have distinct exponents. -/
theorem d_injective : Function.Injective d := by
  intro a b hab
  have h3 : x + algebraMap F E a = x + algebraMap F E b := by
    rw [← hd a, ← hd b, hab]
  exact (algebraMap F E).injective (add_left_cancel h3)

include hd in
/-- `D[q,k]` has `q = |F|` elements. -/
theorem card : (boseChowlaSet d).card = Fintype.card F := by
  rw [boseChowlaSet, Finset.card_image_of_injOn]
  · simp
  · exact fun a _ b _ hab => d_injective hd hab

section

variable [FiniteDimensional F E] {k : ℕ}
  (hfin : Module.finrank F E = k) (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y)

include hd hfin hx in
/-- **`D[q,k]` is a `B_k`-set**: all `k`-term sums of elements of the Bose–Chowla set are
distinct.

Indeed, if `d_{i_1} + ⋯ + d_{i_k} = d_{j_1} + ⋯ + d_{j_k}`, then
`∏_t (x + α_{i_t}) = x^{d_{i_1} + ⋯ + d_{i_k}} = x^{d_{j_1} + ⋯ + d_{j_k}} = ∏_t (x + α_{j_t})`.
Both products are the value at `x` of a monic polynomial of degree `k` over `GF(q)`; their difference
has degree `< k`, so by `aeval_ne_zero` it is zero.  Hence the two products coincide, and since both
split into linear factors their multisets of roots `{-α_{i_t}}` and `{-α_{j_t}}` are equal
(`prodPoly_injective`), so `{i_1, …, i_k} = {j_1, …, j_k}`. -/
theorem isBkSeq_of_pow_eq : BkSet.IsBkSeq k (boseChowlaSet d) := by
  have hpow : ∀ as : Multiset F, x ^ (as.map d).sum
      = (as.map fun a => x + algebraMap F E a).prod := by
    intro as
    rw [pow_multiset_sum]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => hd a)
  intro s t hs ht hcs hct hsum
  -- lift the multisets of exponents back to multisets of field elements
  have lift : ∀ u : Multiset ℕ, (∀ e ∈ u, e ∈ boseChowlaSet d) →
      ∃ as : Multiset F, as.map d = u := by
    intro u hu
    refine ⟨u.map (Function.invFun d), ?_⟩
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
    intro e he
    exact Function.invFun_eq (mem_boseChowlaSet.mp (hu e he))
  obtain ⟨as, has_map⟩ := lift s hs
  obtain ⟨bt, hbt_map⟩ := lift t ht
  have has_card : as.card = k := by rw [← Multiset.card_map d, has_map, hcs]
  have hbt_card : bt.card = k := by rw [← Multiset.card_map d, hbt_map, hct]
  -- the values at `x` of the two products coincide
  have hvalues : (as.map fun a => x + algebraMap F E a).prod
      = (bt.map fun a => x + algebraMap F E a).prod := by
    rw [← hpow as, ← hpow bt, has_map, hbt_map, hsum]
  have haeval : aeval x (prodPoly as) = aeval x (prodPoly bt) := by
    rw [aeval_prodPoly, aeval_prodPoly, hvalues]
  -- hence the two products are the same polynomial
  have hprod : prodPoly as = prodPoly bt := by
    by_contra hne
    have hdiff : prodPoly as - prodPoly bt ≠ 0 := sub_ne_zero.mpr hne
    have hdeg : (prodPoly as - prodPoly bt).natDegree < k := by
      rw [natDegree_lt_iff_degree_lt hdiff]
      have hdeg_eq : (prodPoly as).degree = (prodPoly bt).degree := by
        rw [degree_eq_natDegree (prodPoly_monic as).ne_zero,
          degree_eq_natDegree (prodPoly_monic bt).ne_zero, prodPoly_natDegree,
          prodPoly_natDegree, has_card, hbt_card]
      have hlt := degree_sub_lt_left hdeg_eq (prodPoly_monic as).ne_zero (by
        rw [(prodPoly_monic as).leadingCoeff, (prodPoly_monic bt).leadingCoeff])
      rwa [degree_eq_natDegree (prodPoly_monic as).ne_zero, prodPoly_natDegree,
        has_card] at hlt
    refine aeval_ne_zero hfin hx hdiff hdeg ?_
    rw [map_sub, haeval, sub_self]
  have hbeq : as = bt := prodPoly_injective hprod
  rw [← has_map, ← hbt_map, hbeq]

include hfin hx in
/-- **The Bose–Chowla exponents exist** (for `k ≥ 2`).  For every `α : F` the element `x + α` is
nonzero — otherwise `x = -α` would be a root of the linear polynomial `X + C α`, contradicting
`aeval_ne_zero` — so it is a power of the primitive element `x`.  Choosing such an exponent for each
`α` turns `D[q,k]` into a `B_k`-set with `q` elements, by `isBkSeq_of_pow_eq` and `card`. -/
theorem exists_isBkSeq (hk : 2 ≤ k) :
    ∃ d : F → ℕ, (∀ a : F, x ^ d a = x + algebraMap F E a) ∧
      BkSet.IsBkSeq k (boseChowlaSet d) ∧ (boseChowlaSet d).card = Fintype.card F := by
  let dexp : F → ℕ := fun a =>
    Classical.choose (hx (x + algebraMap F E a) (add_algebraMap_ne_zero hfin hx hk a))
  have hdexp : ∀ a : F, x ^ dexp a = x + algebraMap F E a := fun a =>
    Classical.choose_spec (hx (x + algebraMap F E a) (add_algebraMap_ne_zero hfin hx hk a))
  exact ⟨dexp, hdexp, isBkSeq_of_pow_eq hdexp hfin hx, card hdexp⟩


end

end BoseChowla

end BoseChowla

namespace BoseChowla

/-! ## Canonical representatives `1 ≤ d_i < q ^ k` -/

section RangeZero

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {x : E} {k : ℕ}
  (hfin : Module.finrank F E = k) (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y)

include hfin hx in
/-- The primitive element is nonzero. -/
theorem x_ne_zero (hk : 2 ≤ k) : x ≠ 0 := by
  have h := add_algebraMap_ne_zero hfin hx hk (0 : F)
  simpa using h

end RangeZero

section RangeCards

variable {F : Type*} [Field F] [Fintype F]

/-- `q ^ k - 1` is positive for `q = |F| ≥ 2`. -/
theorem card_pow_sub_one_pos {k : ℕ} (hk : 2 ≤ k) : 0 < Fintype.card F ^ k - 1 := by
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hk0 : k ≠ 0 := by omega
  have h3 : 1 < Fintype.card F ^ k := one_lt_pow₀ h1 hk0
  omega

/-- The canonical representative of `d a` in `[1, q ^ k - 1]`, where `q = |F|`. -/
def canon (k : ℕ) (d : F → ℕ) (a : F) : ℕ :=
  if d a % (Fintype.card F ^ k - 1) = 0 then Fintype.card F ^ k - 1
  else d a % (Fintype.card F ^ k - 1)

theorem canon_pos {k : ℕ} (hk : 2 ≤ k) (d : F → ℕ) (a : F) : 1 ≤ canon k d a := by
  have hM : 0 < Fintype.card F ^ k - 1 := card_pow_sub_one_pos hk
  unfold canon
  split_ifs with h
  · omega
  · exact Nat.pos_of_ne_zero h

theorem canon_lt {k : ℕ} (hk : 2 ≤ k) (d : F → ℕ) (a : F) :
    canon k d a < Fintype.card F ^ k := by
  have hM : 0 < Fintype.card F ^ k - 1 := card_pow_sub_one_pos hk
  have h2 : 2 ≤ Fintype.card F ^ k := by omega
  unfold canon
  split_ifs with h
  · omega
  · have := Nat.mod_lt (d a) hM
    omega

end RangeCards

section Range

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [FiniteDimensional F E]
  {x : E} {k : ℕ} (hfin : Module.finrank F E = k)
  (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y)

include hfin hx in
/-- Fermat's little theorem in the extension: `x ^ (q ^ k - 1) = 1`. -/
theorem pow_card_ext_sub_one (hk : 2 ≤ k) : x ^ (Fintype.card F ^ k - 1) = 1 := by
  have _ : Fintype E := Module.fintypeOfFintype (Module.finBasis F E)
  have hcard : Fintype.card E = Fintype.card F ^ k := by
    rw [Module.card_eq_pow_finrank (K := F) (V := E), hfin]
  rw [← hcard]
  exact FiniteField.pow_card_sub_one_eq_one x (x_ne_zero hfin hx hk)

include hfin hx in
/-- Reducing the exponent modulo `q ^ k - 1` does not change the power. -/
theorem pow_mod_card (hk : 2 ≤ k) (n : ℕ) :
    x ^ (n % (Fintype.card F ^ k - 1)) = x ^ n := by
  have hdvd : orderOf x ∣ Fintype.card F ^ k - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr (pow_card_ext_sub_one hfin hx hk)
  rw [← pow_mod_orderOf x (n % (Fintype.card F ^ k - 1)), ← pow_mod_orderOf x n,
    Nat.mod_mod_of_dvd n hdvd]

include hfin hx in
/-- The canonical representative has the same power. -/
theorem pow_canon (hk : 2 ≤ k) (d : F → ℕ) (a : F) :
    x ^ canon k d a = x ^ d a := by
  unfold canon
  split_ifs with h
  · rw [← pow_mod_card hfin hx hk (d a), h, pow_zero]
    exact pow_card_ext_sub_one hfin hx hk
  · exact pow_mod_card hfin hx hk (d a)

include hfin hx in
/-- **Canonical exponents**: any exponent function `d` with `x ^ d a = x + α` can be replaced by
one with values in `[1, q ^ k - 1]` without changing the powers. -/
theorem exists_range_of_pow_eq (hk : 2 ≤ k) (d : F → ℕ)
    (hd : ∀ a : F, x ^ d a = x + algebraMap F E a) :
    ∃ d' : F → ℕ, (∀ a : F, x ^ d' a = x + algebraMap F E a) ∧
      ∀ a : F, 1 ≤ d' a ∧ d' a < Fintype.card F ^ k :=
  ⟨canon k d, fun a => by rw [pow_canon hfin hx hk d a, hd a],
    fun a => ⟨canon_pos hk d a, canon_lt hk d a⟩⟩

include hfin hx in
/-- **The Bose–Chowla set with canonical exponents** `1 ≤ d_i < q ^ k`: it is a `B_k`-set with
`q` elements, all of whose exponents lie in `[1, q ^ k - 1]`. -/
theorem exists_isBkSeq_range (hk : 2 ≤ k) :
    ∃ d : F → ℕ, (∀ a : F, x ^ d a = x + algebraMap F E a) ∧
      (∀ a : F, 1 ≤ d a ∧ d a < Fintype.card F ^ k) ∧
      BkSet.IsBkSeq k (boseChowlaSet d) ∧ (boseChowlaSet d).card = Fintype.card F := by
  obtain ⟨d, hd, -, -⟩ := exists_isBkSeq (x := x) hfin hx hk
  obtain ⟨d', hd', hrange⟩ := exists_range_of_pow_eq hfin hx hk d hd
  exact ⟨d', hd', hrange, isBkSeq_of_pow_eq hd' hfin hx, card hd'⟩

end Range

end BoseChowla

namespace BoseChowla

open Polynomial

section RootOfUnity

theorem pow_eq_of_modEq {M : Type*} [Monoid M] {y : M} {m a b : ℕ} (hm : y ^ m = 1)
    (h : a ≡ b [MOD m]) : y ^ a = y ^ b := by
  have hdvd : orderOf y ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hm
  have h' : a % orderOf y = b % orderOf y := Nat.ModEq.of_dvd hdvd h
  rw [← pow_mod_orderOf y a, ← pow_mod_orderOf y b, h']

end RootOfUnity

section ModEqSum

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [FiniteDimensional F E]
  {x : E} {k : ℕ}

theorem eq_of_pow_sum (hfin : Module.finrank F E = k)
    (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y) {d : F → ℕ}
    (hd : ∀ a : F, x ^ d a = x + algebraMap F E a) {s t : Multiset ℕ}
    (hs : ∀ e ∈ s, e ∈ boseChowlaSet d) (ht : ∀ e ∈ t, e ∈ boseChowlaSet d)
    (hcs : s.card = k) (hct : t.card = k) (h : x ^ s.sum = x ^ t.sum) : s = t := by
  have hpow : ∀ as : Multiset F, x ^ (as.map d).sum
      = (as.map fun a => x + algebraMap F E a).prod := by
    intro as
    rw [pow_multiset_sum]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => hd a)
  have lift : ∀ u : Multiset ℕ, (∀ e ∈ u, e ∈ boseChowlaSet d) →
      ∃ as : Multiset F, as.map d = u := by
    intro u hu
    refine ⟨u.map (Function.invFun d), ?_⟩
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
    intro e he
    exact Function.invFun_eq (mem_boseChowlaSet.mp (hu e he))
  obtain ⟨as, has_map⟩ := lift s hs
  obtain ⟨bt, hbt_map⟩ := lift t ht
  have has_card : as.card = k := by rw [← Multiset.card_map d, has_map, hcs]
  have hbt_card : bt.card = k := by rw [← Multiset.card_map d, hbt_map, hct]
  have hvalues : (as.map fun a => x + algebraMap F E a).prod
      = (bt.map fun a => x + algebraMap F E a).prod := by
    rw [← hpow as, ← hpow bt, has_map, hbt_map, h]
  have haeval : aeval x (prodPoly as) = aeval x (prodPoly bt) := by
    rw [aeval_prodPoly, aeval_prodPoly, hvalues]
  have hprod : prodPoly as = prodPoly bt := by
    by_contra hne
    have hdiff : prodPoly as - prodPoly bt ≠ 0 := sub_ne_zero.mpr hne
    have hdeg : (prodPoly as - prodPoly bt).natDegree < k := by
      rw [natDegree_lt_iff_degree_lt hdiff]
      have hdeg_eq : (prodPoly as).degree = (prodPoly bt).degree := by
        rw [degree_eq_natDegree (prodPoly_monic as).ne_zero,
          degree_eq_natDegree (prodPoly_monic bt).ne_zero, prodPoly_natDegree,
          prodPoly_natDegree, has_card, hbt_card]
      have hlt := degree_sub_lt_left hdeg_eq (prodPoly_monic as).ne_zero (by
        rw [(prodPoly_monic as).leadingCoeff, (prodPoly_monic bt).leadingCoeff])
      rwa [degree_eq_natDegree (prodPoly_monic as).ne_zero, prodPoly_natDegree,
        has_card] at hlt
    refine aeval_ne_zero hfin hx hdiff hdeg ?_
    rw [map_sub, haeval, sub_self]
  have hbeq : as = bt := prodPoly_injective hprod
  rw [← has_map, ← hbt_map, hbeq]

/-- Casting a multiset sum of naturals into `ZMod n`. -/
theorem natCast_multiset_sum (n : ℕ) (u : Multiset ℕ) :
    ((u.sum : ℕ) : ZMod n) = (u.map fun (e : ℕ) => (e : ZMod n)).sum := by
  induction u using Multiset.induction_on with
  | empty => simp
  | cons a u ih =>
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, ih]

/-- `(· : ℕ → ZMod (q^k - 1))` is injective on the canonical range `[1, q^k)`. -/
theorem natCast_injOn_range (hk : 2 ≤ k) {a b : ℕ} (ha1 : 1 ≤ a)
    (hab : a < Fintype.card F ^ k) (hb1 : 1 ≤ b) (hbb : b < Fintype.card F ^ k)
    (h : (a : ZMod (Fintype.card F ^ k - 1)) = (b : ZMod (Fintype.card F ^ k - 1))) : a = b := by
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hu : 1 < Fintype.card F ^ k := one_lt_pow₀ hq1 (by omega)
  have key : ∀ {x y : ℕ}, 1 ≤ x → x < Fintype.card F ^ k → 1 ≤ y →
      y < Fintype.card F ^ k →
      (x : ZMod (Fintype.card F ^ k - 1)) = (y : ZMod (Fintype.card F ^ k - 1)) → x ≤ y → x = y := by
    intro x y hx1 hxx hy1 hyy hxy hle
    have hyx : y - x < Fintype.card F ^ k - 1 := by omega
    have hzero : ((y - x : ℕ) : ZMod (Fintype.card F ^ k - 1)) = 0 := by
      have hcast : ((x : ZMod (Fintype.card F ^ k - 1)) +
          ((y - x : ℕ) : ZMod (Fintype.card F ^ k - 1))) = (x : ZMod (Fintype.card F ^ k - 1)) := by
        rw [← Nat.cast_add, show x + (y - x) = y by omega, hxy]
      have h0 : ((x : ZMod (Fintype.card F ^ k - 1)) +
          ((y - x : ℕ) : ZMod (Fintype.card F ^ k - 1))) =
          ((x : ZMod (Fintype.card F ^ k - 1)) + 0) := by
        rw [add_zero]; exact hcast
      exact add_left_cancel h0
    have hdvd : Fintype.card F ^ k - 1 ∣ y - x :=
      (ZMod.natCast_eq_zero_iff (y - x) (Fintype.card F ^ k - 1)).mp hzero
    have hzero' : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hyx
    omega
  rcases le_total a b with hle | hle
  · exact key ha1 hab hb1 hbb h hle
  · exact (key hb1 hbb ha1 hab h.symm hle).symm

/-- The image of `D[q,k]` in `ℤ/(q^k-1)`. -/
def cycD (d : F → ℕ) (k : ℕ) : Finset (ZMod (Fintype.card F ^ k - 1)) :=
  (boseChowlaSet d).image fun (e : ℕ) => (e : ZMod (Fintype.card F ^ k - 1))

omit [Field F] in
theorem mem_cycD {d : F → ℕ} {k : ℕ} {e : ZMod (Fintype.card F ^ k - 1)} :
    e ∈ cycD d k ↔ ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e := by
  simp only [cycD, Finset.mem_image, mem_boseChowlaSet]
  constructor
  · rintro ⟨e', ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨d a, ⟨a, rfl⟩, rfl⟩

/-- **The cyclic Bose–Chowla lemma**: `D[q,k]` is a `B_k`-set modulo `q^k - 1`, i.e. two `k`-term
sums of elements of `D[q,k]` that are congruent modulo `q^k - 1` coincide as multisets. -/
theorem isBkSeq_zmod (hk : 2 ≤ k) (hfin : Module.finrank F E = k)
    (hx : ∀ y : E, y ≠ 0 → ∃ n : ℕ, x ^ n = y) {d : F → ℕ}
    (hd : ∀ a : F, x ^ d a = x + algebraMap F E a)
    (_hrange : ∀ a : F, 1 ≤ d a ∧ d a < Fintype.card F ^ k) :
    BkSet.IsBkSeq k (cycD (F := F) d k) := by
  intro s t hs ht hcs hct hsum
  let sec : ZMod (Fintype.card F ^ k - 1) → ℕ := fun e =>
    if h : ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e then d h.choose else 0
  have hsec_cast : ∀ e : ZMod (Fintype.card F ^ k - 1),
      (∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e) →
      (sec e : ZMod (Fintype.card F ^ k - 1)) = e := by
    intro e he
    have hunf : sec e = (if h : ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e then
        d h.choose else 0) := rfl
    rw [hunf, dite_eq_left he]
    exact he.choose_spec
  have hsec_mem : ∀ e : ZMod (Fintype.card F ^ k - 1),
      (∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e) → sec e ∈ boseChowlaSet d := by
    intro e he
    have hunf : sec e = (if h : ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e then
        d h.choose else 0) := rfl
    rw [hunf, dite_eq_left he]
    exact mem_boseChowlaSet.mpr ⟨he.choose, rfl⟩
  have hex_of_mem : ∀ e ∈ s, ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e :=
    fun e he => mem_cycD.mp (hs e he)
  have hex_of_mem' : ∀ e ∈ t, ∃ a : F, (d a : ZMod (Fintype.card F ^ k - 1)) = e :=
    fun e he => mem_cycD.mp (ht e he)
  have hsmap : (s.map sec).map (fun (e : ℕ) => (e : ZMod (Fintype.card F ^ k - 1))) = s := by
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id s)
    intro e he
    exact hsec_cast e (hex_of_mem e he)
  have htmap : (t.map sec).map (fun (e : ℕ) => (e : ZMod (Fintype.card F ^ k - 1))) = t := by
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id t)
    intro e he
    exact hsec_cast e (hex_of_mem' e he)
  have hs' : ∀ e ∈ s.map sec, e ∈ boseChowlaSet d := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
    exact hsec_mem e₀ (hex_of_mem e₀ he₀)
  have ht' : ∀ e ∈ t.map sec, e ∈ boseChowlaSet d := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
    exact hsec_mem e₀ (hex_of_mem' e₀ he₀)
  have hcs' : (s.map sec).card = k := by rw [Multiset.card_map, hcs]
  have hct' : (t.map sec).card = k := by rw [Multiset.card_map, hct]
  have hcong : ((s.map sec).sum : ℕ) ≡ ((t.map sec).sum : ℕ) [MOD Fintype.card F ^ k - 1] := by
    rw [← ZMod.natCast_eq_natCast_iff, natCast_multiset_sum, natCast_multiset_sum, hsmap, htmap]
    exact hsum
  have hpow : x ^ (s.map sec).sum = x ^ (t.map sec).sum :=
    pow_eq_of_modEq (pow_card_ext_sub_one hfin hx hk) hcong
  have heq : s.map sec = t.map sec := eq_of_pow_sum hfin hx hd hs' ht' hcs' hct' hpow
  calc s = (s.map sec).map (fun (e : ℕ) => (e : ZMod (Fintype.card F ^ k - 1))) := hsmap.symm
    _ = (t.map sec).map (fun (e : ℕ) => (e : ZMod (Fintype.card F ^ k - 1))) := by rw [heq]
    _ = t := htmap

end ModEqSum

end BoseChowla

namespace BoseChowla

/-! ## Base-5 digits: sums of at most four powers of five -/

/-- `wsum u = ∑_{i ∈ u} 5 ^ i`. -/
def wsum (u : Multiset ℕ) : ℕ := (u.map fun i => 5 ^ i).sum

@[simp]
theorem wsum_zero : wsum 0 = 0 := rfl

theorem wsum_cons (a : ℕ) (u : Multiset ℕ) : wsum (a ::ₘ u) = 5 ^ a + wsum u := by
  simp [wsum]

/-- The elements of `u` that are equal to `0`. -/
def zeros (u : Multiset ℕ) : Multiset ℕ := u.filter (fun x => x = 0)

/-- The nonzero elements of `u`, decreased by one. -/
def unshift (u : Multiset ℕ) : Multiset ℕ := (u.filter fun x => x ≠ 0).map fun x => x - 1

theorem zeros_cons_zero (u : Multiset ℕ) : zeros ((0 : ℕ) ::ₘ u) = 0 ::ₘ zeros u := by
  simp [zeros]

theorem zeros_cons_of_ne {a : ℕ} (ha : a ≠ 0) (u : Multiset ℕ) :
    zeros (a ::ₘ u) = zeros u := by
  simp [zeros, ha]

theorem unshift_cons_zero (u : Multiset ℕ) : unshift ((0 : ℕ) ::ₘ u) = unshift u := by
  simp [unshift]

theorem unshift_cons_of_ne {a : ℕ} (ha : a ≠ 0) (u : Multiset ℕ) :
    unshift (a ::ₘ u) = (a - 1) ::ₘ unshift u := by
  simp [unshift, ha, Multiset.map_cons]

theorem zeros_eq_of_card_eq {u v : Multiset ℕ} (h : (zeros u).card = (zeros v).card) :
    zeros u = zeros v := by
  have hu : zeros u = Multiset.replicate (zeros u).card 0 :=
    Multiset.eq_replicate_card.mpr (fun b hb => (Multiset.mem_filter.mp hb).2)
  have hv : zeros v = Multiset.replicate (zeros v).card 0 :=
    Multiset.eq_replicate_card.mpr (fun b hb => (Multiset.mem_filter.mp hb).2)
  rw [hu, hv, h]

theorem wsum_eq (u : Multiset ℕ) : wsum u = (zeros u).card + 5 * wsum (unshift u) := by
  induction u using Multiset.induction_on with
  | empty => simp [zeros, unshift]
  | cons a u ih =>
      rcases eq_or_ne a 0 with rfl | ha
      · rw [wsum_cons, zeros_cons_zero, unshift_cons_zero, Multiset.card_cons, pow_zero]
        omega
      · rw [wsum_cons, zeros_cons_of_ne ha, unshift_cons_of_ne ha, wsum_cons]
        have h5 : 5 ^ a = 5 * 5 ^ (a - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)]
          rw [pow_succ, mul_comm]
        omega

theorem card_zeros_le (u : Multiset ℕ) : (zeros u).card ≤ u.card :=
  Multiset.card_le_card (Multiset.filter_le (fun x => x = 0) u)

theorem card_unshift_le (u : Multiset ℕ) : (unshift u).card ≤ u.card := by
  rw [unshift, Multiset.card_map]
  exact Multiset.card_le_card (Multiset.filter_le (fun x => x ≠ 0) u)

theorem zeros_add_unshift : ∀ u : Multiset ℕ,
    zeros u + (unshift u).map (fun x => x + 1) = u := by
  intro u
  induction u using Multiset.induction_on with
  | empty => rfl
  | cons a u ih =>
      rcases eq_or_ne a 0 with rfl | ha
      · rw [zeros_cons_zero, unshift_cons_zero, Multiset.cons_add, ih]
      · rw [zeros_cons_of_ne ha, unshift_cons_of_ne ha, Multiset.map_cons]
        have h3 : a - 1 + 1 = a := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)
        rw [h3, Multiset.add_cons, ih]

theorem wsum_mod_five {u : Multiset ℕ} (h : u.card ≤ 4) : wsum u % 5 = (zeros u).card := by
  have h1 : (zeros u).card ≤ 4 := le_trans (card_zeros_le u) h
  have h2 := wsum_eq u
  rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem unshift_lt {u : Multiset ℕ} {K : ℕ} (h : ∀ x ∈ u, x < K + 1) :
    ∀ x ∈ unshift u, x < K := by
  intro x hx
  rw [unshift, Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ∈ u := (Multiset.mem_filter.mp hy).1
  have hy2 : y ≠ 0 := (Multiset.mem_filter.mp hy).2
  have := h y hy1
  omega

/-- **Base-5 uniqueness**: a sum of at most four powers of `5` with exponents below `K` determines
the multiset of exponents. -/
theorem wsum_inj : ∀ (K : ℕ) (u v : Multiset ℕ), u.card ≤ 4 → v.card ≤ 4 →
    (∀ x ∈ u, x < K) → (∀ x ∈ v, x < K) → wsum u = wsum v → u = v := by
  intro K
  induction K with
  | zero =>
      intro u v _ _ hu hv _
      have hu' : u = 0 := by
        by_contra hne
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
        have := hu x hx
        omega
      have hv' : v = 0 := by
        by_contra hne
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
        have := hv x hx
        omega
      rw [hu', hv']
  | succ K ih =>
      intro u v hu hv hb hb' h
      have hzc : (zeros u).card = (zeros v).card := by
        rw [← wsum_mod_five hu, ← wsum_mod_five hv, h]
      have hzc' : wsum u = (zeros u).card + 5 * wsum (unshift u) := wsum_eq u
      have hzv' : wsum v = (zeros v).card + 5 * wsum (unshift v) := wsum_eq v
      have hmul : wsum (unshift u) = wsum (unshift v) := by
        have hh : (zeros u).card + 5 * wsum (unshift u)
            = (zeros v).card + 5 * wsum (unshift v) := by
          rw [← hzc', ← hzv']
          exact h
        rw [hzc] at hh
        exact Nat.mul_left_cancel (by norm_num) (Nat.add_left_cancel hh)
      have hun : unshift u = unshift v :=
        ih _ _ (le_trans (card_unshift_le u) hu) (le_trans (card_unshift_le v) hv)
          (unshift_lt hb) (unshift_lt hb') hmul
      rw [← zeros_add_unshift u, ← zeros_add_unshift v, zeros_eq_of_card_eq hzc, hun]

theorem le_pow_five (x : ℕ) : x ≤ 5 ^ x := by
  induction x with
  | zero => simp
  | succ k ih =>
      have hpos : 0 < 5 ^ k := pow_pos (by norm_num) k
      rw [pow_succ]
      nlinarith

/-- **Base-5 uniqueness for four summands**: a sum of four powers of `5` determines the multiset of
exponents. -/
theorem wsum_inj_four {u v : Multiset ℕ} (hu : u.card = 4) (hv : v.card = 4)
    (h : wsum u = wsum v) : u = v := by
  have key : ∀ x ∈ u, x < wsum u + 1 := by
    intro x hx
    have h1 : 5 ^ x ≤ wsum u := by
      rw [wsum]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hx)
    have h2 := le_pow_five x
    omega
  have key' : ∀ x ∈ v, x < wsum u + 1 := by
    intro x hx
    have h1 : 5 ^ x ≤ wsum v := by
      rw [wsum]
      exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hx)
    have h2 := le_pow_five x
    omega
  exact wsum_inj _ u v (by omega) (by omega) key key' h

/-! ## The Bose–Chowla set over `GF(q ^ 2)`: the concrete instance `D[q,2]` -/

section Inst
variable (q : ℕ) [Fact q.Prime]

theorem primitive_of_galois :
    ∃ x : GaloisField q 2, ∀ y : GaloisField q 2, y ≠ 0 → ∃ n : ℕ, x ^ n = y := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField q 2)ˣ)
  refine ⟨(g : GaloisField q 2), fun y hy => ?_⟩
  obtain ⟨n, hn⟩ : Units.mk0 y hy ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    exact hg _
  exact ⟨n, by simpa using congrArg Units.val hn⟩

theorem exists_bc_data :
    ∃ (x : GaloisField q 2) (d : ZMod q → ℕ),
      Module.finrank (ZMod q) (GaloisField q 2) = 2 ∧
      (∀ y : GaloisField q 2, y ≠ 0 → ∃ m : ℕ, x ^ m = y) ∧
      (∀ a : ZMod q, x ^ d a = x + algebraMap (ZMod q) (GaloisField q 2) a) ∧
      (∀ a : ZMod q, 1 ≤ d a ∧ d a < Fintype.card (ZMod q) ^ 2) ∧
      BkSet.IsBkSeq 2 (cycD (F := ZMod q) d 2) ∧
      (cycD (F := ZMod q) d 2).card = Fintype.card (ZMod q) := by
  obtain ⟨x, hx⟩ := primitive_of_galois q
  have hfin : Module.finrank (ZMod q) (GaloisField q 2) = 2 :=
    GaloisField.finrank q (n := 2) (by norm_num)
  obtain ⟨d, hd, hrange, -, -⟩ := exists_isBkSeq_range (F := ZMod q) (E := GaloisField q 2)
    (x := x) (k := 2) hfin hx (by norm_num)
  refine ⟨x, d, hfin, hx, hd, hrange, ?_, ?_⟩
  · exact isBkSeq_zmod (F := ZMod q) (E := GaloisField q 2) (x := x) (k := 2) (by norm_num)
      hfin hx hd hrange
  · refine (Finset.card_image_of_injOn ?_).trans (card hd)
    intro u hu v hv huv
    obtain ⟨a, rfl⟩ := mem_boseChowlaSet.mp hu
    obtain ⟨b, rfl⟩ := mem_boseChowlaSet.mp hv
    exact natCast_injOn_range (F := ZMod q) (k := 2) (by norm_num) (a := d a) (b := d b)
      (hrange a).1 (hrange a).2 (hrange b).1 (hrange b).2 huv

end Inst


/-! ## Pairing uniqueness for `B'`

The next two lemmas are the combinatorial core of the Sidon property of the set `B'` in Theorem 5.
Suppose that four `2`-element multisets of indices `p1, p2, p3, p4` below `M` satisfy
`p1 + p2 = p3 + p4`, and that two of their sums are congruent modulo `M` while the multisets share an
element.  Then the pairings `{p1, p2}` and `{p3, p4}` coincide: a "cross" pairing of the same four
indices is excluded because it would produce two congruent `2`-term sums of the `B_2`-set `D`.
-/


variable {M : ℕ}

theorem eq_of_sum_modEq_of_shared {p q : Multiset ℕ} (hp : p.card = 2) (hq : q.card = 2)
    (hpM : ∀ y ∈ p, y < M) (hqM : ∀ y ∈ q, y < M) (hsum : p.sum ≡ q.sum [MOD M])
    {x : ℕ} (hxp : x ∈ p) (hxq : x ∈ q) : p = q := by
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hp
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hq
  have haM : a < M := hpM a (by simp)
  have hbM : b < M := hpM b (by simp)
  have hcM : c < M := hqM c (by simp)
  have hdM : d < M := hqM d (by simp)
  have hsum' : a + b ≡ c + d [MOD M] := by simpa using hsum
  have hxp' : x = a ∨ x = b := by simpa using hxp
  have hxq' : x = c ∨ x = d := by simpa using hxq
  rcases hxp' with hxa | hxb <;> rcases hxq' with hxc | hxd
  · have hbd : b = d := by
      refine Nat.ModEq.eq_of_lt_of_lt ?_ hbM hdM
      have h := hsum'
      rw [← hxa, ← hxc] at h
      exact Nat.ModEq.add_left_cancel' x h
    rw [← hxa, ← hxc, hbd]
  · have hbc : b = c := by
      refine Nat.ModEq.eq_of_lt_of_lt ?_ hbM hcM
      have h := hsum'
      rw [← hxa, ← hxd, add_comm x b] at h
      exact Nat.ModEq.add_right_cancel' x h
    rw [← hxa, ← hxd, hbc]
    exact Multiset.pair_comm x c
  · have had : a = d := by
      refine Nat.ModEq.eq_of_lt_of_lt ?_ haM hdM
      have h := hsum'
      rw [← hxb, ← hxc, add_comm a x] at h
      exact Nat.ModEq.add_left_cancel' x h
    rw [← hxb, ← hxc, had]
    exact Multiset.pair_comm d x
  · have hac : a = c := by
      refine Nat.ModEq.eq_of_lt_of_lt ?_ haM hcM
      have h := hsum'
      rw [← hxb, ← hxd] at h
      exact Nat.ModEq.add_right_cancel' x h
    rw [← hxb, ← hxd, hac]

theorem pairing_eq_of_sum {p1 p2 p3 p4 : Multiset ℕ}
    (h1 : p1.card = 2) (h2 : p2.card = 2) (h3 : p3.card = 2) (h4 : p4.card = 2)
    (b1 : ∀ x ∈ p1, x < M) (_b2 : ∀ x ∈ p2, x < M) (b3 : ∀ x ∈ p3, x < M)
    (b4 : ∀ x ∈ p4, x < M) (hU : p1 + p2 = p3 + p4)
    (hs : p1.sum ≡ p3.sum [MOD M] ∨ p1.sum ≡ p4.sum [MOD M]) :
    ({p1, p2} : Multiset (Multiset ℕ)) = {p3, p4} := by
  have h3le : p3 ≤ p1 + p2 := by rw [hU]; exact Multiset.le_add_right p3 p4
  have h4le : p4 ≤ p1 + p2 := by rw [hU]; exact Multiset.le_add_left p4 p3
  rcases hs with hs | hs
  · by_cases hshare : ∃ x, x ∈ p1 ∧ x ∈ p3
    · obtain ⟨x, hx1, hx3⟩ := hshare
      have h13 : p1 = p3 := eq_of_sum_modEq_of_shared h1 h3 b1 b3 hs hx1 hx3
      have h24 : p2 = p4 := by
        have h := hU
        rw [h13] at h
        exact add_left_cancel h
      rw [h13, h24]
    · have h32 : p3 = p2 := by
        refine Multiset.eq_of_le_of_card_le ?_ (by omega)
        rw [Multiset.le_iff_count]
        intro x
        have hle : p3.count x ≤ (p1 + p2).count x := by
          rw [Multiset.le_iff_count] at h3le
          exact h3le x
        rw [Multiset.count_add] at hle
        by_cases hx : x ∈ p1
        · have hzero : p3.count x = 0 := by
            by_contra hne
            exact hshare ⟨x, hx, Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)⟩
          omega
        · have hzero : p1.count x = 0 := by
            by_contra hne
            exact hx (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
          omega
      have h41 : p4 = p1 := by
        have h := hU
        rw [h32, add_comm p1 p2] at h
        exact (add_left_cancel h).symm
      rw [h32, h41, Multiset.pair_comm]
  · by_cases hshare : ∃ x, x ∈ p1 ∧ x ∈ p4
    · obtain ⟨x, hx1, hx4⟩ := hshare
      have h14 : p1 = p4 := eq_of_sum_modEq_of_shared h1 h4 b1 b4 hs hx1 hx4
      have h23 : p2 = p3 := by
        have h := hU
        rw [h14, add_comm p4 p2] at h
        exact add_right_cancel h
      rw [h14, h23]
      exact Multiset.pair_comm p4 p3
    · have h42 : p4 = p2 := by
        refine Multiset.eq_of_le_of_card_le ?_ (by omega)
        rw [Multiset.le_iff_count]
        intro x
        have hle : p4.count x ≤ (p1 + p2).count x := by
          rw [Multiset.le_iff_count] at h4le
          exact h4le x
        rw [Multiset.count_add] at hle
        by_cases hx : x ∈ p1
        · have hzero : p4.count x = 0 := by
            by_contra hne
            exact hshare ⟨x, hx, Multiset.count_pos.mp (Nat.pos_of_ne_zero hne)⟩
          omega
        · have hzero : p1.count x = 0 := by
            by_contra hne
            exact hx (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
          omega
      have h31 : p3 = p1 := by
        have h := hU
        rw [h42] at h
        exact (add_right_cancel h).symm
      rw [h42, h31]

end BoseChowla

end

namespace Theorem5

open Theorem4


open Theorem4

/-! ### The base-5 `B₄`-set `A r = {5^r + 5^i | i < r}` -/

/-- The `B₄`-set `A r = {5^r + 5^i | i < r}`, which lies in `[5^r, 2 * 5^r)`. -/
def A (r : ℕ) : Finset ℕ := (Finset.range r).image fun i => 5 ^ r + 5 ^ i

theorem mem_A {r x : ℕ} : x ∈ A r ↔ ∃ i < r, x = 5 ^ r + 5 ^ i := by
  simp only [A, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h.symm⟩⟩

theorem A_card (r : ℕ) : (A r).card = r := by
  have hinj : ∀ i ∈ Finset.range r, ∀ j ∈ Finset.range r,
      5 ^ r + 5 ^ i = 5 ^ r + 5 ^ j → i = j := by
    intro i _ j _ h
    exact Nat.pow_right_injective (a := 5) (by norm_num) (Nat.add_left_cancel h)
  rw [A, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- The base-5 digit of an element of `A r`: if `x = 5^r + 5^i` then `dig r x = i`. -/
def dig (r x : ℕ) : ℕ := Nat.log 5 (x - 5 ^ r)

theorem dig_shift {r i : ℕ} (_hi : i < r) : dig r (5 ^ r + 5 ^ i) = i := by
  rw [dig, Nat.add_sub_cancel_left, Nat.log_pow (by norm_num)]

theorem dig_lt {r x : ℕ} (hx : x ∈ A r) : dig r x < r := by
  obtain ⟨i, hi, rfl⟩ := mem_A.mp hx
  rw [dig_shift hi]; exact hi

theorem shift_dig {r x : ℕ} (hx : x ∈ A r) : 5 ^ r + 5 ^ (dig r x) = x := by
  obtain ⟨i, hi, rfl⟩ := mem_A.mp hx
  rw [dig_shift hi]

theorem A_ge {r x : ℕ} (hx : x ∈ A r) : 5 ^ r ≤ x := by
  obtain ⟨i, -, rfl⟩ := mem_A.mp hx
  exact Nat.le_add_right _ _

theorem A_lt {r x : ℕ} (hx : x ∈ A r) : x < 2 * 5 ^ r := by
  obtain ⟨i, hi, rfl⟩ := mem_A.mp hx
  have h : 5 ^ i < 5 ^ r := Nat.pow_lt_pow_right (by norm_num) hi
  have : 0 < 5 ^ r := by positivity
  omega

/-! ### Sums of four shifted powers of five -/

theorem wsum_add (u v : Multiset ℕ) :
    BoseChowla.wsum (u + v) = BoseChowla.wsum u + BoseChowla.wsum v := by
  induction u using Multiset.induction_on with
  | empty => simp
  | cons a u ih => rw [Multiset.cons_add, BoseChowla.wsum_cons, BoseChowla.wsum_cons, ih]; ring

theorem sum_map_shift (N : ℕ) (u : Multiset ℕ) :
    (u.map (fun i => N + 5 ^ i)).sum = u.card * N + BoseChowla.wsum u := by
  induction u using Multiset.induction_on with
  | empty => simp
  | cons a u ih => rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih,
      BoseChowla.wsum_cons]; ring

theorem sum_inj_shift {N : ℕ} {u v : Multiset ℕ} (hu : u.card = 4) (hv : v.card = 4)
    (h : (u.map (fun i => N + 5 ^ i)).sum = (v.map (fun i => N + 5 ^ i)).sum) : u = v := by
  rw [sum_map_shift, sum_map_shift, hu, hv] at h
  have h' : BoseChowla.wsum u = BoseChowla.wsum v := by omega
  exact BoseChowla.wsum_inj_four hu hv h'

theorem map_dig_map {r : ℕ} {u : Multiset ℕ} (hu : ∀ x ∈ u, x ∈ A r) :
    (u.map (dig r)).map (fun i => 5 ^ r + 5 ^ i) = u := by
  rw [Multiset.map_map]
  refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
  intro x hx
  exact shift_dig (hu x hx)

/-- **`A r` is a `B₄`-set.** -/
theorem A_isBkSeq (r : ℕ) : BkSet.IsBkSeq 4 (A r) := by
  intro s t hs ht hcs hct hsum
  have hs' := map_dig_map hs
  have ht' := map_dig_map ht
  have h1 : (s.map (dig r)).card = 4 := by rw [Multiset.card_map, hcs]
  have h2 : (t.map (dig r)).card = 4 := by rw [Multiset.card_map, hct]
  have h3 : ((s.map (dig r)).map (fun i => 5 ^ r + 5 ^ i)).sum
      = ((t.map (dig r)).map (fun i => 5 ^ r + 5 ^ i)).sum := by rw [hs', ht']; exact hsum
  rw [← hs', ← ht', sum_inj_shift h1 h2 h3]


/-! ## Extending an addition chain

A chain computing `A` can be extended one step at a time to compute a set all of whose elements are
sums of two already computed values; this is how the proof passes from `A` to `B ⊆ B' ⊆ A + A`.
-/


open Theorem4

/-- Extend an addition chain by one value which is the sum of two available values. -/
theorem AddChain.exists_append {c : AddChain} {A : Finset ℕ} (hc : c.Computes A) {v : ℕ}
    (hv : ∃ x z : ℕ, (x = 1 ∨ ∃ j < c.L, c.y j = x) ∧ (z = 1 ∨ ∃ j < c.L, c.y j = z) ∧
      v = x + z) :
    ∃ c' : AddChain, c'.L = c.L + 1 ∧ c'.Computes (insert v A) := by
  classical
  obtain ⟨x, z, hx, hz, hxz⟩ := hv
  set y' : ℕ → ℕ := fun k => if k < c.L then c.y k else v with hy'
  have hy'_lt : ∀ j < c.L, y' j = c.y j := by intro j hj; simp [hy', hj]
  have hy'_last : y' c.L = v := by simp [hy']
  have hpool : ∀ (k : ℕ), k ≤ c.L → ∀ u : Option (Fin k), npPool y' k u = npPool c.y k u := by
    intro k hk u
    rcases u with _ | ⟨j, hj⟩
    · rfl
    · simp only [npPool_some]
      exact hy'_lt j (lt_of_lt_of_le hj hk)
  have hval : ∀ k < c.L + 1, ∃ u w : Option (Fin k), y' k = npPool y' k u + npPool y' k w := by
    intro k hk
    rcases lt_or_ge k c.L with hk1 | hk1
    · obtain ⟨u, w, huw⟩ := c.valid k hk1
      refine ⟨u, w, ?_⟩
      have hp := hpool k (le_of_lt hk1)
      rw [hy'_lt k hk1, huw, hp u, hp w]
    · have hkc : k = c.L := by omega
      subst hkc
      have avail : ∀ y : ℕ, (y = 1 ∨ ∃ j < c.L, c.y j = y) → ∃ u : Option (Fin c.L),
          npPool y' c.L u = y := by
        intro y hy
        rcases hy with rfl | ⟨j, hj, rfl⟩
        · exact ⟨none, rfl⟩
        · exact ⟨some ⟨j, hj⟩, by simp only [npPool_some]; exact hy'_lt j hj⟩
      obtain ⟨u, hu⟩ := avail x hx
      obtain ⟨w, hw⟩ := avail z hz
      exact ⟨u, w, by rw [hy'_last, hxz, hu, hw]⟩
  let c' : AddChain := { L := c.L + 1, y := y', valid := hval }
  have hc'L : c'.L = c.L + 1 := rfl
  have hc'y : ∀ k, c'.y k = y' k := fun k => rfl
  refine ⟨c', hc'L, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hbA
  · exact Or.inr ⟨c.L, by omega, by rw [hc'y]; exact hy'_last⟩
  · rcases hc b hbA with rfl | ⟨j, hj, hyj⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨j, by omega, by rw [hc'y, hy'_lt j hj]; exact hyj⟩

/-- A sequence of values, each the sum of two values already available, gives an upper bound on
`setL`. -/
theorem setL_le_of_seq (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (f : ℕ → ℕ) :
    ∀ n : ℕ, (∀ k < n, ∃ x z : ℕ, (x = 1 ∨ x ∈ A ∨ ∃ j < k, f j = x) ∧
        (z = 1 ∨ z ∈ A ∨ ∃ j < k, f j = z) ∧ f k = x + z) →
      setL (A ∪ (Finset.range n).image f) ≤ setL A + n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.image_empty, Finset.union_empty, Nat.add_zero]
    exact le_rfl
  | succ n ih =>
    intro hf
    have hfn : ∀ k < n, ∃ x z : ℕ, (x = 1 ∨ x ∈ A ∨ ∃ j < k, f j = x) ∧
        (z = 1 ∨ z ∈ A ∨ ∃ j < k, f j = z) ∧ f k = x + z := fun k hk => hf k (by omega)
    have hstep : setL (A ∪ (Finset.range n).image f) ≤ setL A + n := ih hfn
    have fpos : ∀ k < n, 1 ≤ f k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ihk =>
        intro hk
        obtain ⟨x, z, hx, hz, hxz⟩ := hf k (by omega)
        have hx1 : 1 ≤ x := by
          rcases hx with rfl | hxA | ⟨j, hj, rfl⟩
          · exact le_rfl
          · exact hA x hxA
          · exact ihk j hj (by omega)
        have hz1 : 1 ≤ z := by
          rcases hz with rfl | hzA | ⟨j, hj, rfl⟩
          · exact le_rfl
          · exact hA z hzA
          · exact ihk j hj (by omega)
        rw [hxz]; omega
    have hA1 : ∀ a ∈ A ∪ (Finset.range n).image f, 1 ≤ a := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hA a ha
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
        exact fpos j (Finset.mem_range.mp hj)
    obtain ⟨c, hcL, hcc⟩ := exists_optimal hA1
    obtain ⟨x, z, hx, hz, hxz⟩ := hf n (by omega)
    have havail : ∃ x z : ℕ, (x = 1 ∨ ∃ j < c.L, c.y j = x) ∧
        (z = 1 ∨ ∃ j < c.L, c.y j = z) ∧ f n = x + z := by
      refine ⟨x, z, ?_, ?_, hxz⟩
      · rcases hx with rfl | hxA | ⟨j, hj, rfl⟩
        · exact Or.inl rfl
        · exact hcc x (Finset.mem_union_left _ hxA)
        · exact hcc (f j) (Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_range.mpr hj)))
      · rcases hz with rfl | hzA | ⟨j, hj, rfl⟩
        · exact Or.inl rfl
        · exact hcc z (Finset.mem_union_left _ hzA)
        · exact hcc (f j) (Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_range.mpr hj)))
    obtain ⟨c', hc'L, hc'c⟩ := AddChain.exists_append hcc havail
    have hset : A ∪ (Finset.range (n + 1)).image f
        = insert (f n) (A ∪ (Finset.range n).image f) := by
      have hrange : Finset.range (n + 1) = insert n (Finset.range n) := by
        ext b
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hrange, Finset.image_insert, Finset.union_insert]
    calc setL (A ∪ (Finset.range (n + 1)).image f)
        = setL (insert (f n) (A ∪ (Finset.range n).image f)) := by rw [hset]
      _ ≤ c'.L := setL_le hc'c
      _ = c.L + 1 := hc'L
      _ = setL (A ∪ (Finset.range n).image f) + 1 := by rw [hcL]
      _ ≤ setL A + n + 1 := by omega

open Theorem4

/-! ### The filtered pair sums `B'` -/

/-- `pval r u = ∑_{i ∈ u} (5^r + 5^i)`: the value attached to an index multiset `u` (a tuple of
elements of `A r`). -/
def pval (r : ℕ) (u : Multiset ℕ) : ℕ := (u.map fun i => 5 ^ r + 5 ^ i).sum

theorem pval_add (r : ℕ) (u v : Multiset ℕ) : pval r (u + v) = pval r u + pval r v := by
  simp only [pval, Multiset.map_add, Multiset.sum_add]

theorem pval_eq (r : ℕ) (u : Multiset ℕ) : pval r u = u.card * 5 ^ r + BoseChowla.wsum u :=
  sum_map_shift (5 ^ r) u

/-- The index multiset of a pair of indices. -/
def pairMs {r : ℕ} (p : Fin r × Fin r) : Multiset ℕ := {p.1.val, p.2.val}

theorem pairMs_card {r : ℕ} (p : Fin r × Fin r) : (pairMs p).card = 2 := by
  simp [pairMs]

theorem pairMs_lt {r : ℕ} (p : Fin r × Fin r) : ∀ x ∈ pairMs p, x < r := by
  intro x hx
  have h : x = p.1.val ∨ x = p.2.val := by simpa [pairMs] using hx
  rcases h with h | h
  · rw [h]; exact p.1.isLt
  · rw [h]; exact p.2.isLt

theorem pairMs_sum {r : ℕ} (p : Fin r × Fin r) : (pairMs p).sum = p.1.val + p.2.val := by
  simp [pairMs]

theorem pval_pairMs {r : ℕ} (p : Fin r × Fin r) :
    pval r (pairMs p) = (5 ^ r + 5 ^ p.1.val) + (5 ^ r + 5 ^ p.2.val) := by
  simp [pval, pairMs]

/-- The pairs of indices whose sum of indices lies in `D`, modulo `r`. -/
def Pairs (r : ℕ) (D : Finset (ZMod r)) : Finset (Fin r × Fin r) :=
  Finset.univ.filter fun p => ((p.1.val + p.2.val : ℕ) : ZMod r) ∈ D

theorem mem_Pairs {r : ℕ} {D : Finset (ZMod r)} {p : Fin r × Fin r} :
    p ∈ Pairs r D ↔ ((p.1.val + p.2.val : ℕ) : ZMod r) ∈ D := by
  simp [Pairs]

/-- The set `B'` of the proof of Theorem 5: all sums `a_i + a_j` of two elements of `A r` whose
index sum is congruent modulo `r` to an element of `D`. -/
def Bp (r : ℕ) (D : Finset (ZMod r)) : Finset ℕ :=
  (Pairs r D).image fun p => pval r (pairMs p)

theorem mem_Bp {r : ℕ} {D : Finset (ZMod r)} {b : ℕ} :
    b ∈ Bp r D ↔ ∃ p ∈ Pairs r D, pval r (pairMs p) = b := by
  simp [Bp]

/-- An element of `B'`, together with a pair of indices producing it. -/
theorem exists_index_of_mem_Bp {r : ℕ} {D : Finset (ZMod r)} {b : ℕ} (hb : b ∈ Bp r D) :
    ∃ q : Multiset ℕ, q.card = 2 ∧ (∀ x ∈ q, x < r) ∧ ((q.sum : ℕ) : ZMod r) ∈ D ∧
      pval r q = b := by
  obtain ⟨p, hp, rfl⟩ := mem_Bp.mp hb
  refine ⟨pairMs p, pairMs_card p, pairMs_lt p, ?_, rfl⟩
  rw [pairMs_sum]
  exact mem_Pairs.mp hp

theorem Bp_ge {r : ℕ} {D : Finset (ZMod r)} {b : ℕ} (hb : b ∈ Bp r D) : 2 * 5 ^ r ≤ b := by
  obtain ⟨p, -, rfl⟩ := mem_Bp.mp hb
  rw [pval_pairMs]
  have h1 : (0 : ℕ) < 5 ^ p.1.val := by positivity
  have h2 : (0 : ℕ) < 5 ^ p.2.val := by positivity
  omega

theorem Bp_lt {r : ℕ} {D : Finset (ZMod r)} {b : ℕ} (hb : b ∈ Bp r D) : b < 4 * 5 ^ r := by
  obtain ⟨p, -, rfl⟩ := mem_Bp.mp hb
  rw [pval_pairMs]
  have h1 : 5 ^ p.1.val < 5 ^ r := Nat.pow_lt_pow_right (by norm_num) p.1.isLt
  have h2 : 5 ^ p.2.val < 5 ^ r := Nat.pow_lt_pow_right (by norm_num) p.2.isLt
  have h3 : 0 < 5 ^ r := by positivity
  omega

/-- `B'` is sum-free: its elements lie in `[2 * 5^r, 4 * 5^r)`, so the sum of two of them is at
least `4 * 5^r`. -/
theorem Bp_sumFree (r : ℕ) (D : Finset (ZMod r)) : SumFree (Bp r D) := by
  intro a ha b hb hab
  have h1 : 2 * 5 ^ r ≤ a := Bp_ge ha
  have h2 : 2 * 5 ^ r ≤ b := Bp_ge hb
  have h3 : a + b < 4 * 5 ^ r := Bp_lt hab
  omega

/-- Every element of `B'` is a sum of two elements of `A r`. -/
theorem Bp_subset_A_add {r : ℕ} {D : Finset (ZMod r)} {b : ℕ} (hb : b ∈ Bp r D) :
    ∃ x ∈ A r, ∃ y ∈ A r, b = x + y := by
  obtain ⟨p, -, rfl⟩ := mem_Bp.mp hb
  rw [pval_pairMs]
  exact ⟨_, mem_A.mpr ⟨p.1.val, p.1.isLt, rfl⟩, _, mem_A.mpr ⟨p.2.val, p.2.isLt, rfl⟩, rfl⟩

open Theorem4

/-- `pval` is injective on `2`-element index multisets below `r`: the sum of two shifted powers of
five determines the two exponents. -/
theorem pval_inj_two {r : ℕ} {u v : Multiset ℕ} (hu : u.card = 2) (hv : v.card = 2)
    (hub : ∀ x ∈ u, x < r) (hvb : ∀ x ∈ v, x < r) (h : pval r u = pval r v) : u = v := by
  rw [pval_eq, pval_eq, hu, hv] at h
  have h' : BoseChowla.wsum u = BoseChowla.wsum v := by omega
  exact BoseChowla.wsum_inj r u v (by omega) (by omega) hub hvb h'

/-- **`B'` is a Sidon set.**  A coincidence of two sums of two elements of `B'` lifts, via the
`B₄` property of `A`, to an equality of the four index multisets; the `B₂` property of `D` then
forces the two pairings to coincide. -/
theorem Bp_isBkSeq (r : ℕ) (D : Finset (ZMod r)) (hD : BkSet.IsBkSeq 2 D) :
    BkSet.IsBkSeq 2 (Bp r D) := by
  intro s t hs ht hcs hct hsum
  obtain ⟨b1, b2, rfl⟩ := Multiset.card_eq_two.mp hcs
  obtain ⟨b3, b4, rfl⟩ := Multiset.card_eq_two.mp hct
  have hb1 : b1 ∈ Bp r D := hs b1 (by simp)
  have hb2 : b2 ∈ Bp r D := hs b2 (by simp)
  have hb3 : b3 ∈ Bp r D := ht b3 (by simp)
  have hb4 : b4 ∈ Bp r D := ht b4 (by simp)
  obtain ⟨q1, hq1c, hq1lt, hq1D, hq1v⟩ := exists_index_of_mem_Bp hb1
  obtain ⟨q2, hq2c, hq2lt, hq2D, hq2v⟩ := exists_index_of_mem_Bp hb2
  obtain ⟨q3, hq3c, hq3lt, hq3D, hq3v⟩ := exists_index_of_mem_Bp hb3
  obtain ⟨q4, hq4c, hq4lt, hq4D, hq4v⟩ := exists_index_of_mem_Bp hb4
  have hsum' : b1 + b2 = b3 + b4 := by simpa using hsum
  -- Step 1: the four index multisets satisfy the same `4`-term sum
  have hpq : q1 + q2 = q3 + q4 := by
    have hval : pval r (q1 + q2) = pval r (q3 + q4) := by
      rw [pval_add, pval_add, hq1v, hq2v, hq3v, hq4v, hsum']
    have hc4 : (q1 + q2).card = 4 := by rw [Multiset.card_add, hq1c, hq2c]
    have hc4' : (q3 + q4).card = 4 := by rw [Multiset.card_add, hq3c, hq4c]
    have hw : BoseChowla.wsum (q1 + q2) = BoseChowla.wsum (q3 + q4) := by
      have h1 := pval_eq r (q1 + q2)
      have h2 := pval_eq r (q3 + q4)
      rw [hc4] at h1
      rw [hc4'] at h2
      omega
    exact BoseChowla.wsum_inj_four hc4 hc4' hw
  -- Step 2: the index sums are congruent mod `r`, because `D` is a `B₂`-set
  have hsumZ : ((q1.sum : ℕ) : ZMod r) + ((q2.sum : ℕ) : ZMod r)
      = ((q3.sum : ℕ) : ZMod r) + ((q4.sum : ℕ) : ZMod r) := by
    have h : (q1 + q2).sum = (q3 + q4).sum := by rw [hpq]
    rw [Multiset.sum_add, Multiset.sum_add] at h
    rw [← Nat.cast_add, ← Nat.cast_add, h]
  have memD : ∀ {a b : ZMod r}, a ∈ D → b ∈ D →
      ∀ x ∈ ({a, b} : Multiset (ZMod r)), x ∈ D := by
    intro a b ha hb x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha
    · rw [Multiset.mem_singleton.mp hx]; exact hb
  have hpairD : ({((q1.sum : ℕ) : ZMod r), ((q2.sum : ℕ) : ZMod r)} : Multiset (ZMod r))
      = {((q3.sum : ℕ) : ZMod r), ((q4.sum : ℕ) : ZMod r)} :=
    hD _ _ (memD hq1D hq2D) (memD hq3D hq4D) (by simp) (by simp) (by simpa using hsumZ)
  have hmod : q1.sum ≡ q3.sum [MOD r] ∨ q1.sum ≡ q4.sum [MOD r] := by
    have hmem : ((q1.sum : ℕ) : ZMod r) ∈
        ({((q3.sum : ℕ) : ZMod r), ((q4.sum : ℕ) : ZMod r)} : Multiset (ZMod r)) := by
      rw [← hpairD]; simp
    rcases Multiset.mem_cons.mp hmem with h | h
    · exact Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
    · exact Or.inr ((ZMod.natCast_eq_natCast_iff _ _ _).mp (Multiset.mem_singleton.mp h))
  -- Step 3: the pairing of the four indices is determined
  have hpair := BoseChowla.pairing_eq_of_sum hq1c hq2c hq3c hq4c
    hq1lt hq2lt hq3lt hq4lt hpq hmod
  have hfin : ({b1, b2} : Multiset ℕ) = {b3, b4} := by
    have h := congrArg (fun x : Multiset (Multiset ℕ) => x.map (pval r)) hpair
    simpa [hq1v, hq2v, hq3v, hq4v] using h
  exact hfin

theorem pairMs_eq {a b c d : ℕ} (h : ({a, b} : Multiset ℕ) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Multiset ℕ) := h ▸ (by simp)
  rcases Multiset.mem_cons.mp ha with hac | had
  · refine Or.inl ⟨hac, ?_⟩
    have h' : ({b} : Multiset ℕ) = {d} := by
      have hh := h
      rw [← hac] at hh
      exact (Multiset.cons_inj_right a).mp (by simpa using hh)
    exact Multiset.singleton_inj.mp h'
  · have had' : a = d := Multiset.mem_singleton.mp had
    refine Or.inr ⟨had', ?_⟩
    have h' : b = c := by
      have hh := h
      rw [← had'] at hh
      rw [Multiset.pair_comm a b] at hh
      exact (Multiset.cons_inj_left ({a} : Multiset ℕ)).mp (by simpa using hh)
    exact h'

theorem card_pairs_fiber (r : ℕ) [NeZero r] (D : Finset (ZMod r)) (i : Fin r) :
    (Finset.filter (fun p : Fin r × Fin r => p.1 = i) (Pairs r D)).card = D.card := by
  classical
  refine Finset.card_bij (fun p _ => ((p.1.val + p.2.val : ℕ) : ZMod r)) ?_ ?_ ?_
  · intro p hp
    exact mem_Pairs.mp (Finset.mem_filter.mp hp).1
  · intro p1 hp1 p2 hp2 heq
    have h1 : p1.1 = p2.1 := by rw [(Finset.mem_filter.mp hp1).2, (Finset.mem_filter.mp hp2).2]
    have hmod : p1.1.val + p1.2.val ≡ p2.1.val + p2.2.val [MOD r] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
    rw [h1] at hmod
    have h2 : p1.2 = p2.2 := Fin.ext <| Nat.ModEq.eq_of_lt_of_lt
      (Nat.ModEq.add_left_cancel' _ hmod) p1.2.isLt p2.2.isLt
    exact Prod.ext h1 h2
  · intro d hd
    refine ⟨(i, ⟨(d - (i : ZMod r)).val, ZMod.val_lt _⟩), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, rfl⟩
      rw [mem_Pairs]
      rw [show ((i.val + (d - (i : ZMod r)).val : ℕ) : ZMod r) = d from by
        rw [Nat.cast_add, show ((i.val : ℕ) : ZMod r) = (i : ZMod r) from rfl,
          ZMod.natCast_zmod_val, add_sub_cancel]]
      exact hd
    · exact show ((i.val + (d - (i : ZMod r)).val : ℕ) : ZMod r) = d from by
        rw [Nat.cast_add, show ((i.val : ℕ) : ZMod r) = (i : ZMod r) from rfl,
          ZMod.natCast_zmod_val, add_sub_cancel]

theorem card_Pairs (r : ℕ) [NeZero r] (D : Finset (ZMod r)) : (Pairs r D).card = r * D.card := by
  classical
  calc (Pairs r D).card
      = ∑ i : Fin r, (Finset.filter (fun p : Fin r × Fin r => p.1 = i) (Pairs r D)).card :=
        Finset.card_eq_sum_card_fiberwise (f := fun p : Fin r × Fin r => p.1)
          (t := Finset.univ) (fun p _ => Finset.mem_univ _)
    _ = ∑ _i : Fin r, D.card := Finset.sum_congr rfl (fun i _ => card_pairs_fiber r D i)
    _ = r * D.card := by simp [Finset.card_univ]

theorem card_fiber_le_two (r : ℕ) (D : Finset (ZMod r)) (b : ℕ) :
    (Finset.filter (fun p : Fin r × Fin r => pval r (pairMs p) = b) (Pairs r D)).card ≤ 2 := by
  classical
  by_cases hne : (Finset.filter (fun p : Fin r × Fin r => pval r (pairMs p) = b)
      (Pairs r D)).card = 0
  · omega
  · obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    have hp0' := Finset.mem_filter.mp hp0
    have hsub : Finset.filter (fun p : Fin r × Fin r => pval r (pairMs p) = b) (Pairs r D)
        ⊆ {p0, (p0.2, p0.1)} := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpv : pval r (pairMs p) = pval r (pairMs p0) := by rw [hp'.2, hp0'.2]
      have hEq : pairMs p = pairMs p0 :=
        pval_inj_two (pairMs_card p) (pairMs_card p0) (pairMs_lt p) (pairMs_lt p0) hpv
      rcases pairMs_eq (by simpa [pairMs] using hEq) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Finset.mem_insert.mpr (Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h2)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (Prod.ext (Fin.ext h1) (Fin.ext h2))))
    have h1 := Finset.card_le_card hsub
    have h2 : ({p0, (p0.2, p0.1)} : Finset (Fin r × Fin r)).card ≤ 2 := by
      have hle := Finset.card_insert_le p0 ({(p0.2, p0.1)} : Finset (Fin r × Fin r))
      simp at hle
      omega
    omega

theorem two_mul_card_Bp_ge (r : ℕ) [NeZero r] (D : Finset (ZMod r)) :
    r * D.card ≤ 2 * (Bp r D).card := by
  have h := Finset.card_le_mul_card_image (s := Pairs r D)
    (f := fun p => pval r (pairMs p)) 2 (fun b _ => card_fiber_le_two r D b)
  rwa [card_Pairs r D] at h

/-! ### Addition chains for `A r` -/

theorem setL_mono {A B : Finset ℕ} (h : A ⊆ B) (hB : ∀ b ∈ B, 1 ≤ b) : setL A ≤ setL B := by
  obtain ⟨c, hcL, hcc⟩ := exists_optimal hB
  rw [← hcL]
  exact setL_le (hcc.mono h)

/-- Inserting a value which is the sum of two available values lengthens a shortest chain by at
most one. -/
theorem setL_insert_le {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) {v : ℕ}
    (hv : ∃ x z : ℕ, (x = 1 ∨ x ∈ S) ∧ (z = 1 ∨ z ∈ S) ∧ v = x + z) :
    setL (insert v S) ≤ setL S + 1 := by
  obtain ⟨c, hcL, hcc⟩ := exists_optimal hS
  obtain ⟨x, z, hx, hz, hxz⟩ := hv
  have havail : ∃ x z : ℕ, (x = 1 ∨ ∃ j < c.L, c.y j = x) ∧
      (z = 1 ∨ ∃ j < c.L, c.y j = z) ∧ v = x + z := by
    refine ⟨x, z, ?_, ?_, hxz⟩
    · rcases hx with rfl | hxS
      · exact Or.inl rfl
      · exact hcc x hxS
    · rcases hz with rfl | hzS
      · exact Or.inl rfl
      · exact hcc z hzS
  obtain ⟨c', hc'L, hc'c⟩ := AddChain.exists_append hcc havail
  calc setL (insert v S) ≤ c'.L := setL_le hc'c
    _ = c.L + 1 := hc'L
    _ = setL S + 1 := by rw [hcL]

/-- Adding `B.card` values, each a sum of two elements of `A`, lengthens a chain for `A` by at most
`B.card`. -/
theorem setL_le_add_card {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) :
    ∀ B : Finset ℕ, (∀ b ∈ B, ∃ x ∈ A, ∃ y ∈ A, b = x + y) →
      setL (A ∪ B) ≤ setL A + B.card := by
  intro B
  induction B using Finset.induction_on with
  | empty => intro _; simp
  | insert b B hb ih =>
    intro hB
    have hB' : ∀ b' ∈ B, ∃ x ∈ A, ∃ y ∈ A, b' = x + y :=
      fun b' hb' => hB b' (Finset.mem_insert_of_mem hb')
    have hpos : ∀ a ∈ A ∪ B, 1 ≤ a := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hA a ha
      · obtain ⟨x, hxA, y, hyA, rfl⟩ := hB' a ha
        have h1 := hA x hxA
        have h2 := hA y hyA
        omega
    obtain ⟨c, hcL, hcc⟩ := exists_optimal hpos
    obtain ⟨x, hxA, y, hyA, hxy⟩ := hB b (Finset.mem_insert_self b B)
    have havail : ∃ x z : ℕ, (x = 1 ∨ ∃ j < c.L, c.y j = x) ∧
        (z = 1 ∨ ∃ j < c.L, c.y j = z) ∧ b = x + z := by
      refine ⟨x, y, ?_, ?_, hxy⟩
      · exact hcc x (Finset.mem_union_left _ hxA)
      · exact hcc y (Finset.mem_union_left _ hyA)
    obtain ⟨c', hc'L, hc'c⟩ := AddChain.exists_append hcc havail
    have hcard : (insert b B).card = B.card + 1 := Finset.card_insert_of_notMem hb
    have hset : A ∪ insert b B = insert b (A ∪ B) := by
      ext u
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hstep := ih hB'
    calc setL (A ∪ insert b B) = setL (insert b (A ∪ B)) := by rw [hset]
      _ ≤ c'.L := setL_le hc'c
      _ = c.L + 1 := hc'L
      _ = setL (A ∪ B) + 1 := by rw [hcL]
      _ ≤ setL A + B.card + 1 := by omega
      _ = setL A + (insert b B).card := by rw [hcard]; ring

/-- The set of powers `{5^i | i ≤ r}`. -/
def powSet (r : ℕ) : Finset ℕ := (Finset.range (r + 1)).image fun i => 5 ^ i

theorem mem_powSet {r i : ℕ} : 5 ^ i ∈ powSet r ↔ i ≤ r := by
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
    rw [Finset.mem_range] at hj
    have hji' : j = i := Nat.pow_right_injective (a := 5) (by norm_num) hji
    omega
  · intro hi
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem one_le_powSet {r a : ℕ} (ha : a ∈ powSet r) : 1 ≤ a := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  have : 0 < 5 ^ i := by positivity
  omega

/-- The powers `5^1, …, 5^r` are computed in `3 r` additions by successive multiplication by `5`
as `5 x = 4 x + x`. -/
theorem setL_powSet_le (r : ℕ) : setL (powSet r) ≤ 3 * r := by
  induction r with
  | zero =>
      have h : powSet 0 = {1} := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
          rw [Finset.mem_range] at hi
          rw [Finset.mem_singleton]
          rw [← hix]
          have hi0 : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
          rw [hi0, pow_zero]
        · intro hx
          rw [Finset.mem_singleton] at hx
          rw [hx, show (1 : ℕ) = 5 ^ 0 by rw [pow_zero]]
          exact mem_powSet.mpr (by omega)
      rw [h]
      have hc : (⟨0, fun (_ : ℕ) => 0,
          by intro k hk; exact absurd hk (Nat.not_lt_zero k)⟩ : AddChain).Computes
          ({1} : Finset ℕ) := by
        intro a ha
        rw [Finset.mem_singleton] at ha
        exact Or.inl ha
      calc setL {1} ≤ _ := setL_le hc
        _ = 0 := rfl
  | succ r ih =>
      have h1 : 1 ≤ 5 ^ r := by
        have : 0 < 5 ^ r := by positivity
        omega
      have hmem : 5 ^ r ∈ powSet r := mem_powSet.mpr le_rfl
      have step1 : setL (insert (2 * 5 ^ r) (powSet r)) ≤ setL (powSet r) + 1 :=
        setL_insert_le (fun a ha => one_le_powSet ha)
          ⟨5 ^ r, 5 ^ r, Or.inr hmem, Or.inr hmem, by ring⟩
      have hmem2 : 2 * 5 ^ r ∈ insert (2 * 5 ^ r) (powSet r) :=
        Finset.mem_insert_self _ _
      have hpos2 : ∀ a ∈ insert (2 * 5 ^ r) (powSet r), 1 ≤ a := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · omega
        · exact one_le_powSet ha
      have step2 : setL (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r)))
          ≤ setL (insert (2 * 5 ^ r) (powSet r)) + 1 :=
        setL_insert_le hpos2
          ⟨2 * 5 ^ r, 2 * 5 ^ r, Or.inr hmem2, Or.inr hmem2, by ring⟩
      have hmem3 : 4 * 5 ^ r ∈ insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r)) :=
        Finset.mem_insert_self _ _
      have hmem4 : 5 ^ r ∈ insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r)) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)
      have hpos3 : ∀ a ∈ insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r)), 1 ≤ a := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · omega
        · exact hpos2 a ha
      have step3 : setL (insert (5 ^ (r + 1)) (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r))))
          ≤ setL (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r))) + 1 :=
        setL_insert_le hpos3
          ⟨4 * 5 ^ r, 5 ^ r, Or.inr hmem3, Or.inr hmem4, by rw [pow_succ]; ring⟩
      have hsub : powSet (r + 1) ⊆
          insert (5 ^ (r + 1)) (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r))) := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        rw [Finset.mem_range] at hi
        rcases Nat.lt_or_ge i (r + 1) with hlt | hge
        · rcases Nat.lt_or_ge i r with hlt' | hge'
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem (mem_powSet.mpr (by omega))))
          · have hir : i = r := by omega
            subst hir
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_insert_of_mem hmem))
        · have hir : i = r + 1 := by omega
          subst hir
          exact Finset.mem_insert_self _ _
      calc setL (powSet (r + 1))
          ≤ setL (insert (5 ^ (r + 1)) (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r)))) :=
            setL_mono hsub (by
              intro a ha
              rcases Finset.mem_insert.mp ha with rfl | ha
              · have : 0 < 5 ^ (r + 1) := by positivity
                omega
              rcases Finset.mem_insert.mp ha with rfl | ha
              · omega
              rcases Finset.mem_insert.mp ha with rfl | ha
              · omega
              · exact one_le_powSet ha)
        _ ≤ setL (insert (4 * 5 ^ r) (insert (2 * 5 ^ r) (powSet r))) + 1 := step3
        _ ≤ (setL (insert (2 * 5 ^ r) (powSet r)) + 1) + 1 := by omega
        _ ≤ ((setL (powSet r) + 1) + 1) + 1 := by omega
        _ ≤ 3 * (r + 1) := by omega

/-- `A r` is computed by a chain of length at most `4 r`: first the powers `5^i`, then the sums
`5^r + 5^i`. -/
theorem setL_A_le (r : ℕ) : setL (A r) ≤ 4 * r := by
  have hA : ∀ a ∈ powSet r, 1 ≤ a := fun a ha => one_le_powSet ha
  have hB : ∀ b ∈ A r, ∃ x ∈ powSet r, ∃ y ∈ powSet r, b = x + y := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := mem_A.mp hb
    exact ⟨5 ^ r, mem_powSet.mpr le_rfl, 5 ^ i, mem_powSet.mpr (by omega), rfl⟩
  have h := setL_le_add_card hA (A r) hB
  rw [A_card] at h
  have hsub : A r ⊆ powSet r ∪ A r := fun x hx => Finset.mem_union_right _ hx
  have hpos : ∀ a ∈ powSet r ∪ A r, 1 ≤ a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact one_le_powSet ha
    · obtain ⟨i, -, rfl⟩ := mem_A.mp ha
      have : 0 < 5 ^ r := by positivity
      have : 0 < 5 ^ i := by positivity
      omega
  have hmono := setL_mono hsub hpos
  have hp := setL_powSet_le r
  omega

/-- For every `m ≥ 2` there is a prime `q` with `m ≤ q² < 4 m`: take the prime between `√m` and
`2√m` given by Bertrand's postulate. -/
theorem exists_prime_sq_between (m : ℕ) (hm : 2 ≤ m) :
    ∃ q : ℕ, q.Prime ∧ m ≤ q ^ 2 ∧ q ^ 2 < 4 * m := by
  set s := Nat.sqrt m with hs
  have hs2 : s ^ 2 ≤ m := Nat.sqrt_le' m
  have hlt : m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' m
  rcases lt_or_eq_of_le hs2 with hstr | heq
  · have hs1 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · rw [h0] at hlt
        simp at hlt
        omega
      · exact hpos
    obtain ⟨q, hq, hqs, hq2s⟩ := Nat.exists_prime_lt_and_le_two_mul s (by omega)
    have hqge : s + 1 ≤ q := hqs
    refine ⟨q, hq, ?_, ?_⟩
    · exact le_of_lt (calc m < (s + 1) ^ 2 := hlt
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hqge 2)
    · have h1 : q ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left hq2s 2
      have h2 : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
      nlinarith [hstr, h1, h2]
  · have hs2' : 2 ≤ s := by
      have h : 2 ≤ s ^ 2 := heq ▸ hm
      by_contra hcon
      have h1 : s ≤ 1 := by omega
      have h2 : s ^ 2 ≤ 1 := by
        have := Nat.pow_le_pow_left h1 2
        simpa using this
      omega
    obtain ⟨q, hq, hqs, hq2s⟩ := Nat.exists_prime_lt_and_le_two_mul (s - 1) (by omega)
    have hqge : s ≤ q := by omega
    refine ⟨q, hq, ?_, ?_⟩
    · calc m = s ^ 2 := heq.symm
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hqge 2
    · rw [← heq]
      have h1 : q ^ 2 ≤ (2 * (s - 1)) ^ 2 := Nat.pow_le_pow_left hq2s 2
      have hlt' : (s - 1) ^ 2 < s ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      have h3 : (2 * (s - 1)) ^ 2 = 4 * (s - 1) ^ 2 := by ring
      nlinarith [h1, hlt', h3]

set_option maxHeartbeats 2000000 in
/-- **Theorem 5, combinatorial core.**  If `16 n² ≤ m³` and `m ≥ 2`, there is a sum-free Sidon set
`B` of cardinality `n` with `L(B) ≤ n + 16 m`. -/
theorem theorem5_core (m n : ℕ) (hm : 2 ≤ m) (hn : 16 * n ^ 2 ≤ m ^ 3) :
    ∃ B : Finset ℕ, SumFree B ∧ BkSet.IsBkSeq 2 B ∧ B.card = n ∧ setL B ≤ n + 16 * m := by
  obtain ⟨q, hq, hmq, hq4m⟩ := exists_prime_sq_between m hm
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨_, d, _, _, _, _, hD, hDcard⟩ := BoseChowla.exists_bc_data q
  set r := Fintype.card (ZMod q) ^ 2 - 1 with hrdef
  have hrq : r = q ^ 2 - 1 := by rw [hrdef, ZMod.card]
  have hq2 : 2 ≤ q := hq.two_le
  have hrpos : 0 < r := by
    rw [hrq]
    have hq22 : 2 ≤ q ^ 2 := by nlinarith
    omega
  have : NeZero r := ⟨by omega⟩
  have hrq' : r * q = q ^ 3 - q := by
    rw [hrq, Nat.sub_mul, one_mul]
    have h : q ^ 2 * q = q ^ 3 := by ring
    rw [h]
  -- `4 n ≤ q³`
  have h4n : 4 * n ≤ q ^ 3 := by
    have h1 : (4 * n) ^ 2 ≤ (q ^ 3) ^ 2 := by
      calc (4 * n) ^ 2 = 16 * n ^ 2 := by ring
        _ ≤ m ^ 3 := hn
        _ ≤ (q ^ 2) ^ 3 := Nat.pow_le_pow_left hmq 3
        _ = (q ^ 3) ^ 2 := by ring
    have hs := Nat.sqrt_le_sqrt h1
    rwa [Nat.sqrt_eq', Nat.sqrt_eq'] at hs
  have hq2sq : 2 ≤ q ^ 2 := by nlinarith
  -- `2 n ≤ r q`
  have h2n : 2 * n ≤ r * q := by
    rw [hrq']
    have h7 : 2 * n + q ≤ q ^ 3 := by nlinarith
    have h6 : q ≤ q ^ 3 := by nlinarith
    omega
  -- cardinality of `B'`
  have htwo := two_mul_card_Bp_ge r (BoseChowla.cycD (F := ZMod q) d 2)
  rw [hDcard, ZMod.card, hrq'] at htwo
  have hnle : n ≤ (Bp r (BoseChowla.cycD (F := ZMod q) d 2)).card := by omega
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hnle
  refine ⟨B, ?_, ?_, hBcard, ?_⟩
  · intro a ha b hb hab
    exact Bp_sumFree r (BoseChowla.cycD (F := ZMod q) d 2) a (hBsub ha) b (hBsub hb) (hBsub hab)
  · exact isBkSeq_subset (Bp_isBkSeq r (BoseChowla.cycD (F := ZMod q) d 2) hD) hBsub
  · have hposA : ∀ a ∈ A r, 1 ≤ a := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := mem_A.mp ha
      have h1 : 0 < 5 ^ r := by positivity
      have h2 : 0 < 5 ^ i := by positivity
      omega
    have hBsum : ∀ b ∈ B, ∃ x ∈ A r, ∃ y ∈ A r, b = x + y :=
      fun b hb => Bp_subset_A_add (hBsub hb)
    have hstep := setL_le_add_card hposA B hBsum
    have hmono : setL B ≤ setL (A r ∪ B) := by
      refine setL_mono (fun x hx => Finset.mem_union_right _ hx) ?_
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hposA x hx
      · obtain ⟨y, hy, z, hz, rfl⟩ := hBsum x hx
        have h1 := hposA y hy
        have h2 := hposA z hz
        omega
    have hA := setL_A_le r
    have hr16 : r ≤ 4 * m := by omega
    omega

/-- **Theorem 5** (Sergeev, Math. Notes 2024): for every `n` there is a sum-free Sidon set `B` with
`|B| = n` and `L(B) = n + O(n^(2/3))`; here with the explicit bound `n + 96 (n+1)^(2/3)`. -/
theorem theorem5 (n : ℕ) :
    ∃ B : Finset ℕ, SumFree B ∧ BkSet.IsBkSeq 2 B ∧ B.card = n ∧
      (setL B : ℝ) ≤ (n : ℝ) + 96 * ((n : ℝ) + 1) ^ (2 / 3 : ℝ) := by
  set c := ⌈((n : ℝ) + 1) ^ (2 / 3 : ℝ)⌉₊ with hcdef
  have hxpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx1 : 1 ≤ ((n : ℝ) + 1) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxpos _)
  have hm : 2 ≤ 3 * c := by omega
  have hle_c : ((n : ℝ) + 1) ^ (2 / 3 : ℝ) ≤ (c : ℝ) := by
    rw [hcdef]
    exact Nat.le_ceil _
  have hR : (16 : ℝ) * (n : ℝ) ^ 2 ≤ 27 * (c : ℝ) ^ 3 := by
    have hcube : (((n : ℝ) + 1) ^ (2 / 3 : ℝ)) ^ (3 : ℝ) = ((n : ℝ) + 1) ^ 2 := by
      rw [← Real.rpow_mul (le_of_lt hxpos) (2 / 3 : ℝ) (3 : ℝ)]
      norm_num
    have hle : (((n : ℝ) + 1) ^ (2 / 3 : ℝ)) ^ (3 : ℝ) ≤ (c : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hxpos) _) hle_c (by norm_num)
    have hc3 : (c : ℝ) ^ (3 : ℝ) = (c : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [hcube, hc3] at hle
    nlinarith
  have hn : 16 * n ^ 2 ≤ (3 * c) ^ 3 := by
    have h3 : (3 * c) ^ 3 = 27 * c ^ 3 := by ring
    rw [h3]
    exact_mod_cast hR
  obtain ⟨B, hsf, hsid, hcard, hL⟩ := theorem5_core (3 * c) n hm hn
  refine ⟨B, hsf, hsid, hcard, ?_⟩
  have hLr : (setL B : ℝ) ≤ (n : ℝ) + 16 * ((3 * c : ℕ) : ℝ) := by exact_mod_cast hL
  push_cast at hLr
  have hcu : (c : ℝ) < ((n : ℝ) + 1) ^ (2 / 3 : ℝ) + 1 := by
    rw [hcdef]
    exact Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hxpos _))
  linarith

/-- The shape stated in the paper: for `n ≥ 1`, `L(B) ≤ n + O(n^(2/3))`, here with the explicit
constant `192`. -/
theorem theorem5_of_one_le (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : Finset ℕ, SumFree B ∧ BkSet.IsBkSeq 2 B ∧ B.card = n ∧
      (setL B : ℝ) ≤ (n : ℝ) + 192 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨B, hsf, hsid, hcard, hL⟩ := theorem5 n
  refine ⟨B, hsf, hsid, hcard, ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hshift : ((n : ℝ) + 1) ^ (2 / 3 : ℝ) ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h1 : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
    have h2 : ((n : ℝ) + 1) ^ (2 / 3 : ℝ) ≤ (2 * (n : ℝ)) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (2 * (n : ℝ)) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h4 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      simpa using h
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (2 / 3 : ℝ)]
  linarith

end Theorem5
